"""
Pelagic — Cross-Platform Prediction Market Trading Bot
"""

import os
import re
import uuid
import math
import atexit
import base64
import datetime
try:
    from zoneinfo import ZoneInfo
    _PACIFIC = ZoneInfo("America/Los_Angeles")
except ImportError:
    _PACIFIC = datetime.timezone(datetime.timedelta(hours=-7))  # fallback PDT
import requests
import xml.etree.ElementTree as ET
from html import unescape as html_unescape
from urllib.parse import quote_plus
from difflib import SequenceMatcher
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError
from flask import Flask, jsonify, request
from flask_cors import CORS
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.backends import default_backend
app = Flask(__name__)
CORS(app)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
KALSHI_API_KEY_ID = os.environ.get("KALSHI_API_KEY_ID", "b5321140-8a40-47f5-a99e-edff618c887c")
KALSHI_BASE_URL   = "https://api.elections.kalshi.com"
KALSHI_API_PREFIX  = "/trade-api/v2"
PRIVATE_KEY_PEM = os.environ.get("KALSHI_PRIVATE_KEY", "")
DISCORD_WEBHOOK_URL = os.environ.get("DISCORD_WEBHOOK_URL", "")

PLATFORM_FEES = {
    "kalshi":     0.07,
    "polymarket": 0.02,
    "predictit":  0.10,
    "manifold":   0.00,
}

STOP_WORDS = {
    "will", "the", "a", "an", "be", "in", "on", "at", "to", "of", "by",
    "for", "is", "it", "do", "does", "did", "has", "have", "had", "was",
    "were", "been", "being", "are", "this", "that", "these", "those",
    "before", "after", "during", "from", "with", "or", "and", "not", "no",
    "yes", "if", "than", "what", "who", "how", "when", "where", "which",
}

TIMEOUT = 8

# ---------------------------------------------------------------------------
# Bot version — tags every trade so we can separate old vs new performance
BOT_VERSION = "v3.0-quant"  # v1=yolo, v2=disciplined, v3=quant engine
BOT_VERSION_DATE = "2026-03-15"

# Bot configuration and state
# ---------------------------------------------------------------------------
BOT_CONFIG = {
    "enabled": True,  # default ON — safety floor will auto-disable if needed
    "max_bet_usd": 25.0,          # max $25 per single trade — let Kelly size up on high-edge bets
    "max_daily_usd": 150.0,        # max $150/day — scales with bankroll via smart sizing
    "min_balance_usd": 250.0,     # SAFETY FLOOR: stop all trading if cash below $250
    "min_cash_reserve_pct": 0.05, # keep 5% of portfolio in cash — legacy positions skew ratio
    "max_open_positions": 150,    # high limit — legacy positions settling, bot uses daily trade cap instead
    "min_deviation": 0.08,        # 8% mispricing — catch more edges
    "min_platforms": 1,           # single platform OK — MoonShark is our main strategy
    "min_volume": 50,             # include smaller markets
    "scan_interval_seconds": 45,  # faster scanning during game hours
    "max_category_exposure": 3,   # max 3 positions per category — diversified
    "blocked_categories": ["weather", "golf", "politics", "economics", "nfl"],  # block proven losers: golf 0/18, politics 0/4, economics 0/2, NFL offseason
    "blocked_keywords": ["title holder", "title on dec", "prime minister", "next president", "ipo first", "gas price", "billboard", "netflix", "spotify", "golf", "pga", "lpga", "masters", "election", "congress", "senate", "governor"],  # block long-dated + losing categories
    "moonshark_enabled": True,  # MoonShark longshot sniper toggle
}

BOT_STATE = {
    "last_scan": None,
    "last_scan_markets": 0,
    "last_scan_mispriced": 0,
    "trades_today": [],
    "daily_spent_usd": 0.0,
    "trade_date": None,
    "all_trades": [],
    "errors": [],
    "pick_history": [],  # every pick we recommend, timestamped
    "activity_log": [],  # live feed of bot actions (last 50)
}

def _send_discord(msg, color=0x00dc5a):
    """Send a Discord webhook notification. Non-blocking, fire-and-forget."""
    if not DISCORD_WEBHOOK_URL:
        return
    try:
        import threading as _th
        def _send():
            try:
                requests.post(DISCORD_WEBHOOK_URL, json={
                    "embeds": [{
                        "description": msg[:2000],
                        "color": color,
                        "footer": {"text": "TradeShark 🦈"},
                        "timestamp": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                    }]
                }, timeout=5)
            except Exception:
                pass
        _th.Thread(target=_send, daemon=True).start()
    except Exception:
        pass

# Discord alert levels — only important events get pushed
_DISCORD_TRIGGERS = {
    "MOONSHARK HIT": 0x00d4ff,    # cyan — new bet placed
    "CLOSEGAME HIT": 0xffd700,    # gold — close game bet
    "ARB HIT": 0x00ff00,          # green — free money
    "BLOWOUT EXIT": 0xff5000,     # orange — cutting losses
    "WIN": 0x00dc5a,              # green — game won
    "LOSS": 0xff3333,             # red — game lost
    "MOMENTUM": 0xffb400,         # yellow — momentum shift
    "LEAD CHANGE": 0xff00ff,      # purple — our team took lead
    "PRICE MOVE": 0x7a7aff,       # blue — significant price change
}


def _log_activity(msg, level="info"):
    """Add a timestamped message to the activity log. Deduplicates consecutive identical messages."""
    log = BOT_STATE["activity_log"]
    # Skip if last message is identical (prevents duplicates from concurrent threads)
    if log and log[-1].get("msg") == msg:
        return
    log.append({
        "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        "msg": msg,
        "level": level,
    })
    BOT_STATE["activity_log"] = log[-50:]
    # Push important events to Discord
    for trigger, color in _DISCORD_TRIGGERS.items():
        if trigger in msg.upper():
            _send_discord(msg, color)
            break

import json as _json

_STATE_FILE = "/tmp/tradeshark_state.json"

# Cumulative tracking — declared early so _load_state() can populate them.
# The later sections that reference these will use the same objects (not re-assign).
_TRADE_JOURNAL = []  # List of enriched trade records with full metadata
_CATEGORY_STATS = {}  # {cat: {"wins": 0, "losses": 0, "pnl": 0.0}}
_LEARNING_STATE = {
    "last_run": None,
    "version": 0,
    "parameters": {},  # learned thresholds/weights per dimension
    "insights": [],    # human-readable learning outputs
}

def _save_state():
    """Persist trade data to disk.
    NOTE: /tmp does NOT survive Railway deploys. This cache only helps within a
    single deployment (e.g. dyno restarts).  On fresh deploy, _hydrate_from_kalshi()
    and _rebuild_journal_from_kalshi() rebuild from the Kalshi API as source of truth.
    """
    try:
        data = {
            "all_trades": BOT_STATE["all_trades"],
            "trades_today": BOT_STATE["trades_today"],
            "daily_spent_usd": BOT_STATE["daily_spent_usd"],
            "trade_date": BOT_STATE["trade_date"],
            "pick_history": BOT_STATE.get("pick_history", [])[-500:],  # keep last 500
            # Persist trade journal & category stats so they survive in-deployment restarts
            "trade_journal": _TRADE_JOURNAL[-500:],  # keep last 500 journal entries
            "category_stats": _CATEGORY_STATS,
            # Persist snipe daily counters
            "snipe_daily_spent": BOT_STATE.get("snipe_daily_spent", 0.0),
            "snipe_trades_today": BOT_STATE.get("snipe_trades_today", []),
            "snipe_date": BOT_STATE.get("snipe_date"),
            # Persist MoonShark daily counters
            "moonshark_daily_spent": BOT_STATE.get("moonshark_daily_spent", 0.0),
            "moonshark_trades_today": BOT_STATE.get("moonshark_trades_today", []),
            "moonshark_date": BOT_STATE.get("moonshark_date"),
            # Persist manual trades today
            "manual_trades_today": BOT_STATE.get("manual_trades_today", []),
            # Learning engine state
            "learning_state": _LEARNING_STATE,
            # Timestamp for date-check on load
            "save_date": datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d"),
        }
        with open(_STATE_FILE, "w") as f:
            _json.dump(data, f)
    except Exception as e:
        print(f"[STATE] Save error: {e}")

def _load_state():
    """Restore trade data from disk, then hydrate from Kalshi fills API."""
    global _TRADE_JOURNAL, _CATEGORY_STATS
    # First try local cache
    try:
        with open(_STATE_FILE, "r") as f:
            data = _json.load(f)
        BOT_STATE["all_trades"] = data.get("all_trades", [])
        BOT_STATE["pick_history"] = data.get("pick_history", [])

        saved_date = data.get("save_date") or data.get("trade_date", None)
        # Use Pacific time consistently (matches MoonShark/Snipe daily reset)
        today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
        is_same_day = (saved_date == today_str)

        # --- Daily counters: reset if new day, restore if same day ---
        if is_same_day:
            BOT_STATE["trades_today"] = data.get("trades_today", [])
            # Restore daily_spent on same-day redeploy so it reflects actual spending
            BOT_STATE["daily_spent_usd"] = data.get("daily_spent_usd", 0.0)
            BOT_STATE["trade_date"] = today_str
            # Restore snipe counters for same-day
            BOT_STATE["snipe_daily_spent"] = data.get("snipe_daily_spent", 0.0)
            BOT_STATE["snipe_trades_today"] = data.get("snipe_trades_today", [])
            BOT_STATE["snipe_date"] = today_str
            # Restore MoonShark counters for same-day
            BOT_STATE["moonshark_daily_spent"] = data.get("moonshark_daily_spent", 0.0)
            BOT_STATE["moonshark_trades_today"] = data.get("moonshark_trades_today", [])
            BOT_STATE["moonshark_date"] = today_str
            # Restore manual trades for same-day
            BOT_STATE["manual_trades_today"] = data.get("manual_trades_today", [])
        else:
            # New day — reset all daily counters
            BOT_STATE["trades_today"] = []
            BOT_STATE["daily_spent_usd"] = 0.0
            BOT_STATE["trade_date"] = today_str
            BOT_STATE["snipe_daily_spent"] = 0.0
            BOT_STATE["snipe_trades_today"] = []
            BOT_STATE["snipe_date"] = today_str
            BOT_STATE["moonshark_daily_spent"] = 0.0
            BOT_STATE["moonshark_trades_today"] = []
            BOT_STATE["moonshark_date"] = today_str
            BOT_STATE["manual_trades_today"] = []

        # --- Cumulative data: always restore regardless of day ---
        saved_journal = data.get("trade_journal", [])
        if saved_journal:
            _TRADE_JOURNAL.clear()
            _TRADE_JOURNAL.extend(saved_journal)
            print(f"[STATE] Restored {len(_TRADE_JOURNAL)} trade journal entries from disk")

        saved_cat_stats = data.get("category_stats", {})
        if saved_cat_stats:
            _CATEGORY_STATS.clear()
            _CATEGORY_STATS.update(saved_cat_stats)
            print(f"[STATE] Restored {len(_CATEGORY_STATS)} category stats from disk")

        saved_learning = data.get("learning_state", {})
        if saved_learning:
            _LEARNING_STATE.clear()
            _LEARNING_STATE.update(saved_learning)
            print(f"[STATE] Restored learning state v{_LEARNING_STATE.get('version', 0)} from disk")

        print(f"[STATE] Restored {len(BOT_STATE['all_trades'])} trades from disk, "
              f"daily_spent reset to $0 for new session, same_day={is_same_day}")
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"[STATE] Load error: {e}")

def _hydrate_from_kalshi():
    """Pull actual trade fills from Kalshi API to rebuild state after deploy."""
    import requests as _req
    try:
        path = "/portfolio/fills"
        headers = signed_headers("GET", path)
        if not headers:
            print("[HYDRATE] No API key — skipping")
            return
        # Paginate to get ALL fills (not just 200)
        fills = []
        cursor = None
        for _page in range(20):  # max 20 pages = 4000 fills
            params = {"limit": 200}
            if cursor:
                params["cursor"] = cursor
            _ph = signed_headers("GET", path)
            resp = _req.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=_ph, params=params, timeout=15,
            )
            if not resp.ok:
                print(f"[HYDRATE] Fills API returned {resp.status_code} on page {_page}")
                break
            fills_data = resp.json()
            page_fills = fills_data.get("fills", [])
            fills.extend(page_fills)
            cursor = fills_data.get("cursor")
            if not cursor or not page_fills:
                break
        print(f"[HYDRATE] Loaded {len(fills)} total fills")
        if fills:
            print(f"[HYDRATE] Sample fill keys: {list(fills[0].keys())}")
        if not fills:
            print("[HYDRATE] No fills found")
            return

        today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
        existing_ids = {t.get("order_id") for t in BOT_STATE["all_trades"] if t.get("order_id")}

        new_count = 0
        today_count = 0
        today_spent = 0.0
        all_trades_rebuilt = []

        for fill in fills:
            order_id = fill.get("order_id", "")
            ticker = fill.get("ticker", "")
            side = fill.get("side", "")
            action = fill.get("action", "buy")
            # Kalshi v2 removed integer count on March 12 2026 — use count_fp string
            count = 0
            try:
                count_raw = fill.get("count_fp") or fill.get("count") or 0
                count = int(float(str(count_raw)))
            except Exception:
                pass
            price_cents = 0
            try:
                yes_price = fill.get("yes_price_dollars") or fill.get("yes_price")
                no_price = fill.get("no_price_dollars") or fill.get("no_price")
                if side == "yes" and yes_price:
                    price_cents = int(round(float(str(yes_price)) * 100))
                elif side == "no" and no_price:
                    price_cents = int(round(float(str(no_price)) * 100))
            except Exception:
                pass

            created = fill.get("created_time", "")
            cost_usd = (price_cents * count) / 100
            # Infer strategy for bot attribution after restart
            _inferred_strategy = None
            _is_today = created and created[:10] == today_str
            _tk_upper = ticker.upper()
            # Sport/event tickers are bot trades (MoonShark)
            _bot_prefixes = ("KXKBL", "KXATP", "KXWTA", "KXNCAA", "KXNBA",
                             "KXNHL", "KXMLB", "KXUFC", "KXMMA", "KXEPL",
                             "KXNFL", "KXMLS", "KXWNBA", "KXSOCCER", "KXPGA")
            if any(_tk_upper.startswith(p) for p in _bot_prefixes):
                _inferred_strategy = "moonshark"
            elif _is_today and action == "buy" and price_cents <= 30:
                _inferred_strategy = "moonshark"
            trade_rec = {
                "timestamp": created,
                "ticker": ticker,
                "side": side,
                "action": action,
                "price_cents": price_cents,
                "count": count,
                "cost_usd": round(cost_usd, 2),
                "order_id": order_id,
                "source": "kalshi_fill",
                "strategy": _inferred_strategy,
                "bot_version": "v1-legacy" if created and created[:10] < BOT_VERSION_DATE else BOT_VERSION,
            }
            all_trades_rebuilt.append(trade_rec)

            # Count today's trades
            if created and created[:10] == today_str and action == "buy":
                today_count += 1
                today_spent += cost_usd

            if order_id not in existing_ids:
                new_count += 1

        # Enrich with market titles (batch unique tickers)
        unique_tickers = list(set(t["ticker"] for t in all_trades_rebuilt if t.get("ticker")))
        title_map = {}
        for tk in unique_tickers[:50]:  # cap at 50 to avoid long startup
            try:
                mkt_path = f"/markets/{tk}"
                mkt_h = signed_headers("GET", mkt_path)
                mkt_r = _req.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + mkt_path, headers=mkt_h, timeout=5)
                if mkt_r.ok:
                    title_map[tk] = mkt_r.json().get("market", {}).get("title", tk)
            except Exception:
                pass
        for t in all_trades_rebuilt:
            if t["ticker"] in title_map:
                t["question"] = title_map[t["ticker"]]
            t["success"] = True  # Kalshi fills are confirmed trades

        # Rebuild state from Kalshi truth
        BOT_STATE["all_trades"] = all_trades_rebuilt
        BOT_STATE["trade_date"] = today_str
        today_trades = [t for t in all_trades_rebuilt if (t.get("timestamp") or "")[:10] == today_str and t.get("action") == "buy"]
        BOT_STATE["trades_today"] = today_trades
        # Rebuild per-strategy daily counters from today's fills so the bot
        # respects daily caps after a deploy (was ignoring pre-deploy trades)
        _ms_today = [t for t in today_trades if t.get("strategy") == "moonshark"]
        _snipe_today = [t for t in today_trades if t.get("strategy") == "snipe"]
        if len(_ms_today) > len(BOT_STATE.get("moonshark_trades_today", [])):
            BOT_STATE["moonshark_trades_today"] = _ms_today
            BOT_STATE["moonshark_daily_spent"] = round(sum(t.get("cost_usd", 0) for t in _ms_today), 2)
            BOT_STATE["moonshark_date"] = today_str
        if len(_snipe_today) > len(BOT_STATE.get("snipe_trades_today", [])):
            BOT_STATE["snipe_trades_today"] = _snipe_today
            BOT_STATE["snipe_daily_spent"] = round(sum(t.get("cost_usd", 0) for t in _snipe_today), 2)
            BOT_STATE["snipe_date"] = today_str
        BOT_STATE["daily_spent_usd"] = round(today_spent, 2)
        # Also seed global event lock with today's events
        for t in today_trades:
            tk = t.get("ticker", "")
            parts = tk.split("-")
            if len(parts) >= 2:
                _EVENTS_BET_TODAY.add("-".join(parts[:2]))
        _save_state()
        print(f"[HYDRATE] Rebuilt {len(all_trades_rebuilt)} trades from Kalshi ({new_count} new), today: {today_count} trades (MS:{len(_ms_today)} SN:{len(_snipe_today)}), ${today_spent:.2f} spent, titles: {len(title_map)}")
    except Exception as e:
        print(f"[HYDRATE] Error: {e}")
        import traceback
        traceback.print_exc()

_load_state()


def _rebuild_journal_from_kalshi():
    """Rebuild _TRADE_JOURNAL and _CATEGORY_STATS from Kalshi settled positions.

    This is the real persistence fix: /tmp doesn't survive Railway deploys, but
    the Kalshi API is the source of truth for all settled positions.  On every
    startup we paginate through ALL settled positions, rebuild the trade journal,
    and recompute category stats.  Only adds entries that aren't already in the
    journal (by ticker), so it's safe to call after _load_state().
    """
    global _TRADE_JOURNAL, _CATEGORY_STATS
    import requests as _req
    try:
        path = "/portfolio/positions"
        headers = signed_headers("GET", path)
        if not headers:
            print("[JOURNAL-REBUILD] No API key — skipping")
            return

        # Paginate all settled positions
        positions_list = []
        cursor = None
        for _ in range(10):  # max 10 pages = 2000 positions
            params = {"limit": 200, "settlement_status": "settled"}
            if cursor:
                params["cursor"] = cursor
            h = signed_headers("GET", path)
            resp = _req.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=h, params=params, timeout=15,
            )
            if not resp.ok:
                print(f"[JOURNAL-REBUILD] API returned {resp.status_code}")
                break
            page = resp.json()
            positions_list.extend(page.get("market_positions", []))
            cursor = page.get("cursor")
            if not cursor:
                break

        if not positions_list:
            print("[JOURNAL-REBUILD] No settled positions found")
            return

        # Tickers already in journal — don't duplicate
        existing_tickers = {r["ticker"] for r in _TRADE_JOURNAL if r.get("ticker")}
        # Also build set of tickers in all_trades for bot_version lookup
        trade_map = {}
        for t in BOT_STATE.get("all_trades", []):
            if t.get("ticker"):
                trade_map[t["ticker"]] = t

        new_count = 0
        # Fetch market titles in batch (cap at 50 unique to avoid slow startup)
        unique_tickers = list(set(
            p.get("ticker", "") for p in positions_list
            if p.get("ticker", "") not in existing_tickers
        ))
        title_map = {}
        for tk in unique_tickers[:50]:
            try:
                mkt_path = f"/markets/{tk}"
                mkt_h = signed_headers("GET", mkt_path)
                mkt_r = _req.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + mkt_path, headers=mkt_h, timeout=5)
                if mkt_r.ok:
                    mkt = mkt_r.json().get("market", {})
                    title_map[tk] = {
                        "title": mkt.get("title", tk),
                        "close_time": mkt.get("close_time", ""),
                    }
            except Exception:
                pass

        # Rebuild category stats from scratch using ALL settled positions
        _CATEGORY_STATS.clear()

        for pos in positions_list:
            ticker = pos.get("ticker", "")
            pnl_cents = _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl"))
            pnl_usd = pnl_cents / 100
            won = pnl_usd > 0

            # Get title from cache or existing trade data
            title = ""
            if ticker in title_map:
                title = title_map[ticker]["title"]
            elif ticker in trade_map:
                title = trade_map[ticker].get("question", "") or trade_map[ticker].get("ticker", "")
            else:
                title = ticker

            # Update category stats for ALL settled positions
            cat = classify_market_category(title, ticker)
            if cat not in _CATEGORY_STATS:
                _CATEGORY_STATS[cat] = {"wins": 0, "losses": 0, "pnl": 0.0}
            if won:
                _CATEGORY_STATS[cat]["wins"] += 1
            else:
                _CATEGORY_STATS[cat]["losses"] += 1
            _CATEGORY_STATS[cat]["pnl"] += pnl_usd

            # Add to journal if not already present
            if ticker in existing_tickers:
                continue

            # Build journal entry from settled position data
            side = pos.get("side", "")
            count = 0
            try:
                count = int(float(str(pos.get("total_count_fp") or pos.get("total_count") or 0)))
            except Exception:
                pass
            entry_cents = 0
            try:
                if side == "yes":
                    entry_cents = int(round(float(str(
                        pos.get("average_yes_price_dollars") or pos.get("average_yes_price") or 0
                    )) * 100))
                else:
                    entry_cents = int(round(float(str(
                        pos.get("average_no_price_dollars") or pos.get("average_no_price") or 0
                    )) * 100))
            except Exception:
                pass
            cost_usd = (entry_cents * count) / 100

            # Determine bot version from trade history
            trade_rec = trade_map.get(ticker, {})
            bot_version = trade_rec.get("bot_version", "v1-legacy")
            strategy = trade_rec.get("strategy", "unknown")
            created = trade_rec.get("timestamp", "")
            close_time = title_map.get(ticker, {}).get("close_time", "")

            journal_entry = {
                "ticker": ticker,
                "title": title,
                "side": side,
                "price_cents": entry_cents,
                "count": count,
                "cost_usd": round(cost_usd, 2),
                "strategy": strategy,
                "category": cat,
                "sport_type": "other",
                "is_live": False,
                "volatility": 0,
                "entry_time": created or close_time or "",
                "entry_hour": 0,
                "entry_day": "",
                "entry_date": (created or "")[:10] if created else "",
                "result": "win" if won else ("loss" if pnl_usd < -0.005 else "even"),
                "pnl_usd": round(pnl_usd, 2),
                "settlement_time": close_time or "",
                "hold_duration_mins": None,
                "price_at_entry": entry_cents,
                "bot_version": bot_version,
                "source": "kalshi_rebuild",
            }
            _TRADE_JOURNAL.append(journal_entry)
            new_count += 1

        _save_state()
        total_cats = len(_CATEGORY_STATS)
        total_journal = len(_TRADE_JOURNAL)
        print(f"[JOURNAL-REBUILD] Rebuilt from {len(positions_list)} settled positions: "
              f"{new_count} new journal entries (total {total_journal}), "
              f"{total_cats} categories tracked")
    except Exception as e:
        print(f"[JOURNAL-REBUILD] Error: {e}")
        import traceback
        traceback.print_exc()


# ---------------------------------------------------------------------------
# Kalshi auth helpers
# ---------------------------------------------------------------------------

def load_private_key():
    pem = PRIVATE_KEY_PEM.strip()
    if not pem:
        print("KALSHI_PRIVATE_KEY environment variable is not set")
        return None
    if not pem.startswith("-----"):
        try:
            pem = base64.b64decode(pem).decode("utf-8")
        except Exception:
            pass
    pem = pem.replace("\\n", "\n")
    if "BEGIN" not in pem and len(pem) > 100:
        raw = pem.replace("\n", "").replace("\r", "").replace(" ", "")
        lines = [raw[i:i+64] for i in range(0, len(raw), 64)]
        pem = "-----BEGIN RSA PRIVATE KEY-----\n" + "\n".join(lines) + "\n-----END RSA PRIVATE KEY-----"
    try:
        return serialization.load_pem_private_key(pem.encode(), password=None, backend=default_backend())
    except Exception as e:
        print(f"Key load error: {e}")
        return None


def sign_pss_text(private_key, text):
    signature = private_key.sign(
        text.encode("utf-8"),
        padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.DIGEST_LENGTH),
        hashes.SHA256(),
    )
    return base64.b64encode(signature).decode("utf-8")


def signed_headers(method, path):
    key = load_private_key()
    if not key:
        return {}
    full_path = KALSHI_API_PREFIX + path
    ts = str(int(datetime.datetime.now().timestamp() * 1000))
    msg_string = ts + method.upper() + full_path.split("?")[0]
    return {
        "KALSHI-ACCESS-KEY":       KALSHI_API_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": ts,
        "KALSHI-ACCESS-SIGNATURE": sign_pss_text(key, msg_string),
        "Content-Type":            "application/json",
    }

# ---------------------------------------------------------------------------
# Parlay detection
# ---------------------------------------------------------------------------

def _is_parlay_title(title):
    """Return True if a market title looks like a multi-leg parlay.
    Kalshi parlays have comma-separated legs like:
      'yes Team A,yes Team B,no Player: 25+'
    Normal titles might contain 'no' or 'yes' naturally, so we look for
    the specific parlay pattern: comma-separated segments starting with yes/no.
    """
    if not title:
        return False
    # Split by comma and check if multiple segments start with yes/no
    segments = [s.strip().lower() for s in title.split(",")]
    leg_count = sum(1 for s in segments if s.startswith("yes ") or s.startswith("no "))
    return leg_count >= 2

# ---------------------------------------------------------------------------
# Sports classification — server-side using ticker prefixes + targeted keywords
# ---------------------------------------------------------------------------

_SPORTS_TICKER_PREFIXES = (
    "KXMVESPORTS", "KXMVECROSS",  # multivariate sports/cross-category parlays
    "KXNBA", "KXNFL", "KXMLB", "KXNHL", "KXNCAA", "KXUFC",
    "KXSOCCER", "KXPGA", "KXNASCAR", "KXTENNIS", "KXMMA", "KXBOXING",
    "KXEPL", "KXCHAMPIONS", "KXFIFA", "KXWNBA", "KXMLS",
)

_SPORTS_TITLE_KEYWORDS = [
    # Leagues
    "nba", "nfl", "mlb", "nhl", "ufc", "ncaa", "nascar", "pga", "wnba", "mls",
    "premier league", "champions league", "la liga", "serie a", "bundesliga",
    # Stats
    "points", "rebounds", "assists", "goals scored", "touchdowns", "strikeouts",
    "home runs", "passing yards", "rushing yards", "receiving yards",
    "wins by", "over under", "spread", "moneyline", "parlay",
    # NBA teams
    "lakers", "celtics", "warriors", "bulls", "heat", "nuggets", "mavericks",
    "clippers", "knicks", "nets", "hawks", "hornets", "wizards", "pacers",
    "pistons", "spurs", "blazers", "suns", "bucks",
    "raptors", "grizzlies", "pelicans", "timberwolves",
    "cavaliers", "76ers", "sixers",
    # NFL teams
    "chiefs", "eagles", "cowboys", "49ers", "ravens", "bills", "dolphins",
    "lions", "bengals", "steelers", "chargers", "packers", "vikings",
    "commanders", "saints", "falcons", "buccaneers",
    "seahawks", "rams", "jaguars", "colts", "texans",
    # MLB teams
    "yankees", "dodgers", "mets", "braves", "astros", "padres", "phillies",
    "cubs", "red sox", "white sox", "orioles", "guardians", "twins", "royals",
    "mariners", "diamondbacks", "marlins",
    "pirates", "brewers",
    # NHL teams
    "oilers", "bruins", "avalanche", "maple leafs",
    "golden knights", "penguins", "flyers",
    "blackhawks", "blue jackets", "red wings", "minnesota wild",
    "canucks", "canadiens", "sabres", "islanders",
    "kraken",
    # Soccer
    "liverpool", "arsenal", "manchester", "chelsea", "bayern", "barcelona",
    "real madrid", "tottenham", "sporting cp",
    # NBA players (distinctive names only — avoid generic surnames)
    "lebron", "jokic", "jokić", "doncic", "dončić", "giannis",
    "embiid", "westbrook", "haliburton", "gilgeous",
    "nikola jokic", "luka doncic", "anthony davis", "kawhi leonard",
    "jalen brunson", "paolo banchero", "bam adebayo", "austin reaves",
    # NFL players (distinctive names only)
    "mahomes", "kelce", "lamar jackson",
    # Tennis (distinctive names)
    "djokovic", "alcaraz", "sinner", "swiatek", "sabalenka",
    # College basketball / football
    "march madness", "ncaa tournament", "final four", "sweet sixteen",
    "elite eight", "round of 32", "round of 64", "championship game",
    "national championship", "college basketball",
    # General sports
    "game 1", "game 2", "game 3", "game 4", "game 5", "game 6", "game 7",
    "playoff", "stanley cup", "super bowl", "world series",
    "the players championship", "masters tournament",
    "win the ", "qualify for the men",  # catches "Will X qualify for the men's..."
]


def _is_sports_market(ticker, event_ticker, title):
    """Classify a Kalshi market as sports or not using ticker prefix + targeted title keywords."""
    t = (ticker or "").upper()
    et = (event_ticker or "").upper()
    for pfx in _SPORTS_TICKER_PREFIXES:
        if t.startswith(pfx) or et.startswith(pfx):
            return True
    lower_title = (title or "").lower()
    # Also catch parlay-style titles (these are sports parlays)
    if _is_parlay_title(title):
        return True
    return any(kw in lower_title for kw in _SPORTS_TITLE_KEYWORDS)


# ---------------------------------------------------------------------------
# Platform fetchers
# ---------------------------------------------------------------------------

def fetch_kalshi():
    """Fetch Kalshi markets: get events first, then fetch their markets."""
    path = "/markets"
    h = signed_headers("GET", "/events")
    if not h:
        return []

    start_time = datetime.datetime.utcnow()

    # Step 1: Get non-parlay event tickers (3 pages for broader coverage)
    event_tickers = []
    cursor = None
    for _ep in range(3):
        try:
            eh = signed_headers("GET", "/events")
            ep = {"limit": 200, "status": "open"}
            if cursor:
                ep["cursor"] = cursor
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/events",
                headers=eh, params=ep, timeout=8,
            )
            if resp.ok:
                evts = resp.json().get("events", [])
                for ev in evts:
                    et = ev.get("event_ticker", "")
                    if not et.upper().startswith("KXMVE"):
                        event_tickers.append(et)
                cursor = resp.json().get("cursor")
                print(f"[FETCH] kalshi events page {_ep+1}: {len(evts)} events, {len(event_tickers)} non-parlay total")
                if not cursor or len(evts) < 200:
                    break
            else:
                print(f"[FETCH] kalshi events: HTTP {resp.status_code}")
                break
        except Exception as e:
            print(f"[FETCH] kalshi events error: {e}")
            break

    # Step 2: Fetch markets for each event (cap at 80 events to stay within time limit)
    raw = []
    fetched_events = 0
    for et in event_tickers[:80]:
        elapsed = (datetime.datetime.utcnow() - start_time).total_seconds()
        if elapsed > 20:
            print(f"[FETCH] kalshi: time limit, fetched {fetched_events}/{len(event_tickers)} events = {len(raw)} markets")
            break
        try:
            mh = signed_headers("GET", path)
            r = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=mh,
                params={"limit": 200, "event_ticker": et, "status": "open"},
                timeout=5,
            )
            if r.ok:
                raw.extend(r.json().get("markets", []))
            fetched_events += 1
        except Exception as e:
            print(f"[FETCH] kalshi event {et}: ERROR {e}")
            fetched_events += 1
            continue

    print(f"[FETCH] kalshi: {len(raw)} markets from {fetched_events} events")

    # Step 3: Fetch markets closing in 2026 using min/max_close_ts
    # This is the KEY fetch — events approach gets long-term markets,
    # but we need short-term ones that settle this year for compounding
    existing_tickers = {m.get("ticker") for m in raw}
    import calendar
    now_ts = int(datetime.datetime.utcnow().timestamp())
    end_2026_ts = int(datetime.datetime(2026, 12, 31, 23, 59, 59).timestamp())
    close_cursor = None
    short_term_added = 0
    try:
        for close_page in range(5):  # up to 1000 short-term markets
            mh = signed_headers("GET", path)
            close_params = {
                "limit": 200,
                "status": "open",
                "min_close_ts": now_ts,
                "max_close_ts": end_2026_ts,
            }
            if close_cursor:
                close_params["cursor"] = close_cursor
            cr = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=mh, params=close_params, timeout=8,
            )
            if cr.ok:
                close_mkts = cr.json().get("markets", [])
                close_cursor = cr.json().get("cursor")
                added = 0
                for cm in close_mkts:
                    tk = cm.get("ticker", "")
                    if tk not in existing_tickers:
                        raw.append(cm)
                        existing_tickers.add(tk)
                        added += 1
                short_term_added += added
                print(f"[FETCH] kalshi 2026-markets page {close_page+1}: +{added} new ({len(close_mkts)} total on page)")
                if not close_cursor or len(close_mkts) < 200:
                    break
            else:
                print(f"[FETCH] kalshi 2026-markets: HTTP {cr.status_code} - {cr.text[:200]}")
                break
    except Exception as e:
        print(f"[FETCH] kalshi 2026-markets error: {e}")
    print(f"[FETCH] kalshi: +{short_term_added} short-term 2026 markets added")

    # Fallback: if events approach yielded nothing, do a simple paginated fetch
    if not raw:
        print("[FETCH] kalshi: events approach yielded 0, trying direct pagination")
        cursor = None
        for page_num in range(3):
            try:
                mh = signed_headers("GET", "/markets")
                params = {"limit": 1000, "status": "open"}
                if cursor:
                    params["cursor"] = cursor
                r = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                    headers=mh, params=params, timeout=10,
                )
                if not r.ok:
                    print(f"[FETCH] kalshi fallback page {page_num+1}: HTTP {r.status_code}")
                    break
                data = r.json()
                raw.extend(data.get("markets", []))
                cursor = data.get("cursor")
                print(f"[FETCH] kalshi fallback page {page_num+1}: {len(raw)} total markets")
                if not cursor:
                    break
            except Exception as e:
                print(f"[FETCH] kalshi fallback error: {e}")
                break
    print(f"[FETCH] kalshi: processing {len(raw)} raw markets")
    out = []
    skipped_parlays = 0
    for m in raw:
        try:
            event_ticker = m.get("event_ticker", "")
            # Skip multivariate (parlay) markets — they start with KXMVE
            if event_ticker.upper().startswith("KXMVE"):
                skipped_parlays += 1
                continue
            # Also skip if title looks like a parlay
            title = m.get("title") or ""
            if _is_parlay_title(title):
                skipped_parlays += 1
                continue
            # Handle Kalshi API field names — v2 uses _dollars suffix with string values
            def _dollars_to_cents(field_names):
                """Try multiple field names, convert dollar string to cents."""
                for fn in field_names:
                    v = m.get(fn)
                    if v is not None:
                        if isinstance(v, str):
                            try:
                                return max(0, int(round(float(v) * 100)))
                            except:
                                continue
                        elif isinstance(v, (int, float)):
                            return int(v) if v > 1 else int(round(v * 100))
                return None

            yes_ask = _dollars_to_cents(["yes_ask_dollars", "yes_ask"])
            no_ask = _dollars_to_cents(["no_ask_dollars", "no_ask"])
            last_price = _dollars_to_cents(["last_price_dollars", "last_price"])
            if yes_ask is None:
                yes_ask = last_price if last_price is not None else 50
            if no_ask is None:
                no_ask = 100 - yes_ask
            yes = yes_ask / 100
            no  = no_ask / 100
            ticker = m["ticker"]
            # Volume: try multiple field names
            vol_raw = m.get("volume") or m.get("volume_fp") or m.get("volume_24h_fp") or "0"
            vol = int(float(vol_raw))
            # Capture YES/NO subtitles so the UI can explain what each side means
            yes_label = m.get("yes_sub_title") or m.get("yes_subtitle") or "Yes"
            no_label = m.get("no_sub_title") or m.get("no_subtitle") or "No"
            out.append({
                "platform": "kalshi",
                "id":       ticker,
                "ticker":   ticker,
                "question": m.get("title") or ticker,
                "yes":      round(yes, 4),
                "no":       round(no, 4),
                "yes_ask_cents": int(yes_ask),
                "no_ask_cents":  int(no_ask),
                "yes_label": yes_label,
                "no_label":  no_label,
                "volume":   vol,
                "close_time": m.get("expected_expiration_time") or m.get("close_time"),
                "url":      "https://kalshi.com/markets/" + ticker,
                "event_ticker": event_ticker,
                "is_sports": _is_sports_market(ticker, event_ticker, m.get("title", "")),
            })
        except Exception as e:
            continue
    print(f"[FETCH] kalshi: {len(out)} real markets, {skipped_parlays} parlays skipped from {len(raw)} total")
    return out


def fetch_polymarket():
    all_raw = []
    # Fetch multiple pages sorted by volume for maximum coverage
    for offset in (0, 200, 400, 600, 800):
        try:
            resp = requests.get(
                "https://gamma-api.polymarket.com/markets",
                params={"active": "true", "closed": "false", "limit": 200,
                        "offset": offset, "order": "volume", "ascending": "false"},
                timeout=TIMEOUT,
            )
            resp.raise_for_status()
            page = resp.json()
            if not page:
                break
            all_raw.extend(page)
        except Exception:
            break
    out = []
    seen = set()
    for m in all_raw:
        try:
            mid = str(m.get("id", ""))
            if mid in seen:
                continue
            seen.add(mid)
            prices = m.get("outcomePrices", "[]")
            if isinstance(prices, str):
                prices = eval(prices)
            if len(prices) < 2:
                continue
            yes = float(prices[0])
            no  = float(prices[1])
            if yes == 0 and no == 0:
                continue
            slug = m.get("slug", m.get("id", ""))
            out.append({
                "platform": "polymarket",
                "id":       mid,
                "question": m.get("question", ""),
                "yes":      round(yes, 4),
                "no":       round(no, 4),
                "volume":   int(float(m.get("volume", 0))),
                "url":      "https://polymarket.com/event/" + slug if slug else "",
            })
        except Exception:
            continue
    return out


def fetch_predictit():
    try:
        resp = requests.get(
            "https://www.predictit.org/api/marketdata/all/",
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        raw = resp.json().get("markets", [])
    except Exception:
        return []
    out = []
    for market in raw:
        for contract in market.get("contracts", []):
            try:
                yes = contract.get("bestBuyYesCost") or contract.get("lastTradePrice") or 0
                no  = contract.get("bestBuyNoCost") or (1 - yes) if yes else 0
                if yes == 0 and no == 0:
                    continue
                cid = contract.get("id", "")
                out.append({
                    "platform": "predictit",
                    "id":       str(cid),
                    "question": contract.get("name") or market.get("name", ""),
                    "yes":      round(float(yes), 4),
                    "no":       round(float(no), 4),
                    "volume":   0,
                    "url":      market.get("url", "https://www.predictit.org"),
                })
            except Exception:
                continue
    return out


def fetch_manifold():
    try:
        resp = requests.get(
            "https://api.manifold.markets/v0/markets",
            params={"limit": 500, "sort": "liquidity"},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        raw = resp.json()
    except Exception:
        return []
    out = []
    for m in raw:
        try:
            if m.get("outcomeType") != "BINARY":
                continue
            prob = m.get("probability", 0)
            if prob == 0:
                continue
            mid = m.get("id", "")
            slug = m.get("slug", "")
            out.append({
                "platform": "manifold",
                "id":       mid,
                "question": m.get("question", ""),
                "yes":      round(prob, 4),
                "no":       round(1 - prob, 4),
                "volume":   int(m.get("volume", 0)),
                "url":      "https://manifold.markets/" + (m.get("creatorUsername", "") + "/" + slug if slug else mid),
            })
        except Exception:
            continue
    return out


def fetch_metaculus():
    """Fetch binary questions from Metaculus — great for science, tech, economics."""
    try:
        resp = requests.get(
            "https://www.metaculus.com/api2/questions/",
            params={"status": "open", "type": "binary", "limit": 200,
                    "order_by": "-activity"},
            timeout=TIMEOUT,
            headers={"Accept": "application/json"},
        )
        resp.raise_for_status()
        raw = resp.json().get("results", [])
    except Exception:
        return []
    out = []
    for m in raw:
        try:
            prob = m.get("community_prediction", {})
            if isinstance(prob, dict):
                yes = prob.get("full", {}).get("q2", 0)  # median prediction
            else:
                yes = float(prob) if prob else 0
            if yes <= 0 or yes >= 1:
                continue
            qid = m.get("id", "")
            out.append({
                "platform": "metaculus",
                "id": str(qid),
                "question": m.get("title", ""),
                "yes": round(yes, 4),
                "no": round(1 - yes, 4),
                "volume": m.get("number_of_predictions", 0),
                "url": f"https://www.metaculus.com/questions/{qid}/",
            })
        except Exception:
            continue
    return out


def fetch_smarkets():
    """Fetch popular markets from Smarkets (UK prediction market)."""
    # Smarkets requires multiple nested API calls per event which is too slow.
    # Use their popular/featured endpoint instead for a quick snapshot.
    try:
        resp = requests.get(
            "https://api.smarkets.com/v3/popular/event_ids/sport/",
            timeout=5,
        )
        # If the popular endpoint doesn't work, just return empty
        if resp.status_code != 200:
            return []
        event_ids = resp.json().get("popular_event_ids", [])[:10]  # top 10 only
    except Exception:
        return []
    out = []
    for eid in event_ids:
        try:
            ev_resp = requests.get(f"https://api.smarkets.com/v3/events/{eid}/", timeout=3)
            if ev_resp.status_code != 200:
                continue
            ev = ev_resp.json().get("event", {})
            ev_name = ev.get("name", "")
            mkt_resp = requests.get(f"https://api.smarkets.com/v3/events/{eid}/markets/", timeout=3)
            if mkt_resp.status_code != 200:
                continue
            for mkt in mkt_resp.json().get("markets", [])[:3]:  # max 3 markets per event
                mid = mkt.get("id", "")
                try:
                    pr = requests.get(f"https://api.smarkets.com/v3/markets/{mid}/last_executed_prices/", timeout=3)
                    if pr.status_code != 200:
                        continue
                    for cid, pd in pr.json().get("last_executed_prices", {}).items():
                        yes = float(pd.get("last_executed_price", 0)) / 10000
                        if 0.02 < yes < 0.98:
                            out.append({
                                "platform": "smarkets", "id": f"{mid}_{cid}",
                                "question": f"{ev_name} - {mkt.get('name', '')}",
                                "yes": round(yes, 4), "no": round(1 - yes, 4),
                                "volume": 0, "url": f"https://smarkets.com/event/{eid}",
                            })
                        break  # only first contract
                except Exception:
                    continue
        except Exception:
            continue
        if len(out) >= 20:
            break
    return out


ALL_FETCHERS = {
    "kalshi":     fetch_kalshi,
    "polymarket": fetch_polymarket,
    "predictit":  fetch_predictit,
    "manifold":   fetch_manifold,
    "metaculus":  fetch_metaculus,
    "smarkets":   fetch_smarkets,
}

# Platform weights for consensus — higher liquidity = more trusted
PLAT_WEIGHT_GLOBAL = {"polymarket": 3.0, "predictit": 2.0, "manifold": 1.0, "metaculus": 1.5, "smarkets": 1.5}

# ---------------------------------------------------------------------------
# News Research Engine — fetch headlines from trusted sources
# ---------------------------------------------------------------------------

_news_cache = {}  # query -> {"headlines": [...], "time": datetime}
_NEWS_CACHE_TTL = 300  # 5 minutes

def _extract_search_terms(question):
    """Extract 2-4 key search terms from a market question."""
    q = re.sub(r"[^a-zA-Z0-9\s]", "", question)
    tokens = q.split()
    # Remove common prediction market words
    skip = {"will", "the", "be", "in", "on", "at", "to", "of", "by", "for",
            "is", "it", "do", "does", "did", "has", "have", "had", "was",
            "were", "been", "are", "this", "that", "before", "after",
            "above", "below", "over", "under", "more", "less", "than",
            "how", "many", "much", "what", "when", "where", "which", "who",
            "yes", "no", "or", "and", "not", "if", "a", "an", "with", "from"}
    important = [t for t in tokens if t.lower() not in skip and len(t) > 1]
    # Keep proper nouns (capitalized) and numbers as highest priority
    proper = [t for t in important if t[0].isupper() or t[0].isdigit()]
    if len(proper) >= 2:
        return " ".join(proper[:4])
    return " ".join(important[:4])


def fetch_news_headlines(query, max_results=5):
    """Fetch recent news headlines from Google News RSS for a query."""
    now = datetime.datetime.utcnow()
    cache_key = query.lower().strip()
    if cache_key in _news_cache:
        cached = _news_cache[cache_key]
        if (now - cached["time"]).total_seconds() < _NEWS_CACHE_TTL:
            return cached["headlines"]

    headlines = []
    try:
        url = f"https://news.google.com/rss/search?q={quote_plus(query)}&hl=en-US&gl=US&ceid=US:en"
        resp = requests.get(url, timeout=5, headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        root = ET.fromstring(resp.content)
        for item in root.findall(".//item")[:max_results]:
            title = item.findtext("title", "")
            source = item.findtext("source", "")
            pub_date = item.findtext("pubDate", "")
            link = item.findtext("link", "")
            # Clean up title (often has " - Source" at end)
            clean_title = html_unescape(title)
            if " - " in clean_title:
                parts = clean_title.rsplit(" - ", 1)
                clean_title = parts[0]
                if not source:
                    source = parts[1]
            # Parse date
            age = ""
            if pub_date:
                try:
                    from email.utils import parsedate_to_datetime
                    pd = parsedate_to_datetime(pub_date)
                    diff = now - pd.replace(tzinfo=None)
                    hours = int(diff.total_seconds() / 3600)
                    if hours < 1:
                        age = f"{int(diff.total_seconds()/60)}m ago"
                    elif hours < 24:
                        age = f"{hours}h ago"
                    else:
                        age = f"{hours//24}d ago"
                except Exception:
                    pass
            headlines.append({
                "title": clean_title,
                "source": source or "News",
                "age": age,
                "url": link,
            })
    except Exception as e:
        print(f"[NEWS] Error fetching for '{query}': {e}")

    _news_cache[cache_key] = {"headlines": headlines, "time": now}
    # Trim cache to prevent memory bloat
    if len(_news_cache) > 200:
        oldest = sorted(_news_cache.keys(), key=lambda k: _news_cache[k]["time"])
        for k in oldest[:100]:
            del _news_cache[k]

    return headlines


def research_market(question):
    """Research a market question and return news + sentiment signal."""
    terms = _extract_search_terms(question)
    if not terms or len(terms) < 3:
        return {"headlines": [], "search_terms": terms, "sentiment": "neutral", "news_count": 0}
    headlines = fetch_news_headlines(terms, max_results=5)
    # Simple sentiment: count bullish/bearish keywords in headlines
    bullish_words = {"surge", "soar", "jump", "rise", "gain", "rally", "record", "high",
                     "boost", "strong", "beat", "exceed", "above", "growth", "up", "wins",
                     "launch", "approve", "success", "increase", "expand"}
    bearish_words = {"fall", "drop", "crash", "decline", "loss", "cut", "layoff", "fire",
                     "slash", "below", "miss", "fail", "delay", "cancel", "down", "lose",
                     "recession", "default", "bankruptcy", "collapse", "shrink", "reduce"}
    bull_count = 0
    bear_count = 0
    for h in headlines:
        words = set(h["title"].lower().split())
        bull_count += len(words & bullish_words)
        bear_count += len(words & bearish_words)
    if bull_count > bear_count + 1:
        sentiment = "bullish"
    elif bear_count > bull_count + 1:
        sentiment = "bearish"
    else:
        sentiment = "neutral"
    return {
        "headlines": headlines,
        "search_terms": terms,
        "sentiment": sentiment,
        "news_count": len(headlines),
        "bull_signals": bull_count,
        "bear_signals": bear_count,
    }

_market_cache = {"data": [], "time": None}

def fetch_all_markets():
    # Cache for 12 seconds (scanning every 15s, leave buffer)
    now = datetime.datetime.utcnow()
    if _market_cache["time"] and (now - _market_cache["time"]).total_seconds() < 12 and _market_cache["data"]:
        return _market_cache["data"]
    all_markets = []
    with ThreadPoolExecutor(max_workers=6) as pool:
        futures = {pool.submit(fn): name for name, fn in ALL_FETCHERS.items()}
        try:
            for future in as_completed(futures, timeout=30):
                name = futures[future]
                try:
                    result = future.result(timeout=15)
                    print(f"[FETCH] {name}: {len(result)} markets")
                    all_markets.extend(result)
                except Exception as e:
                    print(f"[FETCH] {name}: ERROR/TIMEOUT {e}")
                    continue
        except TimeoutError:
            print("[FETCH] Global timeout — using markets fetched so far")
        except Exception as e:
            print(f"[FETCH] Unexpected error: {e}")
    if all_markets:
        _market_cache["data"] = all_markets
        _market_cache["time"] = now
    return all_markets

# ---------------------------------------------------------------------------
# Fuzzy matching helpers
# ---------------------------------------------------------------------------

DISTINGUISHING_CATEGORIES = {
    "country": {
        "uk", "brazil", "china", "russia", "ukraine", "india",
        "israel", "iran", "canada", "mexico", "france", "germany", "japan",
        "italy", "spain", "australia", "korea", "taiwan", "greenland",
        "europe", "european", "african", "asian",
    },
    "name_qualifier": {
        "jr", "junior", "sr", "senior", "iii", "ii",
    },
    "sport": {
        "nba", "nfl", "mlb", "nhl", "ufc", "fifa", "atp", "wta",
        "ncaa", "pga", "f1", "nascar",
    },
    "party": {
        "democrat", "democratic", "republican", "gop", "libertarian",
    },
}

# Words that indicate the ACTION/OUTCOME type of a prediction market question
_ACTION_VERBS = {
    "win", "wins", "winning", "lose", "loses", "beat", "beats",
    "release", "releases", "launch", "launches", "announce", "announces",
    "attend", "attends", "visit", "visits", "sign", "signs",
    "resign", "resigns", "fire", "fires", "fired", "hire", "hires",
    "ipo", "merge", "merges", "acquire", "acquires", "buy", "buys",
    "sell", "sells", "ban", "bans", "pass", "passes",
    "approve", "approves", "veto", "vetoes", "confirm", "confirms",
    "invade", "invades", "attack", "attacks", "strike", "strikes",
    "elect", "elected", "nominate", "nominated", "appoint", "appointed",
    "score", "scores", "hit", "hits", "reach", "reaches",
    "default", "defaults", "collapse", "collapses",
    "die", "dies", "arrest", "arrested", "indict", "indicted",
    "convict", "convicted", "impeach", "impeached",
    "drop", "drops", "rise", "rises", "fall", "falls",
    "tweet", "tweets", "post", "posts", "say", "says",
    "trade", "traded", "trades", "draft", "drafted",
    "start", "starts", "end", "ends", "close", "closes", "open", "opens",
    "lead", "leads", "leader", "head", "president", "governor", "mayor",
    "champion", "championship", "mvp", "award", "awards",
    "album", "song", "movie", "film", "show", "book",
    "token", "coin", "airdrop",
}

# Sport team names and identifiers for sports-specific matching
_SPORT_LEAGUES = {"nba", "nfl", "mlb", "nhl", "ufc", "mls", "wnba",
                  "ncaa", "pga", "f1", "nascar", "atp", "wta", "fifa",
                  "epl", "premier", "league", "serie", "bundesliga", "ligue"}


def normalize_question(q):
    q = q.lower()
    q = re.sub(r"[^a-z0-9\s]", "", q)
    tokens = [t for t in q.split() if t not in STOP_WORDS and len(t) > 1]
    return " ".join(tokens)


def extract_categories(q):
    q_clean = re.sub(r"[^a-z0-9\s]", "", q.lower())
    tokens = set(q_clean.split())
    result = {}
    for cat, words in DISTINGUISHING_CATEGORIES.items():
        found = tokens & words
        if found:
            result[cat] = found
    return result


def keyword_overlap(a, b):
    set_a = set(a.split())
    set_b = set(b.split())
    if not set_a or not set_b:
        return 0
    intersection = set_a & set_b
    return len(intersection) / min(len(set_a), len(set_b))


def _extract_entities(raw_q):
    """Extract named entities (people, companies, teams) from a question.
    Returns a set of lowercase multi-word entity strings AND individual tokens.
    Groups consecutive capitalized words into phrases (e.g. 'Jorge Rodriguez').
    This way 'Jorge Rodriguez' != 'Delcy Rodriguez' because the full-name
    entities differ even though they share a last name."""
    words = raw_q.split()
    entities = set()
    current_phrase = []
    _skip_starts = {"will", "what", "when", "where", "who", "how", "is", "are",
                    "does", "do", "can", "should", "if", "the", "a", "an"}

    for i, w in enumerate(words):
        clean = re.sub(r"[^a-zA-Z0-9']", "", w)
        if not clean or len(clean) <= 1:
            # Flush any accumulated phrase
            if current_phrase:
                entities.add(" ".join(current_phrase))
                current_phrase = []
            continue
        is_cap = clean[0].isupper() and clean.lower() not in STOP_WORDS
        # Skip sentence-start common words
        if i == 0 and clean.lower() in _skip_starts:
            is_cap = False
        if is_cap:
            current_phrase.append(clean.lower())
        else:
            if current_phrase:
                entities.add(" ".join(current_phrase))
                current_phrase = []
    if current_phrase:
        entities.add(" ".join(current_phrase))

    # Also add individual words from multi-word entities for partial matching
    multi_words = [e for e in entities if " " in e]
    for mw in multi_words:
        for part in mw.split():
            entities.add(part)

    return entities


def _extract_timeframe(raw_q):
    """Extract date/deadline from a question. Returns a (year, month, day) tuple
    or None. Partial dates return what's available, e.g. (2026, None, None)."""
    q = raw_q.lower()
    # Pattern: "by/before/in/on March 31, 2026" or "2026" alone
    # Month name + day + year
    m = re.search(r'(jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:tember)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\s+(\d{1,2})(?:\s*,)?\s*(\d{4})', q)
    if m:
        month_map = {"jan": 1, "feb": 2, "mar": 3, "apr": 4, "may": 5, "jun": 6,
                     "jul": 7, "aug": 8, "sep": 9, "oct": 10, "nov": 11, "dec": 12}
        mon_str = m.group(1)[:3]
        return (int(m.group(3)), month_map.get(mon_str, 0), int(m.group(2)))
    # Month name + year (no day)
    m = re.search(r'(jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:tember)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\s+(\d{4})', q)
    if m:
        month_map = {"jan": 1, "feb": 2, "mar": 3, "apr": 4, "may": 5, "jun": 6,
                     "jul": 7, "aug": 8, "sep": 9, "oct": 10, "nov": 11, "dec": 12}
        mon_str = m.group(1)[:3]
        return (int(m.group(2)), month_map.get(mon_str, 0), None)
    # "Q1/Q2/Q3/Q4 2026"
    m = re.search(r'q([1-4])\s*(\d{4})', q)
    if m:
        quarter = int(m.group(1))
        quarter_end_month = quarter * 3
        return (int(m.group(2)), quarter_end_month, None)
    # Bare year: "in 2026" or "2026" or "before 2027"
    m = re.search(r'\b(20\d{2})\b', q)
    if m:
        return (int(m.group(1)), None, None)
    return None


def _timeframes_compatible(tf_a, tf_b):
    """Check if two timeframes are compatible for arbitrage matching.
    Both must refer to essentially the same deadline."""
    if tf_a is None or tf_b is None:
        # If neither has a timeframe, that's fine (both open-ended)
        # If only one has a timeframe, penalize but don't block
        return tf_a is None and tf_b is None
    year_a, mon_a, day_a = tf_a
    year_b, mon_b, day_b = tf_b
    # Years must match
    if year_a != year_b:
        return False
    # If both have months, they must match (or be within 1 month)
    if mon_a is not None and mon_b is not None:
        if abs(mon_a - mon_b) > 1:
            return False
        # If both have days and months match, days must be close
        if mon_a == mon_b and day_a is not None and day_b is not None:
            if abs(day_a - day_b) > 7:
                return False
    return True


def _extract_actions(raw_q):
    """Extract action/outcome words from a question."""
    q_clean = re.sub(r"[^a-z0-9\s]", "", raw_q.lower())
    tokens = set(q_clean.split())
    return tokens & _ACTION_VERBS


def _is_sports_market(raw_q):
    """Check if a question is about sports."""
    q_lower = raw_q.lower()
    tokens = set(re.sub(r"[^a-z0-9\s]", "", q_lower).split())
    return bool(tokens & _SPORT_LEAGUES)


def _sports_compatible(raw_a, raw_b):
    """For sports markets, check that the same teams and outcome type match."""
    ents_a = _extract_entities(raw_a)
    ents_b = _extract_entities(raw_b)
    # Remove sport league names from entity sets — we want team/player names
    ents_a -= _SPORT_LEAGUES
    ents_b -= _SPORT_LEAGUES
    if not ents_a or not ents_b:
        return True  # Can't tell, don't block
    # At least 50% of entities from the shorter set must appear in the longer
    smaller = ents_a if len(ents_a) <= len(ents_b) else ents_b
    larger = ents_b if len(ents_a) <= len(ents_b) else ents_a
    overlap = smaller & larger
    if len(overlap) < len(smaller) * 0.5:
        return False
    return True


def similarity(a, b, raw_a="", raw_b=""):
    """Compute similarity between two normalized questions.
    Returns a float 0-1. Uses category checks, entity matching, timeframe
    validation, action matching, and keyword overlap to minimize false positives.

    Also sets a _last_match_details dict on the function for quality scoring.
    """
    ra = raw_a or a
    rb = raw_b or b

    # ── Category check (existing) ──
    cats_a = extract_categories(ra)
    cats_b = extract_categories(rb)
    penalty = 1.0
    for cat in cats_a:
        if cat in cats_b and not (cats_a[cat] & cats_b[cat]):
            return 0
    exclusive = {"country", "name_qualifier"}
    for cat in exclusive:
        a_has = cat in cats_a
        b_has = cat in cats_b
        if a_has != b_has:
            penalty *= 0.7

    # ── Entity check — both questions must be about the same subject ──
    ents_a = _extract_entities(ra)
    ents_b = _extract_entities(rb)
    if ents_a and ents_b:
        # Multi-word entities (full names) are the strongest signal
        multi_a = {e for e in ents_a if " " in e}
        multi_b = {e for e in ents_b if " " in e}
        # If both have full names, at least one must match
        if multi_a and multi_b:
            if not (multi_a & multi_b):
                return 0  # "Jorge Rodriguez" != "Delcy Rodriguez"
        # Check overlap of all entity tokens
        overlap = ents_a & ents_b
        if not overlap:
            return 0
        smaller_ent = min(len(ents_a), len(ents_b))
        ent_ratio = len(overlap) / smaller_ent if smaller_ent > 0 else 0
        if ent_ratio < 0.5:
            penalty *= 0.3

    # ── Action/outcome check ──
    acts_a = _extract_actions(ra)
    acts_b = _extract_actions(rb)
    if acts_a and acts_b:
        # If both have action verbs but share none, likely different questions
        if not (acts_a & acts_b):
            # Check for synonyms: win/beat, launch/release, etc.
            _synonyms = [
                {"win", "wins", "winning", "beat", "beats", "champion", "championship"},
                {"launch", "launches", "release", "releases"},
                {"resign", "resigns", "fire", "fires", "fired"},
                {"ipo"},
                {"elect", "elected", "win", "wins"},
                {"leader", "head", "president"},
                {"album", "song"},
                {"movie", "film"},
                {"token", "coin", "airdrop"},
                {"attend", "attends", "visit", "visits"},
                {"ban", "bans"},
                {"approve", "approves", "pass", "passes"},
            ]
            synonym_match = False
            for syn_group in _synonyms:
                if (acts_a & syn_group) and (acts_b & syn_group):
                    synonym_match = True
                    break
            if not synonym_match:
                penalty *= 0.2  # heavy penalty for different actions

    # ── Timeframe check ──
    tf_a = _extract_timeframe(ra)
    tf_b = _extract_timeframe(rb)
    if tf_a is not None and tf_b is not None:
        if not _timeframes_compatible(tf_a, tf_b):
            return 0  # Different deadlines = NOT the same bet

    # One has timeframe, other doesn't — mild penalty
    if (tf_a is None) != (tf_b is None):
        penalty *= 0.85

    # ── Sports-specific check ──
    if _is_sports_market(ra) or _is_sports_market(rb):
        if not _sports_compatible(ra, rb):
            return 0

    # ── Base similarity scores ──
    seq = SequenceMatcher(None, a, b).ratio()
    kw = keyword_overlap(a, b)

    # Stricter cutoffs
    if kw < 0.5:
        return 0
    if seq < 0.35:
        return 0

    raw_score = (seq * 0.4 + kw * 0.6) * penalty

    # ── Store match details for quality scoring ──
    ent_overlap = len(ents_a & ents_b) / max(1, min(len(ents_a), len(ents_b))) if (ents_a and ents_b) else (1.0 if not ents_a and not ents_b else 0.5)
    act_overlap = len(acts_a & acts_b) / max(1, min(len(acts_a), len(acts_b))) if (acts_a and acts_b) else (1.0 if not acts_a and not acts_b else 0.5)
    tf_compat = 1.0 if _timeframes_compatible(tf_a, tf_b) else 0.0
    similarity._last_match_details = {
        "seq_ratio": round(seq, 3),
        "kw_overlap": round(kw, 3),
        "entity_overlap": round(ent_overlap, 3),
        "action_overlap": round(act_overlap, 3),
        "timeframe_compatible": tf_compat,
        "penalty": round(penalty, 3),
    }

    return raw_score


def match_quality_score(sim_score, details=None):
    """Compute a 0-100 match quality score for an opportunity.
    Uses the similarity score plus sub-component details."""
    if details is None:
        details = getattr(similarity, '_last_match_details', {})
    if not details:
        return int(min(100, sim_score * 100))

    # Weighted components
    score = 0
    score += details.get("seq_ratio", 0) * 15         # 0-15 for sequence match
    score += details.get("kw_overlap", 0) * 25         # 0-25 for keyword overlap
    score += details.get("entity_overlap", 0) * 25     # 0-25 for entity match
    score += details.get("action_overlap", 0) * 15     # 0-15 for action match
    score += details.get("timeframe_compatible", 0) * 15  # 0-15 for timeframe
    score += (1.0 if details.get("penalty", 1.0) >= 0.9 else 0.5) * 5  # 0-5 for no penalties

    return int(min(100, max(0, score)))

# ---------------------------------------------------------------------------
# Arbitrage scanner (existing)
# ---------------------------------------------------------------------------

def _build_keyword_index(entries):
    """Build inverted index: keyword -> set of entry indices."""
    idx = {}
    for i, (nq, m) in enumerate(entries):
        for word in set(nq.split()):
            if word not in idx:
                idx[word] = set()
            idx[word].add(i)
    return idx


def _candidate_pairs(entries, keyword_index, min_shared=2):
    """Yield (i, j) pairs that share at least min_shared keywords."""
    seen = set()
    for i, (nq, _) in enumerate(entries):
        words = set(nq.split())
        candidate_counts = {}
        for w in words:
            for j in keyword_index.get(w, ()):
                if j <= i:
                    continue
                candidate_counts[j] = candidate_counts.get(j, 0) + 1
        for j, count in candidate_counts.items():
            if count >= min_shared and (i, j) not in seen:
                seen.add((i, j))
                yield i, j


def find_opportunities(all_markets, min_similarity=0.85, max_cost=0.98):
    entries = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        # Skip parlays
        if _is_parlay_title(m.get("question", "")):
            continue
        entries.append((nq, m))

    keyword_index = _build_keyword_index(entries)
    opportunities = []
    seen = set()

    for i, j in _candidate_pairs(entries, keyword_index, min_shared=2):
        nq_a, a = entries[i]
        nq_b, b = entries[j]
        if a["platform"] == b["platform"]:
            continue
        pair_key = tuple(sorted([a["platform"] + a["id"], b["platform"] + b["id"]]))
        if pair_key in seen:
            continue
        sim = similarity(nq_a, nq_b, a["question"], b["question"])
        if sim < min_similarity:
            continue
        # Capture match quality details before they get overwritten
        details = getattr(similarity, '_last_match_details', {}).copy()
        quality = match_quality_score(sim, details)
        seen.add(pair_key)

        fee_a = PLATFORM_FEES.get(a["platform"], 0)
        fee_b = PLATFORM_FEES.get(b["platform"], 0)
        cost_1 = a["yes"] + b["no"]
        avg_fee = (fee_a + fee_b) / 2
        profit_1 = (1 - avg_fee) - cost_1
        cost_2 = a["no"] + b["yes"]
        profit_2 = (1 - avg_fee) - cost_2
        best_cost = min(cost_1, cost_2)
        best_profit = max(profit_1, profit_2)
        if best_cost >= max_cost or best_profit <= 0:
            continue
        if cost_1 <= cost_2:
            buy_yes_platform, buy_no_platform = a, b
            cost, profit = cost_1, profit_1
        else:
            buy_yes_platform, buy_no_platform = b, a
            cost, profit = cost_2, profit_2
        opportunities.append({
            "question_a": a["question"],
            "question_b": b["question"],
            "similarity": round(sim, 3),
            "match_quality": quality,
            "buy_yes": {"platform": buy_yes_platform["platform"], "price": buy_yes_platform["yes"], "url": buy_yes_platform["url"]},
            "buy_no":  {"platform": buy_no_platform["platform"],  "price": buy_no_platform["no"],  "url": buy_no_platform["url"]},
            "cost": round(cost, 4),
            "estimated_profit": round(profit, 4),
            "profit_pct": round(profit / cost * 100, 2) if cost > 0 else 0,
        })

    opportunities.sort(key=lambda x: x["estimated_profit"], reverse=True)
    return opportunities

# ---------------------------------------------------------------------------
# Consensus mispricing detector (NEW)
# ---------------------------------------------------------------------------

def find_consensus_mispricings(all_markets):
    """
    Find Kalshi markets where the price deviates from the consensus of
    other platforms. Requires 1+ platform match with any meaningful deviation.
    Skips parlay markets that can't match cross-platform.
    """
    min_dev = 0.05  # 5% minimum deviation — any edge counts
    min_plats = 1   # Just 1 other platform agreeing is enough

    # BLOCKED CATEGORIES — these markets lose money consistently
    _BLOCKED_KEYWORDS = [
        "temperature", "weather", "highest temp", "lowest temp", "degrees",
        "fahrenheit", "celsius", "rainfall", "snow", "hurricane", "tornado",
    ]

    def _is_blocked_market(question):
        q = question.lower()
        return any(kw in q for kw in _BLOCKED_KEYWORDS)

    kalshi = []
    others = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        # Skip parlays
        if m["platform"] == "kalshi" and _is_parlay_title(m.get("question", "")):
            continue
        # Skip weather/temperature markets — illiquid penny traps
        if _is_blocked_market(m.get("question", "")):
            continue
        if m["platform"] == "kalshi":
            kalshi.append((nq, m))
        else:
            others.append((nq, m))

    # Build keyword index for fast lookup
    other_kw_idx = {}
    for i, (nq_o, om) in enumerate(others):
        for word in set(nq_o.split()):
            if word not in other_kw_idx:
                other_kw_idx[word] = set()
            other_kw_idx[word].add(i)

    mispricings = []

    for nq_k, km in kalshi:
        matches = []
        # Find candidates sharing 2+ keywords
        candidate_counts = {}
        for w in set(nq_k.split()):
            for idx_o in other_kw_idx.get(w, ()):
                candidate_counts[idx_o] = candidate_counts.get(idx_o, 0) + 1
        candidates = [i for i, cnt in candidate_counts.items() if cnt >= 2]
        for idx_o in candidates:
            nq_o, om = others[idx_o]
            sim = similarity(nq_k, nq_o, km["question"], om["question"])
            if sim >= 0.75:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                details = getattr(similarity, '_last_match_details', {}).copy()
                quality = match_quality_score(sim, details)
                matches.append({"platform": om["platform"], "yes": om["yes"], "similarity": round(sim, 3), "match_quality": quality})

        if len(matches) < min_plats:
            continue

        total_w = sum(PLAT_WEIGHT_GLOBAL.get(m["platform"], 1.0) for m in matches)
        consensus_yes = sum(m["yes"] * PLAT_WEIGHT_GLOBAL.get(m["platform"], 1.0) for m in matches) / total_w
        deviation = abs(km["yes"] - consensus_yes)

        if deviation < min_dev:
            continue
        if deviation > 0.40:
            continue

        if km["yes"] < consensus_yes:
            signal = "buy_yes"
            price_cents = int(km["yes"] * 100)
        else:
            signal = "buy_no"
            price_cents = int(km["no"] * 100)

        avg_quality = int(sum(m["match_quality"] for m in matches) / len(matches)) if matches else 0
        mispricings.append({
            "kalshi_ticker": km["id"],
            "kalshi_question": km["question"],
            "kalshi_yes_price": km["yes"],
            "kalshi_url": km["url"],
            "consensus_yes_price": round(consensus_yes, 4),
            "deviation": round(deviation, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": matches,
            "match_quality": avg_quality,
        })

    mispricings.sort(key=lambda x: x["deviation"], reverse=True)
    return mispricings

# ---------------------------------------------------------------------------
# Kalshi order placement (NEW)
# ---------------------------------------------------------------------------

def place_kalshi_order(ticker, side, price_cents, count=1, action="buy", aggressive=True):
    path = "/portfolio/orders"
    headers = signed_headers("POST", path)
    if not headers:
        return {"error": "No API key"}

    # Bump price above ask to ensure fills
    fill_price = price_cents
    if aggressive and action == "buy":
        fill_price = min(price_cents + 3, 99)  # pay 3c more, cap at 99c
    elif aggressive and action == "sell":
        fill_price = max(price_cents - 3, 1)   # accept 3c less, floor at 1c

    # Convert cents to dollar string — use 2 decimal places (Kalshi standard)
    price_dollars = f"{fill_price / 100:.2f}"
    count_int = max(1, int(count))
    payload = {
        "ticker": ticker,
        "action": action,
        "side": side,
        "type": "limit",
        "count": count_int,
        "client_order_id": str(uuid.uuid4()),
    }
    # Set price field for the chosen side
    if side == "yes":
        payload["yes_price"] = fill_price  # cents as integer
    else:
        payload["no_price"] = fill_price   # cents as integer

    try:
        print(f"[ORDER] {action.upper()} {side} {ticker} @ {fill_price}c (ask={price_cents}c) x{count_int}")
        resp = requests.post(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            json=payload,
            timeout=TIMEOUT,
        )
        if resp.status_code == 409:
            # Retry with _dollars format and IOC
            print(f"[ORDER] 409 with cents format, retrying with dollars format...")
            payload2 = {
                "ticker": ticker,
                "action": action,
                "side": side,
                "type": "limit",
                "count_fp": f"{count_int}.00",
                "client_order_id": str(uuid.uuid4()),
                "time_in_force": "immediate_or_cancel",
            }
            if side == "yes":
                payload2["yes_price_dollars"] = price_dollars
            else:
                payload2["no_price_dollars"] = price_dollars
            resp = requests.post(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=headers,
                json=payload2,
                timeout=TIMEOUT,
            )
        resp.raise_for_status()
        result = resp.json()
        filled = 0
        try:
            filled = int(float(str(result.get("order", {}).get("filled_count_fp") or result.get("order", {}).get("filled_count") or 0)))
        except Exception:
            pass
        print(f"[ORDER] OK: {ticker} filled={filled}/{count_int}")
        return result
    except requests.exceptions.HTTPError as e:
        body = ""
        try:
            body = e.response.text[:300]
        except Exception:
            pass
        print(f"[ORDER] REJECT {e.response.status_code}: {ticker} {side} @ {fill_price}c — {body}")
        return {"error": str(e), "response_body": body}
    except Exception as e:
        return {"error": str(e)}

_resting_sells = set()  # tickers with resting sell orders, avoid duplicates

def sell_kalshi_position(ticker, side, price_cents, count=1, resting=False):
    """Sell an existing position on Kalshi."""
    path = "/portfolio/orders"
    headers = signed_headers("POST", path)
    if not headers:
        return {"error": "No API key"}

    # If resting and we already have a resting order for this ticker, skip
    if resting and ticker in _resting_sells:
        return {"error": "Resting sell already exists", "skipped": True}

    price_dollars = f"{price_cents / 100:.4f}"
    tif = "gtc" if resting else "immediate_or_cancel"
    payload = {
        "ticker": ticker,
        "action": "sell",
        "side": side,
        "type": "limit",
        "count_fp": f"{int(count)}.00",
        "client_order_id": str(uuid.uuid4()),
        "time_in_force": tif,
    }
    if side == "yes":
        payload["yes_price_dollars"] = price_dollars
    else:
        payload["no_price_dollars"] = price_dollars

    try:
        resp = requests.post(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            json=payload,
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.HTTPError as e:
        body = ""
        try:
            body = e.response.text
        except Exception:
            pass
        return {"error": str(e), "response_body": body}
    except Exception as e:
        return {"error": str(e)}


def _parse_kalshi_dollars(val):
    """Parse Kalshi v2 dollar string fields (e.g. '19.5500') to cents int."""
    if val is None:
        return 0
    try:
        if isinstance(val, str):
            return int(round(float(val) * 100))
        elif isinstance(val, (int, float)):
            return int(val) if val > 1 else int(round(val * 100))
    except Exception:
        pass
    return 0


def _parse_kalshi_position(pos):
    """Extract position count from Kalshi v2 fields. Returns (count, side).
    Positive count = YES, negative = NO (for v1). In v2, position_fp is always positive and represents YES contracts."""
    # v2: position_fp is a string like "23.00"
    pos_fp = pos.get("position_fp")
    if pos_fp is not None:
        try:
            count = int(round(float(pos_fp)))
            if count != 0:
                return abs(count), "yes" if count > 0 else "no"
        except Exception:
            pass
    # v1 fallback
    position = pos.get("position", 0)
    if position != 0:
        return abs(position), "yes" if position > 0 else "no"
    return 0, "yes"


def check_position_prices():
    """Check current market prices for all open positions.
    Returns list of positions with current price, entry price, P&L."""
    path = "/portfolio/positions"
    headers = signed_headers("GET", path)
    if not headers:
        return []
    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 100, "settlement_status": "unsettled"},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        positions_list = resp.json().get("market_positions", [])
        enriched = []

        # Build market lookup from cache (fast) instead of 57 individual API calls
        _mkt_lookup = {}
        for m in (_market_cache.get("data") or []):
            _mkt_lookup[m.get("ticker", "")] = m

        # For tickers not in cache, batch-fetch them (max 1 API call)
        missing_tickers = []
        for pos in positions_list:
            ticker = pos.get("ticker", "")
            abs_count, _ = _parse_kalshi_position(pos)
            if abs_count > 0 and ticker not in _mkt_lookup:
                missing_tickers.append(ticker)

        # Fetch missing tickers individually but with short timeout
        for ticker in missing_tickers[:20]:  # cap at 20 to avoid slow loads
            try:
                market_path = f"/markets/{ticker}"
                mkt_headers = signed_headers("GET", market_path)
                mkt_resp = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + market_path,
                    headers=mkt_headers, timeout=3,
                )
                if mkt_resp.ok:
                    _mkt_lookup[ticker] = mkt_resp.json().get("market", {})
            except Exception:
                pass

        for pos in positions_list:
            ticker = pos.get("ticker", "")
            abs_count, side = _parse_kalshi_position(pos)
            if abs_count == 0:
                continue  # no active position

            # Get current market price from lookup (fast)
            mkt = _mkt_lookup.get(ticker, {})
            title = mkt.get("title") or mkt.get("question") or ticker
            close_time = mkt.get("expected_expiration_time") or mkt.get("close_time")
            current_yes_price = None
            current_no_price = None
            # Handle both cache format (yes_ask_cents) and raw API format (yes_ask as decimal)
            if mkt.get("yes_ask_cents"):
                current_yes_price = int(mkt["yes_ask_cents"])
                current_no_price = int(mkt.get("no_ask_cents", 100 - current_yes_price))
            else:
                yes_ask = mkt.get("yes_ask_dollars") or mkt.get("yes_ask")
                no_ask = mkt.get("no_ask_dollars") or mkt.get("no_ask")
                if yes_ask:
                    try:
                        current_yes_price = int(round(float(yes_ask) * 100)) if isinstance(yes_ask, str) else int(yes_ask * 100 if yes_ask < 1 else yes_ask)
                    except Exception:
                        pass
                if no_ask:
                    try:
                        current_no_price = int(round(float(no_ask) * 100)) if isinstance(no_ask, str) else int(no_ask * 100 if no_ask < 1 else no_ask)
                    except Exception:
                        pass

            # Find our entry price from trade history
            entry_price = None
            for t in BOT_STATE.get("all_trades", []):
                if t.get("ticker") == ticker:
                    entry_price = t.get("price_cents")
                    break
            # Fallback: estimate from market_exposure / count
            if entry_price is None and abs_count > 0:
                exposure = _parse_kalshi_dollars(pos.get("market_exposure_dollars") or pos.get("market_exposure"))
                if exposure > 0:
                    entry_price = int(round(exposure / abs_count))

            current_price = current_yes_price if side == "yes" else current_no_price
            unrealized_pnl = None
            pnl_pct = None
            if entry_price and current_price:
                unrealized_pnl = (current_price - entry_price) * abs_count
                pnl_pct = round((current_price - entry_price) / max(1, entry_price) * 100, 1)

            # Enriched metadata
            cat = classify_market_category(title, ticker)
            is_live = False
            t_upper = ticker.upper()
            for pfx in LIVE_GAME_SERIES:
                if t_upper.startswith(pfx):
                    is_live = True
                    break
            # Check if closing soon (within 24h)
            time_left_str = ""
            closing_soon = False
            if close_time:
                try:
                    ct_dt = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                    delta = ct_dt - datetime.datetime.utcnow()
                    secs = int(delta.total_seconds())
                    if secs > 0:
                        if secs < 3600:
                            time_left_str = f"{secs // 60}m"
                            closing_soon = True
                        elif secs < 86400:
                            time_left_str = f"{secs // 3600}h {(secs % 3600) // 60}m"
                            is_live = True
                        else:
                            time_left_str = f"{secs // 86400}d"
                except Exception:
                    pass

            vol_score = get_volatility_score(ticker)

            # Determine who placed this bet: check journal, all_trades, and today's trade lists
            placed_by = None
            # 1) Check trade journal (most reliable if server hasn't restarted)
            for jt in reversed(_TRADE_JOURNAL):
                if jt.get("ticker") == ticker and jt.get("side") == side:
                    strat = jt.get("strategy", "")
                    if strat in ("moonshark", "live_sniper", "consensus_mispricing", "arb", "closegame"):
                        placed_by = "bot"
                    elif strat in ("moonshark_manual", "manual", "quant"):
                        placed_by = "you"
                    else:
                        placed_by = "you"
                    break
            # 2) Check all_trades history
            if not placed_by:
                for at in reversed(BOT_STATE.get("all_trades", [])):
                    if at.get("ticker") == ticker:
                        if at.get("manual"):
                            placed_by = "you"
                        elif at.get("strategy") in ("moonshark", "live_sniper", "consensus_mispricing", "arb", "closegame"):
                            placed_by = "bot"
                        break
            # 3) Check today's bot trade lists (survives journal wipe on restart)
            if not placed_by:
                for tlist in [BOT_STATE.get("moonshark_trades_today", []),
                              BOT_STATE.get("snipe_trades_today", []),
                              BOT_STATE.get("trades_today", [])]:
                    for bt in tlist:
                        if bt.get("ticker") == ticker:
                            placed_by = "bot"
                            break
                    if placed_by:
                        break
            # 4) Check manual trades today
            if not placed_by:
                for mt in BOT_STATE.get("manual_trades_today", []):
                    if mt.get("ticker") == ticker:
                        placed_by = "you"
                        break
            # 5) If no bot strategy claimed it, check if it's a legacy pre-Day-1 trade
            # After restart, all trades come in as kalshi_fill with no strategy info.
            # If the bot placed it, it would be in one of the bot lists above.
            if not placed_by:
                # Check if trade was placed before Day 1 (March 16, 2026)
                _trade_date = ""
                for _at in BOT_STATE.get("all_trades", []):
                    if _at.get("ticker") == ticker:
                        _trade_date = (_at.get("timestamp", "") or "")[:10]
                        break
                if _trade_date and _trade_date < TRADE_JOURNAL_START:
                    placed_by = "legacy"  # pre-Day-1 — not yours, not bot's
                else:
                    placed_by = "you"  # manual bet on kalshi.com

            enriched.append({
                "ticker": ticker,
                "title": title,
                "side": side,
                "count": abs_count,
                "entry_price": entry_price,
                "current_price": current_price,
                "current_yes": current_yes_price,
                "current_no": current_no_price,
                "unrealized_pnl_cents": unrealized_pnl,
                "pnl_pct": pnl_pct,
                "close_time": close_time,
                "market_exposure_cents": _parse_kalshi_dollars(pos.get("market_exposure_dollars")),
                "category": cat,
                "is_live": is_live,
                "closing_soon": closing_soon,
                "time_left": time_left_str,
                "volatility": vol_score,
                "placed_by": placed_by,
            })
        return enriched
    except Exception as e:
        print(f"[MONITOR] Error: {e}")
        import traceback
        traceback.print_exc()
        return []


# Auto-exit thresholds — DISABLED for event-outcome bets
# These bets settle at $0 or $1 — mid-event price swings are noise.
# Stop-losses caused us to sell Zakharova at 5c right before she WON (would have been +$27).
TAKE_PROFIT_PCT = 100   # sell at 2x entry price (100% profit)
STOP_LOSS_PCT = -70     # cut losses at 70% down (position is likely dead)

def auto_exit_check():
    """DISABLED — event-outcome bets should be held to settlement.
    Auto-exit was selling winners mid-game (e.g. Zakharova at 5c before she won).
    These bets pay $0 or $1 — price swings during events are noise."""
    return []  # fully disabled — hold everything to settlement
    exits = []
    for pos in positions:
        pnl_pct = pos.get("pnl_pct")
        if pnl_pct is None:
            continue
        ticker = pos["ticker"]
        side = pos["side"]
        count = pos["count"]
        current = pos["current_price"]

        action = None
        reason = None

        # Skip illiquid positions — no buyers under 25c, let them settle
        if current and current < 25:
            continue
        # Skip old bot junk by keyword
        _exit_blocked = ["gas price", "netflix", "spotify", "billboard", "nuclear", "truth social", "title holder", "featherweight", "bantamweight", "pga tour"]
        ptitle = (pos.get("title", "") or ticker).lower()
        if any(kw in ptitle for kw in _exit_blocked):
            continue

        if pnl_pct >= TAKE_PROFIT_PCT:
            action = "take_profit"
            reason = f"Up {pnl_pct}% — taking profit"
        elif pnl_pct <= STOP_LOSS_PCT:
            action = "stop_loss"
            reason = f"Down {pnl_pct}% — cutting losses"

        if action and current:
            # Sell aggressively to ensure fill — drop price significantly
            # For take profit: we're already up, accept slightly less to guarantee exit
            # For stop loss: cut losses fast, sell at steep discount
            entry = pos.get("entry_price") or current
            if action == "take_profit":
                # Sell at entry + small profit margin (guarantee we still profit)
                min_profit_price = max(1, entry + 1)
                sell_price = max(min_profit_price, current - 3)
            else:
                # Stop loss: sell at any price above 1c to get out ASAP
                sell_price = max(1, current - 5)

            result = sell_kalshi_position(ticker, side, sell_price, count)
            success = "error" not in result

            # Check if order actually filled (not just accepted)
            order_data = result.get("order", {})
            filled = 0
            try:
                filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
            except Exception:
                pass
            remaining = count - filled

            exits.append({
                "ticker": ticker,
                "title": pos["title"],
                "action": action,
                "reason": reason,
                "pnl_pct": pnl_pct,
                "sell_price": sell_price,
                "result": result,
                "success": success,
                "filled": filled,
            })
            if success and filled > 0:
                pnl_usd = (sell_price - entry) * filled / 100
                _log_activity(f"Auto-exit: {action} {ticker} (Up {pnl_pct}% — taking profit) SOLD {filled}x @ {sell_price}c = ${pnl_usd:+.2f}", "success" if pnl_usd >= 0 else "error")
                print(f"[AUTO-EXIT] {action}: {ticker} FILLED {filled}/{count} at {sell_price}c (${pnl_usd:+.2f})")
            elif success and filled == 0:
                # No instant fill — place a resting GTC order so it sits on the book
                if ticker not in _resting_sells:
                    resting_result = sell_kalshi_position(ticker, side, sell_price, count, resting=True)
                    if "error" not in resting_result:
                        _resting_sells.add(ticker)
                        _log_activity(f"Auto-exit: {ticker} — placed resting sell at {sell_price}c (waiting for buyer)", "info")
                        print(f"[AUTO-EXIT] {action}: {ticker} — resting sell placed at {sell_price}c")
                    else:
                        _log_activity(f"Auto-exit: {ticker} — no buyer at {sell_price}c, resting order failed", "error")
                else:
                    pass  # already have a resting order, skip silently
            else:
                print(f"[AUTO-EXIT] FAILED {action}: {ticker} — {result.get('error', '')[:100]}")
                _log_activity(f"Auto-exit FAILED: {ticker} — {result.get('error', '')[:80]}", "error")
    return exits


# ---------------------------------------------------------------------------
# Bot scanner
# ---------------------------------------------------------------------------

def run_bot_scan():
    now = datetime.datetime.utcnow()
    today = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")  # Pacific date for daily reset

    # Daily reset
    if BOT_STATE["trade_date"] != today:
        BOT_STATE["trade_date"] = today
        BOT_STATE["trades_today"] = []
        BOT_STATE["daily_spent_usd"] = 0.0
        BOT_STATE["manual_trades_today"] = []
        _log_activity("Daily reset — new trading day started")
        # Send daily summary to Discord
        try:
            ms_trades = len(BOT_STATE.get("moonshark_trades_today", []))
            cg_trades = len(BOT_STATE.get("closegame_trades_today", []))
            ms_spent = BOT_STATE.get("moonshark_daily_spent", 0)
            cg_spent = BOT_STATE.get("closegame_daily_spent", 0)
            total_pnl = _PORTFOLIO_CACHE.get("data", {}).get("total_realized_usd", 0)
            _send_discord(
                f"📊 **Daily Summary**\n"
                f"MoonShark: {ms_trades} trades (${ms_spent:.2f})\n"
                f"CloseGame: {cg_trades} trades (${cg_spent:.2f})\n"
                f"Total P&L: ${total_pnl:+.2f}",
                0x7a7aff
            )
        except Exception:
            pass

    BOT_STATE["last_scan"] = now.isoformat()

    try:
        all_markets = fetch_all_markets()
        BOT_STATE["last_scan_markets"] = len(all_markets)
        BOT_STATE["last_scan_mispriced"] = 0  # consensus disabled

        # Count live game markets for the log
        _live_count = sum(1 for m in all_markets if m.get("platform") == "kalshi" and any(pfx in (m.get("id") or "") for pfx in LIVE_GAME_SERIES))
        _total_bets = len(BOT_STATE.get("trades_today", [])) + len(BOT_STATE.get("snipe_trades_today", [])) + len(BOT_STATE.get("moonshark_trades_today", [])) + len(BOT_STATE.get("closegame_trades_today", [])) + len(BOT_STATE.get("manual_trades_today", []))
        _log_activity(f"Scan: {_live_count} live | {_total_bets} bets today")

        if not BOT_CONFIG["enabled"]:
            _log_activity("Auto-trade OFF — skipping trades")
            return

        # Consensus trading disabled — live strategies handle all trading
        return

        # SAFETY: check balance floor before trading
        min_balance = BOT_CONFIG.get("min_balance_usd", 200.0)
        current_balance = 0
        try:
            bal_path = "/portfolio/balance"
            bal_h = signed_headers("GET", bal_path)
            bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + bal_path, headers=bal_h, timeout=TIMEOUT)
            if bal_r.ok:
                current_balance = bal_r.json().get("balance", 0) / 100
                if current_balance < min_balance:
                    _log_activity(f"SAFETY STOP: Balance ${current_balance:.2f} below ${min_balance:.2f} floor — no trades", "error")
                    BOT_CONFIG["enabled"] = False
                    _log_activity("Auto-trade DISABLED by safety floor", "error")
                    return
        except Exception as e:
            _log_activity(f"Balance check failed: {e} — skipping trades for safety", "error")
            return

        # DAILY LIMIT: combined bot + sniper spending
        total_daily = BOT_STATE["daily_spent_usd"] + BOT_STATE.get("snipe_daily_spent", 0)
        if total_daily >= BOT_CONFIG["max_daily_usd"]:
            _log_activity(f"Daily limit reached (${total_daily:.2f}/{BOT_CONFIG['max_daily_usd']:.2f})")
            return

        # POSITION LIMIT: don't overextend
        existing_positions = []
        traded_events = set()
        try:
            existing_positions = check_position_prices()
            for pos in existing_positions:
                parts = pos.get("ticker", "").split("-")
                if parts:
                    traded_events.add(parts[0])
        except Exception:
            pass

        max_positions = BOT_CONFIG.get("max_open_positions", 20)
        if len(existing_positions) >= max_positions:
            _log_activity(f"Position limit: {len(existing_positions)}/{max_positions} — no new trades")
            return

        # CASH RESERVE: keep 50% of portfolio in cash
        reserve_pct = BOT_CONFIG.get("min_cash_reserve_pct", 0.50)
        total_invested = sum(p.get("market_exposure_cents", 0) for p in existing_positions) / 100
        portfolio_total = current_balance + total_invested
        if portfolio_total > 0 and current_balance / portfolio_total < reserve_pct:
            _log_activity(f"Cash reserve: ${current_balance:.2f} is {current_balance/portfolio_total*100:.0f}% of portfolio (need {reserve_pct*100:.0f}%) — no new trades")
            return

        trades_this_cycle = 0
        for opp in mispricings:
            total_daily = BOT_STATE["daily_spent_usd"] + BOT_STATE.get("snipe_daily_spent", 0)
            if total_daily >= BOT_CONFIG["max_daily_usd"]:
                _log_activity("Daily spending limit hit — stopping trades")
                break

            # Extract event from ticker (e.g. KXPGAMAJORWIN-26-WZAL -> KXPGAMAJORWIN)
            ticker_parts = opp["kalshi_ticker"].split("-")
            event_key = ticker_parts[0] if ticker_parts else opp["kalshi_ticker"]

            if event_key in traded_events:
                continue  # Already traded this event — skip other outcomes
            traded_events.add(event_key)

            # Block banned categories (weather etc — illiquid penny traps)
            blocked = BOT_CONFIG.get("blocked_categories", [])
            if blocked:
                market_cat = classify_market_category(
                    opp.get("kalshi_question", ""), opp["kalshi_ticker"]
                )
                if market_cat in blocked:
                    continue
            # Block specific keywords (long-dated predictions that lose money)
            blocked_kw = BOT_CONFIG.get("blocked_keywords", [])
            q_lower = (opp.get("kalshi_question", "") or "").lower()
            if any(kw in q_lower for kw in blocked_kw):
                continue

            # CORRELATION CHECK: don't over-concentrate in one category
            cat_allowed, cat_name, cat_count = check_category_limit(
                opp.get("kalshi_question", ""), opp["kalshi_ticker"], existing_positions
            )
            if not cat_allowed:
                _log_activity(f"Category limit: {cat_name} has {cat_count} positions — skipping {opp['kalshi_ticker']}")
                continue

            # EDGE CHECK: must have real cross-platform validation
            plat_count = opp.get("platform_count", 0) or len(opp.get("matching_platforms", []))
            deviation = opp.get("deviation", 0)
            if plat_count < BOT_CONFIG.get("min_platforms", 2):
                continue  # Not enough platforms to confirm edge
            if deviation < BOT_CONFIG.get("min_deviation", 0.15):
                continue  # Edge too small

            # VOLUME CHECK: skip illiquid markets we can't sell
            volume = opp.get("volume", 0) or 0
            if volume < BOT_CONFIG.get("min_volume", 100):
                continue  # Too illiquid

            pc = opp["price_cents"]
            # Skip penny markets (illiquid, can't sell)
            if pc < 20:
                continue
            # KELLY CRITERION sizing — scales bets with bankroll + edge
            consensus = opp.get("consensus_yes_price", 0.5)
            count = kelly_count(current_balance, pc, consensus)
            cost_usd = (pc * count) / 100.0
            if cost_usd > BOT_CONFIG["max_bet_usd"]:
                count = max(1, int(BOT_CONFIG["max_bet_usd"] * 100 / pc))
                cost_usd = (pc * count) / 100.0
            if BOT_STATE["daily_spent_usd"] + cost_usd > BOT_CONFIG["max_daily_usd"]:
                continue

            side = opp["signal"].replace("buy_", "")
            _log_activity(f"Placing order: {side.upper()} {opp['kalshi_ticker']} @ {pc}c x{count} (${cost_usd:.2f})")
            result = place_kalshi_order(opp["kalshi_ticker"], side, pc, count=count)

            trade_record = {
                "timestamp": now.isoformat(),
                "ticker": opp["kalshi_ticker"],
                "question": opp["kalshi_question"],
                "side": side,
                "price_cents": pc,
                "count": count,
                "cost_usd": cost_usd,
                "deviation": opp["deviation"],
                "consensus_price": opp["consensus_yes_price"],
                "kalshi_price": opp["kalshi_yes_price"],
                "matching_platforms": opp["matching_platforms"],
                "result": result,
                "success": "error" not in result,
                "bot_version": BOT_VERSION,
                "strategy": "consensus_mispricing",
            }

            BOT_STATE["trades_today"].append(trade_record)
            BOT_STATE["all_trades"].append(trade_record)
            if trade_record["success"]:
                BOT_STATE["daily_spent_usd"] += cost_usd
                _log_activity(f"FILLED: {side.upper()} {opp['kalshi_ticker']} @ {pc}c x{count}", "success")
                trades_this_cycle += 1
            else:
                err_msg = result.get("error", result.get("response_body", "Unknown"))
                _log_activity(f"FAILED: {opp['kalshi_ticker']} — {str(err_msg)[:80]}", "error")
            print(f"[BOT] Trade: {side} {opp['kalshi_ticker']} @ {opp['price_cents']}c | success={trade_record['success']}")
            _save_state()

        if trades_this_cycle > 0:
            _log_activity(f"Cycle done: {trades_this_cycle} new trades, ${BOT_STATE['daily_spent_usd']:.2f} spent today")

    except Exception as e:
        BOT_STATE["errors"].append({"time": now.isoformat(), "error": str(e)})
        BOT_STATE["errors"] = BOT_STATE["errors"][-50:]
        _log_activity(f"Scan error: {str(e)[:100]}", "error")
        print(f"[BOT] Scan error: {e}")

# ---------------------------------------------------------------------------
# LIVE GAME SNIPER — buy near-certain outcomes in live sports
# ---------------------------------------------------------------------------

# Sports series to scan for live games
LIVE_GAME_SERIES = [
    "KXMLBGAME",           # MLB game winners
    "KXNBAGAME",           # NBA game winners
    "KXNHLGAME",           # NHL game winners
    "KXNCAAMBGAME",        # NCAA Men's Basketball game winners
    "KXNCAAWBGAME",        # NCAA Women's Basketball game winners
    "KXKBLGAME",           # KBO Korean baseball (morning hours, less competition)
    # REMOVED: Tennis (0% win rate), Soccer (low volume), NFL (off-season)
]

# Sniper settings
SNIPE_MIN_PRICE = 65   # cents — catch games earlier when edge is bigger
SNIPE_MAX_PRICE = 85   # cents — cap at 85c (need 15%+ profit margin, one upset can't wipe 6 wins)
SNIPE_BET_USD = 15.0   # fallback — now uses _smart_bet_size() for bankroll scaling
SNIPE_MAX_DAILY = 150.0  # daily safety cap — Kelly sizes the actual bets
SNIPE_MAX_TRADES = 20    # more room — this is our best strategy

BOT_STATE["snipe_trades_today"] = []
BOT_STATE["snipe_daily_spent"] = 0.0
BOT_STATE["snipe_wins"] = 0
BOT_STATE["snipe_losses"] = 0
BOT_STATE["snipe_profit_usd"] = 0.0

# MoonShark settings — KELLY-SIZED: fewer bets, larger when edge is real
MOONSHARK_MIN_PRICE = 25   # cents — skip sub-25c lottery tickets
MOONSHARK_MAX_PRICE = 40   # cents — tighter range, only best underdogs
MOONSHARK_MAX_DAILY = 75.0  # daily safety cap (not used for Kelly sizing)
MOONSHARK_BET_USD = 3.0     # fallback only — Kelly sizes most bets
MOONSHARK_MIN_TRADES = 0    # no floor — only trade when edge is real
MOONSHARK_MAX_TRADES = 10   # max 10/day

BOT_STATE["moonshark_trades_today"] = []
BOT_STATE["moonshark_daily_spent"] = 0.0
BOT_STATE["moonshark_date"] = None

# GLOBAL event lock — prevents ALL strategies from betting both sides of the same game
# Key = event (e.g. "KXMLBGAME-26APR012020CLELAD"), resets daily
import threading as _threading
_EVENT_LOCK = _threading.Lock()
_EVENTS_BET_TODAY = set()  # shared across all strategies
_EVENTS_BET_DATE = None

def _check_and_claim_event(event_key):
    """Thread-safe check: returns True if this event hasn't been bet yet (and claims it).
    Returns False if we already bet on this event today."""
    global _EVENTS_BET_DATE
    today = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
    with _EVENT_LOCK:
        if _EVENTS_BET_DATE != today:
            _EVENTS_BET_DATE = today
            _EVENTS_BET_TODAY.clear()
        if event_key in _EVENTS_BET_TODAY:
            return False
        _EVENTS_BET_TODAY.add(event_key)
        return True

def live_game_snipe():
    """Scan LIVE SPORTS markets for high-probability outcomes (70-90c).
    Strategy: only live sports + vetted short-term markets with volume.
    Profit: 10-30c per contract on settlement."""
    if not BOT_CONFIG.get("enabled"):
        return []

    # Daily reset check (Pacific time — matches dashboard display)
    today = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
    if BOT_STATE.get("snipe_date") != today:
        BOT_STATE["snipe_date"] = today
        BOT_STATE["snipe_trades_today"] = []
        BOT_STATE["snipe_daily_spent"] = 0.0

    if BOT_STATE["snipe_daily_spent"] >= SNIPE_MAX_DAILY:
        return []

    # Check balance
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bal = bal_r.json().get("balance", 0) / 100
            if bal < BOT_CONFIG.get("min_balance_usd", 200):
                return []
    except Exception:
        return []

    # Get existing position tickers and events to avoid doubling down
    existing_tickers = set()
    existing_events = set()
    try:
        positions = check_position_prices()
        for p in positions:
            existing_tickers.add(p.get("ticker", ""))
            parts = p.get("ticker", "").split("-")
            if len(parts) >= 2:
                existing_events.add("-".join(parts[:2]))
    except Exception:
        pass
    # Also include today's trades from ALL strategies to prevent cross-strategy dupes
    for _tlist in [BOT_STATE.get("snipe_trades_today", []), BOT_STATE.get("moonshark_trades_today", []),
                   BOT_STATE.get("closegame_trades_today", []), BOT_STATE.get("manual_trades_today", [])]:
        for _t in _tlist:
            _tk = _t.get("ticker", "")
            if _tk:
                existing_tickers.add(_tk)
                _tp = _tk.split("-")
                if len(_tp) >= 2:
                    existing_events.add("-".join(_tp[:2]))

    snipes = []
    _ms_reasons = {}  # rejection tracking (shared name with moonshark for consistency)

    # Max snipes per day
    if len(BOT_STATE.get("snipe_trades_today", [])) >= SNIPE_MAX_TRADES:
        return []

    # Scan LIVE sports games + markets closing soon (the "Live" area)
    scan_sources = []
    for series in LIVE_GAME_SERIES:
        scan_sources.append({"series_ticker": series})
    # Also scan markets closing within next 24h — these are the "live" ones
    # One API call to get all near-expiry markets
    close_cutoff = (datetime.datetime.utcnow() + datetime.timedelta(hours=24)).strftime("%Y-%m-%dT%H:%M:%SZ")
    scan_sources.append({"close_time_max": close_cutoff, "status": "open"})
    for source_params in scan_sources:
        if BOT_STATE["snipe_daily_spent"] >= SNIPE_MAX_DAILY:
            break

        try:
            mh = signed_headers("GET", "/markets")
            params = {"limit": 200, "status": "open"}
            params.update(source_params)
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh,
                params=params,
                timeout=8,
            )
            if not resp.ok:
                continue

            markets = resp.json().get("markets", [])

            # Sort so closing-soon markets get priority (before we hit daily cap)
            def _close_sort(m):
                ct = m.get("close_time", "")
                if not ct:
                    return 99999
                try:
                    cd = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00")).replace(tzinfo=None)
                    return max(0, (cd - datetime.datetime.utcnow()).total_seconds() / 60)
                except Exception:
                    return 99999
            markets.sort(key=_close_sort)

            for mkt in markets:
                ticker = mkt.get("ticker", "")
                title = mkt.get("title", "")

                # Skip if we already hold this ticker or event (match-specific)
                if ticker in existing_tickers:
                    continue
                # Event key = first 2 parts: e.g. "KXATPCHALLENGERMATCH-26MAR26SANCAR"
                # This blocks both sides of same match but allows different matches
                _parts = ticker.split("-") if ticker else []
                event_key = "-".join(_parts[:2]) if len(_parts) >= 2 else (ticker or "")
                if event_key in existing_events:
                    continue
                # Global cross-strategy dedup — prevents betting both sides
                if event_key in _EVENTS_BET_TODAY:
                    continue

                # STRICT FILTERING — only bet on what we understand
                # Block banned categories
                blocked = BOT_CONFIG.get("blocked_categories", [])
                mcat = classify_market_category(title, ticker)
                if mcat in blocked:
                    continue

                # Block known junk keywords — stuff the old bot wasted money on
                title_lower = title.lower()
                _SNIPE_BLOCKED_KEYWORDS = [
                    "netflix", "spotify", "billboard", "top song", "top artist",
                    "youtube", "subscribers", "ishowspeed", "tiktok", "instagram",
                    "nuclear fusion", "title holder", "featherweight", "bantamweight",
                    "flyweight", "middleweight", "welterweight", "lightweight",
                    "heavyweight", "pga tour major", "ballon d'or", "fields medal",
                    "temperature", "weather", "rainfall", "snow", "hurricane",
                    "tornado", "fahrenheit", "celsius", "highest temp", "lowest temp",
                    "gas price", "oil price", "wti", "brent",
                    "truth social", "tweets", "followers",
                ]
                if any(kw in title_lower for kw in _SNIPE_BLOCKED_KEYWORDS):
                    continue

                # Only allow vetted categories for auto-trading
                _ALLOWED_CATEGORIES = ["tennis", "nba", "nfl", "nhl", "mlb", "soccer", "mma"]

                # WHITELIST: Only bet on major league ticker prefixes we understand
                _ALLOWED_TICKER_PREFIXES = [
                    "KXMLBGAME", "KXNBAGAME", "KXNHLGAME", "KXNFLGAME",  # US major leagues
                    "KXSOCCERGAME",                                        # Soccer
                    "KXATPMATCH", "KXWTAMATCH", "KXATPCHALLENGERMATCH",   # Tennis
                    "KXUFCFIGHT",                                          # UFC/MMA
                    "KXAFLGAME",                                           # AFL
                ]
                # BLACKLIST: Block minor/foreign leagues and esports
                _BLOCKED_TICKER_PREFIXES = [
                    "KXKHLGAME", "KXVTBGAME", "KXCS2GAME", "KXVALGAME",  # Russian hockey, basketball, esports
                    "KXDOTAGAME", "KXLOLGAME", "KXCOD",                    # More esports
                    "KXCRICKET", "KXKABADDI",                              # Niche sports
                ]
                t_upper = ticker.upper()
                # Block blacklisted prefixes
                if any(t_upper.startswith(bp) for bp in _BLOCKED_TICKER_PREFIXES):
                    continue
                # For the catch-all time-based scan, require whitelisted prefix OR allowed category
                if "series_ticker" not in source_params:
                    is_whitelisted = any(t_upper.startswith(wp) for wp in _ALLOWED_TICKER_PREFIXES)
                    if not is_whitelisted and mcat not in _ALLOWED_CATEGORIES:
                        continue

                # Liquidity check — use order book depth (volume field doesn't exist in API)
                _ask_size = float(str(mkt.get("yes_ask_size_fp") or mkt.get("no_ask_size_fp") or 0))
                if _ask_size < 50:
                    _ms_reasons["low_liquidity"] = _ms_reasons.get("low_liquidity", 0) + 1
                    continue

                # Close time check — skip for series-scanned markets (Kalshi sets
                # close_time to series end, not individual game time)
                close_time_str = mkt.get("close_time", "")
                if "series_ticker" not in source_params:
                    if close_time_str:
                        try:
                            close_dt_chk = datetime.datetime.fromisoformat(close_time_str.replace("Z", "+00:00")).replace(tzinfo=None)
                            hours_to_close = (close_dt_chk - datetime.datetime.utcnow()).total_seconds() / 3600
                            if hours_to_close > 24:
                                continue
                        except Exception:
                            pass
                else:
                    # For series-scanned: only bet on today's/yesterday's games
                    today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%y%b%d").upper()  # e.g. 26MAR25
                    yesterday_str = (datetime.datetime.now(tz=_PACIFIC) - datetime.timedelta(days=1)).strftime("%y%b%d").upper()
                    if today_str not in ticker.upper() and yesterday_str not in ticker.upper():
                        continue

                # Parse prices
                yes_ask = None
                no_ask = None
                try:
                    ya = mkt.get("yes_ask_dollars") or mkt.get("yes_ask")
                    if ya:
                        yes_ask = int(round(float(str(ya)) * 100))
                    na = mkt.get("no_ask_dollars") or mkt.get("no_ask")
                    if na:
                        no_ask = int(round(float(str(na)) * 100))
                except Exception:
                    continue

                # Find the near-certain side
                side = None
                price = None
                if yes_ask and SNIPE_MIN_PRICE <= yes_ask <= SNIPE_MAX_PRICE:
                    side = "yes"
                    price = yes_ask
                elif no_ask and SNIPE_MIN_PRICE <= no_ask <= SNIPE_MAX_PRICE:
                    side = "no"
                    price = no_ask

                if not side:
                    continue

                # Check daily limit
                if BOT_STATE["snipe_daily_spent"] >= SNIPE_MAX_DAILY:
                    break

                # SAFETY: check total spending across BOTH bot + sniper vs cash
                total_daily = BOT_STATE.get("daily_spent_usd", 0) + BOT_STATE["snipe_daily_spent"]
                if total_daily >= BOT_CONFIG["max_daily_usd"]:
                    break

                # Closing time edge — markets closing in <30min at 70%+ rarely flip
                closing_boost = 1.0
                close_time = mkt.get("close_time", "")
                if close_time:
                    try:
                        close_dt = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                        mins_left = (close_dt - datetime.datetime.utcnow()).total_seconds() / 60
                        if 0 < mins_left <= 30:
                            closing_boost = 1.5  # 50% bigger bet on closing markets
                            _log_activity(
                                f"CLOSING EDGE: {ticker} closes in {int(mins_left)}m @ {price}c — boosting bet 50%",
                                "info"
                            )
                    except Exception:
                        pass

                # CONVICTION SCORE — require multiple signals before betting
                # Check if game is LIVE (in-progress)
                _snipe_game = None
                try:
                    _snipe_scores = _fetch_all_espn_scores()
                    _snipe_team = ticker.split("-")[-1].upper() if "-" in ticker else ""
                    if _snipe_team:
                        _snipe_game = _snipe_scores.get(_snipe_team.lower())
                except Exception:
                    pass
                # MUST be LIVE or recently finished — no pre-game bets
                if _snipe_game and _snipe_game.get("state") == "pre":
                    continue  # skip pre-game — prices are efficient
                conviction = 0
                if _snipe_game and _snipe_game.get("state") == "in":
                    conviction += 2  # LIVE = strong signal
                    # Bonus: close game
                    try:
                        _margin = abs(int(_snipe_game.get("home_score", 0)) - int(_snipe_game.get("away_score", 0)))
                        if _margin <= 5:
                            conviction += 1  # close game, volatile
                    except Exception:
                        pass
                elif _snipe_game and _snipe_game.get("state") == "post":
                    conviction += 1  # finished, might be settling
                else:
                    conviction += 1  # no score data, give benefit of doubt
                # Signal 2: High volume / liquidity
                if _ask_size >= 50:
                    conviction += 1
                # Signal 3: Price in sweet spot (75-88c for sniper = highest win rate)
                if 75 <= price <= 88:
                    conviction += 1
                # Signal 4: Closing soon (live edge)
                if closing_boost > 1:
                    conviction += 1
                # Require minimum conviction of 2 to bet
                if conviction < 2:
                    continue

                # Calculate quantity — bankroll-scaled sizing for compound growth
                cat_mult = _learning_multiplier(ticker, title, price)
                if cat_mult <= 0:
                    continue  # blocked by learning engine
                bet_usd = _smart_bet_size(price, bankroll=bal if bal > 0 else None) * closing_boost * cat_mult
                count = max(1, min(50, int(bet_usd * 100 / price)))
                cost_usd = (price * count) / 100.0

                if BOT_STATE["snipe_daily_spent"] + cost_usd > SNIPE_MAX_DAILY:
                    continue

                # Check expected profit — only snipe if profit is meaningful
                profit_per = 100 - price  # cents profit per contract if we win
                expected_profit = profit_per * count / 100.0
                if expected_profit < 1.00:  # skip if less than $1 potential profit
                    continue

                # Vetting log — show WHY this trade passed all filters
                reasons = []
                reasons.append(f"cat={mcat}")
                reasons.append(f"vol={_ask_size:.0f}")
                if closing_boost > 1:
                    reasons.append(f"CLOSING EDGE")
                if cat_mult > 1:
                    reasons.append(f"hot category x{cat_mult}")
                elif cat_mult < 1:
                    reasons.append(f"cold category x{cat_mult}")
                vetting = " | ".join(reasons)

                _log_activity(
                    f"🎯 SNIPE {side.upper()} {title[:35]} @ {price}c x{count} (${cost_usd:.2f})",
                    "info"
                )

                # Thread-safe claim — prevents other strategies from betting same game
                if not _check_and_claim_event(event_key):
                    _log_activity(f"SNIPE SKIP: {ticker} — already bet this event", "info")
                    continue

                result = place_kalshi_order(ticker, side, price, count=count)
                success = "error" not in result

                if success:
                    # Check fill
                    order_data = result.get("order", {})
                    filled = 0
                    try:
                        filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
                    except Exception:
                        pass

                    if filled > 0:
                        actual_cost = (price * filled) / 100.0
                        potential = (100 - price) * filled / 100.0
                        BOT_STATE["snipe_daily_spent"] += actual_cost
                        # Build edge reasons for tooltip
                        _snipe_edge_reasons = list(reasons)  # already built above
                        if _snipe_game and _snipe_game.get("state") == "in":
                            _snipe_edge_reasons.insert(0, "LIVE game")
                        _snipe_edge_pct = None
                        if closing_boost > 1:
                            _snipe_edge_pct = f"closing boost {closing_boost:.1f}x"
                        _snipe_order_id = order_data.get("order_id", "")
                        if _snipe_order_id:
                            _known_fill_ids.add(_snipe_order_id)
                        BOT_STATE["snipe_trades_today"].append({
                            "ticker": ticker, "title": title, "side": side,
                            "price": price, "count": filled, "cost": actual_cost,
                            "potential_profit": potential,
                            "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                            "bot_version": BOT_VERSION,
                            "strategy": "live_sniper",
                            "category": classify_market_category(title, ticker),
                            "edge_reasons": _snipe_edge_reasons,
                            "conviction": conviction,
                            "order_id": _snipe_order_id,
                        })
                        # Track in trade journal for pattern analysis (pass orderbook if available)
                        _snipe_ob = None
                        try:
                            _snipe_ob = analyze_orderbook(ticker)
                        except Exception:
                            pass
                        _journal_trade(ticker, title, side, price, filled, actual_cost, "live_sniper", is_live=True, close_time=mkt.get("close_time", ""), orderbook_data=_snipe_ob)
                        _log_activity(
                            f"🎯 SNIPED! {side.upper()} {ticker} @ {price}c x{filled} "
                            f"= ${actual_cost:.2f} (potential +${potential:.2f}) | {title[:40]}",
                            "success"
                        )
                        snipes.append({"ticker": ticker, "filled": filled, "cost": actual_cost, "potential": potential})
                        existing_tickers.add(ticker)
                        existing_events.add(event_key)
                    else:
                        _log_activity(f"🎯 Snipe missed: {ticker} — 0 filled at {price}c", "error")
                else:
                    err = result.get("error", "")[:60]
                    body = result.get("response_body", "")[:100]
                    print(f"[SNIPER] Order rejected: {ticker} side={side} price={price}c err={err} body={body}")

        except Exception as e:
            print(f"[SNIPER] Error scanning source: {e}")
            continue

    if snipes:
        total_cost = sum(s["cost"] for s in snipes)
        total_potential = sum(s["potential"] for s in snipes)
        _log_activity(f"🎯 Sniper round: {len(snipes)} trades, ${total_cost:.2f} invested, potential +${total_potential:.2f}", "success")
        # Persist updated journal & snipe counters after snipe round
        _save_state()

    return snipes


# ---------------------------------------------------------------------------
# MoonShark — Longshot Underdog Sniper (10-30c contracts)
# ---------------------------------------------------------------------------

def moonshark_snipe():
    """Scan LIVE SPORTS markets for cheap longshot contracts (10-30c).
    Strategy: small bets on underdog outcomes in liquid, closing-soon markets.
    Profit: 70-90c per contract on settlement (rare but huge)."""
    if not BOT_CONFIG.get("enabled"):
        return []
    if not BOT_CONFIG.get("moonshark_enabled", True):
        return []

    # Daily reset check (Pacific time — matches dashboard display)
    today = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
    if BOT_STATE.get("moonshark_date") != today:
        BOT_STATE["moonshark_date"] = today
        BOT_STATE["moonshark_trades_today"] = []
        BOT_STATE["moonshark_daily_spent"] = 0.0

    if BOT_STATE["moonshark_daily_spent"] >= MOONSHARK_MAX_DAILY:
        return []

    if len(BOT_STATE.get("moonshark_trades_today", [])) >= MOONSHARK_MAX_TRADES:
        return []

    _ms_count = len(BOT_STATE.get("moonshark_trades_today", []))
    if _ms_count < MOONSHARK_MIN_TRADES:
        _log_activity(f"🦈 MoonShark FLOOR MODE: {_ms_count}/{MOONSHARK_MIN_TRADES} trades — relaxing filters", "info")

    # Check balance
    bal = 0
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bal = bal_r.json().get("balance", 0) / 100
            if bal < BOT_CONFIG.get("min_balance_usd", 200):
                return []
    except Exception:
        return []

    # Get existing position tickers and events to avoid doubling down
    existing_tickers = set()
    existing_events = set()
    try:
        positions = check_position_prices()
        for p in positions:
            existing_tickers.add(p.get("ticker", ""))
            parts = p.get("ticker", "").split("-")
            if len(parts) >= 2:
                existing_events.add("-".join(parts[:2]))
    except Exception:
        pass
    # Also include today's trades from ALL strategies to prevent cross-strategy dupes
    for _tlist in [BOT_STATE.get("snipe_trades_today", []), BOT_STATE.get("moonshark_trades_today", []),
                   BOT_STATE.get("closegame_trades_today", []), BOT_STATE.get("manual_trades_today", [])]:
        for _t in _tlist:
            _tk = _t.get("ticker", "")
            if _tk:
                existing_tickers.add(_tk)
                _tp = _tk.split("-")
                if len(_tp) >= 2:
                    existing_events.add("-".join(_tp[:2]))

    snipes = []

    # Scan LIVE sports games + markets closing within 24h
    scan_sources = []
    for series in LIVE_GAME_SERIES:
        scan_sources.append({"series_ticker": series})
    close_cutoff = (datetime.datetime.utcnow() + datetime.timedelta(hours=24)).strftime("%Y-%m-%dT%H:%M:%SZ")
    scan_sources.append({"close_time_max": close_cutoff, "status": "open"})

    _ms_total_scanned = 0
    _ms_reasons = {}  # track rejection reasons
    for source_params in scan_sources:
        if BOT_STATE["moonshark_daily_spent"] >= MOONSHARK_MAX_DAILY:
            break
        if len(BOT_STATE.get("moonshark_trades_today", [])) >= MOONSHARK_MAX_TRADES:
            break

        try:
            mh = signed_headers("GET", "/markets")
            params = {"limit": 200, "status": "open"}
            params.update(source_params)
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh,
                params=params,
                timeout=8,
            )
            if not resp.ok:
                _ms_reasons["api_error"] = _ms_reasons.get("api_error", 0) + 1
                continue

            markets = resp.json().get("markets", [])
            _ms_total_scanned += len(markets)

            # Sort so closing-soon markets get priority
            def _close_sort(m):
                ct = m.get("close_time", "")
                if not ct:
                    return 99999
                try:
                    cd = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00")).replace(tzinfo=None)
                    return max(0, (cd - datetime.datetime.utcnow()).total_seconds() / 60)
                except Exception:
                    return 99999
            markets.sort(key=_close_sort)

            for mkt in markets:
                ticker = mkt.get("ticker", "")
                title = mkt.get("title", "")

                # Skip if we already hold this ticker or match (match-specific key)
                if ticker in existing_tickers:
                    _ms_reasons["already_held"] = _ms_reasons.get("already_held", 0) + 1
                    continue
                _parts = ticker.split("-") if ticker else []
                event_key = "-".join(_parts[:2]) if len(_parts) >= 2 else (ticker or "")
                if event_key in existing_events or event_key in _EVENTS_BET_TODAY:
                    _ms_reasons["event_held"] = _ms_reasons.get("event_held", 0) + 1
                    continue

                # Block banned categories
                blocked = BOT_CONFIG.get("blocked_categories", [])
                mcat = classify_market_category(title, ticker)
                if mcat in blocked:
                    _ms_reasons["blocked_cat"] = _ms_reasons.get("blocked_cat", 0) + 1
                    continue

                # Block known junk keywords
                title_lower = title.lower()
                _MOONSHARK_BLOCKED_KEYWORDS = [
                    "netflix", "spotify", "billboard", "top song", "top artist",
                    "youtube", "subscribers", "ishowspeed", "tiktok", "instagram",
                    "nuclear fusion", "title holder", "title on dec", "featherweight", "bantamweight",
                    "flyweight", "middleweight", "welterweight", "lightweight",
                    "heavyweight", "pga tour major", "ballon d'or", "fields medal",
                    "temperature", "weather", "rainfall", "snow", "hurricane",
                    "tornado", "fahrenheit", "celsius", "highest temp", "lowest temp",
                    "gas price", "oil price", "wti", "brent",
                    "truth social", "tweets", "followers",
                    "prime minister", "next president", "ipo first",
                ]
                if any(kw in title_lower for kw in _MOONSHARK_BLOCKED_KEYWORDS):
                    _ms_reasons["blocked_kw"] = _ms_reasons.get("blocked_kw", 0) + 1
                    continue

                # Only allow vetted categories
                _ALLOWED_CATEGORIES = ["tennis", "nba", "nfl", "nhl", "mlb", "soccer", "mma", "ncaab", "ncaawb"]

                # WHITELIST: Only bet on major league ticker prefixes
                _ALLOWED_TICKER_PREFIXES = [
                    "KXMLBGAME", "KXNBAGAME", "KXNHLGAME", "KXNFLGAME",
                    "KXSOCCERGAME",
                    "KXATPMATCH", "KXWTAMATCH", "KXATPCHALLENGERMATCH",
                    "KXUFCFIGHT",
                    "KXAFLGAME",
                    "KXNCAAMBGAME", "KXNCAAWBGAME",
                ]
                # BLACKLIST: Block minor/foreign leagues and esports
                _BLOCKED_TICKER_PREFIXES = [
                    "KXKHLGAME", "KXVTBGAME", "KXCS2GAME", "KXVALGAME",
                    "KXDOTAGAME", "KXLOLGAME", "KXCOD",
                    "KXCRICKET", "KXKABADDI",
                ]
                t_upper = ticker.upper()
                if any(t_upper.startswith(bp) for bp in _BLOCKED_TICKER_PREFIXES):
                    _ms_reasons["blacklisted"] = _ms_reasons.get("blacklisted", 0) + 1
                    continue
                if "series_ticker" not in source_params:
                    is_whitelisted = any(t_upper.startswith(wp) for wp in _ALLOWED_TICKER_PREFIXES)
                    if not is_whitelisted and mcat not in _ALLOWED_CATEGORIES:
                        _ms_reasons["not_whitelisted"] = _ms_reasons.get("not_whitelisted", 0) + 1
                        continue

                # Liquidity check — use order book depth (volume field doesn't exist in API)
                _ask_size = float(str(mkt.get("yes_ask_size_fp") or mkt.get("no_ask_size_fp") or 0))
                if _ask_size < 50:
                    _ms_reasons["low_liquidity"] = _ms_reasons.get("low_liquidity", 0) + 1
                    continue

                # Close time check — skip for series-scanned markets (Kalshi sets
                # close_time to series end, not individual game time)
                close_time_str = mkt.get("close_time", "")
                if "series_ticker" not in source_params:
                    if not close_time_str:
                        _ms_reasons["no_close_time"] = _ms_reasons.get("no_close_time", 0) + 1
                        continue
                    try:
                        close_dt_chk = datetime.datetime.fromisoformat(close_time_str.replace("Z", "+00:00")).replace(tzinfo=None)
                        hours_to_close = (close_dt_chk - datetime.datetime.utcnow()).total_seconds() / 3600
                        if hours_to_close > 24 or hours_to_close < 0:
                            _ms_reasons["close_time_range"] = _ms_reasons.get("close_time_range", 0) + 1
                            continue
                    except Exception:
                        _ms_reasons["close_time_parse"] = _ms_reasons.get("close_time_parse", 0) + 1
                        continue
                # For series-scanned markets, check if game is TODAY by parsing date from ticker
                else:
                    today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%y%b%d").upper()  # e.g. 26MAR25
                    yesterday_str = (datetime.datetime.now(tz=_PACIFIC) - datetime.timedelta(days=1)).strftime("%y%b%d").upper()
                    if today_str not in ticker.upper() and yesterday_str not in ticker.upper():
                        _ms_reasons["not_today"] = _ms_reasons.get("not_today", 0) + 1
                        continue

                # Must be a GAME or MATCH (binary outcome, not futures/props)
                _tk_upper = ticker.upper()
                if not any(kw in _tk_upper for kw in ["GAME", "MATCH", "FIGHT"]):
                    continue

                # Parse prices
                yes_ask = None
                no_ask = None
                try:
                    ya = mkt.get("yes_ask_dollars") or mkt.get("yes_ask")
                    if ya:
                        yes_ask = int(round(float(str(ya)) * 100))
                    na = mkt.get("no_ask_dollars") or mkt.get("no_ask")
                    if na:
                        no_ask = int(round(float(str(na)) * 100))
                except Exception:
                    continue

                # No floor mode — only trade when real edge exists
                _ms_below_floor = False
                _ms_max_price = MOONSHARK_MAX_PRICE

                # Find the cheap longshot side (25-40c range)
                side = None
                price = None
                if yes_ask and MOONSHARK_MIN_PRICE <= yes_ask <= _ms_max_price:
                    side = "yes"
                    price = yes_ask
                elif no_ask and MOONSHARK_MIN_PRICE <= no_ask <= _ms_max_price:
                    side = "no"
                    price = no_ask

                if not side:
                    continue

                # Check daily limits
                if BOT_STATE["moonshark_daily_spent"] >= MOONSHARK_MAX_DAILY:
                    break
                if len(BOT_STATE.get("moonshark_trades_today", [])) >= MOONSHARK_MAX_TRADES:
                    break

                # SAFETY: check total spending across ALL strategies vs cash
                total_daily = (BOT_STATE.get("daily_spent_usd", 0)
                               + BOT_STATE.get("snipe_daily_spent", 0)
                               + BOT_STATE["moonshark_daily_spent"])
                if total_daily >= BOT_CONFIG["max_daily_usd"]:
                    break

                # Calculate quantity using Kelly Criterion
                implied_prob = price / 100.0

                # TRY REAL SPORTSBOOK ODDS FIRST (ESPN moneylines)
                espn_edge = None
                espn_implied = 0
                _bet_team_odds = None
                _game_info = None  # will be populated by _check_blowout later
                # Try to get live scores for odds check
                # _fetch_all_espn_scores() returns flat dict: team_key(lowercase) -> game_info
                try:
                    _scores_for_odds = _fetch_all_espn_scores()
                    _bet_team = ticker.split("-")[-1].upper() if "-" in ticker else ""
                    if _bet_team:
                        _game_info = _scores_for_odds.get(_bet_team.lower())
                except Exception:
                    pass
                try:
                    _tk_parts_odds = ticker.split("-")
                    _bet_team_odds_abbrev = _tk_parts_odds[-1].upper() if len(_tk_parts_odds) >= 2 else None
                    if _bet_team_odds_abbrev and _game_info and _game_info.get("odds"):
                        _odds_info = _game_info["odds"]
                        if _game_info["home_abbrev"] == _bet_team_odds_abbrev:
                            espn_implied = _odds_info.get("home_implied", 0)
                        elif _game_info["away_abbrev"] == _bet_team_odds_abbrev:
                            espn_implied = _odds_info.get("away_implied", 0)
                        else:
                            espn_implied = 0
                        if espn_implied > 0:
                            espn_edge = espn_implied - implied_prob
                            # SKIP unless ESPN gives at least 3% edge over Kalshi price
                            # e.g., ESPN says 30% but Kalshi prices at 20c (20%) = +10% edge = BET
                            # ESPN says 22% and Kalshi prices at 20c (20%) = +2% edge = SKIP (too thin)
                            if espn_edge < 0.03:
                                _ms_reasons["no_edge"] = _ms_reasons.get("no_edge", 0) + 1
                                continue
                except Exception:
                    pass

                # MUST be a LIVE in-progress game — no pre-game bets
                # Pre-game prices are efficient. The edge is during live action.
                if not _game_info or _game_info.get("state") != "in":
                    _ms_reasons["not_live"] = _ms_reasons.get("not_live", 0) + 1
                    continue

                # CONVICTION SCORE — require multiple signals for MoonShark
                ms_conviction = 2  # already LIVE (required above)
                _conv_reasons = []

                # Signal 2: ESPN sportsbook edge exists and is positive
                if espn_edge is not None and espn_edge > 0.03:
                    ms_conviction += 2  # real sportsbook edge
                    _conv_reasons.append(f"ESPN+{espn_edge:.0%}")
                elif espn_edge is not None and espn_edge > 0:
                    ms_conviction += 1  # small edge

                # Signal 3: Good liquidity
                if _ask_size >= 30:
                    ms_conviction += 1

                # Signal 4: Close game + win probability model
                if _game_info:
                    _home_sc = int(_game_info.get("home_score", 0) or 0)
                    _away_sc = int(_game_info.get("away_score", 0) or 0)
                    _margin = abs(_home_sc - _away_sc)
                    _clock = _game_info.get("clock", "")
                    _league = (_game_info.get("league") or "").lower()

                    # Use win probability model to estimate real odds
                    _model_prob = _lookup_win_prob(_league, _margin, _clock)
                    _model_edge = _model_prob - implied_prob
                    if _model_edge > 0.05:
                        ms_conviction += 2  # model says underpriced by 5%+
                        _conv_reasons.append(f"model+{_model_edge:.0%}")
                    elif _model_edge > 0.02:
                        ms_conviction += 1

                    if _margin <= 5:
                        ms_conviction += 2  # close game = highest value
                        _conv_reasons.append(f"close({_margin}pt)")
                    elif _margin <= 10:
                        ms_conviction += 1  # competitive

                    # Signal 5: Momentum — is the team trending up?
                    _tracker = _game_score_tracker.get(ticker, {})
                    if _tracker:
                        _last_deficit = _tracker.get("last_deficit")
                        if _last_deficit is not None and _margin < _last_deficit:
                            ms_conviction += 1  # deficit shrinking = momentum
                            _conv_reasons.append("momentum")

                # Signal 6: Price in sweet spot (25-30c = best MoonShark range)
                if 25 <= price <= 30:
                    ms_conviction += 1

                # Require minimum conviction — never drop below 3, even in floor mode
                _ms_min_conviction = 3 if _ms_below_floor else 4
                if ms_conviction < _ms_min_conviction:
                    _ms_reasons["low_conviction"] = _ms_reasons.get("low_conviction", 0) + 1
                    continue
                if _ms_below_floor:
                    _conv_reasons.append("FLOOR_MODE")

                # Use real edge if available — SKIP if no ESPN data (no guessing)
                if espn_edge is not None and espn_edge > 0:
                    edge_estimate = espn_edge
                    win_prob = min(espn_implied, 0.45)  # use sportsbook probability
                else:
                    # No real edge data — skip this trade instead of guessing
                    _ms_reasons["no_espn_edge"] = _ms_reasons.get("no_espn_edge", 0) + 1
                    continue
                remaining_budget = MOONSHARK_MAX_DAILY - BOT_STATE["moonshark_daily_spent"]
                trades_left = MOONSHARK_MAX_TRADES - len(BOT_STATE.get("moonshark_trades_today", []))
                # Kelly sizes against REAL bankroll (actual cash), not daily budget
                kelly_bankroll = bal
                profit_if_win = (100 - price) / 100.0
                odds_decimal = profit_if_win / (price / 100.0)
                kelly_usd = kelly_bet_size(kelly_bankroll, win_prob, odds_decimal)
                # No artificial floor — if Kelly says $0, don't bet
                max_per_trade = remaining_budget / max(trades_left, 1)
                # Learning multiplier — bet bigger on proven patterns, skip losers
                cat_mult = _learning_multiplier(ticker, title, price)
                if cat_mult <= 0:
                    continue  # blocked by learning engine

                # Live sports priority — same-day events get 2x, >12h gets 1x
                live_boost = 1.0
                close_time_str2 = mkt.get("close_time", "")
                if close_time_str2:
                    try:
                        close_dt2 = datetime.datetime.fromisoformat(close_time_str2.replace("Z", "+00:00")).replace(tzinfo=None)
                        hours_left = (close_dt2 - datetime.datetime.utcnow()).total_seconds() / 3600
                        if 0 < hours_left <= 6:
                            live_boost = 2.0  # live/imminent — highest priority
                        elif hours_left <= 12:
                            live_boost = 1.5  # same-day
                        # >12h stays at 1.0x
                    except Exception:
                        pass

                # Apply multipliers BEFORE capping — so Kelly cap is never exceeded
                adjusted_kelly = kelly_usd * cat_mult * live_boost
                # No artificial $3 floor — trust Kelly. If edge is small, bet small.
                if adjusted_kelly < 1.0:
                    _ms_reasons["kelly_too_small"] = _ms_reasons.get("kelly_too_small", 0) + 1
                    continue  # Kelly says edge isn't worth it
                bet_usd = min(adjusted_kelly, max_per_trade, remaining_budget, BOT_CONFIG["max_bet_usd"])
                count = max(1, int(bet_usd * 100 / price))
                cost_usd = (price * count) / 100.0

                if BOT_STATE["moonshark_daily_spent"] + cost_usd > MOONSHARK_MAX_DAILY:
                    continue

                # Potential profit — the whole point of longshots
                profit_per = 100 - price  # cents profit per contract if we win
                expected_profit = profit_per * count / 100.0

                # BLOWOUT CHECK — skip if our team is getting destroyed
                _bet_team = None
                _tk_parts = ticker.split("-")
                if len(_tk_parts) >= 2:
                    _bet_team = _tk_parts[-1]  # e.g., "UVA" from KXNCAAMBGAME-26MAR22TENNUVA-UVA
                is_blowout, blowout_reason, _game_info = _check_blowout(ticker, title, _bet_team)
                if is_blowout:
                    _log_activity(f"MOONSHARK SKIP: {title[:35]} — {blowout_reason}", "info")
                    continue

                # Vetting log
                reasons = []
                reasons.append(f"cat={mcat}")
                reasons.append(f"vol={_ask_size:.0f}")
                reasons.append(f"payout={profit_per}c/contract")
                reasons.append(f"kelly=${kelly_usd:.2f}")
                reasons.append(f"edge={edge_estimate:.1%}")
                reasons.append(f"winP={win_prob:.1%}")
                if cat_mult != 1.0:
                    reasons.append(f"cat_mult={cat_mult}x")
                if live_boost > 1.0:
                    reasons.append(f"LIVE BOOST {live_boost}x")
                if espn_edge is not None:
                    reasons.append(f"ESPN_EDGE={espn_edge:.1%}")
                if blowout_reason and not is_blowout:
                    reasons.append(f"score={blowout_reason}")
                vetting = " | ".join(reasons)

                # Check orderbook spread — skip illiquid markets with wide spreads
                _ob = None
                try:
                    _ob = analyze_orderbook(ticker)
                    if _ob and _ob.get("spread", 99) > 8:
                        _log_activity(f"MOONSHARK SKIP: {ticker} — wide spread ({_ob['spread']}c)", "info")
                        continue
                except Exception:
                    pass

                _log_activity(
                    f"🦈 MOON {side.upper()} {title[:30]} @ {price}c x{count} (${cost_usd:.2f}) [{','.join(_conv_reasons[:3])}]",
                    "info"
                )

                # Thread-safe claim — prevents other strategies from betting same game
                if not _check_and_claim_event(event_key):
                    _log_activity(f"MOONSHARK SKIP: {ticker} — already bet this event", "info")
                    continue

                result = place_kalshi_order(ticker, side, price, count=count)
                success = "error" not in result

                if success:
                    order_data = result.get("order", {})
                    filled = 0
                    try:
                        filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
                    except Exception:
                        pass

                    if filled > 0:
                        actual_cost = (price * filled) / 100.0
                        potential = (100 - price) * filled / 100.0
                        BOT_STATE["moonshark_daily_spent"] += actual_cost
                        # Build edge reasons for tooltip
                        _ms_edge_reasons = list(_conv_reasons) if _conv_reasons else []
                        _ms_edge_detail = None
                        if espn_edge is not None:
                            _ms_edge_detail = f"ESPN edge: +{espn_edge:.1%}"
                            _ms_edge_reasons.insert(0, _ms_edge_detail)
                        _ms_order_id = order_data.get("order_id", "")
                        if _ms_order_id:
                            _known_fill_ids.add(_ms_order_id)
                        BOT_STATE["moonshark_trades_today"].append({
                            "ticker": ticker, "title": title, "side": side,
                            "price": price, "count": filled, "cost": actual_cost,
                            "potential_profit": potential,
                            "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                            "bot_version": BOT_VERSION,
                            "strategy": "moonshark",
                            "category": classify_market_category(title, ticker),
                            "edge_reasons": _ms_edge_reasons,
                            "conviction": ms_conviction,
                            "espn_edge": round(espn_edge, 4) if espn_edge is not None else None,
                            "order_id": _ms_order_id,
                        })
                        # Track in trade journal for pattern analysis
                        _edge_data = None
                        try:
                            if espn_edge is not None:
                                _edge_data = {"espn_implied": espn_implied, "espn_edge": espn_edge}
                        except Exception:
                            pass
                        _ob_data = None
                        try:
                            _ob_data = _ob
                        except Exception:
                            pass
                        _journal_trade(ticker, title, side, price, filled, actual_cost, "moonshark", is_live=True, close_time=mkt.get("close_time", ""),
                                       game_info=_game_info, espn_edge_data=_edge_data, orderbook_data=_ob_data)
                        _log_activity(
                            f"🦈 BET PLACED! {side.upper()} {title[:25]} @ {price}c x{filled} = ${actual_cost:.2f} [{','.join(_conv_reasons[:3])}]",
                            "success"
                        )
                        snipes.append({"ticker": ticker, "filled": filled, "cost": actual_cost, "potential": potential})
                        existing_tickers.add(ticker)
                        existing_events.add(event_key)
                    else:
                        _log_activity(f"MOONSHARK missed: {ticker} — 0 filled at {price}c", "error")
                else:
                    err = result.get("error", "")[:60]
                    body = result.get("response_body", "")[:100]
                    print(f"[MOONSHARK] Order rejected: {ticker} side={side} price={price}c count={count} err={err} body={body}")
                    _log_activity(f"MOONSHARK failed: {title[:25]} — {body[:50] or err[:50]}", "error")

        except Exception as e:
            print(f"[MOONSHARK] Error scanning source: {e}")
            continue

    if snipes:
        total_cost = sum(s["cost"] for s in snipes)
        total_potential = sum(s["potential"] for s in snipes)
        _log_activity(f"MOONSHARK round: {len(snipes)} trades, ${total_cost:.2f} invested, potential +${total_potential:.2f}", "success")
        _save_state()
    else:
        # Log why no trades were placed (diagnostic)
        reason_str = ", ".join(f"{k}:{v}" for k, v in sorted(_ms_reasons.items(), key=lambda x: -x[1])[:5])
        if _ms_total_scanned > 0 or reason_str:
            print(f"[MOONSHARK] Scanned {_ms_total_scanned} markets, 0 trades. Rejections: {reason_str or 'none found in price range'}")

    return snipes


# ---------------------------------------------------------------------------
# Close-Game Sniper — buy underdogs in tight late-game situations
# ---------------------------------------------------------------------------
CLOSEGAME_MAX_DAILY = 25.0   # budget per day — REDUCED (underdog strategy, unproven)
CLOSEGAME_MAX_TRADES = 5     # max 5 — quality over quantity
CLOSEGAME_MIN_PRICE = 30     # buy at 30-45c (tighter range, skip cheapest)
CLOSEGAME_MAX_PRICE = 45

def closegame_snipe():
    """Buy underdogs in live, close games (within 5 points in late game).
    Strategy: Kalshi prices lag live action. A team down 2 in Q4 at 35c
    is often mispriced — real win probability is closer to 40-45%.
    Key: ONLY bet when the game is tight AND late."""
    if not BOT_CONFIG.get("enabled"):
        return []
    if not BOT_CONFIG.get("closegame_enabled", True):
        return []

    # Daily reset (Pacific time — matches dashboard display)
    today = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
    if BOT_STATE.get("closegame_date") != today:
        BOT_STATE["closegame_date"] = today
        BOT_STATE["closegame_trades_today"] = []
        BOT_STATE["closegame_daily_spent"] = 0.0

    if BOT_STATE.get("closegame_daily_spent", 0) >= CLOSEGAME_MAX_DAILY:
        return []
    if len(BOT_STATE.get("closegame_trades_today", [])) >= CLOSEGAME_MAX_TRADES:
        return []

    # Check balance
    bal = 0
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bal = bal_r.json().get("balance", 0) / 100
            if bal < BOT_CONFIG.get("min_balance_usd", 200):
                return []
    except Exception:
        return []

    # Get existing positions
    existing_tickers = set()
    existing_events = set()
    try:
        positions = check_position_prices()
        for p in positions:
            existing_tickers.add(p.get("ticker", ""))
            parts = p.get("ticker", "").split("-")
            if len(parts) >= 2:
                existing_events.add("-".join(parts[:2]))
    except Exception:
        pass

    # Get live scores
    try:
        scores = _fetch_all_espn_scores()
    except Exception:
        return []
    if not scores:
        return []

    # Find games that are LIVE, CLOSE, and LATE
    # _fetch_all_espn_scores() returns flat dict (team_key -> game_info)
    # Deduplicate by building unique games from values
    _seen_matchups = set()
    _unique_games = []
    for _ginfo in scores.values():
        _matchup_key = f"{_ginfo.get('home_abbrev', '')}_{_ginfo.get('away_abbrev', '')}"
        if _matchup_key not in _seen_matchups:
            _seen_matchups.add(_matchup_key)
            _unique_games.append(_ginfo)

    close_games = []
    for game in _unique_games:
        if game.get("state") != "in":
            continue
        sport = game.get("league", "").lower()
        home_score = int(game.get("home_score", 0))
        away_score = int(game.get("away_score", 0))
        margin = abs(home_score - away_score)
        period = game.get("clock", "")

        # Define "late game" by sport — FINAL period only for highest edge
        is_late = False
        if sport == "nba":
            is_late = any(p in period for p in ["Q4", "OT", "4th"])
            max_margin = 6  # NBA: within 6 in Q4 (tighter = better edge)
        elif sport == "ncaab":
            is_late = any(p in period for p in ["2H", "OT", "2nd"])
            max_margin = 5  # College BB men: within 5 in 2H
        elif sport == "ncaawb":
            is_late = any(p in period for p in ["Q4", "4th", "OT"])
            max_margin = 5  # College BB women: Q4 only (tighter)
        elif sport == "nhl":
            is_late = any(p in period for p in ["P3", "3rd", "OT"])
            max_margin = 1  # Hockey: within 1 goal in P3 (tighter)
        elif sport in ("mlb", "kbo"):
            try:
                inning = int(''.join(c for c in period if c.isdigit()) or "0")
                is_late = inning >= 7
            except Exception:
                is_late = False
            max_margin = 3  # Baseball: within 3 in 7th+
        elif sport in ("atp", "wta"):
            is_late = True
            max_margin = 1  # Within 1 set
        elif sport in ("mls", "epl"):
            try:
                minutes = int(''.join(c for c in period if c.isdigit()) or "0")
                is_late = minutes >= 60
            except Exception:
                is_late = True
            max_margin = 1  # Soccer: within 1 goal in 60th+
        else:
            max_margin = 5
            is_late = True  # default: any live game

        if is_late and margin <= max_margin:
            if home_score < away_score:
                underdog = game.get("home_abbrev", "")
                underdog_name = game.get("home_name", "")
            elif away_score < home_score:
                underdog = game.get("away_abbrev", "")
                underdog_name = game.get("away_name", "")
            else:
                continue  # Tied game — skip

            close_games.append({
                "sport": sport,
                "game": game,
                "underdog": underdog,
                "underdog_name": underdog_name,
                "margin": margin,
                "period": period,
                "home": game.get("home_abbrev", ""),
                "away": game.get("away_abbrev", ""),
                "home_score": home_score,
                "away_score": away_score,
            })

    if not close_games:
        return []

    _log_activity(f"CLOSEGAME: Found {len(close_games)} close late games", "info")

    # Now find Kalshi markets for these close games
    snipes = []
    for cg in close_games:
        if BOT_STATE.get("closegame_daily_spent", 0) >= CLOSEGAME_MAX_DAILY:
            break
        if len(BOT_STATE.get("closegame_trades_today", [])) >= CLOSEGAME_MAX_TRADES:
            break

        underdog = cg["underdog"].upper()
        # Search for Kalshi market matching this game
        try:
            mh = signed_headers("GET", "/markets")
            # Search for the game ticker
            sport_prefix_map = {
                "nba": "KXNBAGAME", "ncaab": "KXNCAAMBGAME", "ncaawb": "KXNCAAWBGAME",
                "nhl": "KXNHLGAME", "mlb": "KXMLBGAME", "kbo": "KXKBLGAME",
                "atp": "KXATPMATCH", "wta": "KXWTAMATCH",
                "mls": "KXMLSGAME", "epl": "KXEPLGAME",
            }
            prefix = sport_prefix_map.get(cg["sport"])
            if not prefix:
                continue

            today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%y%b%d").upper()  # e.g., 26MAR25
            # Try to find the market
            params = {"limit": 50, "status": "open", "ticker_contains": prefix}
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh,
                params=params,
                timeout=8,
            )
            if not resp.ok:
                continue

            markets = resp.json().get("markets", [])

            for mkt in markets:
                ticker = mkt.get("ticker", "")
                title = mkt.get("title", "")

                # Match the underdog team to the ticker
                if underdog not in ticker.upper():
                    continue

                if ticker in existing_tickers:
                    continue
                event_key = "-".join(ticker.split("-")[:2]) if ticker else ""
                if event_key in existing_events or event_key in _EVENTS_BET_TODAY:
                    continue

                # Parse prices
                yes_ask = None
                no_ask = None
                try:
                    ya = mkt.get("yes_ask_dollars") or mkt.get("yes_ask")
                    if ya:
                        yes_ask = int(round(float(str(ya)) * 100))
                    na = mkt.get("no_ask_dollars") or mkt.get("no_ask")
                    if na:
                        no_ask = int(round(float(str(na)) * 100))
                except Exception:
                    continue

                # Find side where underdog wins at our price range
                side = None
                price = None
                # The underdog ticker usually means YES on that team
                if yes_ask and CLOSEGAME_MIN_PRICE <= yes_ask <= CLOSEGAME_MAX_PRICE:
                    side = "yes"
                    price = yes_ask
                elif no_ask and CLOSEGAME_MIN_PRICE <= no_ask <= CLOSEGAME_MAX_PRICE:
                    side = "no"
                    price = no_ask

                if not side:
                    continue

                # Validate edge with ESPN sportsbook odds (same as MoonShark)
                kalshi_implied = price / 100.0
                espn_edge_cg = None
                espn_win_prob_cg = None
                try:
                    _cg_scores = _fetch_all_espn_scores()
                    _cg_team_key = underdog.lower()
                    _cg_game = _cg_scores.get(_cg_team_key)
                    if _cg_game and _cg_game.get("odds"):
                        _cg_odds = _cg_game["odds"]
                        if _cg_game["home_abbrev"] == underdog:
                            espn_win_prob_cg = _cg_odds.get("home_implied", 0)
                        elif _cg_game["away_abbrev"] == underdog:
                            espn_win_prob_cg = _cg_odds.get("away_implied", 0)
                        if espn_win_prob_cg and espn_win_prob_cg > 0:
                            espn_edge_cg = espn_win_prob_cg - kalshi_implied
                except Exception:
                    pass

                # Require real ESPN edge — no more guessing with hardcoded model
                if espn_edge_cg is None or espn_edge_cg < 0.03:
                    _log_activity(
                        f"CLOSEGAME SKIP: {title[:35]} — no ESPN edge (need 3%+, got {espn_edge_cg:.1%} )" if espn_edge_cg else f"CLOSEGAME SKIP: {title[:35]} — no ESPN odds data",
                        "info"
                    )
                    continue

                estimated_win_prob = espn_win_prob_cg
                edge = espn_edge_cg

                # Size the bet
                remaining = CLOSEGAME_MAX_DAILY - BOT_STATE.get("closegame_daily_spent", 0)
                profit_if_win = (100 - price) / 100.0
                odds_decimal = profit_if_win / (price / 100.0)
                kelly_usd = kelly_bet_size(remaining, estimated_win_prob, odds_decimal)
                bet_usd = max(3.0, min(kelly_usd, remaining / max(1, CLOSEGAME_MAX_TRADES - len(BOT_STATE.get("closegame_trades_today", []))), remaining))
                bet_usd = min(bet_usd, BOT_CONFIG["max_bet_usd"], remaining)
                count = max(1, int(bet_usd * 100 / price))
                cost_usd = (price * count) / 100.0

                score_str = f"{cg['away']} {cg['away_score']} - {cg['home']} {cg['home_score']} {cg['period']}"
                _log_activity(
                    f"🎯 CLOSEGAME: {side.upper()} {ticker} @ {price}c x{count} "
                    f"(${cost_usd:.2f}) | {score_str} | edge={edge:.0%} winP={estimated_win_prob:.0%}",
                    "info"
                )

                # Thread-safe claim — prevents other strategies from betting same game
                if not _check_and_claim_event(event_key):
                    _log_activity(f"CLOSEGAME SKIP: {ticker} — already bet this event", "info")
                    continue

                result = place_kalshi_order(ticker, side, price, count=count)
                success = "error" not in result

                if success:
                    order_data = result.get("order", {})
                    filled = 0
                    try:
                        filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
                    except Exception:
                        pass

                    if filled > 0:
                        actual_cost = (price * filled) / 100.0
                        potential = (100 - price) * filled / 100.0
                        BOT_STATE["closegame_daily_spent"] = BOT_STATE.get("closegame_daily_spent", 0) + actual_cost
                        # Build edge reasons for tooltip
                        _cg_edge_reasons = []
                        _cg_edge_reasons.append(f"Close game: {score_str}")
                        _cg_edge_reasons.append(f"Margin: {cg['margin']} pts")
                        if edge:
                            _cg_edge_reasons.append(f"ESPN edge: +{edge:.1%}")
                        _cg_edge_reasons.append(f"Win prob: {estimated_win_prob:.0%}")
                        _cg_order_id = order_data.get("order_id", "")
                        if _cg_order_id:
                            _known_fill_ids.add(_cg_order_id)
                        BOT_STATE.setdefault("closegame_trades_today", []).append({
                            "ticker": ticker, "title": title, "side": side,
                            "price": price, "count": filled, "cost": actual_cost,
                            "potential_profit": potential,
                            "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                            "strategy": "closegame",
                            "score": score_str,
                            "margin": cg["margin"],
                            "period": cg["period"],
                            "edge_reasons": _cg_edge_reasons,
                            "espn_edge": round(edge, 4) if edge else None,
                            "order_id": _cg_order_id,
                        })
                        _cg_game_info = {"home_score": cg.get("home_score"), "away_score": cg.get("away_score"), "clock": cg.get("period", ""), "state": "in", "league": cg.get("sport", "")}
                        _cg_edge = None
                        try:
                            if edge:
                                _cg_edge = {"espn_implied": estimated_win_prob, "espn_edge": edge}
                        except Exception:
                            pass
                        _journal_trade(ticker, title, side, price, filled, actual_cost, "closegame", is_live=True, close_time=mkt.get("close_time", ""),
                                       game_info=_cg_game_info, espn_edge_data=_cg_edge)
                        _log_activity(
                            f"🎯 CLOSEGAME HIT! {side.upper()} {underdog} @ {price}c x{filled} "
                            f"= ${actual_cost:.2f} (potential +${potential:.2f}) | {score_str}",
                            "success"
                        )
                        snipes.append({"ticker": ticker, "filled": filled, "cost": actual_cost, "potential": potential})
                        existing_tickers.add(ticker)
                        existing_events.add(event_key)
                    else:
                        _log_activity(f"CLOSEGAME missed: {ticker} — 0 filled at {price}c", "error")
                else:
                    err = result.get("error", "")[:60]
                    _log_activity(f"CLOSEGAME failed: {ticker} — {err}", "error")

        except Exception as e:
            print(f"[CLOSEGAME] Error: {e}")
            continue

    if snipes:
        total_cost = sum(s["cost"] for s in snipes)
        total_potential = sum(s["potential"] for s in snipes)
        _log_activity(f"🎯 CLOSEGAME round: {len(snipes)} trades, ${total_cost:.2f} invested, potential +${total_potential:.2f}", "success")
        _save_state()

    return snipes


# ---------------------------------------------------------------------------
# Scheduler
# ---------------------------------------------------------------------------

def _warm_picks_cache():
    """Pre-populate picks cache so the dashboard loads instantly."""
    try:
        _generate_picks()
        print(f"[CACHE] Picks cache warmed: {_picks_cache['data']['total_scanned'] if _picks_cache.get('data') else 0} markets")
    except Exception as e:
        import traceback
        print(f"[CACHE] Warm error: {e}")
        traceback.print_exc()

# ===========================================================================
# QUANT ENGINE — Professional trading strategies adapted for prediction markets
# ===========================================================================

# ---------------------------------------------------------------------------
# 1. KELLY CRITERION — Optimal bet sizing based on bankroll + edge
# ---------------------------------------------------------------------------
# f* = (bp - q) / b  where b=odds, p=win_prob, q=1-p
# We use half-Kelly for safety (less volatile)

def kelly_bet_size(bankroll, win_prob, odds_decimal):
    """Calculate optimal Kelly Criterion bet size.

    Args:
        bankroll: total available cash in dollars
        win_prob: estimated probability of winning (0-1)
        odds_decimal: decimal odds (e.g., buy at 60c = payout 100c, odds = 100/60 - 1 = 0.667)

    Returns:
        Optimal bet in dollars (half-Kelly for safety)
    """
    if win_prob <= 0 or win_prob >= 1 or odds_decimal <= 0:
        return 0
    q = 1 - win_prob
    b = odds_decimal
    kelly_fraction = (b * win_prob - q) / b
    if kelly_fraction <= 0:
        return 0  # negative edge — don't bet
    # Half-Kelly for safety — reduces variance while keeping ~75% of growth rate
    half_kelly = kelly_fraction / 2
    # Cap at 5% of bankroll per trade (risk management)
    capped = min(half_kelly, 0.05)
    bet = bankroll * capped
    # No artificial floor — trust Kelly. Ceiling from config.
    if bet < 1.0:
        return 0  # Kelly says edge isn't worth it
    return min(bet, BOT_CONFIG["max_bet_usd"])


def kelly_count(bankroll, price_cents, consensus_price):
    """Calculate contract count using Kelly Criterion.

    Args:
        bankroll: cash in dollars
        price_cents: what we'd pay per contract
        consensus_price: what we think true probability is (0-1)
    """
    if price_cents <= 0 or price_cents >= 100:
        return 1
    our_cost = price_cents / 100.0  # what we pay
    win_prob = consensus_price       # estimated true probability
    # If buying YES at 60c, payout is 100c, so profit = 40c, odds = 40/60
    profit_if_win = (100 - price_cents) / 100.0
    odds = profit_if_win / our_cost
    bet_usd = kelly_bet_size(bankroll, win_prob, odds)
    count = max(1, int(bet_usd * 100 / price_cents))
    # Cap at 50 contracts for any single trade
    return min(count, 50)


# ---------------------------------------------------------------------------
# 2. MOMENTUM TRACKER — Detect price trends on Kalshi markets
# ---------------------------------------------------------------------------
# Track price snapshots over time. If price is consistently moving in one
# direction, ride the momentum (trend following).

_price_history = {}  # ticker -> deque of (timestamp, yes_price_cents)
_MOMENTUM_WINDOW = 6  # number of snapshots to track (at 30s intervals = 3 min window)
_MOMENTUM_THRESHOLD = 5  # cents — price must move 5c+ in window to signal

def record_price_snapshot(ticker, yes_price_cents):
    """Record a price datapoint for momentum analysis."""
    now = datetime.datetime.utcnow()
    if ticker not in _price_history:
        _price_history[ticker] = deque(maxlen=_MOMENTUM_WINDOW)
    _price_history[ticker].append((now, yes_price_cents))


def get_momentum(ticker):
    """Calculate momentum score for a ticker.

    Returns:
        dict with 'direction' ('up', 'down', 'flat'), 'magnitude' (cents),
        'velocity' (cents per minute), 'snapshots' count
    """
    history = _price_history.get(ticker)
    if not history or len(history) < 3:
        return {"direction": "flat", "magnitude": 0, "velocity": 0, "snapshots": 0}

    prices = [p for _, p in history]
    first_price = prices[0]
    last_price = prices[-1]
    magnitude = last_price - first_price

    # Time span in minutes
    first_time = history[0][0]
    last_time = history[-1][0]
    span_min = max(0.5, (last_time - first_time).total_seconds() / 60)
    velocity = magnitude / span_min  # cents per minute

    # Check consistency — is the trend monotonic?
    ups = sum(1 for i in range(1, len(prices)) if prices[i] > prices[i-1])
    downs = sum(1 for i in range(1, len(prices)) if prices[i] < prices[i-1])
    total_moves = ups + downs

    # Strong trend = 70%+ moves in same direction
    if total_moves == 0:
        direction = "flat"
    elif ups / total_moves >= 0.7 and magnitude >= _MOMENTUM_THRESHOLD:
        direction = "up"
    elif downs / total_moves >= 0.7 and magnitude <= -_MOMENTUM_THRESHOLD:
        direction = "down"
    else:
        direction = "flat"

    return {
        "direction": direction,
        "magnitude": magnitude,
        "velocity": round(velocity, 2),
        "snapshots": len(history),
        "consistency": round(max(ups, downs) / max(1, total_moves), 2),
    }


def scan_momentum_opportunities():
    """Find markets with strong momentum — potential trend-following trades.

    Strategy: If a market's YES price is rising steadily AND is still below
    our consensus estimate, the momentum confirms our edge. Buy with more
    confidence (and larger Kelly size).
    """
    opportunities = []
    for ticker, history in _price_history.items():
        if len(history) < 3:
            continue
        mom = get_momentum(ticker)
        if mom["direction"] == "flat":
            continue
        # Only report significant moves
        if abs(mom["magnitude"]) >= _MOMENTUM_THRESHOLD:
            opportunities.append({
                "ticker": ticker,
                "momentum": mom,
                "current_price": history[-1][1],
            })
    opportunities.sort(key=lambda x: abs(x["momentum"]["magnitude"]), reverse=True)
    return opportunities


# ---------------------------------------------------------------------------
# 3. MEAN REVERSION — Bet against extreme price moves
# ---------------------------------------------------------------------------
# If a market spikes sharply (panic buying/selling), bet it reverts to the mean.
# Works best on liquid markets where temporary supply/demand imbalances resolve.

_price_averages = {}  # ticker -> {"ema": float, "snapshots": int}
_EMA_ALPHA = 0.15  # exponential moving average smoothing factor

def update_ema(ticker, price_cents):
    """Update exponential moving average for a ticker."""
    if ticker not in _price_averages:
        _price_averages[ticker] = {"ema": float(price_cents), "snapshots": 1}
        return
    state = _price_averages[ticker]
    state["ema"] = _EMA_ALPHA * price_cents + (1 - _EMA_ALPHA) * state["ema"]
    state["snapshots"] += 1


def find_mean_reversion_signals(all_markets):
    """Find markets where current price deviates significantly from its EMA.

    Strategy: If price jumped 10+ cents above EMA → overreaction, buy NO.
    If price dropped 10+ cents below EMA → panic sell, buy YES.
    Only on liquid markets (volume 500+).
    """
    _REVERSION_THRESHOLD = 8  # cents deviation from EMA
    signals = []

    for m in all_markets:
        if m["platform"] != "kalshi":
            continue
        ticker = m["id"]
        yes_cents = int(m["yes"] * 100)
        vol = m.get("volume", 0) or 0

        # Update EMA with current price
        update_ema(ticker, yes_cents)
        # Also record for momentum tracker
        record_price_snapshot(ticker, yes_cents)

        state = _price_averages.get(ticker)
        if not state or state["snapshots"] < 5:
            continue  # need enough data

        ema = state["ema"]
        deviation = yes_cents - ema

        if abs(deviation) < _REVERSION_THRESHOLD:
            continue
        if vol < 500:  # only liquid markets
            continue
        # Skip extreme prices — penny bets are illiquid and hard to exit
        if yes_cents < 20 or yes_cents > 80:
            continue

        if deviation > 0:
            # Price spiked UP above average — expect reversion DOWN
            signal = "buy_no"
            price_cents = 100 - yes_cents  # NO price
        else:
            # Price dropped below average — expect reversion UP
            signal = "buy_yes"
            price_cents = yes_cents

        signals.append({
            "ticker": ticker,
            "question": m["question"],
            "signal": signal,
            "price_cents": price_cents,
            "current_yes": yes_cents,
            "ema": round(ema, 1),
            "deviation_cents": round(deviation, 1),
            "volume": vol,
            "strategy": "mean_reversion",
            "url": m.get("url", ""),
        })

    signals.sort(key=lambda x: abs(x["deviation_cents"]), reverse=True)
    return signals[:10]  # top 10 signals


# ---------------------------------------------------------------------------
# 4. MARKET MAKING — Capture bid-ask spread on liquid markets
# ---------------------------------------------------------------------------
# Place both a buy and a sell order around the current price.
# If both fill, we profit the spread. Low-risk, high-frequency strategy.

_market_maker_orders = {}  # ticker -> {"buy_id": str, "sell_id": str, "time": datetime}
_MM_SPREAD_CENTS = 4  # we try to capture 4c spread (2c each side)
_MM_MAX_POSITIONS = 5  # max 5 active market-making positions

def market_make_opportunity(ticker, current_yes_cents, volume):
    """Evaluate if a market is suitable for market making.

    Good MM targets:
    - High volume (1000+)
    - Mid-range prices (30c-70c) — widest natural spread
    - Not already being market-made by us
    """
    if ticker in _market_maker_orders:
        return None
    if len(_market_maker_orders) >= _MM_MAX_POSITIONS:
        return None
    if volume < 1000:
        return None
    if current_yes_cents < 30 or current_yes_cents > 70:
        return None

    # Place buy 2c below current, sell 2c above
    buy_price = current_yes_cents - (_MM_SPREAD_CENTS // 2)
    sell_price = current_yes_cents + (_MM_SPREAD_CENTS // 2)

    if buy_price < 20 or sell_price > 80:
        return None

    return {
        "ticker": ticker,
        "buy_yes_price": buy_price,
        "sell_yes_price": sell_price,
        "spread_cents": sell_price - buy_price,
        "potential_profit_cents": sell_price - buy_price,
    }


def run_market_maker(all_markets):
    """Scan for market making opportunities and place spread orders."""
    if not BOT_CONFIG.get("enabled"):
        return []

    # Check balance
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bal = bal_r.json().get("balance", 0) / 100
            if bal < BOT_CONFIG.get("min_balance_usd", 200):
                return []
    except Exception:
        return []

    fills = []
    for m in all_markets:
        if m["platform"] != "kalshi":
            continue
        ticker = m["id"]
        yes_cents = int(m["yes"] * 100)
        vol = m.get("volume", 0) or 0

        opp = market_make_opportunity(ticker, yes_cents, vol)
        if not opp:
            continue

        # Place buy order (resting limit)
        buy_result = place_kalshi_order(ticker, "yes", opp["buy_yes_price"], count=5)
        if "error" not in buy_result:
            _market_maker_orders[ticker] = {
                "buy_price": opp["buy_yes_price"],
                "sell_price": opp["sell_yes_price"],
                "time": datetime.datetime.utcnow(),
            }
            _log_activity(
                f"📊 MM: {ticker} — BUY@{opp['buy_yes_price']}c / target SELL@{opp['sell_yes_price']}c "
                f"(spread: {opp['spread_cents']}c)",
                "info"
            )
            fills.append(opp)

        if len(fills) >= 2:  # max 2 new MM positions per cycle
            break

    # Clean up old MM orders (> 10 min)
    now = datetime.datetime.utcnow()
    expired = [t for t, o in _market_maker_orders.items()
               if (now - o["time"]).total_seconds() > 600]
    for t in expired:
        del _market_maker_orders[t]

    return fills


# ---------------------------------------------------------------------------
# 5. NEWS SENTIMENT TRADING — Trade on breaking news catalysts
# ---------------------------------------------------------------------------
# Already have news fetching (fetch_news_headlines + research_market).
# This layer automatically trades when strong sentiment aligns with edge.

def news_driven_scan(all_markets):
    """Scan high-value markets for news catalysts that create trading opportunities.

    Strategy: If news is strongly bullish AND Kalshi price is below consensus,
    the news confirms our edge → trade with higher confidence.
    """
    if not BOT_CONFIG.get("enabled"):
        return []

    signals = []
    kalshi_markets = [m for m in all_markets if m["platform"] == "kalshi"]

    # Only check markets with decent volume (news matters less on illiquid markets)
    liquid = [m for m in kalshi_markets if (m.get("volume", 0) or 0) >= 200]
    # Sample top 10 by volume to avoid hammering news API
    liquid.sort(key=lambda x: x.get("volume", 0), reverse=True)

    for m in liquid[:10]:
        question = m["question"]
        research = research_market(question)

        if research["news_count"] == 0:
            continue

        sentiment = research["sentiment"]
        yes_cents = int(m["yes"] * 100)

        # Strong bullish news + low YES price → buy YES
        if sentiment == "bullish" and research["bull_signals"] >= 3 and yes_cents < 60:
            signals.append({
                "ticker": m["id"],
                "question": question,
                "signal": "buy_yes",
                "price_cents": yes_cents,
                "news_sentiment": sentiment,
                "bull_signals": research["bull_signals"],
                "bear_signals": research["bear_signals"],
                "headline_count": research["news_count"],
                "top_headline": research["headlines"][0]["title"] if research["headlines"] else "",
                "strategy": "news_sentiment",
                "volume": m.get("volume", 0),
                "url": m.get("url", ""),
            })
        # Strong bearish news + high YES price → buy NO
        elif sentiment == "bearish" and research["bear_signals"] >= 3 and yes_cents > 40:
            signals.append({
                "ticker": m["id"],
                "question": question,
                "signal": "buy_no",
                "price_cents": 100 - yes_cents,
                "news_sentiment": sentiment,
                "bull_signals": research["bull_signals"],
                "bear_signals": research["bear_signals"],
                "headline_count": research["news_count"],
                "top_headline": research["headlines"][0]["title"] if research["headlines"] else "",
                "strategy": "news_sentiment",
                "volume": m.get("volume", 0),
                "url": m.get("url", ""),
            })

    return signals


# ---------------------------------------------------------------------------
# 6. ENHANCED AUTO-EXIT — Trailing stop + time-based exit
# ---------------------------------------------------------------------------

TRAILING_STOP_PCT = 5    # lock in profit — if we were up 20% and drop 5%, sell
TAKE_PROFIT_TIERS = [    # graduated take-profit tiers
    (30, 0.50),   # sell 50% at +30% profit
    (50, 0.75),   # sell 75% at +50% profit
    (80, 1.00),   # sell 100% at +80% profit
]
TIME_EXIT_HOURS = 72     # force exit after 72 hours if no movement

_position_high_water = {}  # ticker -> highest pnl_pct seen

def enhanced_auto_exit():
    """Advanced exit strategy with trailing stops and time-based exits."""
    if not BOT_CONFIG.get("enabled"):
        return []

    positions = check_position_prices()
    exits = []
    now = datetime.datetime.utcnow()

    for pos in positions:
        pnl_pct = pos.get("pnl_pct")
        ticker = pos["ticker"]

        # NEVER auto-exit same-day game/match bets — let them settle at $0 or $1
        # MoonShark buys underdogs; selling mid-game kills the upside
        _tk = ticker.upper()
        _game_prefixes = ("KXKBL", "KXATP", "KXWTA", "KXNCAA", "KXNBA", "KXNHL",
                          "KXMLB", "KXUFC", "KXMMA", "KXEPL", "KXNFL", "KXMLS",
                          "KXWNBA", "KXSOCCER", "KXPGA", "KXNBA")
        if any(_tk.startswith(p) for p in _game_prefixes):
            continue

        if pnl_pct is None:
            continue

        # Update high water mark
        if ticker not in _position_high_water:
            _position_high_water[ticker] = pnl_pct
        else:
            _position_high_water[ticker] = max(_position_high_water[ticker], pnl_pct)

        high_water = _position_high_water[ticker]
        side = pos["side"]
        count = pos["count"]
        current = pos.get("current_price")
        entry = pos.get("entry_price") or current

        if not current:
            continue

        action = None
        reason = None
        sell_count = count

        # TRAILING STOP: if we were up 15%+ and dropped 5% from peak, sell
        if high_water >= 15 and pnl_pct < high_water - TRAILING_STOP_PCT:
            action = "trailing_stop"
            reason = f"Trailing stop: peak +{high_water}%, now +{pnl_pct}%"

        # GRADUATED TAKE PROFIT
        elif pnl_pct >= TAKE_PROFIT_TIERS[0][0]:
            for threshold, sell_pct in TAKE_PROFIT_TIERS:
                if pnl_pct >= threshold:
                    action = "take_profit"
                    reason = f"Take profit tier: +{pnl_pct}% (threshold {threshold}%)"
                    sell_count = max(1, int(count * sell_pct))

        # STOP LOSS (from original)
        elif pnl_pct <= STOP_LOSS_PCT:
            action = "stop_loss"
            reason = f"Stop loss: {pnl_pct}%"

        # TIME-BASED EXIT: positions stuck for 72+ hours with < 5% gain
        if not action and abs(pnl_pct) < 5:
            # Check trade timestamp
            for t in BOT_STATE.get("all_trades", []):
                if t.get("ticker") == ticker and t.get("timestamp"):
                    try:
                        trade_time = datetime.datetime.fromisoformat(t["timestamp"].replace("Z", ""))
                        hours_held = (now - trade_time).total_seconds() / 3600
                        if hours_held >= TIME_EXIT_HOURS:
                            action = "time_exit"
                            reason = f"Time exit: held {int(hours_held)}h with only +{pnl_pct}%"
                    except Exception:
                        pass
                    break

        if action and current:
            # Price to sell at — aggressive for stop loss, patient for take profit
            if action == "stop_loss":
                sell_price = max(1, current - 5)
            elif action == "time_exit":
                sell_price = max(1, current - 3)
            else:
                sell_price = max(1, entry + 1) if entry else max(1, current - 3)

            result = sell_kalshi_position(ticker, side, sell_price, sell_count)
            success = "error" not in result

            filled = 0
            try:
                order_data = result.get("order", {})
                filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
            except Exception:
                pass

            if success and filled > 0:
                pnl_usd = (sell_price - (entry or current)) * filled / 100
                _log_activity(
                    f"🔄 {action.upper()}: {ticker} SOLD {filled}x @ {sell_price}c "
                    f"(${pnl_usd:+.2f}) — {reason}",
                    "success" if pnl_usd >= 0 else "error"
                )
                exits.append({"ticker": ticker, "action": action, "filled": filled, "pnl_usd": pnl_usd})
                # Clean up tracking
                if filled >= count and ticker in _position_high_water:
                    del _position_high_water[ticker]
            elif success and filled == 0:
                # Place resting order
                if ticker not in _resting_sells:
                    resting = sell_kalshi_position(ticker, side, sell_price, sell_count, resting=True)
                    if "error" not in resting:
                        _resting_sells.add(ticker)
                        _log_activity(f"🔄 {action}: {ticker} — resting sell at {sell_price}c", "info")

    return exits


# ---------------------------------------------------------------------------
# 7. QUANT STRATEGY ORCHESTRATOR — Combine all signals
# ---------------------------------------------------------------------------
# Each strategy produces signals. The orchestrator scores them, deduplicates,
# and executes the best ones with Kelly-sized bets.

BOT_STATE["quant_stats"] = {
    "momentum_signals": 0,
    "mean_reversion_signals": 0,
    "news_signals": 0,
    "mm_fills": 0,
    "kelly_avg_size": 0,
    "strategies_active": [],
}

def run_quant_strategies(all_markets):
    """Master orchestrator — runs all quant strategies and executes best signals."""
    if not BOT_CONFIG.get("enabled"):
        return

    # Get current bankroll for Kelly sizing
    bankroll = 0
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bankroll = bal_r.json().get("balance", 0) / 100
            if bankroll < BOT_CONFIG.get("min_balance_usd", 200):
                return
    except Exception:
        return

    # Check daily limit
    total_daily = BOT_STATE["daily_spent_usd"] + BOT_STATE.get("snipe_daily_spent", 0)
    if total_daily >= BOT_CONFIG["max_daily_usd"]:
        return

    # Get existing positions/events for dedup
    existing_tickers = set()
    existing_events = set()
    try:
        positions = check_position_prices()
        for p in positions:
            existing_tickers.add(p.get("ticker", ""))
            parts = p.get("ticker", "").split("-")
            if len(parts) >= 2:
                existing_events.add("-".join(parts[:2]))
        # Position limit check
        if len(positions) >= BOT_CONFIG.get("max_open_positions", 20):
            return
    except Exception:
        pass

    # Collect signals from all strategies
    all_signals = []
    active_strategies = []

    # Mean reversion signals
    try:
        mr_signals = find_mean_reversion_signals(all_markets)
        BOT_STATE["quant_stats"]["mean_reversion_signals"] = len(mr_signals)
        if mr_signals:
            active_strategies.append("mean_reversion")
        for sig in mr_signals:
            sig["confidence"] = min(0.9, 0.5 + abs(sig["deviation_cents"]) / 30)
            sig["strategy"] = "mean_reversion"
            all_signals.append(sig)
    except Exception as e:
        print(f"[QUANT] Mean reversion error: {e}")

    # News sentiment signals (only every 5th cycle to avoid rate limiting)
    try:
        cycle = BOT_STATE.get("_quant_cycle", 0)
        if cycle % 5 == 0:
            news_signals = news_driven_scan(all_markets)
            BOT_STATE["quant_stats"]["news_signals"] = len(news_signals)
            if news_signals:
                active_strategies.append("news_sentiment")
            for sig in news_signals:
                sig["confidence"] = min(0.85, 0.4 + sig.get("bull_signals", 0) * 0.1)
                all_signals.append(sig)
    except Exception as e:
        print(f"[QUANT] News scan error: {e}")

    # Momentum — boost confidence of existing consensus signals
    momentum_opps = scan_momentum_opportunities()
    BOT_STATE["quant_stats"]["momentum_signals"] = len(momentum_opps)
    if momentum_opps:
        active_strategies.append("momentum")

    # Economic data signals (every 10th cycle — data is slow-moving)
    try:
        cycle = BOT_STATE.get("_quant_cycle", 0)
        if cycle % 10 == 0 and FRED_API_KEY:
            kalshi_mkts = [m for m in all_markets if m["platform"] == "kalshi"]
            econ_signals_found = 0
            for m in kalshi_mkts[:50]:  # check top 50 for economic relevance
                econ_sig = econ_enhanced_signal(m["question"], m["yes"])
                if econ_sig:
                    econ_signals_found += 1
                    yes_cents = int(m["yes"] * 100)
                    all_signals.append({
                        "ticker": m["id"],
                        "question": m["question"],
                        "signal": econ_sig["signal"],
                        "price_cents": yes_cents if econ_sig["signal"] == "buy_yes" else 100 - yes_cents,
                        "confidence": econ_sig["confidence"],
                        "strategy": "economic_data",
                        "econ_indicator": econ_sig["indicator"],
                        "econ_trend": econ_sig["trend"],
                        "url": m.get("url", ""),
                    })
            if econ_signals_found:
                active_strategies.append("economic_data")
                BOT_STATE["quant_stats"]["econ_signals"] = econ_signals_found
    except Exception as e:
        print(f"[QUANT] Economic data error: {e}")

    BOT_STATE["quant_stats"]["strategies_active"] = active_strategies
    BOT_STATE["_quant_cycle"] = BOT_STATE.get("_quant_cycle", 0) + 1

    # ORDERBOOK CONFIRMATION — boost confidence of signals with favorable order book
    for sig in all_signals:
        try:
            ticker = sig.get("ticker", "")
            ob = analyze_orderbook(ticker)
            if ob and ob.get("signal"):
                # If orderbook agrees with our signal, boost confidence
                if ob["signal"] == sig.get("signal"):
                    sig["confidence"] = min(0.95, sig.get("confidence", 0.5) + 0.15)
                    sig["ob_confirmed"] = True
                # If orderbook disagrees, reduce confidence
                elif ob["signal"] and ob["signal"] != sig.get("signal"):
                    sig["confidence"] = max(0.1, sig.get("confidence", 0.5) - 0.1)
                    sig["ob_confirmed"] = False
                sig["ob_imbalance"] = ob["imbalance"]
                sig["ob_spread"] = ob["spread"]
                sig["ob_liquidity"] = ob["liquidity_score"]
        except Exception:
            pass

    # VOLATILITY BOOST — prefer higher volatility markets (more profit opportunity)
    for sig in all_signals:
        ticker = sig.get("ticker", "")
        vol_score = get_volatility_score(ticker)
        if vol_score >= 5:
            sig["confidence"] = min(0.95, sig.get("confidence", 0.5) + 0.05)
            sig["volatility_score"] = vol_score

    # Score and sort all signals
    all_signals.sort(key=lambda x: x.get("confidence", 0), reverse=True)

    # Execute top signals with Kelly sizing
    trades_this_round = 0
    kelly_sizes = []

    for sig in all_signals[:5]:  # max 5 quant trades per cycle
        ticker = sig.get("ticker", "")
        if ticker in existing_tickers:
            continue
        event_key = ticker.split("-")[0] if ticker else ""
        if event_key in existing_events:
            continue

        # Block banned categories (weather etc)
        blocked = BOT_CONFIG.get("blocked_categories", [])
        if blocked:
            qcat = classify_market_category(sig.get("question", ""), ticker)
            if qcat in blocked:
                continue

        # CORRELATION CHECK — don't over-concentrate
        cat_allowed, cat_name, cat_count = check_category_limit(
            sig.get("question", ""), ticker, positions
        )
        if not cat_allowed:
            continue

        # Daily limit re-check
        total_daily = BOT_STATE["daily_spent_usd"] + BOT_STATE.get("snipe_daily_spent", 0)
        if total_daily >= BOT_CONFIG["max_daily_usd"]:
            break

        price_cents = sig.get("price_cents", 0)
        if price_cents < 20 or price_cents > 80:
            continue

        # Kelly sizing
        confidence = sig.get("confidence", 0.5)
        count = kelly_count(bankroll, price_cents, confidence)
        cost_usd = (price_cents * count) / 100.0

        # Cap cost to remaining daily budget
        remaining = BOT_CONFIG["max_daily_usd"] - total_daily
        if cost_usd > remaining:
            count = max(1, int(remaining * 100 / price_cents))
            cost_usd = (price_cents * count) / 100.0

        if cost_usd > BOT_CONFIG["max_bet_usd"]:
            count = max(1, int(BOT_CONFIG["max_bet_usd"] * 100 / price_cents))
            cost_usd = (price_cents * count) / 100.0

        side = sig["signal"].replace("buy_", "")
        strategy = sig.get("strategy", "unknown")

        _log_activity(
            f"🧠 QUANT [{strategy}]: {side.upper()} {ticker} @ {price_cents}c x{count} "
            f"(${cost_usd:.2f}, conf={confidence:.0%}) — {sig.get('question', '')[:40]}",
            "info"
        )

        result = place_kalshi_order(ticker, side, price_cents, count=count)
        success = "error" not in result

        trade_record = {
            "timestamp": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "ticker": ticker,
            "question": sig.get("question", ""),
            "side": side,
            "price_cents": price_cents,
            "count": count,
            "cost_usd": cost_usd,
            "strategy": strategy,
            "confidence": confidence,
            "result": result,
            "success": success,
            "bot_version": BOT_VERSION,
        }

        BOT_STATE["all_trades"].append(trade_record)
        if success:
            BOT_STATE["daily_spent_usd"] += cost_usd
            BOT_STATE["trades_today"].append(trade_record)
            trades_this_round += 1
            kelly_sizes.append(cost_usd)
            existing_tickers.add(ticker)
            existing_events.add(event_key)
            _log_activity(
                f"🧠 FILLED [{strategy}]: {side.upper()} {ticker} @ {price_cents}c x{count} = ${cost_usd:.2f}",
                "success"
            )
        else:
            err = result.get("error", "")[:60]
            _log_activity(f"🧠 FAILED [{strategy}]: {ticker} — {err}", "error")

        _save_state()

    if kelly_sizes:
        BOT_STATE["quant_stats"]["kelly_avg_size"] = round(sum(kelly_sizes) / len(kelly_sizes), 2)

    # Run market maker (separate from directional trades)
    try:
        mm_fills = run_market_maker(all_markets)
        BOT_STATE["quant_stats"]["mm_fills"] = len(mm_fills)
        if mm_fills:
            active_strategies.append("market_making")
    except Exception as e:
        print(f"[QUANT] Market maker error: {e}")

    if trades_this_round > 0:
        _log_activity(
            f"🧠 Quant round: {trades_this_round} trades via {active_strategies}",
            "success"
        )


# ===========================================================================
# SPEED + INTELLIGENCE UPGRADES
# ===========================================================================

# ---------------------------------------------------------------------------
# 8. PARALLEL ORDER EXECUTION — Place multiple trades simultaneously
# ---------------------------------------------------------------------------

def place_orders_parallel(orders):
    """Execute multiple Kalshi orders in parallel using ThreadPoolExecutor.

    Args:
        orders: list of dicts with {ticker, side, price_cents, count, metadata}

    Returns:
        list of {order, result, success} dicts
    """
    if not orders:
        return []

    def _exec_order(order):
        result = place_kalshi_order(
            order["ticker"], order["side"], order["price_cents"],
            count=order.get("count", 1)
        )
        return {
            "order": order,
            "result": result,
            "success": "error" not in result,
        }

    results = []
    with ThreadPoolExecutor(max_workers=min(5, len(orders))) as pool:
        futures = {pool.submit(_exec_order, o): o for o in orders}
        for future in as_completed(futures, timeout=15):
            try:
                results.append(future.result(timeout=10))
            except Exception as e:
                results.append({
                    "order": futures[future],
                    "result": {"error": str(e)},
                    "success": False,
                })
    return results


# ---------------------------------------------------------------------------
# 9. ORDER BOOK DEPTH ANALYSIS — See beyond top-of-book
# ---------------------------------------------------------------------------

_orderbook_cache = {}  # ticker -> {"bids": [], "asks": [], "time": datetime}
_OB_CACHE_TTL = 15     # seconds

def fetch_orderbook(ticker):
    """Fetch full order book for a Kalshi market. Returns bid/ask depth."""
    now = datetime.datetime.utcnow()
    cached = _orderbook_cache.get(ticker)
    if cached and (now - cached["time"]).total_seconds() < _OB_CACHE_TTL:
        return cached

    path = f"/markets/{ticker}/orderbook"
    headers = signed_headers("GET", path)
    if not headers:
        return None

    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers, timeout=5,
        )
        if not resp.ok:
            return None
        data = resp.json().get("orderbook", {})
        # Parse yes bids and asks
        yes_bids = []  # people wanting to buy YES (support below)
        yes_asks = []  # people wanting to sell YES (resistance above)
        for level in (data.get("yes") or []):
            price = 0
            try:
                price = int(round(float(str(level.get("price_dollars", level.get("price", 0)))) * 100))
            except Exception:
                continue
            qty = 0
            try:
                qty = int(float(str(level.get("quantity_fp", level.get("quantity", 0)))))
            except Exception:
                pass
            if price > 0 and qty > 0:
                yes_asks.append({"price": price, "qty": qty})

        for level in (data.get("no") or []):
            price = 0
            try:
                price = int(round(float(str(level.get("price_dollars", level.get("price", 0)))) * 100))
            except Exception:
                continue
            qty = 0
            try:
                qty = int(float(str(level.get("quantity_fp", level.get("quantity", 0)))))
            except Exception:
                pass
            if price > 0 and qty > 0:
                yes_bids.append({"price": 100 - price, "qty": qty})

        result = {
            "yes_bids": sorted(yes_bids, key=lambda x: x["price"], reverse=True),
            "yes_asks": sorted(yes_asks, key=lambda x: x["price"]),
            "time": now,
            "spread": 0,
            "bid_depth": sum(b["qty"] for b in yes_bids),
            "ask_depth": sum(a["qty"] for a in yes_asks),
        }
        if yes_bids and yes_asks:
            result["spread"] = yes_asks[0]["price"] - yes_bids[0]["price"]

        _orderbook_cache[ticker] = result
        return result
    except Exception as e:
        print(f"[OB] Error fetching orderbook for {ticker}: {e}")
        return None


def analyze_orderbook(ticker):
    """Analyze order book for trading signals.

    Returns:
        dict with liquidity score, imbalance signal, recommended side, spread
    """
    ob = fetch_orderbook(ticker)
    if not ob:
        return None

    bid_depth = ob["bid_depth"]
    ask_depth = ob["ask_depth"]
    spread = ob["spread"]
    total_depth = bid_depth + ask_depth

    if total_depth == 0:
        return None

    # Imbalance: if bids >> asks, price likely going up (buy YES)
    # if asks >> bids, price likely going down (buy NO)
    imbalance = (bid_depth - ask_depth) / total_depth  # -1 to +1

    liquidity_score = min(100, total_depth)  # 0-100

    signal = None
    if imbalance > 0.3 and spread <= 5:
        signal = "buy_yes"  # strong bid side, price going up
    elif imbalance < -0.3 and spread <= 5:
        signal = "buy_no"   # strong ask side, price going down

    return {
        "bid_depth": bid_depth,
        "ask_depth": ask_depth,
        "spread": spread,
        "imbalance": round(imbalance, 3),
        "liquidity_score": liquidity_score,
        "signal": signal,
    }


# ---------------------------------------------------------------------------
# 10. CORRELATION FILTER — Diversify across categories
# ---------------------------------------------------------------------------
# Don't put all eggs in one basket. Max N positions per category.

_CATEGORY_KEYWORDS = {
    "nba": ["nba", "basketball", "lakers", "celtics", "warriors", "bucks", "nuggets",
            "knicks", "nets", "heat", "76ers", "mavericks", "suns", "cavaliers"],
    "nfl": ["nfl", "football", "chiefs", "eagles", "49ers", "ravens", "bills",
            "cowboys", "dolphins", "packers", "steelers", "bengals"],
    "mlb": ["mlb", "baseball", "yankees", "dodgers", "mets", "braves", "astros",
            "padres", "phillies", "cubs", "red sox"],
    "nhl": ["nhl", "hockey", "oilers", "bruins", "avalanche", "maple leafs",
            "penguins", "rangers", "golden knights"],
    "soccer": ["soccer", "premier league", "epl", "champions league", "liverpool",
               "arsenal", "manchester", "chelsea", "barcelona", "real madrid"],
    "politics": ["president", "election", "congress", "senate", "governor",
                 "democrat", "republican", "trump", "biden", "political"],
    "economics": ["gdp", "inflation", "cpi", "fed", "interest rate", "unemployment",
                  "recession", "jobs report", "economic", "treasury"],
    "weather": ["temperature", "weather", "hurricane", "tornado", "rainfall",
                "snow", "climate", "degrees", "fahrenheit", "celsius"],
    "crypto": ["bitcoin", "ethereum", "crypto", "btc", "eth", "solana"],
    "tech": ["ai", "artificial intelligence", "openai", "google", "apple",
             "microsoft", "meta", "tesla", "spacex", "tech"],
    "entertainment": ["oscar", "grammy", "emmy", "movie", "film", "box office",
                      "netflix", "disney", "streaming"],
    "tennis": ["tennis", "atp", "wta", " vs ", "wimbledon", "us open",
               "french open", "australian open", "grand slam", "challenger",
               "roland garros", "miami open"],
    "mma": ["ufc", "mma", "bellator", "fight night", "ppv", "octagon"],
    "golf": ["pga", "golf", "masters", "open championship", "ryder cup"],
}


def classify_market_category(question, ticker=""):
    """Classify a market into a category for correlation management."""
    text = (question + " " + ticker).lower()
    scores = {}
    for cat, keywords in _CATEGORY_KEYWORDS.items():
        hits = sum(1 for kw in keywords if kw in text)
        if hits > 0:
            scores[cat] = hits
    if not scores:
        return "other"
    return max(scores, key=scores.get)


def get_category_exposure(positions):
    """Count how many positions are in each category."""
    exposure = {}
    for pos in positions:
        title = pos.get("title", "") or pos.get("question", "")
        ticker = pos.get("ticker", "")
        cat = classify_market_category(title, ticker)
        exposure[cat] = exposure.get(cat, 0) + 1
    return exposure


def check_category_limit(question, ticker, positions):
    """Check if adding a position in this category would exceed the limit.

    Returns:
        (allowed: bool, category: str, current_count: int)
    """
    cat = classify_market_category(question, ticker)
    max_per_cat = BOT_CONFIG.get("max_category_exposure", 10)
    exposure = get_category_exposure(positions)
    current = exposure.get(cat, 0)
    return current < max_per_cat, cat, current


# ---------------------------------------------------------------------------
# 11. VOLATILITY SCORING — Focus on high-opportunity markets
# ---------------------------------------------------------------------------
# Markets with more price movement have more profit potential.

_volatility_scores = {}  # ticker -> {"score": float, "samples": int}

def update_volatility(ticker, price_cents):
    """Track price variance for volatility scoring."""
    if ticker not in _volatility_scores:
        _volatility_scores[ticker] = {"prices": deque(maxlen=20), "score": 0}

    state = _volatility_scores[ticker]
    state["prices"].append(price_cents)

    if len(state["prices"]) >= 5:
        prices = list(state["prices"])
        # Calculate standard deviation of recent prices
        mean_p = sum(prices) / len(prices)
        variance = sum((p - mean_p) ** 2 for p in prices) / len(prices)
        state["score"] = round(math.sqrt(variance), 2)


def get_volatility_score(ticker):
    """Get volatility score for a ticker. Higher = more opportunity."""
    state = _volatility_scores.get(ticker)
    if not state:
        return 0
    return state["score"]


def rank_by_volatility(tickers, min_score=2.0):
    """Filter and rank tickers by volatility — focus capital on movers."""
    scored = []
    for t in tickers:
        v = get_volatility_score(t)
        if v >= min_score:
            scored.append((t, v))
    scored.sort(key=lambda x: x[1], reverse=True)
    return scored


# ---------------------------------------------------------------------------
# 12. AUTO-REINVEST ON SETTLEMENT — Immediately redeploy settled capital
# ---------------------------------------------------------------------------

_last_settlement_check = None
_known_settled = set()  # tickers we already processed

# Category win rate tracking — auto-adjust sizing based on what's winning
# _CATEGORY_STATS declared early (near BOT_STATE) so _load_state() can populate it

def _update_category_stats(ticker, title, won, pnl_usd):
    """Track win rate by category for auto-adjustment."""
    cat = classify_market_category(title or "", ticker or "")
    if cat not in _CATEGORY_STATS:
        _CATEGORY_STATS[cat] = {"wins": 0, "losses": 0, "pnl": 0.0}
    if won:
        _CATEGORY_STATS[cat]["wins"] += 1
    else:
        _CATEGORY_STATS[cat]["losses"] += 1
    _CATEGORY_STATS[cat]["pnl"] += pnl_usd

def _category_multiplier(ticker, title):
    """Dynamic bet size multiplier based on ACTUAL category performance.

    Learns from _CATEGORY_STATS (rebuilt from Kalshi on startup).
    Needs 3+ bets in a category before adjusting — avoids overreacting to 1 win.
    """
    cat = classify_market_category(title or "", ticker or "")
    stats = _CATEGORY_STATS.get(cat, {})
    wins = stats.get("wins", 0)
    losses = stats.get("losses", 0)
    total = wins + losses

    # Not enough data — use neutral multiplier
    if total < 3:
        return 1.0

    win_rate = wins / total

    # Dynamic multiplier tiers based on proven win rate
    # NOTE: Never fully block (0.0) a category — use 0.25 floor so the bot
    # can still discover wins.  0% WR on longshots is expected early; a
    # single win flips the economics.  Weather is the only hard-block.
    if win_rate >= 0.25:
        mult = 2.0   # strong performer — bet aggressively
    elif win_rate >= 0.15:
        mult = 1.5   # above average
    elif win_rate >= 0.10:
        mult = 1.0   # break-even territory
    elif win_rate > 0:
        mult = 0.5   # weak — reduce exposure
    else:
        mult = 0.0   # 0% win rate with 3+ trades — hard block, stop burning money

    # Always block weather
    if cat == "weather":
        mult = 0.0

    return mult


# ---------------------------------------------------------------------------
# LEARNING ENGINE — Analyzes trade history to identify winning patterns
# ---------------------------------------------------------------------------

def _price_bucket(price_cents):
    """Map price to a bucket for learning analysis."""
    if not price_cents:
        return "unknown"
    if price_cents < 15:
        return "10-15"
    elif price_cents < 20:
        return "15-20"
    elif price_cents < 25:
        return "20-25"
    elif price_cents < 30:
        return "25-30"
    elif price_cents < 35:
        return "30-35"
    elif price_cents < 45:
        return "35-45"
    elif price_cents < 60:
        return "45-60"
    elif price_cents < 75:
        return "60-75"
    elif price_cents < 90:
        return "75-90"
    else:
        return "90+"


def _game_situation_key(rec):
    """Map game state to a situation bucket for learning."""
    margin = rec.get("game_margin")
    period = rec.get("game_period", "")
    if margin is None:
        return "unknown"
    # Classify period as early/mid/late
    period_phase = "unknown"
    p_upper = period.upper()
    if any(x in p_upper for x in ["Q4", "4TH", "OT", "P3", "3RD", "2H"]):
        period_phase = "late"
    elif any(x in p_upper for x in ["Q3", "Q2", "P2", "2ND", "1H"]):
        period_phase = "mid"
    elif any(x in p_upper for x in ["Q1", "1ST", "P1"]):
        period_phase = "early"
    # Classify margin
    if margin == 0:
        margin_key = "tied"
    elif margin <= 3:
        margin_key = "close_1-3"
    elif margin <= 7:
        margin_key = "mid_4-7"
    elif margin <= 12:
        margin_key = "far_8-12"
    else:
        margin_key = "blowout_13+"
    return f"{period_phase}_{margin_key}"


def _compute_bucket_stats(trades, key_fn):
    """Compute win/loss/ROI stats grouped by a key function."""
    buckets = {}
    for t in trades:
        if not t.get("result"):
            continue  # skip unsettled
        key = key_fn(t)
        if key not in buckets:
            buckets[key] = {"wins": 0, "losses": 0, "pnl": 0.0, "total_cost": 0.0}
        b = buckets[key]
        if t["result"] == "win":
            b["wins"] += 1
        elif t["result"] == "loss":
            b["losses"] += 1
        b["pnl"] += t.get("pnl_usd", 0) or 0
        b["total_cost"] += t.get("cost_usd", 0) or 0

    # Compute derived stats
    result = {}
    for key, b in buckets.items():
        total = b["wins"] + b["losses"]
        if total == 0:
            continue
        win_rate = b["wins"] / total
        roi = b["pnl"] / max(0.01, b["total_cost"])
        # Confidence: 0 for <5, 0.5 for 5-9, 1.0 for 10+
        if total < 5:
            confidence = 0.0
        elif total < 10:
            confidence = 0.5
        else:
            confidence = 1.0
        # Weight: scale by win rate and ROI
        if win_rate >= 0.25:
            weight = 2.5
        elif win_rate >= 0.15:
            weight = 1.8
        elif win_rate >= 0.10:
            weight = 1.2
        elif win_rate > 0:
            weight = 0.5
        else:
            weight = 0.0  # 0% win rate = block
        result[key] = {
            "weight": round(weight, 2),
            "win_rate": round(win_rate, 4),
            "roi": round(roi, 4),
            "sample_size": total,
            "wins": b["wins"],
            "losses": b["losses"],
            "pnl": round(b["pnl"], 2),
            "confidence": confidence,
        }
    return result


def _learning_engine():
    """Analyze trade history and adjust strategy parameters automatically.

    Runs hourly + on startup. Requires 10+ settled trades before making adjustments.
    """
    settled = [t for t in _TRADE_JOURNAL if t.get("result")]
    if len(settled) < 10:
        return  # not enough data to learn from

    insights = []

    # 1. Category performance
    cat_weights = _compute_bucket_stats(settled, lambda t: t.get("category", "other"))
    _LEARNING_STATE["parameters"]["category_weights"] = cat_weights
    # Find best/worst categories
    for cat, stats in sorted(cat_weights.items(), key=lambda x: x[1]["win_rate"], reverse=True):
        if stats["confidence"] >= 0.5:
            if stats["win_rate"] >= 0.15:
                insights.append(f"✅ {cat}: {stats['win_rate']:.0%} win rate ({stats['wins']}W/{stats['losses']}L) → BOOSTED")
            elif stats["win_rate"] == 0 and stats["sample_size"] >= 5:
                insights.append(f"🚫 {cat}: 0% win rate on {stats['sample_size']} trades → BLOCKED")

    # 2. Sport type performance
    sport_weights = _compute_bucket_stats(settled, lambda t: t.get("sport_type", "other"))
    _LEARNING_STATE["parameters"]["sport_weights"] = sport_weights

    # 3. Price range performance
    price_weights = _compute_bucket_stats(settled, lambda t: _price_bucket(t.get("price_cents")))
    _LEARNING_STATE["parameters"]["price_range_weights"] = price_weights
    best_price = max(price_weights.items(), key=lambda x: x[1]["win_rate"], default=(None, None))
    if best_price[1] and best_price[1]["confidence"] >= 0.5:
        insights.append(f"💰 Best price range: {best_price[0]}¢ ({best_price[1]['win_rate']:.0%} win rate)")

    # 4. Game situation performance (only for trades with game data)
    game_trades = [t for t in settled if t.get("game_margin") is not None]
    if len(game_trades) >= 5:
        game_weights = _compute_bucket_stats(game_trades, _game_situation_key)
        _LEARNING_STATE["parameters"]["game_situation_weights"] = game_weights

    # 5. ESPN edge performance
    edge_trades = [t for t in settled if t.get("espn_edge") is not None]
    if len(edge_trades) >= 5:
        def _edge_bucket(t):
            e = t.get("espn_edge", 0) or 0
            if e < 0:
                return "negative"
            elif e < 0.05:
                return "0-5%"
            elif e < 0.10:
                return "5-10%"
            elif e < 0.20:
                return "10-20%"
            else:
                return "20%+"
        edge_weights = _compute_bucket_stats(edge_trades, _edge_bucket)
        _LEARNING_STATE["parameters"]["edge_weights"] = edge_weights
        # Find minimum profitable edge
        for bucket in ["negative", "0-5%", "5-10%", "10-20%", "20%+"]:
            if bucket in edge_weights and edge_weights[bucket].get("win_rate", 0) >= 0.10:
                insights.append(f"📊 Minimum profitable edge: {bucket}")
                break

    # 6. Time of day performance
    hour_weights = _compute_bucket_stats(settled, lambda t: str(t.get("entry_hour", "?")))
    _LEARNING_STATE["parameters"]["hour_weights"] = hour_weights

    # 7. Strategy performance
    strat_weights = _compute_bucket_stats(settled, lambda t: t.get("strategy", "unknown"))
    _LEARNING_STATE["parameters"]["strategy_weights"] = strat_weights

    # 8. Market type performance
    mtype_weights = _compute_bucket_stats(settled, lambda t: t.get("market_type", "unknown"))
    _LEARNING_STATE["parameters"]["market_type_weights"] = mtype_weights

    # Update state
    _LEARNING_STATE["version"] = _LEARNING_STATE.get("version", 0) + 1
    _LEARNING_STATE["last_run"] = datetime.datetime.utcnow().isoformat() + "Z"
    _LEARNING_STATE["insights"] = insights[-20:]  # keep last 20

    _log_activity(
        f"🧠 Learning v{_LEARNING_STATE['version']}: {len(settled)} trades analyzed, "
        f"{len([i for i in insights if '✅' in i])} boosted, "
        f"{len([i for i in insights if '🚫' in i])} blocked",
        "info"
    )
    _save_state()


def _learning_multiplier(ticker, title, price_cents=None, game_info=None, espn_edge=None):
    """Compute composite bet sizing multiplier from all learned dimensions.

    Returns 0.0 (skip) to 3.0 (max confidence). Each dimension contributes
    independently, weighted by confidence. Uses geometric mean.
    """
    import math
    params = _LEARNING_STATE.get("parameters", {})
    if not params:
        return 1.0  # no learned data yet, neutral

    multipliers = []

    # Category weight
    cat = classify_market_category(title or "", ticker or "")
    cat_w = params.get("category_weights", {}).get(cat, {})
    if cat_w.get("confidence", 0) >= 0.5:
        # Hard-block 0% win rate categories — stop burning money on proven losers
        w = cat_w["weight"]
        multipliers.append(w)

    # Sport type weight
    t_upper = (ticker or "").upper()
    sport = "other"
    sport_map = {"KXATP": "tennis", "KXWTA": "tennis", "KXNBA": "basketball", "KXNHL": "hockey",
                 "KXMLB": "baseball", "KXNFL": "football", "KXNCAAMB": "college_basketball",
                 "KXNCAAWB": "college_basketball", "KXKBL": "kbo", "KXSOCCER": "soccer",
                 "KXMLS": "soccer", "KXEPL": "soccer"}
    for pfx, sp in sport_map.items():
        if t_upper.startswith(pfx):
            sport = sp
            break
    sport_w = params.get("sport_weights", {}).get(sport, {})
    if sport_w.get("confidence", 0) >= 0.5:
        # Floor at 0.15 — never fully block a sport (same rationale as categories)
        multipliers.append(max(sport_w["weight"], 0.15))

    # Price range weight
    if price_cents:
        bucket = _price_bucket(price_cents)
        price_w = params.get("price_range_weights", {}).get(bucket, {})
        if price_w.get("confidence", 0) >= 0.5:
            multipliers.append(price_w["weight"])

    # Game situation weight
    if game_info and isinstance(game_info, dict):
        sit_key = _game_situation_key(game_info)
        sit_w = params.get("game_situation_weights", {}).get(sit_key, {})
        if sit_w.get("confidence", 0) >= 0.5:
            multipliers.append(sit_w["weight"])

    # Hour weight
    hour = str(datetime.datetime.utcnow().hour)
    hour_w = params.get("hour_weights", {}).get(hour, {})
    if hour_w.get("confidence", 0) >= 0.5:
        # Floor at 0.15 — don't fully block any hour
        multipliers.append(max(hour_w["weight"], 0.15))

    if not multipliers:
        return 1.0  # no data for any dimension

    # Geometric mean — prevents one dimension from dominating
    product = 1.0
    for m in multipliers:
        product *= max(0.01, m)  # floor at 0.01 to avoid zeroing out
    result = product ** (1.0 / len(multipliers))
    return max(0.0, min(3.0, round(result, 3)))


# ---------------------------------------------------------------------------
# TRADE JOURNAL — Comprehensive data tracking for pattern recognition
# ---------------------------------------------------------------------------
# Day 1 = March 16, 2026. Only count wins/losses from this date forward.
TRADE_JOURNAL_START = "2026-03-16"

# _TRADE_JOURNAL declared early (near BOT_STATE) so _load_state() can populate it

def _enrich_trade_record(ticker, title, side, price_cents, count, cost_usd, strategy, is_live=False, close_time=None, game_info=None, espn_edge_data=None, orderbook_data=None):
    """Create an enriched trade record with all metadata for pattern analysis."""
    now = datetime.datetime.utcnow()
    cat = classify_market_category(title or "", ticker or "")
    vol_score = get_volatility_score(ticker)

    # Detect if it's a sports match
    t_upper = (ticker or "").upper()
    sport_type = "other"
    for pfx in ["KXATP", "KXWTA"]:
        if t_upper.startswith(pfx):
            sport_type = "tennis"
            break
    for pfx in ["KXNBA"]:
        if t_upper.startswith(pfx):
            sport_type = "basketball"
            break
    for pfx in ["KXNHL"]:
        if t_upper.startswith(pfx):
            sport_type = "hockey"
            break
    for pfx in ["KXMLB"]:
        if t_upper.startswith(pfx):
            sport_type = "baseball"
            break
    for pfx in ["KXNFL"]:
        if t_upper.startswith(pfx):
            sport_type = "football"
            break
    for pfx in ["KXSOCCER", "KXMLS", "KXEPL"]:
        if t_upper.startswith(pfx):
            sport_type = "soccer"
            break
    for pfx in ["KXNCAAMB", "KXNCAAWB"]:
        if t_upper.startswith(pfx):
            sport_type = "college_basketball"
            break
    for pfx in ["KXKBL"]:
        if t_upper.startswith(pfx):
            sport_type = "kbo"
            break
    for pfx in ["KXMMA", "KXUFC"]:
        if t_upper.startswith(pfx):
            sport_type = "mma"
            break

    # Hour of day (for time-of-day patterns)
    hour = now.hour
    day_of_week = now.strftime("%A")

    # --- New enrichment fields ---
    # Entry odds: implied probability at entry
    entry_odds = round(price_cents / 100.0, 4) if price_cents else 0

    # Hours to close and market type classification
    hours_to_close = None
    market_type = "unknown"
    if close_time:
        try:
            ct_dt = datetime.datetime.fromisoformat(str(close_time).replace("Z", "+00:00")).replace(tzinfo=None)
            hours_to_close = round((ct_dt - now).total_seconds() / 3600, 2)
            if hours_to_close is not None:
                if hours_to_close <= 0:
                    market_type = "live_sports"
                elif hours_to_close <= 12:
                    market_type = "same_day"
                elif hours_to_close <= 72:
                    market_type = "multi_day"
                else:
                    market_type = "long_dated"
        except Exception:
            pass

    # Underdog / favorite flags
    is_underdog = price_cents < 40 if price_cents else False
    is_favorite = price_cents > 60 if price_cents else False

    # Bet sizing and payout
    bet_size_usd = round(cost_usd, 2)
    potential_payout_usd = round((100 * count) / 100.0, 2) if count else 0
    risk_reward_ratio = round(potential_payout_usd / cost_usd, 3) if cost_usd > 0 else 0

    # --- Game state at entry (from ESPN live scores) ---
    _gs = {}
    if game_info and isinstance(game_info, dict):
        _gs = {
            "game_score_home": game_info.get("home_score"),
            "game_score_away": game_info.get("away_score"),
            "game_margin": None,
            "game_period": game_info.get("clock", ""),
            "game_state": game_info.get("state", ""),
            "game_league": game_info.get("league", ""),
            "bet_team_leading": None,
        }
        try:
            hs = int(game_info.get("home_score", 0))
            as_ = int(game_info.get("away_score", 0))
            _gs["game_margin"] = abs(hs - as_)
        except Exception:
            pass

    # --- Sportsbook edge data ---
    _edge = {}
    if espn_edge_data and isinstance(espn_edge_data, dict):
        _edge = {
            "espn_implied_prob": espn_edge_data.get("espn_implied"),
            "kalshi_implied_prob": round(price_cents / 100.0, 4) if price_cents else None,
            "espn_edge": espn_edge_data.get("espn_edge"),
            "odds_provider": espn_edge_data.get("provider", ""),
        }

    # --- Orderbook data ---
    _ob = {}
    if orderbook_data and isinstance(orderbook_data, dict):
        _ob = {
            "ob_spread": orderbook_data.get("spread"),
            "ob_bid_depth": orderbook_data.get("bid_depth"),
            "ob_ask_depth": orderbook_data.get("ask_depth"),
            "ob_imbalance": orderbook_data.get("imbalance"),
            "ob_liquidity": orderbook_data.get("liquidity_score"),
        }

    # --- Momentum data ---
    _mom = {}
    try:
        mom = get_momentum(ticker)
        if mom:
            _mom = {
                "momentum_direction": mom.get("direction", "flat"),
                "momentum_magnitude": mom.get("magnitude", 0),
                "momentum_velocity": mom.get("velocity", 0),
            }
    except Exception:
        pass

    return {
        "ticker": ticker,
        "title": title,
        "side": side,
        "price_cents": price_cents,
        "count": count,
        "cost_usd": round(cost_usd, 2),
        "strategy": strategy,
        "category": cat,
        "sport_type": sport_type,
        "is_live": is_live,
        "volatility": vol_score,
        "entry_time": now.isoformat() + "Z",
        "entry_hour": hour,
        "entry_day": day_of_week,
        "entry_date": now.strftime("%Y-%m-%d"),
        "result": None,  # filled on settlement: "win", "loss", "even"
        "pnl_usd": None,  # filled on settlement
        "settlement_time": None,
        "hold_duration_mins": None,
        "price_at_entry": price_cents,
        # --- New fields for pattern analysis ---
        "entry_odds": entry_odds,
        "market_type": market_type,
        "hours_to_close": hours_to_close,
        "is_underdog": is_underdog,
        "is_favorite": is_favorite,
        "bet_size_usd": bet_size_usd,
        "potential_payout_usd": potential_payout_usd,
        "risk_reward_ratio": risk_reward_ratio,
        # --- Game state at entry ---
        **_gs,
        # --- Sportsbook edge ---
        **_edge,
        # --- Orderbook ---
        **_ob,
        # --- Momentum ---
        **_mom,
    }


def _journal_trade(ticker, title, side, price_cents, count, cost_usd, strategy, is_live=False, close_time=None, game_info=None, espn_edge_data=None, orderbook_data=None):
    """Add a trade to the journal with full enrichment."""
    rec = _enrich_trade_record(ticker, title, side, price_cents, count, cost_usd, strategy, is_live, close_time=close_time, game_info=game_info, espn_edge_data=espn_edge_data, orderbook_data=orderbook_data)
    _TRADE_JOURNAL.append(rec)
    return rec


def _journal_settle(ticker, won, pnl_usd):
    """Update journal entry with settlement result."""
    now = datetime.datetime.utcnow()
    for rec in reversed(_TRADE_JOURNAL):
        if rec["ticker"] == ticker and rec["result"] is None:
            rec["result"] = "win" if won else ("loss" if pnl_usd < -0.005 else "even")
            rec["pnl_usd"] = round(pnl_usd, 2)
            rec["settlement_time"] = now.isoformat() + "Z"
            try:
                entry_dt = datetime.datetime.fromisoformat(rec["entry_time"].replace("Z", "+00:00")).replace(tzinfo=None)
                rec["hold_duration_mins"] = int((now - entry_dt).total_seconds() / 60)
            except Exception:
                pass
            break


def get_pattern_analysis():
    """Analyze trade journal for patterns in wins vs losses."""
    settled = [t for t in _TRADE_JOURNAL if t["result"] is not None]
    if not settled:
        # Fallback to settled_history from portfolio cache
        return {"message": "No settled trades in journal yet", "patterns": []}

    wins = [t for t in settled if t["result"] == "win"]
    losses = [t for t in settled if t["result"] == "loss"]

    patterns = []

    # Pattern 1: Category performance
    cat_stats = {}
    for t in settled:
        cat = t["category"]
        if cat not in cat_stats:
            cat_stats[cat] = {"wins": 0, "losses": 0, "pnl": 0.0}
        if t["result"] == "win":
            cat_stats[cat]["wins"] += 1
        elif t["result"] == "loss":
            cat_stats[cat]["losses"] += 1
        cat_stats[cat]["pnl"] += t.get("pnl_usd") or 0

    for cat, st in sorted(cat_stats.items(), key=lambda x: x[1]["pnl"], reverse=True):
        total = st["wins"] + st["losses"]
        if total > 0:
            wr = round(st["wins"] / total * 100, 1)
            patterns.append({
                "type": "category",
                "name": cat,
                "wins": st["wins"],
                "losses": st["losses"],
                "win_rate": wr,
                "pnl": round(st["pnl"], 2),
                "signal": "strong" if wr >= 60 else ("weak" if wr < 40 else "neutral"),
            })

    # Pattern 2: Sport type performance
    sport_stats = {}
    for t in settled:
        sp = t.get("sport_type", "other")
        if sp not in sport_stats:
            sport_stats[sp] = {"wins": 0, "losses": 0, "pnl": 0.0}
        if t["result"] == "win":
            sport_stats[sp]["wins"] += 1
        elif t["result"] == "loss":
            sport_stats[sp]["losses"] += 1
        sport_stats[sp]["pnl"] += t.get("pnl_usd") or 0

    # Pattern 3: Price range performance
    price_ranges = {"70-75c": [70, 75], "76-80c": [76, 80], "81-85c": [81, 85], "86-90c": [86, 90], "91-100c": [91, 100]}
    for label, (lo, hi) in price_ranges.items():
        in_range = [t for t in settled if lo <= (t.get("price_cents") or 0) <= hi]
        if in_range:
            w = sum(1 for t in in_range if t["result"] == "win")
            l = sum(1 for t in in_range if t["result"] == "loss")
            pnl = sum(t.get("pnl_usd") or 0 for t in in_range)
            if w + l > 0:
                patterns.append({
                    "type": "price_range",
                    "name": label,
                    "wins": w,
                    "losses": l,
                    "win_rate": round(w / (w + l) * 100, 1),
                    "pnl": round(pnl, 2),
                })

    # Pattern 4: Live vs non-live
    live_w = sum(1 for t in wins if t.get("is_live"))
    live_l = sum(1 for t in losses if t.get("is_live"))
    nonlive_w = sum(1 for t in wins if not t.get("is_live"))
    nonlive_l = sum(1 for t in losses if not t.get("is_live"))
    if live_w + live_l > 0:
        patterns.append({"type": "live_vs_nonlive", "name": "Live", "wins": live_w, "losses": live_l,
                         "win_rate": round(live_w / (live_w + live_l) * 100, 1)})
    if nonlive_w + nonlive_l > 0:
        patterns.append({"type": "live_vs_nonlive", "name": "Non-live", "wins": nonlive_w, "losses": nonlive_l,
                         "win_rate": round(nonlive_w / (nonlive_w + nonlive_l) * 100, 1)})

    # Pattern 5: Time of day
    hour_stats = {}
    for t in settled:
        h = t.get("entry_hour", 0)
        period = "morning" if h < 12 else ("afternoon" if h < 17 else "evening")
        if period not in hour_stats:
            hour_stats[period] = {"wins": 0, "losses": 0}
        if t["result"] == "win":
            hour_stats[period]["wins"] += 1
        elif t["result"] == "loss":
            hour_stats[period]["losses"] += 1

    # Pattern 6: Average hold time for wins vs losses
    win_holds = [t.get("hold_duration_mins") for t in wins if t.get("hold_duration_mins")]
    loss_holds = [t.get("hold_duration_mins") for t in losses if t.get("hold_duration_mins")]

    return {
        "total_tracked": len(settled),
        "wins": len(wins),
        "losses": len(losses),
        "patterns": patterns,
        "sport_stats": sport_stats,
        "hour_stats": hour_stats,
        "avg_win_hold_mins": round(sum(win_holds) / max(1, len(win_holds)), 1) if win_holds else None,
        "avg_loss_hold_mins": round(sum(loss_holds) / max(1, len(loss_holds)), 1) if loss_holds else None,
    }

def check_settlements_and_reinvest():
    """Detect newly settled positions and immediately redeploy the freed capital.

    When a position settles (win or lose), the capital is freed. Instead of
    waiting for the next scan cycle, trigger an immediate trade scan.
    """
    global _last_settlement_check
    now = datetime.datetime.utcnow()

    # Only check every 60 seconds
    if _last_settlement_check and (now - _last_settlement_check).total_seconds() < 60:
        return []
    _last_settlement_check = now

    path = "/portfolio/positions"
    headers = signed_headers("GET", path)
    if not headers:
        return []

    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 200, "settlement_status": "settled"},
            timeout=TIMEOUT,
        )
        if not resp.ok:
            return []

        settled = resp.json().get("market_positions", [])
        new_settlements = []

        for pos in settled:
            ticker = pos.get("ticker", "")
            if ticker in _known_settled:
                continue
            _known_settled.add(ticker)
            pnl_cents = _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl"))
            pnl_usd = pnl_cents / 100
            won = pnl_usd > 0
            # Track category performance
            title = pos.get("market_title", "") or pos.get("title", "") or ticker
            _update_category_stats(ticker, title, won, pnl_usd)
            # Track in trade journal for pattern analysis
            _journal_settle(ticker, won, pnl_usd)
            new_settlements.append({
                "ticker": ticker,
                "pnl_usd": round(pnl_usd, 2),
                "won": won,
            })

        if new_settlements:
            wins = sum(1 for s in new_settlements if s["won"])
            losses = len(new_settlements) - wins
            total_pnl = sum(s["pnl_usd"] for s in new_settlements)
            # Log individual settlements for notifications
            for s in new_settlements:
                tk = s["ticker"]
                pnl = s["pnl_usd"]
                # Try to get a human-readable title
                _stitle = tk
                try:
                    _sm_path = f"/markets/{tk}"
                    _sm_h = signed_headers("GET", _sm_path)
                    if _sm_h:
                        _sm_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + _sm_path, headers=_sm_h, timeout=3)
                        if _sm_r.ok:
                            _stitle = _sm_r.json().get("market", {}).get("title", tk)[:60]
                except Exception:
                    pass
                if s["won"]:
                    _log_activity(f"🦈 WIN! {_stitle} +${pnl:.2f}", "success")
                else:
                    _log_activity(f"LOSS: {_stitle} -${abs(pnl):.2f}", "error")
            _log_activity(
                f"💰 Settlements: {len(new_settlements)} new ({wins}W/{losses}L) "
                f"P&L: ${total_pnl:+.2f} — reinvesting freed capital",
                "success" if total_pnl >= 0 else "info"
            )
            # Persist updated journal & category stats after processing settlements
            _save_state()
            # Trigger immediate rescan to reinvest
            return new_settlements

        # Cap known_settled to prevent memory bloat
        if len(_known_settled) > 500:
            _known_settled.clear()

        return []
    except Exception as e:
        print(f"[SETTLE] Error: {e}")
        return []


# ---------------------------------------------------------------------------
# 13. TWITTER/X SENTIMENT — Social media moves markets first
# ---------------------------------------------------------------------------
# Use Nitter (public Twitter proxy) RSS feeds to scan trending topics

_twitter_cache = {}
_TWITTER_CACHE_TTL = 120  # 2 minutes

def fetch_twitter_sentiment(query, max_results=10):
    """Fetch recent tweets about a topic and analyze sentiment.

    Uses Google News RSS as proxy for trending social topics since
    direct Twitter API requires paid access. Headlines that mention
    Twitter/X posts or social media trends are strong signals.
    """
    now = datetime.datetime.utcnow()
    cache_key = f"tw_{query.lower().strip()}"
    if cache_key in _twitter_cache:
        cached = _twitter_cache[cache_key]
        if (now - cached["time"]).total_seconds() < _TWITTER_CACHE_TTL:
            return cached["data"]

    # Augment query with social media keywords to find viral topics
    social_query = f"{query} twitter OR trending OR viral OR social media"
    headlines = fetch_news_headlines(social_query, max_results=max_results)

    # Score sentiment
    bullish_words = {"surge", "soar", "jump", "rise", "rally", "record", "high",
                     "boost", "strong", "beat", "wins", "launch", "approve",
                     "success", "trending", "viral", "breakout", "bullish"}
    bearish_words = {"fall", "drop", "crash", "decline", "loss", "cut",
                     "fail", "delay", "cancel", "down", "lose", "scandal",
                     "controversy", "backlash", "collapse", "bearish"}

    bull = bear = 0
    for h in headlines:
        words = set(h["title"].lower().split())
        bull += len(words & bullish_words)
        bear += len(words & bearish_words)

    # Amplify signal if multiple sources agree
    if len(headlines) >= 3 and (bull > bear * 2 or bear > bull * 2):
        confidence = "high"
    elif len(headlines) >= 2:
        confidence = "medium"
    else:
        confidence = "low"

    result = {
        "query": query,
        "headlines": headlines,
        "bull_signals": bull,
        "bear_signals": bear,
        "sentiment": "bullish" if bull > bear + 1 else ("bearish" if bear > bull + 1 else "neutral"),
        "confidence": confidence,
        "source_count": len(headlines),
    }

    _twitter_cache[cache_key] = {"data": result, "time": now}
    # Trim cache
    if len(_twitter_cache) > 100:
        oldest = sorted(_twitter_cache.keys(), key=lambda k: _twitter_cache[k]["time"])
        for k in oldest[:50]:
            del _twitter_cache[k]

    return result


# ---------------------------------------------------------------------------
# 14. ECONOMIC DATA FEEDS — Trade on government data releases
# ---------------------------------------------------------------------------
# For inflation, jobs, GDP markets — fetch actual economic indicators

_econ_cache = {}
_ECON_CACHE_TTL = 3600  # 1 hour (gov data doesn't change frequently)

# Key economic data sources (free, no API key needed)
ECON_INDICATORS = {
    "cpi": {
        "url": "https://api.stlouisfed.org/fred/series/observations",
        "series_id": "CPIAUCSL",
        "name": "Consumer Price Index",
        "keywords": ["cpi", "inflation", "consumer price"],
    },
    "unemployment": {
        "url": "https://api.stlouisfed.org/fred/series/observations",
        "series_id": "UNRATE",
        "name": "Unemployment Rate",
        "keywords": ["unemployment", "jobs", "jobless"],
    },
    "gdp": {
        "url": "https://api.stlouisfed.org/fred/series/observations",
        "series_id": "GDP",
        "name": "Gross Domestic Product",
        "keywords": ["gdp", "gross domestic", "economic growth"],
    },
    "fed_rate": {
        "url": "https://api.stlouisfed.org/fred/series/observations",
        "series_id": "FEDFUNDS",
        "name": "Federal Funds Rate",
        "keywords": ["fed", "interest rate", "federal reserve", "fomc"],
    },
}

# FRED API key (free, public data)
FRED_API_KEY = os.environ.get("FRED_API_KEY", "")

def fetch_economic_data(indicator_key):
    """Fetch latest economic data from FRED (Federal Reserve Economic Data)."""
    now = datetime.datetime.utcnow()
    cache_key = f"econ_{indicator_key}"
    if cache_key in _econ_cache:
        cached = _econ_cache[cache_key]
        if (now - cached["time"]).total_seconds() < _ECON_CACHE_TTL:
            return cached["data"]

    indicator = ECON_INDICATORS.get(indicator_key)
    if not indicator or not FRED_API_KEY:
        return None

    try:
        resp = requests.get(
            indicator["url"],
            params={
                "series_id": indicator["series_id"],
                "api_key": FRED_API_KEY,
                "file_type": "json",
                "sort_order": "desc",
                "limit": 12,  # last 12 data points
            },
            timeout=10,
        )
        if not resp.ok:
            return None

        observations = resp.json().get("observations", [])
        if not observations:
            return None

        # Parse values
        values = []
        for obs in observations:
            try:
                val = float(obs.get("value", ""))
                date = obs.get("date", "")
                values.append({"date": date, "value": val})
            except (ValueError, TypeError):
                continue

        if not values:
            return None

        latest = values[0]["value"]
        prev = values[1]["value"] if len(values) > 1 else latest
        change = latest - prev
        trend = "rising" if change > 0 else ("falling" if change < 0 else "flat")

        # Calculate 6-month trend
        if len(values) >= 6:
            avg_recent = sum(v["value"] for v in values[:3]) / 3
            avg_older = sum(v["value"] for v in values[3:6]) / 3
            six_month_trend = "rising" if avg_recent > avg_older else "falling"
        else:
            six_month_trend = trend

        result = {
            "indicator": indicator["name"],
            "latest_value": latest,
            "previous_value": prev,
            "change": round(change, 3),
            "trend": trend,
            "six_month_trend": six_month_trend,
            "latest_date": values[0]["date"],
            "history": values[:6],
        }

        _econ_cache[cache_key] = {"data": result, "time": now}
        return result

    except Exception as e:
        print(f"[ECON] Error fetching {indicator_key}: {e}")
        return None


def match_market_to_econ(question):
    """Check if a market question relates to an economic indicator.

    Returns:
        (indicator_key, confidence) or (None, 0)
    """
    q_lower = question.lower()
    for key, indicator in ECON_INDICATORS.items():
        hits = sum(1 for kw in indicator["keywords"] if kw in q_lower)
        if hits >= 1:
            return key, min(0.9, 0.3 + hits * 0.2)
    return None, 0


def econ_enhanced_signal(question, current_yes_price):
    """Use economic data to enhance a trading signal.

    If CPI is rising and a market asks "Will inflation be above X%?",
    economic data gives us an informed edge.
    """
    indicator_key, confidence = match_market_to_econ(question)
    if not indicator_key or confidence < 0.3:
        return None

    data = fetch_economic_data(indicator_key)
    if not data:
        return None

    q_lower = question.lower()

    # Detect "above" or "below" threshold questions
    signal = None
    import re as _re
    # Pattern: "above X%" or "below X%" or "over X" or "under X"
    above_match = _re.search(r'(above|over|exceed|higher than|at least)\s*(\d+\.?\d*)', q_lower)
    below_match = _re.search(r'(below|under|less than|lower than|at most)\s*(\d+\.?\d*)', q_lower)

    if above_match:
        threshold = float(above_match.group(2))
        # If trend is rising and latest is near/above threshold, likely YES
        if data["trend"] == "rising" and data["latest_value"] >= threshold * 0.95:
            signal = "buy_yes"
        elif data["trend"] == "falling" and data["latest_value"] < threshold:
            signal = "buy_no"
    elif below_match:
        threshold = float(below_match.group(2))
        if data["trend"] == "falling" and data["latest_value"] <= threshold * 1.05:
            signal = "buy_yes"
        elif data["trend"] == "rising" and data["latest_value"] > threshold:
            signal = "buy_no"

    if not signal:
        return None

    return {
        "indicator": data["indicator"],
        "signal": signal,
        "confidence": confidence,
        "latest_value": data["latest_value"],
        "trend": data["trend"],
        "six_month_trend": data["six_month_trend"],
        "strategy": "economic_data",
    }


# Use a simple background thread instead of APScheduler
# APScheduler's threadpool doesn't reliably work with gunicorn
import threading
import time as _time

# Track known fill order_ids so we can detect externally placed bets
_known_fill_ids = set()

def _sync_kalshi_fills():
    """Detect bets placed directly on kalshi.com and add them to today's feed."""
    try:
        today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")
        path = "/portfolio/fills"
        headers = signed_headers("GET", path)
        if not headers:
            return
        # Fetch recent fills — use min_ts to only get today's fills (much faster)
        _today_start_utc = datetime.datetime.now(tz=_PACIFIC).replace(hour=0, minute=0, second=0, microsecond=0).astimezone(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        resp = _req.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 100, "min_ts": _today_start_utc},
            timeout=15,
        )
        if not resp.ok:
            return
        fills = resp.json().get("fills", [])

        # Build set of order_ids we already track (from bot + manual trades)
        tracked_ids = set(_known_fill_ids)  # start with globally tracked IDs
        # Also build set of (ticker, side) pairs the bot placed today
        _bot_ticker_sides = set()
        for _tlist_name in ["snipe_trades_today", "moonshark_trades_today", "closegame_trades_today"]:
            for t in BOT_STATE.get(_tlist_name, []):
                if t.get("order_id"):
                    tracked_ids.add(t["order_id"])
                _bot_ticker_sides.add((t.get("ticker", ""), t.get("side", "")))
        for t in BOT_STATE.get("all_trades", []):
            if t.get("order_id"):
                tracked_ids.add(t["order_id"])
        for t in BOT_STATE.get("trades_today", []):
            if t.get("order_id"):
                tracked_ids.add(t["order_id"])
        for t in BOT_STATE.get("manual_trades_today", []):
            if t.get("order_id"):
                tracked_ids.add(t["order_id"])

        new_external = 0
        for fill in fills:
            order_id = fill.get("order_id", "")
            created = fill.get("created_time", "")
            action = fill.get("action", "buy")

            # Only care about today's buy fills not already tracked
            if not created:
                continue
            try:
                fill_dt = datetime.datetime.fromisoformat(created.replace("Z", "+00:00"))
                fill_pacific_date = fill_dt.astimezone(_PACIFIC).strftime("%Y-%m-%d")
            except Exception:
                fill_pacific_date = created[:10]
            if fill_pacific_date != today_str:
                continue
            if action != "buy":
                continue
            if order_id in tracked_ids:
                continue

            ticker = fill.get("ticker", "")
            side = fill.get("side", "")

            # Skip if this ticker+side was already placed by the bot today
            if (ticker, side) in _bot_ticker_sides:
                _known_fill_ids.add(order_id)
                continue

            _known_fill_ids.add(order_id)

            count = 0
            try:
                count_raw = fill.get("count_fp") or fill.get("count") or 0
                count = int(float(str(count_raw)))
            except Exception:
                pass
            price_cents = 0
            try:
                yes_price = fill.get("yes_price_dollars") or fill.get("yes_price")
                no_price = fill.get("no_price_dollars") or fill.get("no_price")
                if side == "yes" and yes_price:
                    price_cents = int(round(float(str(yes_price)) * 100))
                elif side == "no" and no_price:
                    price_cents = int(round(float(str(no_price)) * 100))
            except Exception:
                pass

            cost_usd = round((price_cents * count) / 100, 2)

            # Look up title
            title = ticker
            try:
                mkt_path = f"/markets/{ticker}"
                mkt_h = signed_headers("GET", mkt_path)
                mkt_r = _req.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + mkt_path, headers=mkt_h, timeout=5)
                if mkt_r.ok:
                    title = mkt_r.json().get("market", {}).get("title", ticker)
            except Exception:
                pass

            # Add to manual_trades_today so it shows in Bets Placed Today
            BOT_STATE.setdefault("manual_trades_today", []).append({
                "ticker": ticker, "title": title, "side": side,
                "price": price_cents, "count": count, "cost": cost_usd,
                "time": created,
                "strategy": "manual",
                "order_id": order_id,
            })

            # Also add to all_trades
            trade_rec = {
                "timestamp": created,
                "ticker": ticker,
                "question": title,
                "side": side,
                "action": "buy",
                "price_cents": price_cents,
                "count": count,
                "cost_usd": cost_usd,
                "order_id": order_id,
                "source": "kalshi_fill",
                "success": True,
                "manual": True,
                "bot_version": BOT_VERSION,
            }
            BOT_STATE["all_trades"].append(trade_rec)

            new_external += 1
            _log_activity(
                f"External bet detected: {side.upper()} {ticker} @ {price_cents}c x{count} (${cost_usd:.2f}) | {title[:40]}",
                "info"
            )

        if new_external > 0:
            print(f"[SYNC] Detected {new_external} external Kalshi fill(s)")
            _save_state()

    except Exception as e:
        print(f"[SYNC] Fill sync error: {e}")


def _background_loop():
    """Simple background loop that runs scans, warms cache, monitors positions."""
    _time.sleep(30)  # wait 30s for server to fully start before scanning
    print("[BG] Background loop started")
    _log_activity("Background engine started — v3 QUANT")
    # Early cache warm — get balance + positions so dashboard shows data immediately
    try:
        _bal_early = 0
        try:
            _bh_e = signed_headers("GET", "/portfolio/balance")
            _br_e = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                                headers=_bh_e, timeout=10)
            if _br_e.ok:
                _bal_data = _br_e.json()
                _bal_early = _bal_data.get("balance", 0) / 100
                # Use Kalshi's own portfolio_balance if available (matches their UI exactly)
                _kalshi_portfolio = _bal_data.get("portfolio_balance", 0) / 100
        except Exception:
            pass
        _pos_early = []
        try:
            _pos_early = check_position_prices()
        except Exception:
            pass
        _mv_early = sum((p.get("current_price") or p.get("entry_price") or 0) * p.get("count", 0)
                       for p in _pos_early) / 100
        _inv_early = sum(p.get("market_exposure_cents", 0) for p in _pos_early) / 100
        # Prefer Kalshi's portfolio value (matches their UI), fallback to our calculation
        _pf_value = _kalshi_portfolio if _kalshi_portfolio > 0 else round(_bal_early + _mv_early, 2)
        _PORTFOLIO_CACHE["data"] = {
            "balance_usd": round(_bal_early, 2),
            "portfolio_value_usd": round(_pf_value, 2),
            "positions_value_usd": round(_pf_value - _bal_early, 2) if _kalshi_portfolio > 0 else round(_mv_early, 2),
            "open_positions": _pos_early,
            "open_count": len(_pos_early),
            "total_invested_usd": round(_inv_early, 2),
            "total_unrealized_usd": round(sum((p.get("unrealized_pnl_cents") or 0) for p in _pos_early) / 100, 2),
            "daily_pnl_usd": round(sum((p.get("unrealized_pnl_cents") or 0) for p in _pos_early) / 100, 2),
            "wins": 0, "losses": 0, "breakeven": 0, "win_rate": 0,
            "total_realized_usd": 0, "settled_history": [],
        }
        # Warm realized P&L on startup so Total P&L doesn't flash $0.00
        # Split into "since Day 1" and "legacy" (pre-Day-1 junk)
        _early_realized = 0.0
        _early_realized_day1 = 0.0  # only since Day 1
        _early_wins = 0
        _early_losses = 0
        _early_wins_day1 = 0
        _early_losses_day1 = 0
        try:
            # Build set of tickers with known buy dates from hydrated trades
            _buy_dates = {}
            for _at in BOT_STATE.get("all_trades", []):
                _atk = _at.get("ticker", "")
                _ats = _at.get("timestamp", "")[:10]
                _ata = _at.get("action", "buy")
                if _atk and _ats and _ata == "buy":
                    if _atk not in _buy_dates or _ats < _buy_dates[_atk]:
                        _buy_dates[_atk] = _ats  # earliest buy date

            for _esf in ["settled", "unsettled"]:
                _esh = signed_headers("GET", "/portfolio/positions")
                _esr = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/positions",
                    headers=_esh, params={"limit": 200, "settlement_status": _esf},
                    timeout=10,
                )
                if _esr.ok:
                    for _esp in _esr.json().get("market_positions", []):
                        _epnl = _parse_kalshi_dollars(_esp.get("realized_pnl_dollars") or _esp.get("realized_pnl"))
                        _epnl_usd = _epnl / 100
                        if _esf == "unsettled" and abs(_epnl_usd) < 0.005:
                            continue
                        _early_realized += _epnl_usd
                        _etk = _esp.get("ticker", "")
                        _ebd = _buy_dates.get(_etk, "")
                        _is_day1 = _ebd >= TRADE_JOURNAL_START if _ebd else False

                        if _epnl_usd > 0.005:
                            _early_wins += 1
                            if _is_day1:
                                _early_wins_day1 += 1
                        elif _epnl_usd < -0.005:
                            _early_losses += 1
                            if _is_day1:
                                _early_losses_day1 += 1
                        if _is_day1:
                            _early_realized_day1 += _epnl_usd

            _PORTFOLIO_CACHE["data"]["total_realized_usd"] = round(_early_realized_day1, 2)  # Show Day 1+ only
            _PORTFOLIO_CACHE["data"]["total_realized_all"] = round(_early_realized, 2)  # Keep all-time for reference
            _PORTFOLIO_CACHE["data"]["wins"] = _early_wins_day1
            _PORTFOLIO_CACHE["data"]["losses"] = _early_losses_day1
            _PORTFOLIO_CACHE["data"]["win_rate"] = round(_early_wins_day1 / max(1, _early_wins_day1 + _early_losses_day1) * 100, 1)
            print(f"[BG] P&L split: Day1+=${_early_realized_day1:+.2f} ({_early_wins_day1}W/{_early_losses_day1}L), All-time=${_early_realized:+.2f}")
        except Exception:
            pass
        _PORTFOLIO_CACHE["ts"] = _time.time()
        print(f"[BG] Early cache warm: ${_bal_early:.2f} cash, {len(_pos_early)} positions, P&L ${_early_realized:+.2f}")
        # Pre-warm settled cache so Performance tab loads instantly
        try:
            with app.test_request_context():
                settled_positions()
                print(f"[BG] Settled cache warmed: {_SETTLED_CACHE['data']['wins']}W/{_SETTLED_CACHE['data']['losses']}L, P&L ${_SETTLED_CACHE['data']['total_pnl_usd']:+.2f}")
        except Exception as _se:
            print(f"[BG] Settled cache warm failed (non-fatal): {_se}")
    except Exception as e:
        print(f"[BG] Early cache warm failed (non-fatal): {e}")
    # Hydrate trade history from Kalshi on startup
    try:
        _hydrate_from_kalshi()
    except Exception as e:
        print(f"[BG] Hydrate error (non-fatal): {e}")
    _log_activity(f"Loaded {len(BOT_STATE['all_trades'])} trades from Kalshi (${BOT_STATE['daily_spent_usd']:.2f} spent today)")

    # Seed known fill IDs so sync doesn't re-detect existing trades
    for t in BOT_STATE.get("all_trades", []):
        if t.get("order_id"):
            _known_fill_ids.add(t["order_id"])
    print(f"[SYNC] Seeded {len(_known_fill_ids)} known fill IDs")

    # Initialize known settled positions on startup
    try:
        sh = signed_headers("GET", "/portfolio/positions")
        if sh:
            sr = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/positions",
                headers=sh, params={"limit": 200, "settlement_status": "settled"},
                timeout=TIMEOUT,
            )
            if sr.ok:
                for pos in sr.json().get("market_positions", []):
                    _known_settled.add(pos.get("ticker", ""))
                print(f"[SETTLE] Initialized {len(_known_settled)} known settled positions")
    except Exception:
        pass
    # Rebuild trade journal & category stats from Kalshi settled positions
    # This is the real persistence: even if /tmp is wiped on deploy, we rebuild from API
    try:
        _rebuild_journal_from_kalshi()
    except Exception as e:
        print(f"[BG] Journal rebuild error (non-fatal): {e}")

    # Run learning engine on startup to compute initial parameters
    try:
        _learning_engine()
    except Exception as e:
        print(f"[BG] Learning engine startup error (non-fatal): {e}")

    cycle = 0
    # Portfolio cache warms naturally on first background cycle — no startup delay
    while True:
        try:
            cycle += 1
            _cycle_start = _time.time()

            # === FAST TRADING LOOP (every cycle) ===
            # These are the money-makers — run them FIRST and FAST
            _snipe_results = live_game_snipe()
            _time.sleep(1)
            _ms_results = moonshark_snipe()
            _time.sleep(1)

            # Check for new settlements
            settlements = check_settlements_and_reinvest()
            if settlements:
                try:
                    live_game_snipe()
                except Exception:
                    pass

            # Sync external Kalshi fills
            try:
                _sync_kalshi_fills()
            except Exception as se:
                print(f"[SYNC] Error: {se}")

            _trade_time = _time.time() - _cycle_start
            print(f"[CYCLE {cycle}] Trading: {_trade_time:.1f}s")

            # === SLOW ANALYTICS (less frequent) ===
            # Bot scan — every 5 cycles (~2.5 min)
            if cycle % 5 == 0:
                try:
                    run_bot_scan()
                except Exception as _bse:
                    print(f"[SCAN] Error: {_bse}")

            # Monitor live scores — every 3 cycles
            if cycle % 3 == 0:
                try:
                    _monitor_live_games()
                except Exception as _mle:
                    print(f"[MONITOR] Error: {_mle}")

            # Learning engine — every 120 cycles (~1 hour)
            if cycle % 120 == 0:
                try:
                    _learning_engine()
                except Exception as _le:
                    print(f"[LEARNING] Error: {_le}")

            # Heavy caches — every 10 cycles (~5 min)
            if cycle % 10 == 0:
                try:
                    _generate_seventy_fivers()
                except Exception:
                    pass
                _warm_picks_cache()
            # Refresh portfolio cache so dashboard always has data
            try:
                _bal2 = 0
                _kalshi_portfolio2 = 0
                try:
                    _bh2 = signed_headers("GET", "/portfolio/balance")
                    _br2 = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                                       headers=_bh2, timeout=10)
                    if _br2.ok:
                        _bal2_data = _br2.json()
                        _bal2 = _bal2_data.get("balance", 0) / 100
                        _kalshi_portfolio2 = _bal2_data.get("portfolio_balance", 0) / 100
                        # Log ALL fields so we can match Kalshi's UI exactly
                        print(f"[PORTFOLIO] Kalshi balance API fields: {list(_bal2_data.keys())}")
                        print(f"[PORTFOLIO] Kalshi API: cash=${_bal2:.2f} portfolio_balance=${_kalshi_portfolio2:.2f}")
                except Exception:
                    if _PORTFOLIO_CACHE["data"]:
                        _bal2 = _PORTFOLIO_CACHE["data"].get("balance_usd", 0)
                _pos2 = []
                try:
                    _pos2 = check_position_prices()
                except Exception:
                    pass
                _mv2 = sum((p.get("current_price") or p.get("entry_price") or 0) * p.get("count", 0)
                           for p in _pos2) / 100
                # Fetch settled positions for win/loss stats
                _wins2 = _losses2 = 0
                _realized2 = 0.0
                _settled_list2 = []
                try:
                    for _sf2 in ["settled", "unsettled"]:
                        _sh2 = signed_headers("GET", "/portfolio/positions")
                        _sr2 = requests.get(
                            KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/positions",
                            headers=_sh2, params={"limit": 200, "settlement_status": _sf2},
                            timeout=10,
                        )
                        if _sr2.ok:
                            for _sp2 in _sr2.json().get("market_positions", []):
                                _pnl2 = _parse_kalshi_dollars(_sp2.get("realized_pnl_dollars") or _sp2.get("realized_pnl"))
                                _pnl2_usd = _pnl2 / 100
                                if _sf2 == "unsettled" and abs(_pnl2_usd) < 0.005:
                                    continue
                                _realized2 += _pnl2_usd
                                if _pnl2_usd > 0.005:
                                    _wins2 += 1
                                    _settled_list2.append({"ticker": _sp2.get("ticker", ""), "pnl_usd": round(_pnl2_usd, 2), "won": True})
                                elif _pnl2_usd < -0.005:
                                    _losses2 += 1
                                    _settled_list2.append({"ticker": _sp2.get("ticker", ""), "pnl_usd": round(_pnl2_usd, 2), "won": False})
                except Exception:
                    # Fall back to cached values
                    if _PORTFOLIO_CACHE["data"]:
                        _wins2 = _PORTFOLIO_CACHE["data"].get("wins", 0)
                        _losses2 = _PORTFOLIO_CACHE["data"].get("losses", 0)
                        _realized2 = _PORTFOLIO_CACHE["data"].get("total_realized_usd", 0)
                        _settled_list2 = _PORTFOLIO_CACHE["data"].get("settled_history", [])
                _wr2 = round(_wins2 / max(1, _wins2 + _losses2) * 100, 1)

                # Day 1+ win rate (only count trades from March 16, 2026 onwards)
                # Use trade journal for Day 1+ tracking, fall back to _CATEGORY_STATS
                _d1_wins = sum(1 for t in _TRADE_JOURNAL if t.get("result") == "win")
                _d1_losses = sum(1 for t in _TRADE_JOURNAL if t.get("result") == "loss")
                # If journal is empty, use category stats (which reset on restart)
                if _d1_wins + _d1_losses == 0:
                    for _cs in _CATEGORY_STATS.values():
                        _d1_wins += _cs.get("wins", 0)
                        _d1_losses += _cs.get("losses", 0)
                _d1_wr = round(_d1_wins / max(1, _d1_wins + _d1_losses) * 100, 1) if (_d1_wins + _d1_losses) > 0 else 0

                # 7-day win rate — only trades settled in last 7 days
                _7d_cutoff = (datetime.datetime.utcnow() - datetime.timedelta(days=7)).isoformat() + "Z"
                _7d_wins = sum(1 for t in _TRADE_JOURNAL if t.get("result") == "win" and (t.get("settlement_time") or "") >= _7d_cutoff)
                _7d_losses = sum(1 for t in _TRADE_JOURNAL if t.get("result") == "loss" and (t.get("settlement_time") or "") >= _7d_cutoff)
                _7d_wr = round(_7d_wins / max(1, _7d_wins + _7d_losses) * 100, 1) if (_7d_wins + _7d_losses) > 0 else 0

                _total_unrealized = round(sum((p.get("unrealized_pnl_cents") or 0) for p in _pos2) / 100, 2)

                # Calculate true daily P&L: today's settled results + current unrealized
                _daily_pnl = _total_unrealized
                try:
                    _today_str = datetime.datetime.utcnow().strftime("%Y-%m-%d")
                    for _jt in _TRADE_JOURNAL:
                        if _jt.get("result") is not None and str(_jt.get("settlement_time") or "")[:10] == _today_str:
                            _daily_pnl += float(_jt.get("pnl") or 0)
                    _daily_pnl = round(_daily_pnl, 2)
                except Exception:
                    pass

                # Prefer Kalshi's portfolio value (matches their UI), fallback to our calculation
                _pf_value2 = _kalshi_portfolio2 if _kalshi_portfolio2 > 0 else round(_bal2 + _mv2, 2)
                _PORTFOLIO_CACHE["data"] = {
                    "balance_usd": round(_bal2, 2),
                    "portfolio_value_usd": round(_pf_value2, 2),
                    "positions_value_usd": round(_pf_value2 - _bal2, 2) if _kalshi_portfolio2 > 0 else round(_mv2, 2),
                    "open_positions": _pos2,
                    "open_count": len(_pos2),
                    "total_invested_usd": round(sum(p.get("market_exposure_cents", 0) for p in _pos2) / 100, 2),
                    "total_unrealized_usd": _total_unrealized,
                    "daily_pnl_usd": _daily_pnl,
                    # Use /settled cache as single source of truth for W/L/P&L
                    # This ensures header and Performance tab always match
                    "wins": _SETTLED_CACHE["data"]["wins"] if _SETTLED_CACHE.get("data") else _d1_wins,
                    "losses": _SETTLED_CACHE["data"]["losses"] if _SETTLED_CACHE.get("data") else _d1_losses,
                    "wins_all_time": _wins2,
                    "losses_all_time": _losses2,
                    "breakeven": 0,
                    "win_rate": round(_SETTLED_CACHE["data"]["wins"] / max(1, _SETTLED_CACHE["data"]["wins"] + _SETTLED_CACHE["data"]["losses"]) * 100, 1) if _SETTLED_CACHE.get("data") else _d1_wr,
                    "win_rate_all_time": _wr2,
                    "win_rate_7d": _7d_wr,
                    "total_realized_usd": _SETTLED_CACHE["data"]["total_pnl_usd"] if _SETTLED_CACHE.get("data") else round(sum(t.get("pnl", 0) for t in _TRADE_JOURNAL) if _TRADE_JOURNAL else _realized2, 2),
                    "total_realized_all": round(_realized2, 2),
                    "settled_history": _settled_list2[-20:],
                }
                _PORTFOLIO_CACHE["ts"] = _time.time()
            except Exception:
                pass
            # Auto-exit DISABLED — all positions settle naturally at $0 or $1
            # Prediction markets aren't stocks; trailing stops just sell winners early
            # exits = enhanced_auto_exit()
            # exits = auto_exit_check()
        except Exception as e:
            import traceback
            _log_activity(f"Background error: {str(e)[:80]}", "error")
            print(f"[BG] Error in background loop: {e}")
            traceback.print_exc()
        # Dynamic scan interval — fastest during peak game hours
        _now_pt = datetime.datetime.now(tz=_PACIFIC)
        _is_peak_hours = 16 <= _now_pt.hour <= 22  # 4PM-10PM PT — most games live
        _is_game_hours = 10 <= _now_pt.hour <= 23
        _sleep_time = 15 if _is_peak_hours else (30 if _is_game_hours else 300)
        _time.sleep(_sleep_time)

_bg_thread = None

def _ensure_bg_thread():
    global _bg_thread
    if _bg_thread is not None and _bg_thread.is_alive():
        return
    _bg_thread = threading.Thread(target=_background_loop, daemon=True)
    _bg_thread.start()
    print("[STARTUP] Background thread started")

    # Close-Game Sniper — fast 10s loop for live game edge
    def _closegame_loop():
        _time.sleep(60)  # wait for main loop to warm up first
        print("[CLOSEGAME] Fast sniper thread started (10s interval)")
        _cg_cycle = 0
        while True:
            try:
                _cg_cycle += 1
                closegame_snipe()
                # Blowout exit every 30s (every 3rd cycle)
                if _cg_cycle % 3 == 0:
                    _blowout_exit()
                # Game monitor every 60s (every 6th cycle)
                if _cg_cycle % 6 == 0:
                    _monitor_live_games()
                # Price tracking every 60s (every 6th cycle, offset)
                if _cg_cycle % 6 == 3:
                    _track_prices()
                # Arbitrage check every 2 min (every 12th cycle)
                if _cg_cycle % 12 == 0:
                    _check_arbitrage()
            except Exception as e:
                print(f"[CLOSEGAME] Error: {e}")
            _time.sleep(10)

    _cg_thread = threading.Thread(target=_closegame_loop, daemon=True)
    _cg_thread.start()
    print("[STARTUP] Close-Game Sniper thread started (10s)")

    # Start keep-alive watchdog (only once)
    global _keepalive_thread
    if _keepalive_thread is None or not _keepalive_thread.is_alive():
        _keepalive_thread = threading.Thread(target=_keep_alive_loop, daemon=True)
        _keepalive_thread.start()
        print("[STARTUP] Keep-alive watchdog started (5 min)")

# Background thread starts on first request via before_request hook
# (not at import time, to avoid issues with gunicorn --preload)

# ---------------------------------------------------------------------------
# SELF-PING KEEP-ALIVE — prevents Railway from idling the service
# Also acts as a watchdog: restarts dead trading threads via /health
# ---------------------------------------------------------------------------
def _keep_alive_loop():
    """Ping our own /health endpoint every 5 minutes to prevent Railway idle timeout.
    Also triggers _ensure_bg_thread() via before_request hook, restarting dead threads."""
    _time.sleep(120)  # wait for server to fully start
    print("[KEEPALIVE] Self-ping watchdog started (5 min interval)")
    _server_url = None
    while True:
        try:
            if _server_url is None:
                import os as _ka_os
                _port = _ka_os.environ.get("PORT", "8080")
                _railway_url = _ka_os.environ.get("RAILWAY_PUBLIC_DOMAIN")
                if _railway_url:
                    _server_url = f"https://{_railway_url}/health"
                else:
                    _server_url = f"http://127.0.0.1:{_port}/health"
            resp = requests.get(_server_url, timeout=30)
            if resp.ok:
                print(f"[KEEPALIVE] ✅ Health OK")
            else:
                print(f"[KEEPALIVE] ⚠️ Health returned {resp.status_code}")
        except Exception as e:
            print(f"[KEEPALIVE] ❌ Self-ping failed: {e}")
        _time.sleep(300)  # every 5 minutes

_keepalive_thread = None  # started on first request, not at import time

# Keep scheduler object for status endpoint compatibility
class _FakeScheduler:
    running = True
    def get_jobs(self):
        return []
    def shutdown(self):
        pass
scheduler = _FakeScheduler()

@app.before_request
def _ensure_bg_on_request():
    """Ensure background thread is running on EVERY HTTP request (including health checks).
    This way Railway's health check can auto-restart dead trading threads."""
    _ensure_bg_thread()

# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

@app.route("/debug-scheduler")
def debug_scheduler():
    return jsonify({
        "bg_thread_alive": _bg_thread.is_alive() if _bg_thread else False,
        "bg_thread_exists": _bg_thread is not None,
        "picks_cache_has_data": _picks_cache["data"] is not None,
        "picks_cache_time": str(_picks_cache["time"]),
        "last_scan": BOT_STATE.get("last_scan"),
        "last_scan_markets": BOT_STATE.get("last_scan_markets", 0),
        "active_threads": threading.active_count(),
        "thread_names": [t.name for t in threading.enumerate()],
    })

@app.route("/health")
def health():
    _bg_alive = _bg_thread is not None and _bg_thread.is_alive()
    return jsonify({
        "status": "ok" if _bg_alive else "degraded",
        "trading_thread": "alive" if _bg_alive else "dead",
        "auto_trade": BOT_CONFIG.get("enabled", False),
        "uptime_cycles": BOT_STATE.get("cycle", 0),
    })


@app.route("/test-fetch")
def test_fetch():
    """Debug: run fetch_kalshi() and return stats."""
    try:
        import time
        t0 = time.time()
        markets = fetch_kalshi()
        elapsed = time.time() - t0
        non_sports = [m for m in markets if not m.get("is_sports")]
        sports = [m for m in markets if m.get("is_sports")]
        return jsonify({
            "total": len(markets),
            "sports": len(sports),
            "non_sports": len(non_sports),
            "elapsed_sec": round(elapsed, 2),
            "sample_non_sports": [{"q": m["question"][:60], "vol": m.get("volume"), "yes": m["yes"]} for m in non_sports[:5]],
            "sample_sports": [{"q": m["question"][:60], "vol": m.get("volume"), "yes": m["yes"]} for m in sports[:5]],
        })
    except Exception as e:
        import traceback
        return jsonify({"error": str(e), "tb": traceback.format_exc()})

@app.route("/test-events")
def test_events():
    """Debug: test the events + markets API."""
    try:
        # 1) Get events
        h = signed_headers("GET", "/events")
        if not h:
            return jsonify({"error": "no auth headers"})
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + "/events",
            headers=h, params={"limit": 5, "status": "open"}, timeout=10,
        )
        if not resp.ok:
            return jsonify({"error": f"events API: {resp.status_code}", "body": resp.text[:200]})
        events = resp.json().get("events", [])
        # 2) Try to fetch markets for first event
        et = events[0].get("event_ticker", "") if events else ""
        mkt_result = {"error": "no event ticker"}
        if et:
            h2 = signed_headers("GET", "/markets")
            mkt_resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=h2, params={"limit": 10, "event_ticker": et, "status": "open"},
                timeout=10,
            )
            mkt_data = mkt_resp.json() if mkt_resp.ok else {}
            mkts = mkt_data.get("markets", [])
            mkt_result = {
                "status": mkt_resp.status_code,
                "count": len(mkts),
                "sample": [{"ticker": m.get("ticker", "")[:40], "title": m.get("title", "")[:60], "yes_ask": m.get("yes_ask"), "yes_ask_dollars": m.get("yes_ask_dollars")} for m in mkts[:3]],
            }
        return jsonify({
            "events_count": len(events),
            "first_event": et,
            "markets_for_first_event": mkt_result,
            "all_events": [{"ticker": e.get("event_ticker"), "title": e.get("title", "")[:60]} for e in events],
        })
    except Exception as e:
        import traceback
        return jsonify({"error": str(e), "traceback": traceback.format_exc()})

@app.route("/debug-markets")
def debug_markets():
    all_m = fetch_all_markets()
    total = len(all_m)
    kalshi = [m for m in all_m if m["platform"] == "kalshi"]
    non_parlay = [m for m in kalshi if not _is_parlay_title(m["question"])]
    non_sports = [m for m in non_parlay if not m.get("is_sports", False)]
    sports = [m for m in non_parlay if m.get("is_sports", False)]
    high_vol_ns = sorted([m for m in non_sports if m.get("volume", 0) >= 500], key=lambda x: x.get("volume", 0), reverse=True)
    other = [m for m in all_m if m["platform"] != "kalshi"]
    return jsonify({
        "total": total,
        "kalshi": len(kalshi),
        "kalshi_non_parlay": len(non_parlay),
        "kalshi_sports": len(sports),
        "kalshi_non_sports": len(non_sports),
        "kalshi_non_sports_high_vol": len(high_vol_ns),
        "other_platforms": len(other),
        "other_by_platform": {p: len([m for m in other if m["platform"] == p]) for p in set(m["platform"] for m in other)},
        "sample_non_sports_high_vol": [{"q": m["question"][:80], "vol": m.get("volume"), "yes": m["yes"], "ticker": m["id"][:30]} for m in high_vol_ns[:10]],
        "sample_non_sports": [{"q": m["question"][:80], "vol": m.get("volume"), "yes": m["yes"]} for m in non_sports[:10]],
    })


@app.route("/markets")
def markets_kalshi():
    return jsonify({"markets": fetch_kalshi()})


@app.route("/debug-kalshi-fetch")
def debug_kalshi_fetch():
    """Debug why fetch_kalshi() returns 0 markets."""
    import traceback
    results = {"events_api": None, "markets_api": None, "auth_test": None}
    try:
        # Test 1: Can we sign headers?
        h = signed_headers("GET", "/events")
        results["auth_test"] = "OK" if h else "FAILED - no headers"
        # Test 2: Events API
        try:
            eh = signed_headers("GET", "/events")
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/events",
                headers=eh, params={"limit": 5, "status": "open"}, timeout=10,
            )
            results["events_api"] = {
                "status": resp.status_code,
                "count": len(resp.json().get("events", [])) if resp.ok else 0,
                "sample": [e.get("event_ticker", "") for e in resp.json().get("events", [])[:3]] if resp.ok else resp.text[:200],
            }
        except Exception as e:
            results["events_api"] = {"error": str(e)}
        # Test 3: Markets API (direct, no event filter)
        try:
            mh = signed_headers("GET", "/markets")
            resp2 = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh, params={"limit": 5, "status": "open"}, timeout=10,
            )
            results["markets_api"] = {
                "status": resp2.status_code,
                "count": len(resp2.json().get("markets", [])) if resp2.ok else 0,
                "sample_tickers": [m.get("ticker", "") for m in resp2.json().get("markets", [])[:3]] if resp2.ok else resp2.text[:200],
            }
        except Exception as e:
            results["markets_api"] = {"error": str(e)}
    except Exception as e:
        results["fatal"] = traceback.format_exc()
    return jsonify(results)


@app.route("/polymarket")
def markets_polymarket():
    return jsonify({"markets": fetch_polymarket()})


@app.route("/predictit")
def markets_predictit():
    return jsonify({"markets": fetch_predictit()})


@app.route("/manifold")
def markets_manifold():
    return jsonify({"markets": fetch_manifold()})


@app.route("/all")
def markets_all():
    all_markets = fetch_all_markets()
    return jsonify({"total": len(all_markets), "markets": all_markets})


@app.route("/opportunities")
def opportunities():
    min_sim = float(request.args.get("min_similarity", 0.85))
    max_cost = float(request.args.get("max_cost", 0.98))
    all_markets = fetch_all_markets()
    opps = find_opportunities(all_markets, min_similarity=min_sim, max_cost=max_cost)
    return jsonify({
        "total_markets_scanned": len(all_markets),
        "opportunities_found": len(opps),
        "opportunities": opps,
    })


@app.route("/research")
def research():
    """Research a market question — returns news headlines and sentiment."""
    q = request.args.get("q", "")
    if not q:
        return jsonify({"error": "Missing ?q= parameter"}), 400
    data = research_market(q)
    return jsonify(data)


@app.route("/balance")
def balance():
    path = "/portfolio/balance"
    headers = signed_headers("GET", path)
    try:
        resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + path, headers=headers, timeout=TIMEOUT)
        resp.raise_for_status()
        return jsonify({"balance_usd": resp.json().get("balance", 0) / 100})
    except Exception as e:
        return jsonify({"error": str(e)})


@app.route("/positions")
def positions():
    # Get portfolio positions
    path = "/portfolio/positions"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"positions": [], "error": "No API key"})
    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 100, "settlement_status": "unsettled"},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        raw = resp.json()
        positions_list = raw.get("market_positions", [])

        # Enrich with market details (title, close time)
        enriched = []
        for pos in positions_list:
            ticker = pos.get("ticker", "")
            abs_count, side = _parse_kalshi_position(pos)
            market_path = f"/markets/{ticker}"
            mkt_headers = signed_headers("GET", market_path)
            title = ticker
            close_time = None
            result = None
            try:
                mkt_resp = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + market_path,
                    headers=mkt_headers,
                    timeout=TIMEOUT,
                )
                mkt_resp.raise_for_status()
                mkt = mkt_resp.json().get("market", {})
                title = mkt.get("title", ticker)
                close_time = mkt.get("expected_expiration_time") or mkt.get("close_time")
                result = mkt.get("result")
            except Exception:
                pass

            enriched.append({
                "ticker": ticker,
                "title": title,
                "side": side,
                "count": abs_count,
                "market_exposure_cents": _parse_kalshi_dollars(pos.get("market_exposure_dollars") or pos.get("market_exposure")),
                "resting_orders_count": pos.get("resting_orders_count", 0),
                "total_traded_cents": _parse_kalshi_dollars(pos.get("total_traded_dollars") or pos.get("total_traded")),
                "realized_pnl_cents": _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl")),
                "close_time": close_time,
                "result": result,
                "fees_paid_cents": _parse_kalshi_dollars(pos.get("fees_paid_dollars") or pos.get("fees_paid")),
            })
        return jsonify({"positions": enriched})
    except Exception as e:
        return jsonify({"positions": [], "error": str(e)})


_SETTLED_CACHE = {"data": None, "ts": 0}
_SETTLED_CACHE_TTL = 300  # 5 minutes — expensive call, data changes slowly

@app.route("/settled")
def settled_positions():
    """Get settled positions from Kalshi realized P&L. Cached for 2 min."""
    import time as _t
    now = _t.time()
    # Only serve cache if it has actual settled data (don't cache empty results)
    if _SETTLED_CACHE["data"] and (now - _SETTLED_CACHE["ts"]) < _SETTLED_CACHE_TTL:
        if _SETTLED_CACHE["data"].get("settled") or _SETTLED_CACHE["data"].get("wins", 0) + _SETTLED_CACHE["data"].get("losses", 0) > 0:
            return jsonify(_SETTLED_CACHE["data"])
    path = "/portfolio/positions"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"settled": [], "error": "No API key"})
    try:
        # Get ALL positions (settled + unsettled) with realized P&L
        positions_list = []
        for _status in ["settled", "unsettled"]:
            cursor = None
            for _ in range(10):
                params = {"limit": 200, "settlement_status": _status}
                if cursor:
                    params["cursor"] = cursor
                h = signed_headers("GET", path)
                resp = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                    headers=h, params=params, timeout=TIMEOUT,
                )
                resp.raise_for_status()
                page = resp.json()
                positions_list.extend(page.get("market_positions", []))
                cursor = page.get("cursor")
                if not cursor:
                    break

        # Only keep positions with non-zero realized P&L (completed trades)
        _day1_cutoff = TRADE_JOURNAL_START  # "2026-03-16"
        wins = 0
        losses = 0
        breakeven = 0
        total_pnl = 0
        total_wagered = 0
        biggest_win = 0
        biggest_loss = 0
        streak = 0
        current_streak_type = None
        settled = []

        # Build a map of BUY timestamps from all_trades + trade journal for date filtering
        # Only use buy fills — sell/settlement fills have today's date for old positions
        _trade_dates = {}
        for _at in BOT_STATE.get("all_trades", []):
            _tk = _at.get("ticker", "")
            _action = _at.get("action", "buy")
            _ts = (_at.get("timestamp", "") or "")[:10]
            if _tk and _ts and _action != "sell":
                if _tk not in _trade_dates or _ts < _trade_dates[_tk]:
                    _trade_dates[_tk] = _ts  # Use EARLIEST buy date
        # Also check trade journal for tickers missing from all_trades
        for _jt in _TRADE_JOURNAL:
            _tk = _jt.get("ticker", "")
            _ts = (_jt.get("trade_date") or (_jt.get("timestamp", "") or "")[:10] or "")
            if _tk and _ts and _tk not in _trade_dates:
                _trade_dates[_tk] = _ts
        # If trade history is empty (post-deploy before hydration), fetch fills from Kalshi
        # so we can still show settled positions. Limit to 1 fast page to avoid blocking startup.
        if not _trade_dates:
            try:
                _fills_h = signed_headers("GET", "/portfolio/fills")
                _fills_r = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/fills",
                    headers=_fills_h, params={"limit": 200}, timeout=10,
                )
                if _fills_r.ok:
                    for _f in _fills_r.json().get("fills", []):
                        _fk = _f.get("ticker", "")
                        _ft = (_f.get("created_time", "") or "")[:10]
                        _fa = _f.get("action", "buy")
                        if _fk and _ft and _fa != "sell":
                            if _fk not in _trade_dates or _ft < _trade_dates[_fk]:
                                _trade_dates[_fk] = _ft
                print(f"[SETTLED] Hydrated {len(_trade_dates)} trade dates from fills API (post-deploy)")
            except Exception as _fe:
                print(f"[SETTLED] Fills fetch error: {_fe}")

        # Cache market titles — pre-populate from trade journal to avoid API calls
        _title_cache = {}
        for _jt in _TRADE_JOURNAL:
            _tk = _jt.get("ticker", "")
            _tt = _jt.get("title", "")
            if _tk and _tt:
                _title_cache[_tk] = _tt
        # Also check all_trades
        for _at in BOT_STATE.get("all_trades", []):
            _tk = _at.get("ticker", "")
            _tt = _at.get("title", "")
            if _tk and _tt and _tk not in _title_cache:
                _title_cache[_tk] = _tt
        def _get_title(ticker):
            if ticker in _title_cache:
                return _title_cache[ticker]
            try:
                mkt_path = f"/markets/{ticker}"
                mkt_h = signed_headers("GET", mkt_path)
                mkt_r = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + mkt_path,
                    headers=mkt_h, timeout=5,
                )
                if mkt_r.ok:
                    mkt = mkt_r.json().get("market", {})
                    _title_cache[ticker] = mkt.get("title", ticker)
                    return _title_cache[ticker]
            except Exception:
                pass
            _title_cache[ticker] = ticker
            return ticker

        # Deduplicate positions by ticker — the same ticker can appear in both
        # "settled" and "unsettled" results with non-zero realized P&L
        _seen_tickers = {}
        for pos in positions_list:
            ticker = pos.get("ticker", "")
            if not ticker:
                continue
            pnl_cents = _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl"))
            if ticker not in _seen_tickers or abs(pnl_cents) > abs(
                _parse_kalshi_dollars(_seen_tickers[ticker].get("realized_pnl_dollars") or _seen_tickers[ticker].get("realized_pnl"))
            ):
                _seen_tickers[ticker] = pos

        for pos in _seen_tickers.values():
            pnl_cents = _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl"))
            pnl = pnl_cents / 100
            # Skip positions with zero realized P&L (still open, no completed trades)
            if abs(pnl) < 0.005:
                continue

            ticker = pos.get("ticker", "")
            # Filter: only Day 1+ trades that are in our trade history
            trade_date = _trade_dates.get(ticker, "")
            if not trade_date:
                continue  # Not in recent trade history — skip
            if trade_date < _day1_cutoff:
                continue  # Pre-Day-1 — skip

            title = _get_title(ticker)
            # total_traded from Kalshi includes settlement payouts, not just cost
            # We'll compute actual cost from entry_price * count after side detection
            traded_cents = _parse_kalshi_dollars(pos.get("total_traded_dollars") or pos.get("total_traded"))

            total_pnl += pnl

            if pnl > 0.005:
                wins += 1
                won = True
                biggest_win = max(biggest_win, pnl)
                if current_streak_type == "win":
                    streak += 1
                else:
                    streak = 1
                    current_streak_type = "win"
            elif pnl < -0.005:
                losses += 1
                won = False
                biggest_loss = min(biggest_loss, pnl)
                if current_streak_type == "loss":
                    streak += 1
                else:
                    streak = 1
                    current_streak_type = "loss"
            else:
                breakeven += 1
                won = None

            # Derive side: for settled positions, position_fp is 0 so
            # _parse_kalshi_position defaults to "yes". Instead, determine side
            # from which average price is non-zero, or fall back to trade history.
            side = ""
            count = 0
            try:
                count = int(float(str(pos.get("total_count_fp") or pos.get("total_count") or 0)))
            except Exception:
                pass
            # Check which side has a non-zero average price
            _avg_yes = float(str(pos.get("average_yes_price_dollars") or pos.get("average_yes_price") or 0))
            _avg_no = float(str(pos.get("average_no_price_dollars") or pos.get("average_no_price") or 0))
            if _avg_yes > 0 and _avg_no > 0:
                # Both have prices — use trade history to determine which side we bought
                pass
            elif _avg_yes > 0:
                side = "yes"
            elif _avg_no > 0:
                side = "no"
            # Fall back to trade history for side and strategy
            trade_strategy = "unknown"
            _trade_date_from_history = ""
            for t in BOT_STATE.get("all_trades", []):
                if t.get("ticker") == ticker:
                    if not side:
                        side = t.get("side") or side
                    trade_strategy = t.get("strategy") or "unknown"
                    _td = (t.get("timestamp") or "")[:10]
                    if _td and (not _trade_date_from_history or _td < _trade_date_from_history):
                        _trade_date_from_history = _td
                    break
            if not side:
                side = "yes"  # last resort default
            # Use trade history date if the lookup table date seems wrong
            if _trade_date_from_history and _trade_date_from_history != trade_date:
                trade_date = _trade_date_from_history

            entry_cents = 0
            try:
                if side == "yes":
                    entry_cents = int(round(_avg_yes * 100))
                else:
                    entry_cents = int(round(_avg_no * 100))
            except Exception:
                pass

            # Calculate actual cost wagered (entry_price * count)
            actual_cost = (entry_cents * count) / 100 if entry_cents > 0 and count > 0 else traded_cents / 100
            total_wagered += actual_cost

            category = classify_market_category(title, ticker)

            # Get settlement time from position data
            settle_time = pos.get("settlement_time") or pos.get("last_updated") or ""

            # Look up edge reasoning from trade journal
            _edge_reasons = []
            _espn_edge = None
            _conviction = 0
            _game_state_at_entry = ""
            _entry_time = ""
            # Check trade journal first (richest data)
            for _jrec in _TRADE_JOURNAL:
                if _jrec.get("ticker") == ticker:
                    # ESPN edge
                    if _jrec.get("espn_edge"):
                        try:
                            _espn_edge = float(_jrec["espn_edge"])
                            _espn_implied = _jrec.get("espn_implied_prob")
                            _kalshi_implied = _jrec.get("kalshi_implied_prob") or (entry_cents / 100.0 if entry_cents else 0)
                            _edge_reasons.append(f"ESPN sportsbook edge: +{_espn_edge:.1%}")
                            if _espn_implied:
                                _edge_reasons.append(f"ESPN implied: {float(_espn_implied):.0%} vs Kalshi: {float(_kalshi_implied):.0%}")
                        except (ValueError, TypeError):
                            _edge_reasons.append(f"ESPN edge detected")
                    # Game state
                    if _jrec.get("game_state") == "in":
                        try:
                            _margin = _jrec.get("game_margin")
                            _period = _jrec.get("game_period", "") or ""
                            _gs_str = "LIVE game"
                            if _margin is not None:
                                _gs_str += f" (margin: {_margin} pts)"
                            if _period:
                                _gs_str += f" {_period}"
                            _edge_reasons.append(_gs_str)
                        except Exception:
                            _edge_reasons.append("LIVE game")
                        _game_state_at_entry = "live"
                    elif _jrec.get("game_state") == "post":
                        _edge_reasons.append("Game finished, settling")
                        _game_state_at_entry = "post"
                    # Strategy reasoning
                    _strat = _jrec.get("strategy", "")
                    if _strat == "live_sniper":
                        _edge_reasons.append(f"Sniper: favorite at {entry_cents}¢ (65-85¢ range)")
                    elif _strat == "moonshark":
                        _edge_reasons.append(f"MoonShark: underdog at {entry_cents}¢ (25-40¢ range)")
                    elif _strat == "closegame":
                        _edge_reasons.append(f"CloseGame: late-game underdog at {entry_cents}¢")
                    # Orderbook
                    if _jrec.get("ob_spread") is not None:
                        _edge_reasons.append(f"Spread: {_jrec['ob_spread']}¢")
                    if _jrec.get("ob_liquidity"):
                        _edge_reasons.append(f"Liquidity: {_jrec['ob_liquidity']}")
                    # Momentum
                    if _jrec.get("momentum_direction") and _jrec["momentum_direction"] != "flat":
                        _mom_mag = _jrec.get('momentum_magnitude') or 0
                        _edge_reasons.append(f"Momentum: {_jrec['momentum_direction']} ({_mom_mag:.0f})")
                    _entry_time = _jrec.get("entry_time", "")
                    break
            # Also check today's trade arrays for edge_reasons (newer trades)
            if not _edge_reasons:
                for _tlist_name in ["snipe_trades_today", "moonshark_trades_today", "closegame_trades_today"]:
                    for _tt in BOT_STATE.get(_tlist_name, []):
                        if _tt.get("ticker") == ticker:
                            _edge_reasons = _tt.get("edge_reasons", [])
                            _conviction = _tt.get("conviction", 0)
                            _espn_edge = _tt.get("espn_edge")
                            break
                    if _edge_reasons:
                        break
            # Default reasoning if nothing found
            if not _edge_reasons:
                if entry_cents >= 65:
                    _edge_reasons.append(f"Favorite at {entry_cents}¢ — high implied probability")
                elif entry_cents <= 40:
                    _edge_reasons.append(f"Underdog at {entry_cents}¢ — high potential payout")
                else:
                    _edge_reasons.append(f"Entry at {entry_cents}¢")

            settled.append({
                "ticker": ticker,
                "title": title,
                "pnl_usd": round(pnl, 2),
                "won": won,
                "total_traded": round(actual_cost, 2),
                "category": category,
                "strategy": trade_strategy,
                "side": side,
                "count": count,
                "entry_cents": entry_cents,
                "trade_date": trade_date,
                "settle_time": settle_time,
                "edge_reasons": _edge_reasons,
                "espn_edge": round(_espn_edge, 4) if _espn_edge else None,
                "conviction": _conviction,
                "game_state_at_entry": _game_state_at_entry,
                "entry_time": _entry_time,
            })

        # Sort by trade_date descending (newest first), then settle_time as tiebreaker
        # trade_date reflects when we BOUGHT, which is what users see in the UI
        settled.sort(key=lambda s: (s.get("trade_date") or "", s.get("settle_time") or ""), reverse=True)

        total_bets = wins + losses + breakeven
        roi = round(total_pnl / max(0.01, total_wagered) * 100, 1) if total_wagered > 0 else 0

        # Category breakdown
        by_category = {}
        for s in settled:
            cat = s.get("category", "other")
            if cat not in by_category:
                by_category[cat] = {"wins": 0, "losses": 0, "pnl_usd": 0, "bets": 0}
            by_category[cat]["bets"] += 1
            by_category[cat]["pnl_usd"] += s["pnl_usd"]
            if s["won"] is True:
                by_category[cat]["wins"] += 1
            elif s["won"] is False:
                by_category[cat]["losses"] += 1
        for cat in by_category:
            c = by_category[cat]
            c["win_rate"] = round(c["wins"] / max(1, c["wins"] + c["losses"]) * 100, 1)
            c["pnl_usd"] = round(c["pnl_usd"], 2)

        result = {
            "settled": settled,
            "wins": wins,
            "losses": losses,
            "breakeven": breakeven,
            "win_rate": round(wins / max(1, wins + losses) * 100, 1),
            "total_pnl_usd": round(total_pnl, 2),
            "total_wagered_usd": round(total_wagered, 2),
            "roi_pct": roi,
            "biggest_win_usd": round(biggest_win, 2),
            "biggest_loss_usd": round(biggest_loss, 2),
            "streak": streak,
            "streak_type": current_streak_type or "none",
            "total_bets": total_bets,
            "by_category": by_category,
        }
        _SETTLED_CACHE["data"] = result
        _SETTLED_CACHE["ts"] = now
        return jsonify(result)
    except Exception as e:
        return jsonify({"settled": [], "error": str(e)})


@app.route("/debug-scan")
def debug_scan():
    """Quick diagnostic: what can the snipers see right now?"""
    results = {"series_scanned": [], "eligible_markets": [], "rejection_summary": {}}
    try:
        for series in LIVE_GAME_SERIES:
            mh = signed_headers("GET", "/markets")
            if not mh:
                continue
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh,
                params={"limit": 50, "status": "open", "series_ticker": series},
                timeout=8,
            )
            if not resp.ok:
                results["series_scanned"].append({"series": series, "count": 0, "error": resp.status_code})
                continue
            mkts = resp.json().get("markets", [])
            # Grab first market's raw price fields for debugging
            if mkts and series not in [s.get("series") for s in results.get("_raw_samples", [])]:
                _sample = mkts[0]
                _price_fields = {k: v for k, v in _sample.items() if any(p in k.lower() for p in ["price", "ask", "bid", "yes", "no", "last"])}
                _price_fields["_ticker"] = _sample.get("ticker", "")[:30]
                _price_fields["_volume"] = _sample.get("volume", "N/A")
                _price_fields["_close_time"] = _sample.get("close_time", "N/A")
                results.setdefault("_raw_samples", []).append({"series": series, "fields": _price_fields})
            results["series_scanned"].append({"series": series, "count": len(mkts)})
            for m in mkts:
                ya = m.get("yes_ask", 0) or m.get("yes_ask_dollars", 0) or 0
                na = m.get("no_ask", 0) or m.get("no_ask_dollars", 0) or 0
                try:
                    yes_cents = int(round(float(str(ya)) * 100)) if ya else 0
                    no_cents = int(round(float(str(na)) * 100)) if na else 0
                except Exception:
                    yes_cents = no_cents = 0
                vol = float(str(m.get("yes_ask_size_fp") or m.get("volume") or 0))
                ct = m.get("close_time", "")
                hours_left = 999
                try:
                    if ct:
                        cd = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00")).replace(tzinfo=None)
                        hours_left = round((cd - datetime.datetime.utcnow()).total_seconds() / 3600, 1)
                except Exception:
                    pass
                # Check if this would be eligible for any strategy
                eligible_for = []
                if 10 <= yes_cents <= 45 and vol >= 50 and 0 < hours_left <= 24:
                    eligible_for.append("moonshark_yes")
                if 10 <= no_cents <= 45 and vol >= 50 and 0 < hours_left <= 24:
                    eligible_for.append("moonshark_no")
                if 70 <= yes_cents <= 90 and vol >= 50:
                    eligible_for.append("sniper_yes")
                if 70 <= no_cents <= 90 and vol >= 50:
                    eligible_for.append("sniper_no")
                if eligible_for:
                    results["eligible_markets"].append({
                        "ticker": m.get("ticker", "")[:40],
                        "title": (m.get("title", "") or "")[:50],
                        "yes": yes_cents, "no": no_cents,
                        "vol": vol, "hours_left": hours_left,
                        "eligible": eligible_for,
                    })
    except Exception as e:
        results["error"] = str(e)
    return jsonify(results)


@app.route("/trends")
def trends_endpoint():
    """Generate daily trends from learning engine + trade data."""
    try:
        return _generate_trends()
    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({"trends": [{"icon": "⚠️", "title": "Trends loading...", "detail": str(e), "color": "#ffb400"}], "enhancements": [], "parameters": {}, "summary": {"total_settled": 0, "overall_win_rate": 0, "total_wins": 0, "total_losses": 0, "learning_version": 0, "dimensions_learned": 0}})

def _generate_trends():
    params = _LEARNING_STATE.get("parameters", {})
    settled = [t for t in _TRADE_JOURNAL if t.get("result")]
    total_settled = len(settled)
    total_wins = sum(1 for t in settled if t["result"] == "win")
    total_losses = total_settled - total_wins
    overall_wr = round(total_wins / max(1, total_settled) * 100, 1)

    trends = []
    enhancements = []

    # --- Trend 1: Best and worst sport ---
    sport_w = params.get("sport_weights", {})
    if sport_w:
        best_sport = max(sport_w.items(), key=lambda x: x[1].get("win_rate") or 0, default=None)
        worst_sport = min((x for x in sport_w.items() if (x[1].get("sample_size") or 0) >= 3), key=lambda x: x[1].get("win_rate") or 0, default=None)
        if best_sport and best_sport[1].get("sample_size", 0) >= 3:
            bs = best_sport[1]
            trends.append({
                "icon": "🏆", "title": f"{best_sport[0].replace('_', ' ').title()} is our best sport",
                "detail": f"{bs['win_rate']:.0%} win rate ({bs['wins']}W/{bs['losses']}L) — ${bs['pnl']:+.2f} P&L",
                "color": "#00dc5a",
            })
            enhancements.append({"icon": "🔼", "text": f"Boosting {best_sport[0]} bets to {bs['weight']}x sizing", "color": "#00dc5a"})
        if worst_sport and worst_sport[1].get("sample_size", 0) >= 3 and worst_sport[0] != (best_sport[0] if best_sport else ""):
            ws = worst_sport[1]
            trends.append({
                "icon": "📉", "title": f"{worst_sport[0].replace('_', ' ').title()} is consistently losing",
                "detail": f"{ws['win_rate']:.0%} win rate ({ws['wins']}W/{ws['losses']}L) — ${ws['pnl']:+.2f} P&L",
                "color": "#ff5000",
            })
            if ws["weight"] == 0:
                enhancements.append({"icon": "🚫", "text": f"Blocked {worst_sport[0]} — 0% win rate on {ws['sample_size']}+ trades", "color": "#ff5000"})
            else:
                enhancements.append({"icon": "🔽", "text": f"Reduced {worst_sport[0]} bets to {ws['weight']}x sizing", "color": "#ffb400"})

    # --- Trend 2: Best price range ---
    price_w = params.get("price_range_weights", {})
    if price_w:
        profitable_ranges = [(k, v) for k, v in price_w.items() if (v.get("win_rate") or 0) > 0 and (v.get("sample_size") or 0) >= 3]
        if profitable_ranges:
            best_pr = max(profitable_ranges, key=lambda x: x[1].get("win_rate") or 0)
            bp = best_pr[1]
            trends.append({
                "icon": "💰", "title": f"Sweet spot: {best_pr[0]}¢ price range",
                "detail": f"{bp['win_rate']:.0%} win rate ({bp['wins']}W/{bp['losses']}L) — best risk/reward zone",
                "color": "#ffb400",
            })
            enhancements.append({"icon": "🎯", "text": f"Prioritizing {best_pr[0]}¢ bets with {bp['weight']}x multiplier", "color": "#ffb400"})
        losing_ranges = [(k, v) for k, v in price_w.items() if (v.get("win_rate") or 0) == 0 and (v.get("sample_size") or 0) >= 5]
        for lr in losing_ranges:
            trends.append({
                "icon": "⚠️", "title": f"{lr[0]}¢ range has 0% win rate",
                "detail": f"0 wins on {lr[1]['sample_size']} trades — dead money zone",
                "color": "#ff5000",
            })

    # --- Trend 3: Category insights ---
    cat_w = params.get("category_weights", {})
    if cat_w:
        blocked = [(k, v) for k, v in cat_w.items() if (v.get("weight") or 0) == 0 and (v.get("sample_size") or 0) >= 3]
        for bc in blocked[:2]:
            trends.append({
                "icon": "🚫", "title": f"{bc[0].title()} category auto-blocked",
                "detail": f"{bc[1]['wins']}W/{bc[1]['losses']}L ({bc[1]['win_rate']:.0%}) — learning engine disabled this",
                "color": "#ff5000",
            })
            enhancements.append({"icon": "🛑", "text": f"Category '{bc[0]}' permanently blocked", "color": "#ff5000"})

    # --- Trend 4: Strategy comparison ---
    strat_w = params.get("strategy_weights", {})
    if strat_w:
        for strat, data in sorted(strat_w.items(), key=lambda x: x[1].get("pnl") or 0, reverse=True):
            if (data.get("sample_size") or 0) >= 3:
                _pnl = data.get("pnl") or 0
                _wr = data.get("win_rate") or 0
                _wins = data.get("wins") or 0
                _losses = data.get("losses") or 0
                _ss = data.get("sample_size") or 0
                color = "#00dc5a" if _pnl > 0 else "#ff5000"
                trends.append({
                    "icon": "📊", "title": f"{strat.replace('_', ' ').title()} strategy: ${_pnl:+.2f}",
                    "detail": f"{_wr:.0%} win rate ({_wins}W/{_losses}L) — {_ss} trades",
                    "color": color,
                })
                break  # just show the best/worst

    # --- Trend 5: Overall trajectory ---
    if total_settled >= 5:
        recent = settled[-20:]  # last 20 trades
        recent_wins = sum(1 for t in recent if t["result"] == "win")
        recent_wr = round(recent_wins / len(recent) * 100, 1)
        trend_dir = "improving" if recent_wr > overall_wr else "declining"
        trends.append({
            "icon": "📈" if recent_wr > overall_wr else "📉",
            "title": f"Win rate is {trend_dir}",
            "detail": f"Last 20 trades: {recent_wr}% ({recent_wins}W/{len(recent)-recent_wins}L) vs overall {overall_wr}%",
            "color": "#00dc5a" if recent_wr > overall_wr else "#ff5000",
        })

    # Fill to 5 trends minimum
    while len(trends) < 5:
        trends.append({
            "icon": "🔍", "title": "Collecting more data",
            "detail": f"{total_settled} trades analyzed — more data = better patterns. Need 50+ for strong signals.",
            "color": "#888",
        })

    # Default enhancements
    if not enhancements:
        enhancements.append({"icon": "🧠", "text": "Learning engine active — analyzing patterns across 8 dimensions", "color": "#00d4ff"})

    enhancements.append({"icon": "🔄", "text": f"Learning engine v{_LEARNING_STATE.get('version', 0)} — last run: {_LEARNING_STATE.get('last_run', 'pending')}", "color": "#888"})

    return jsonify({
        "trends": trends[:5],
        "enhancements": enhancements,
        "summary": {
            "total_settled": total_settled,
            "overall_win_rate": overall_wr,
            "total_wins": total_wins,
            "total_losses": total_losses,
            "learning_version": _LEARNING_STATE.get("version", 0),
            "dimensions_learned": len(params),
        },
        "parameters": params,
    })


@app.route("/analytics/learning")
def analytics_learning():
    """Return current learning state and parameter adjustments."""
    settled_count = sum(1 for t in _TRADE_JOURNAL if t.get("result"))
    return jsonify({
        "version": _LEARNING_STATE.get("version", 0),
        "last_run": _LEARNING_STATE.get("last_run"),
        "parameters": _LEARNING_STATE.get("parameters", {}),
        "insights": _LEARNING_STATE.get("insights", []),
        "trade_journal_size": len(_TRADE_JOURNAL),
        "settled_count": settled_count,
    })


@app.route("/analytics")
def analytics_endpoint():
    """Return processed analytics data from trade journal and category stats."""
    try:
        settled = [t for t in _TRADE_JOURNAL if t.get("result") is not None]

        # --- Win Rate by Sport ---
        by_sport = {}
        for t in settled:
            sport = t.get("sport_type") or t.get("category") or "other"
            if sport not in by_sport:
                by_sport[sport] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
            by_sport[sport]["total"] += 1
            if t["result"] == "win":
                by_sport[sport]["wins"] += 1
            elif t["result"] == "loss":
                by_sport[sport]["losses"] += 1
            by_sport[sport]["pnl"] += t.get("pnl_usd") or 0
        for k in by_sport:
            s = by_sport[k]
            s["pnl"] = round(s["pnl"], 2)
            s["win_rate"] = round(s["wins"] / max(1, s["wins"] + s["losses"]) * 100, 1)

        # --- Win Rate by Price Range ---
        price_buckets = [
            ("70-74", 70, 74),
            ("75-79", 75, 79),
            ("80-84", 80, 84),
            ("85-89", 85, 89),
            ("90-100", 90, 100),
        ]
        by_price = {}
        for label, lo, hi in price_buckets:
            by_price[label] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
        # Also capture trades outside these ranges
        by_price["<70"] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
        for t in settled:
            pc = t.get("price_cents") or 0
            bucket = "<70"
            for label, lo, hi in price_buckets:
                if lo <= pc <= hi:
                    bucket = label
                    break
            by_price[bucket]["total"] += 1
            if t["result"] == "win":
                by_price[bucket]["wins"] += 1
            elif t["result"] == "loss":
                by_price[bucket]["losses"] += 1
            by_price[bucket]["pnl"] += t.get("pnl_usd") or 0
        for k in by_price:
            b = by_price[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = round(b["wins"] / max(1, b["wins"] + b["losses"]) * 100, 1)
            b["avg_pnl"] = round(b["pnl"] / max(1, b["total"]), 2)

        # --- Time of Day Performance ---
        time_periods = {
            "Morning (6am-12pm)": {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0},
            "Afternoon (12pm-6pm)": {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0},
            "Evening (6pm-12am)": {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0},
            "Night (12am-6am)": {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0},
        }
        for t in settled:
            hour = t.get("entry_hour")
            if hour is None:
                continue
            if 6 <= hour < 12:
                period = "Morning (6am-12pm)"
            elif 12 <= hour < 18:
                period = "Afternoon (12pm-6pm)"
            elif 18 <= hour < 24:
                period = "Evening (6pm-12am)"
            else:
                period = "Night (12am-6am)"
            time_periods[period]["total"] += 1
            if t["result"] == "win":
                time_periods[period]["wins"] += 1
            elif t["result"] == "loss":
                time_periods[period]["losses"] += 1
            time_periods[period]["pnl"] += t.get("pnl_usd") or 0
        for k in time_periods:
            p = time_periods[k]
            p["pnl"] = round(p["pnl"], 2)
            p["win_rate"] = round(p["wins"] / max(1, p["wins"] + p["losses"]) * 100, 1)

        # --- Key Insights ---
        total_wins = sum(1 for t in settled if t["result"] == "win")
        total_losses = sum(1 for t in settled if t["result"] == "loss")
        overall_wr = round(total_wins / max(1, total_wins + total_losses) * 100, 1)
        win_pnls = [t.get("pnl_usd", 0) for t in settled if t["result"] == "win"]
        loss_pnls = [t.get("pnl_usd", 0) for t in settled if t["result"] == "loss"]
        avg_win = round(sum(win_pnls) / max(1, len(win_pnls)), 2)
        avg_loss = round(sum(loss_pnls) / max(1, len(loss_pnls)), 2)

        best_sport = max(by_sport.items(), key=lambda x: x[1]["pnl"])[0] if by_sport else "N/A"
        # Best price range (exclude <70 and empty)
        valid_prices = {k: v for k, v in by_price.items() if v["total"] > 0 and k != "<70"}
        best_price = max(valid_prices.items(), key=lambda x: x[1]["win_rate"])[0] if valid_prices else "N/A"

        # Also include _CATEGORY_STATS for broader coverage
        cat_stats_copy = {}
        for cat, data in _CATEGORY_STATS.items():
            cat_stats_copy[cat] = {
                "wins": data.get("wins", 0),
                "losses": data.get("losses", 0),
                "pnl": round(data.get("pnl", 0), 2),
                "win_rate": round(data.get("wins", 0) / max(1, data.get("wins", 0) + data.get("losses", 0)) * 100, 1),
            }

        return jsonify({
            "by_sport": by_sport,
            "by_price": by_price,
            "by_time": time_periods,
            "category_stats": cat_stats_copy,
            "insights": {
                "overall_win_rate": overall_wr,
                "total_trades": len(settled),
                "total_wins": total_wins,
                "total_losses": total_losses,
                "avg_win_profit": avg_win,
                "avg_loss_amount": avg_loss,
                "best_sport": best_sport,
                "best_price_range": best_price,
            },
        })
    except Exception as e:
        return jsonify({"error": str(e)})


@app.route("/analytics/patterns")
def analytics_patterns_endpoint():
    """Deep pattern analysis of trade journal — win rates sliced by every dimension."""
    try:
        settled = [t for t in _TRADE_JOURNAL if t.get("result") is not None]
        if not settled:
            return jsonify({"message": "No settled trades in journal yet", "total_settled": 0})

        wins = [t for t in settled if t["result"] == "win"]
        losses = [t for t in settled if t["result"] == "loss"]
        total_decided = len(wins) + len(losses)

        def _wr(w, l):
            return round(w / max(1, w + l) * 100, 1)

        def _avg(vals):
            return round(sum(vals) / max(1, len(vals)), 2) if vals else 0

        # --- Win rate by hour of day (0-23) ---
        by_hour = {}
        for t in settled:
            h = t.get("entry_hour")
            if h is None:
                continue
            key = str(h)
            if key not in by_hour:
                by_hour[key] = {"hour": h, "wins": 0, "losses": 0, "pnl": 0.0}
            if t["result"] == "win":
                by_hour[key]["wins"] += 1
            elif t["result"] == "loss":
                by_hour[key]["losses"] += 1
            by_hour[key]["pnl"] += t.get("pnl_usd") or 0
        for k in by_hour:
            b = by_hour[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])
            b["total"] = b["wins"] + b["losses"]

        # --- Win rate by day of week ---
        by_day = {}
        for t in settled:
            d = t.get("entry_day", "Unknown")
            if d not in by_day:
                by_day[d] = {"wins": 0, "losses": 0, "pnl": 0.0}
            if t["result"] == "win":
                by_day[d]["wins"] += 1
            elif t["result"] == "loss":
                by_day[d]["losses"] += 1
            by_day[d]["pnl"] += t.get("pnl_usd") or 0
        for k in by_day:
            b = by_day[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])
            b["total"] = b["wins"] + b["losses"]

        # --- Win rate by market_type ---
        by_market_type = {}
        for t in settled:
            mt = t.get("market_type", "unknown")
            if mt not in by_market_type:
                by_market_type[mt] = {"wins": 0, "losses": 0, "pnl": 0.0}
            if t["result"] == "win":
                by_market_type[mt]["wins"] += 1
            elif t["result"] == "loss":
                by_market_type[mt]["losses"] += 1
            by_market_type[mt]["pnl"] += t.get("pnl_usd") or 0
        for k in by_market_type:
            b = by_market_type[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])
            b["total"] = b["wins"] + b["losses"]

        # --- Win rate by price range (5c buckets from 5-45c) ---
        price_range_buckets = [
            ("5-15c", 5, 15), ("15-25c", 15, 25), ("25-35c", 25, 35), ("35-45c", 35, 45),
            ("45-55c", 45, 55), ("55-65c", 55, 65), ("65-75c", 65, 75), ("75-85c", 75, 85),
            ("85-95c", 85, 95), ("95-100c", 95, 100),
        ]
        by_price_range = {}
        for label, lo, hi in price_range_buckets:
            by_price_range[label] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
        by_price_range["<5c"] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
        for t in settled:
            pc = t.get("price_cents") or 0
            bucket = "<5c"
            for label, lo, hi in price_range_buckets:
                if lo <= pc <= hi:
                    bucket = label
                    break
            by_price_range[bucket]["total"] += 1
            if t["result"] == "win":
                by_price_range[bucket]["wins"] += 1
            elif t["result"] == "loss":
                by_price_range[bucket]["losses"] += 1
            by_price_range[bucket]["pnl"] += t.get("pnl_usd") or 0
        # Remove empty buckets, compute win rates
        by_price_range = {k: v for k, v in by_price_range.items() if v["total"] > 0}
        for k in by_price_range:
            b = by_price_range[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])
            b["avg_pnl"] = round(b["pnl"] / max(1, b["total"]), 2)

        # --- Win rate by category ---
        by_category = {}
        for t in settled:
            cat = t.get("category", "unknown")
            if cat not in by_category:
                by_category[cat] = {"wins": 0, "losses": 0, "pnl": 0.0}
            if t["result"] == "win":
                by_category[cat]["wins"] += 1
            elif t["result"] == "loss":
                by_category[cat]["losses"] += 1
            by_category[cat]["pnl"] += t.get("pnl_usd") or 0
        for k in by_category:
            b = by_category[k]
            b["total"] = b["wins"] + b["losses"]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])
            b["avg_pnl"] = round(b["pnl"] / max(1, b["total"]), 2)

        # --- Average P&L by category ---
        avg_pnl_by_category = {k: v["avg_pnl"] for k, v in by_category.items() if v["total"] > 0}

        # --- Win rate by risk/reward ratio bucket ---
        rr_buckets = [("1-2x", 1, 2), ("2-3x", 2, 3), ("3-5x", 3, 5), ("5-10x", 5, 10), ("10x+", 10, 1000)]
        by_risk_reward = {}
        for label, lo, hi in rr_buckets:
            by_risk_reward[label] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
        for t in settled:
            rr = t.get("risk_reward_ratio") or 0
            bucket = None
            for label, lo, hi in rr_buckets:
                if lo <= rr < hi:
                    bucket = label
                    break
            if not bucket:
                continue
            by_risk_reward[bucket]["total"] += 1
            if t["result"] == "win":
                by_risk_reward[bucket]["wins"] += 1
            elif t["result"] == "loss":
                by_risk_reward[bucket]["losses"] += 1
            by_risk_reward[bucket]["pnl"] += t.get("pnl_usd") or 0
        by_risk_reward = {k: v for k, v in by_risk_reward.items() if v["total"] > 0}
        for k in by_risk_reward:
            b = by_risk_reward[k]
            b["pnl"] = round(b["pnl"], 2)
            b["win_rate"] = _wr(b["wins"], b["losses"])

        # --- Underdog vs Favorite ---
        underdog_trades = [t for t in settled if t.get("is_underdog")]
        favorite_trades = [t for t in settled if t.get("is_favorite")]
        underdog_wins = sum(1 for t in underdog_trades if t["result"] == "win")
        underdog_losses = sum(1 for t in underdog_trades if t["result"] == "loss")
        fav_wins = sum(1 for t in favorite_trades if t["result"] == "win")
        fav_losses = sum(1 for t in favorite_trades if t["result"] == "loss")

        # --- Best-of insights ---
        # Most profitable hour
        best_hour = max(by_hour.values(), key=lambda x: x["pnl"]) if by_hour else None
        # Most profitable price range
        best_price_range = max(by_price_range.items(), key=lambda x: x[1]["pnl"])[0] if by_price_range else None
        # Best risk/reward that wins
        winning_rr = {k: v for k, v in by_risk_reward.items() if v["wins"] > 0}
        best_rr = max(winning_rr.items(), key=lambda x: x[1]["win_rate"])[0] if winning_rr else None

        return jsonify({
            "total_settled": len(settled),
            "total_wins": len(wins),
            "total_losses": len(losses),
            "overall_win_rate": _wr(len(wins), len(losses)),
            "by_hour": by_hour,
            "by_day_of_week": by_day,
            "by_market_type": by_market_type,
            "by_price_range": by_price_range,
            "by_category": by_category,
            "avg_pnl_by_category": avg_pnl_by_category,
            "by_risk_reward": by_risk_reward,
            "underdog_vs_favorite": {
                "underdog": {"wins": underdog_wins, "losses": underdog_losses,
                             "win_rate": _wr(underdog_wins, underdog_losses),
                             "pnl": round(sum(t.get("pnl_usd") or 0 for t in underdog_trades), 2)},
                "favorite": {"wins": fav_wins, "losses": fav_losses,
                             "win_rate": _wr(fav_wins, fav_losses),
                             "pnl": round(sum(t.get("pnl_usd") or 0 for t in favorite_trades), 2)},
            },
            "best_insights": {
                "most_profitable_hour": best_hour["hour"] if best_hour else None,
                "most_profitable_hour_pnl": best_hour["pnl"] if best_hour else None,
                "most_profitable_price_range": best_price_range,
                "best_risk_reward_bucket": best_rr,
            },
        })
    except Exception as e:
        return jsonify({"error": str(e)})


_insights_cache = {"data": None, "date": None}

@app.route("/insights")
def insights_endpoint():
    """Generate 5 actionable daily insights from trading data. Refreshes daily at 6am PT."""
    now_pt = datetime.datetime.now(tz=_PACIFIC)
    # Cache key: date string, but only after 6am PT
    cache_date = now_pt.strftime("%Y-%m-%d") if now_pt.hour >= 6 else (now_pt - datetime.timedelta(days=1)).strftime("%Y-%m-%d")
    if _insights_cache["data"] and _insights_cache["date"] == cache_date:
        return jsonify(_insights_cache["data"])
    generated_at = now_pt.strftime("%b %d, %Y %I:%M %p PT")
    try:
        settled = [t for t in _TRADE_JOURNAL if t.get("result") is not None]
        pending = [t for t in _TRADE_JOURNAL if t.get("result") is None]
        markets_scanned = BOT_STATE.get("last_scan_markets", 0)
        mispriced_count = BOT_STATE.get("last_scan_mispriced", 0)
        daily_spent = BOT_STATE.get("daily_spent_usd", 0.0)
        max_daily = BOT_CONFIG.get("max_daily_usd", 150.0)
        moonshark_trades = BOT_STATE.get("moonshark_trades_today", [])
        moonshark_spent = BOT_STATE.get("moonshark_daily_spent", 0.0)

        insights = []

        # If very little data, return "getting started" insights
        if len(settled) < 3:
            insights.append({
                "title": "Scanner Active",
                "detail": f"Monitoring {markets_scanned} markets across 4 platforms. Found {mispriced_count} mispriced opportunities on last scan.",
                "trend": "neutral",
                "action": "Scanning every 60 seconds for arbitrage edges.",
            })
            insights.append({
                "title": "MoonShark Armed",
                "detail": f"Watching for underdog contracts under 30\u00a2 in close live games. {len(moonshark_trades)} moonshot bets placed today (${moonshark_spent:.2f} spent).",
                "trend": "neutral",
                "action": "Will fire when a live underdog has strong momentum signals.",
            })
            insights.append({
                "title": "Waiting for Results",
                "detail": f"{len(_TRADE_JOURNAL)} total trades placed, {len(pending)} still pending settlement. Need settled trades to generate performance insights.",
                "trend": "neutral",
                "action": "Insights will sharpen as more trades settle and patterns emerge.",
            })
            pct_used = round(daily_spent / max(0.01, max_daily) * 100, 1)
            insights.append({
                "title": "Daily Budget",
                "detail": f"${daily_spent:.2f} of ${max_daily:.2f} budget used today ({pct_used}%). Smart sizing adjusts bets based on bankroll.",
                "trend": "positive" if pct_used < 80 else "negative",
                "action": "Budget resets at midnight UTC each day.",
            })
            cat_count = len([c for c, s in _CATEGORY_STATS.items() if (s.get("wins", 0) + s.get("losses", 0)) > 0])
            insights.append({
                "title": "Category Learning",
                "detail": f"Tracking performance across {cat_count} sport categories. Auto-learning adjusts bet sizes as win/loss data accumulates.",
                "trend": "neutral",
                "action": "Categories with 70%+ win rate get 1.5x bet sizing boost.",
            })
            return jsonify({"insights": insights[:5], "generated_at": generated_at})

        # --- Enough data: generate real insights ---
        candidates = []

        # 1. Best/worst performing sport
        by_sport = {}
        for t in settled:
            sport = t.get("sport_type") or t.get("category") or "other"
            if sport not in by_sport:
                by_sport[sport] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
            by_sport[sport]["total"] += 1
            if t["result"] == "win":
                by_sport[sport]["wins"] += 1
            elif t["result"] == "loss":
                by_sport[sport]["losses"] += 1
            by_sport[sport]["pnl"] += t.get("pnl_usd") or 0

        sports_with_data = {k: v for k, v in by_sport.items() if v["total"] >= 2}
        if sports_with_data:
            for k in sports_with_data:
                s = sports_with_data[k]
                s["win_rate"] = round(s["wins"] / max(1, s["wins"] + s["losses"]) * 100, 1)
            best_sport = max(sports_with_data.items(), key=lambda x: x[1]["pnl"])
            worst_sport = min(sports_with_data.items(), key=lambda x: x[1]["pnl"])
            bname, bdata = best_sport
            mult = _category_multiplier("", bname)
            candidates.append({
                "title": f"{bname.upper()} is Your Best Sport",
                "detail": f"{bdata['win_rate']}% win rate across {bdata['total']} trades with ${bdata['pnl']:.2f} P&L. Leading all categories.",
                "trend": "positive",
                "action": f"Category multiplier set to {mult}x for {bname.upper()} bet sizing.",
                "priority": abs(bdata["pnl"]) + 10,
            })
            if len(sports_with_data) > 1 and worst_sport[0] != best_sport[0]:
                wname, wdata = worst_sport
                wmult = _category_multiplier("", wname)
                candidates.append({
                    "title": f"{wname.upper()} Needs Improvement",
                    "detail": f"{wdata['win_rate']}% win rate with ${wdata['pnl']:.2f} P&L across {wdata['total']} trades.",
                    "trend": "negative" if wdata["pnl"] < 0 else "neutral",
                    "action": f"Category multiplier reduced to {wmult}x to limit exposure.",
                    "priority": abs(wdata["pnl"]) + 5,
                })

        # 2. Optimal price range
        price_buckets = [("<70", 0, 69), ("70-74", 70, 74), ("75-79", 75, 79),
                         ("80-84", 80, 84), ("85-89", 85, 89), ("90-100", 90, 100)]
        by_price = {}
        for t in settled:
            pc = t.get("price_cents") or 0
            bucket = "<70"
            for label, lo, hi in price_buckets:
                if lo <= pc <= hi:
                    bucket = label
                    break
            if bucket not in by_price:
                by_price[bucket] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
            by_price[bucket]["total"] += 1
            if t["result"] == "win":
                by_price[bucket]["wins"] += 1
            elif t["result"] == "loss":
                by_price[bucket]["losses"] += 1
            by_price[bucket]["pnl"] += t.get("pnl_usd") or 0

        valid_prices = {k: v for k, v in by_price.items() if v["total"] >= 2}
        if valid_prices:
            for k in valid_prices:
                v = valid_prices[k]
                v["win_rate"] = round(v["wins"] / max(1, v["wins"] + v["losses"]) * 100, 1)
            best_price = max(valid_prices.items(), key=lambda x: x[1]["win_rate"])
            pname, pdata = best_price
            candidates.append({
                "title": f"{pname}\u00a2 is the Sweet Spot",
                "detail": f"{pdata['win_rate']}% win rate in the {pname}\u00a2 range ({pdata['total']} trades, ${pdata['pnl']:.2f} P&L).",
                "trend": "positive" if pdata["pnl"] > 0 else "neutral",
                "action": "Smart sizing already weights these higher-confidence ranges.",
                "priority": pdata["win_rate"] / 10 + 5,
            })

        # 3. Time of day pattern
        time_map = {}
        for t in settled:
            hour = t.get("entry_hour")
            if hour is None:
                continue
            if 6 <= hour < 12:
                period = "Morning"
            elif 12 <= hour < 18:
                period = "Afternoon"
            elif 18 <= hour < 24:
                period = "Evening"
            else:
                period = "Night"
            if period not in time_map:
                time_map[period] = {"wins": 0, "losses": 0, "pnl": 0.0, "total": 0}
            time_map[period]["total"] += 1
            if t["result"] == "win":
                time_map[period]["wins"] += 1
            elif t["result"] == "loss":
                time_map[period]["losses"] += 1
            time_map[period]["pnl"] += t.get("pnl_usd") or 0

        valid_times = {k: v for k, v in time_map.items() if v["total"] >= 2}
        if valid_times:
            for k in valid_times:
                v = valid_times[k]
                v["win_rate"] = round(v["wins"] / max(1, v["wins"] + v["losses"]) * 100, 1)
            best_time = max(valid_times.items(), key=lambda x: x[1]["win_rate"])
            tname, tdata = best_time
            candidates.append({
                "title": f"{tname} Sessions Win Most",
                "detail": f"{tdata['win_rate']}% win rate during {tname.lower()} hours ({tdata['total']} trades, ${tdata['pnl']:.2f} P&L).",
                "trend": "positive" if tdata["pnl"] > 0 else "neutral",
                "action": "Scanner runs 24/7 but edges cluster when more markets are active.",
                "priority": tdata["win_rate"] / 10 + 3,
            })

        # 4. MoonShark performance
        moon_trades = [t for t in _TRADE_JOURNAL if t.get("strategy") == "moonshark"]
        moon_settled = [t for t in moon_trades if t.get("result") is not None]
        moon_wins = sum(1 for t in moon_settled if t["result"] == "win")
        moon_pnl = sum(t.get("pnl_usd", 0) for t in moon_settled)
        if len(moon_trades) > 0:
            if moon_wins > 0:
                candidates.append({
                    "title": f"MoonShark Hit {moon_wins}x",
                    "detail": f"{moon_wins} moonshot wins from {len(moon_settled)} settled bets. Total MoonShark P&L: ${moon_pnl:.2f}.",
                    "trend": "positive",
                    "action": f"Longshots paying off. {len(moon_trades) - len(moon_settled)} still pending.",
                    "priority": 15 if moon_wins > 0 else 5,
                })
            else:
                candidates.append({
                    "title": "MoonShark Hunting",
                    "detail": f"{len(moon_trades)} moonshot bets placed, {len(moon_settled)} settled, 0 hits yet. P&L: ${moon_pnl:.2f}.",
                    "trend": "negative" if moon_pnl < -5 else "neutral",
                    "action": f"{len(moon_trades) - len(moon_settled)} pending \u2014 one big hit can flip MoonShark green.",
                    "priority": 4,
                })

        # 5. Win/loss streak
        recent = sorted(settled, key=lambda t: t.get("entry_time", ""), reverse=True)
        if len(recent) >= 2:
            streak_type = recent[0].get("result")
            streak_count = 0
            for t in recent:
                if t.get("result") == streak_type:
                    streak_count += 1
                else:
                    break
            if streak_count >= 2:
                if streak_type == "win":
                    candidates.append({
                        "title": f"{streak_count}-Trade Win Streak",
                        "detail": f"Last {streak_count} settled trades were winners. Momentum is strong.",
                        "trend": "positive",
                        "action": "Riding the streak \u2014 smart sizing stays disciplined to protect gains.",
                        "priority": streak_count + 8,
                    })
                elif streak_type == "loss":
                    candidates.append({
                        "title": f"{streak_count}-Trade Loss Streak",
                        "detail": f"Last {streak_count} settled trades lost. Variance happens \u2014 expected in high-volume trading.",
                        "trend": "negative",
                        "action": "Category multipliers auto-reduce exposure on losing categories.",
                        "priority": streak_count + 8,
                    })

        # 6. Daily spending efficiency
        pct_used = round(daily_spent / max(0.01, max_daily) * 100, 1)
        trades_today_count = len(BOT_STATE.get("trades_today", []))
        candidates.append({
            "title": f"Budget {pct_used}% Deployed",
            "detail": f"${daily_spent:.2f} of ${max_daily:.2f} daily budget used across {trades_today_count} trades today.",
            "trend": "positive" if 20 < pct_used < 90 else ("negative" if pct_used >= 90 else "neutral"),
            "action": "Near-limit days mean lots of edges found. Low days mean tight markets." if pct_used > 50 else "Plenty of room for afternoon/evening markets.",
            "priority": 6 if pct_used > 10 else 2,
        })

        # 7. Overall win rate trend
        total_wins = sum(1 for t in settled if t["result"] == "win")
        total_losses = sum(1 for t in settled if t["result"] == "loss")
        overall_wr = round(total_wins / max(1, total_wins + total_losses) * 100, 1)
        total_pnl = sum(t.get("pnl_usd", 0) for t in settled)
        candidates.append({
            "title": f"Overall: {overall_wr}% Win Rate",
            "detail": f"{total_wins}W / {total_losses}L with ${total_pnl:.2f} total P&L across {len(settled)} settled trades.",
            "trend": "positive" if overall_wr >= 55 else ("negative" if overall_wr < 45 else "neutral"),
            "action": "Edge holds above 50%. Category learning tunes sizing to amplify winners.",
            "priority": 7,
        })

        # 8. Matching quality / opportunity count
        candidates.append({
            "title": f"{mispriced_count} Live Opportunities",
            "detail": f"Scanner found {mispriced_count} mispriced contracts across {markets_scanned} markets on last sweep.",
            "trend": "positive" if mispriced_count > 5 else ("neutral" if mispriced_count > 0 else "negative"),
            "action": "Cross-platform matching surfaces edges invisible to single-exchange traders.",
            "priority": 3 if mispriced_count > 0 else 1,
        })

        # 9. Portfolio value and $1M progress
        try:
            _bal_path = "/portfolio/balance"
            _bal_hdrs = signed_headers("GET", _bal_path)
            _bal_resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + _bal_path, headers=_bal_hdrs, timeout=3)
            bal = _bal_resp.json().get("balance", 0) / 100 if _bal_resp.ok else 0
            # Estimate total portfolio from settled P&L
            total_pnl_all = sum(t.get("pnl_usd", 0) for t in settled)
            total_val = bal  # cash available
            if bal > 0:
                # $1M progress
                progress_pct = round(bal / 10000, 2)
                candidates.append({
                    "title": f"${bal:.0f} Cash → $1M Goal",
                    "detail": f"Cash available: ${bal:.2f}. Realized P&L so far: ${total_pnl_all:+.2f} across {len(settled)} settled trades.",
                    "trend": "positive" if total_pnl_all > 0 else ("negative" if total_pnl_all < -10 else "neutral"),
                    "action": "Compound gains by reinvesting profits. Every winning trade gets us closer.",
                    "priority": 8,
                })
        except Exception:
            pass

        # 10. Open positions summary
        pending_count = len(pending)
        if pending_count > 0:
            pending_cost = sum(t.get("cost_usd", 0) for t in pending)
            candidates.append({
                "title": f"{pending_count} Bets Awaiting Results",
                "detail": f"${pending_cost:.2f} in {pending_count} unsettled positions. Results incoming as markets close.",
                "trend": "neutral",
                "action": "Most positions settle within 1-7 days. Check the Positions tab for live P&L.",
                "priority": 5,
            })

        # Sort by priority descending, take top 5
        candidates.sort(key=lambda x: x.get("priority", 0), reverse=True)
        for c in candidates:
            c.pop("priority", None)
        insights = candidates[:5]

        result = {"insights": insights, "generated_at": generated_at}
        _insights_cache["data"] = result
        _insights_cache["date"] = cache_date
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e), "insights": [], "generated_at": generated_at})


# ---------------------------------------------------------------------------
# News Feed — top financial headlines from RSS
# ---------------------------------------------------------------------------

_NEWS_FEED_CACHE = {"stories": [], "ts": 0, "date": None}
_NEWS_FEED_TTL = 86400  # 24 hours — refreshes daily at 6am PT

# News impact analysis — keyword-based economic impact + stock picks
_NEWS_IMPACT_RULES = [
    # (keywords_any, impact_text, [(ticker, reason), ...])
    (["iran", "war", "military", "strike", "bomb", "attack", "conflict", "missile"],
     "Geopolitical risk spikes oil prices, weighs on equities. Defense spending up, consumer confidence down.",
     [("LMT", "Lockheed Martin — defense spending surges during conflict"),
      ("XLE", "Energy Select ETF — oil prices spike on supply disruption")]),
    (["tariff", "trade war", "import tax", "trade deal", "sanctions"],
     "Trade barriers raise costs for importers, slow global growth. Domestic producers may benefit short-term.",
     [("DBA", "Agriculture ETF — tariffs shift commodity flows"),
      ("WMT", "Walmart — import cost pressure on retail margins")]),
    (["fed ", "interest rate", "rate cut", "rate hike", "federal reserve", "powell", "monetary policy"],
     "Rate changes ripple through mortgages, bonds, and growth stocks. Lower rates boost tech, higher rates favor banks.",
     [("TLT", "20+ Year Treasury ETF — moves inversely to rate expectations"),
      ("XLF", "Financial Select ETF — banks profit from higher rates")]),
    (["oil", "crude", "opec", "petroleum", "gas price", "energy price", "wti", "brent"],
     "Energy price swings affect transportation, manufacturing costs, and consumer spending power.",
     [("XOM", "ExxonMobil — directly benefits from higher oil prices"),
      ("DAL", "Delta Air Lines — fuel costs are major expense, lower oil = higher margins")]),
    (["inflation", "cpi", "consumer price", "cost of living"],
     "Rising inflation erodes purchasing power, pressures Fed to tighten. Benefits hard assets, hurts growth stocks.",
     [("TIP", "TIPS ETF — inflation-protected treasuries outperform"),
      ("COST", "Costco — pricing power and bulk buying hedge inflation")]),
    (["recession", "gdp", "economic slowdown", "contraction", "unemployment"],
     "Recession fears drive flight to safety — bonds, gold, utilities. Cyclical sectors underperform.",
     [("GLD", "Gold ETF — classic safe haven during downturns"),
      ("XLU", "Utilities ETF — defensive sector with stable dividends")]),
    (["tech", "ai ", "artificial intelligence", "nvidia", "openai", "google", "apple", "microsoft", "semiconductor", "chip"],
     "Tech sector moves drive Nasdaq. AI spending boom benefits chipmakers and cloud providers.",
     [("NVDA", "Nvidia — dominant in AI chip market"),
      ("MSFT", "Microsoft — Azure + OpenAI partnership drives cloud/AI revenue")]),
    (["crypto", "bitcoin", "ethereum", "blockchain", "digital currency"],
     "Crypto moves signal risk appetite. Institutional adoption growing but regulatory uncertainty remains.",
     [("COIN", "Coinbase — revenue tied to crypto trading volume"),
      ("MSTR", "MicroStrategy — large Bitcoin holdings amplify BTC moves")]),
    (["china", "beijing", "chinese economy", "yuan", "ccp"],
     "China's economy impacts global supply chains, commodities demand, and emerging market sentiment.",
     [("FXI", "China Large-Cap ETF — direct exposure to Chinese equities"),
      ("CAT", "Caterpillar — infrastructure demand tied to Chinese growth")]),
    (["housing", "mortgage", "real estate", "home price", "home sale"],
     "Housing market affects consumer wealth, bank balance sheets, and construction employment.",
     [("XHB", "Homebuilders ETF — direct housing market exposure"),
      ("LEN", "Lennar — top homebuilder benefits from strong demand")]),
    (["bank", "banking", "credit", "loan", "financial crisis", "bank failure"],
     "Banking stress tightens lending, slows economic growth. Contagion risk can spread across financial system.",
     [("KRE", "Regional Bank ETF — most exposed to credit stress"),
      ("JPM", "JPMorgan — flight to quality benefits largest banks")]),
    (["fertilizer", "agriculture", "farm", "crop", "food price", "grain"],
     "Agricultural supply disruptions raise food prices globally, impacting emerging markets most severely.",
     [("MOS", "Mosaic — major fertilizer producer benefits from shortages"),
      ("ADM", "Archer-Daniels-Midland — food commodity processing and trading")]),
    (["japan", "yen", "nikkei", "boj", "bank of japan"],
     "Japanese monetary policy shifts impact global bond yields and carry trades. Yen strength = risk-off signal.",
     [("EWJ", "Japan ETF — direct Japanese equity exposure"),
      ("FXY", "Yen ETF — benefits from yen strengthening")]),
    (["trump", "white house", "executive order", "president"],
     "Policy shifts create sector winners and losers. Markets price regulatory and trade uncertainty.",
     [("SPY", "S&P 500 ETF — broad market exposure to policy shifts"),
      ("IWM", "Russell 2000 ETF — small caps most sensitive to domestic policy")]),
]


def _analyze_news_impact(title, summary=""):
    """Analyze a news headline for economic impact and suggest stock picks."""
    text = (title + " " + summary).lower()
    for keywords, impact, stocks in _NEWS_IMPACT_RULES:
        if any(kw in text for kw in keywords):
            return impact, stocks
    # Default fallback
    return "Market impact uncertain — monitor for follow-up developments.", [
        ("SPY", "S&P 500 ETF — broad market barometer"),
        ("QQQ", "Nasdaq 100 ETF — tech-heavy growth exposure"),
    ]

def _fetch_news_feed():
    """Fetch top financial news from RSS feeds. Returns list of story dicts."""
    import urllib.request
    import time as _time

    now = _time.time()
    # Daily refresh at 6am PT
    now_pt = datetime.datetime.now(tz=_PACIFIC)
    news_date = now_pt.strftime("%Y-%m-%d") if now_pt.hour >= 6 else (now_pt - datetime.timedelta(days=1)).strftime("%Y-%m-%d")
    cache_fresh = _NEWS_FEED_CACHE["stories"] and _NEWS_FEED_CACHE.get("date") == news_date
    if cache_fresh:
        return _NEWS_FEED_CACHE["stories"]

    feeds = [
        ("https://feeds.marketwatch.com/marketwatch/topstories/", "MarketWatch"),
        ("https://www.cnbc.com/id/100003114/device/rss/rss.html", "CNBC"),
        ("https://finance.yahoo.com/news/rssindex", "Yahoo Finance"),
    ]

    all_stories = []
    for url, source_name in feeds:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=8) as resp:
                raw = resp.read()
            root = ET.fromstring(raw)
            # RSS feeds use <channel><item>
            for item in root.findall(".//item")[:10]:
                title = item.findtext("title", "").strip()
                link = item.findtext("link", "").strip()
                pub = item.findtext("pubDate", "").strip()
                desc = item.findtext("description", "").strip()
                # Clean HTML from description
                desc = re.sub(r"<[^>]+>", "", desc).strip()
                if len(desc) > 200:
                    desc = desc[:197] + "..."
                if title and link:
                    # Parse pubDate into ISO format
                    pub_iso = ""
                    if pub:
                        try:
                            from email.utils import parsedate_to_datetime
                            dt = parsedate_to_datetime(pub)
                            pub_iso = dt.isoformat()
                        except Exception:
                            pub_iso = pub
                    all_stories.append({
                        "title": html_unescape(title),
                        "link": link,
                        "source": source_name,
                        "published": pub_iso,
                        "summary": html_unescape(desc) if desc else "",
                    })
        except Exception:
            continue

    # Sort by published date descending
    def _sort_key(s):
        try:
            return datetime.datetime.fromisoformat(s["published"].replace("Z", "+00:00"))
        except Exception:
            return datetime.datetime.min
    all_stories.sort(key=_sort_key, reverse=True)
    result = all_stories[:10]

    # Enrich each story with economic impact, stock picks, and 3 bullet points
    for story in result:
        impact, stocks = _analyze_news_impact(story["title"], story.get("summary", ""))
        story["economic_impact"] = impact
        story["stock_picks"] = stocks

        # Match to keyword rules for rich analysis
        text = (story["title"] + " " + story.get("summary", "")).lower()
        matched_rule = None
        for rule in _NEWS_KEYWORD_RULES:
            if any(kw in text for kw in rule["keywords"]):
                matched_rule = rule
                break

        if matched_rule:
            story["category"] = matched_rule["category"]
            story["color"] = matched_rule.get("color", "#888")
            story["sentiment"] = matched_rule.get("sentiment", "neutral")
            # 3 bullet points
            story["plain_english"] = story.get("summary", "") or story["title"]
            story["market_impact"] = matched_rule["market_take"]
            story["trade_idea"] = matched_rule["profit_angle"]
        else:
            story["category"] = "general"
            story["color"] = "#888"
            story["sentiment"] = "neutral"
            story["plain_english"] = story.get("summary", "") or story["title"]
            story["market_impact"] = impact
            story["trade_idea"] = "Monitor for developments — look for prediction markets related to this story."
        # Add stock ticker suggestions as trade ideas
        if stocks:
            stock_str = ", ".join([f"{s[0]} ({s[1]})" for s in stocks[:3]])
            story["trade_idea"] += f" Tickers to watch: {stock_str}"

    _NEWS_FEED_CACHE["stories"] = result
    _NEWS_FEED_CACHE["ts"] = now
    _NEWS_FEED_CACHE["date"] = news_date
    return result


@app.route("/news")
def news_endpoint():
    """Return top 10 financial news stories from RSS feeds."""
    try:
        stories = _fetch_news_feed()
        if not stories:
            return jsonify({"stories": [], "error": "News temporarily unavailable — RSS feeds did not respond."})
        return jsonify({"stories": stories, "cached_at": _NEWS_FEED_CACHE["ts"]})
    except Exception as e:
        return jsonify({"stories": [], "error": f"News temporarily unavailable: {str(e)}"})


@app.route("/news/refresh")
def news_refresh():
    """Force refresh news feed cache."""
    _NEWS_FEED_CACHE["stories"] = []
    _NEWS_FEED_CACHE["ts"] = 0
    try:
        stories = _fetch_news_feed()
        return jsonify({"stories": stories, "cached_at": _NEWS_FEED_CACHE["ts"]})
    except Exception as e:
        return jsonify({"stories": [], "error": str(e)})


# ---------------------------------------------------------------------------
# News Ideas — market analysis from top global headlines
# ---------------------------------------------------------------------------
_NEWS_IDEAS_CACHE = {"ideas": [], "ts": 0, "date": None}
_NEWS_IDEAS_TTL = 86400  # 24 hours — refreshes daily at 6am PT

_NEWS_KEYWORD_RULES = [
    {
        "category": "interest-rates",
        "keywords": ["interest rate", "fed ", "federal reserve", "central bank", "rate hike", "rate cut", "monetary policy", "fomc", "powell", "basis point", "bps"],
        "market_take": "Rate changes directly impact bond prices, bank stocks, and borrowing costs across the economy. Central bank signals move markets before any official decision is made.",
        "profit_angle": "Look for prediction markets on Fed rate decisions and bet on the direction implied by today's rhetoric.",
        "sentiment": "neutral",
        "color": "#5b8def",
    },
    {
        "category": "geopolitics",
        "keywords": ["war ", "conflict", "military", "troops", "invasion", "missile", "nato", "geopolit", "tensions", "sanction", "nuclear", "attack", "ceasefire", "peace deal"],
        "market_take": "Geopolitical instability typically drives oil and gold prices up while equities sell off. Defense sector stocks and safe-haven assets tend to outperform during escalation.",
        "profit_angle": "Look for defense sector and commodity prediction markets that haven't priced in escalation yet.",
        "sentiment": "bearish",
        "color": "#ff5000",
    },
    {
        "category": "tech",
        "keywords": ["tech earn", "layoff", "artificial intelligence", " ai ", "openai", "google", "apple", "microsoft", "meta ", "nvidia", "chip", "semiconductor", "nasdaq", "silicon valley"],
        "market_take": "Tech sector movements create volatility in NASDAQ and ripple through growth stocks. Earnings beats or misses can shift sentiment across the entire sector.",
        "profit_angle": "Watch for prediction markets on tech company earnings and stock price targets that lag behind breaking news.",
        "sentiment": "neutral",
        "color": "#7b2ff7",
    },
    {
        "category": "trade-policy",
        "keywords": ["tariff", "trade war", "trade deal", "import duty", "export ban", "trade restrict", "wto ", "trade deficit", "customs", "trade agreement"],
        "market_take": "Trade restrictions impact import-dependent companies and currencies. Tariff announcements create immediate repricing in affected sectors and trading partners' markets.",
        "profit_angle": "Look for prediction markets on trade policy outcomes — they often misprice speed of implementation.",
        "sentiment": "bearish",
        "color": "#ff8c00",
    },
    {
        "category": "energy",
        "keywords": ["oil ", "crude", "opec", "energy", "natural gas", "petroleum", "fuel", "gasoline", "pipeline", "drilling", "refiner"],
        "market_take": "Energy price shifts ripple through transportation, manufacturing, and consumer spending. OPEC decisions can move oil 5-10% in a single session.",
        "profit_angle": "Watch commodity prediction markets for oil price targets — they lag behind supply-side news.",
        "sentiment": "neutral",
        "color": "#e6a800",
    },
    {
        "category": "housing",
        "keywords": ["housing", "real estate", "mortgage", "home sale", "home price", "rent ", "rental", "property", "foreclosure", "housing start"],
        "market_take": "Housing data signals consumer confidence and bank exposure to mortgage risk. Weakening housing often precedes broader economic slowdowns.",
        "profit_angle": "Watch for markets on economic indicators — housing weakness often leads Fed to cut rates.",
        "sentiment": "neutral",
        "color": "#20b2aa",
    },
    {
        "category": "jobs",
        "keywords": ["jobs ", "unemployment", "labor", "nonfarm", "payroll", "hiring", "workforce", "wage", "employment", "jobless", "layoff"],
        "market_take": "Employment data is a key Fed input. Strong jobs support rate holds, while weak jobs push toward rate cuts — both moves create tradable opportunities.",
        "profit_angle": "Watch Fed decision markets — jobs data shifts rate-cut probabilities within minutes.",
        "sentiment": "neutral",
        "color": "#4682b4",
    },
    {
        "category": "crypto",
        "keywords": ["crypto", "bitcoin", "btc ", "ethereum", "eth ", "blockchain", "stablecoin", "defi", "token", "binance", "coinbase", "sec crypto"],
        "market_take": "Crypto volatility creates prediction market opportunities across price targets, regulatory outcomes, and adoption milestones.",
        "profit_angle": "Look for token price and regulatory outcome markets on Kalshi and Polymarket — crypto news moves fast.",
        "sentiment": "neutral",
        "color": "#f7931a",
    },
    {
        "category": "politics",
        "keywords": ["election", "poll ", "ballot", "vote ", "campaign", "congress", "senate", "democrat", "republican", "president", "governor", "political", "legislation", "bill pass"],
        "market_take": "Political shifts impact regulation, taxes, and trade policy. Markets price in policy changes before they happen, creating edge for fast movers.",
        "profit_angle": "Prediction markets on election outcomes can be highly profitable — political news creates mispricing windows.",
        "sentiment": "neutral",
        "color": "#dc143c",
    },
    {
        "category": "healthcare",
        "keywords": ["pharma", "fda ", "drug approv", "biotech", "vaccine", "clinical trial", "health care", "healthcare", "hospital", "medical", "therapeut"],
        "market_take": "Drug approvals and health policy changes move biotech stocks sharply. FDA decisions are binary events with outsized impact.",
        "profit_angle": "Watch FDA decision prediction markets — approval/rejection outcomes create massive volatility.",
        "sentiment": "neutral",
        "color": "#00c9a7",
    },
    {
        "category": "climate",
        "keywords": ["climate", "hurricane", "flood", "wildfire", "drought", "earthquake", "storm", "tornado", "natural disaster", "extreme weather", "emissions"],
        "market_take": "Extreme weather impacts agriculture, insurance, and energy sectors. Natural disasters can disrupt supply chains and spike commodity prices.",
        "profit_angle": "Look for weather prediction markets on Kalshi — disaster impacts are often underpriced early.",
        "sentiment": "bearish",
        "color": "#2e8b57",
    },
]


def _classify_headline(title):
    """Match a headline to a category and return market analysis."""
    title_lower = title.lower()
    for rule in _NEWS_KEYWORD_RULES:
        for kw in rule["keywords"]:
            if kw in title_lower:
                return rule
    # Default/general
    return {
        "category": "general",
        "market_take": "Major news events create market volatility and shift trader sentiment. Watch for related prediction markets that may be mispriced as the crowd reacts.",
        "profit_angle": "Monitor prediction markets in related sectors — breaking news creates brief mispricing windows before odds adjust.",
        "sentiment": "neutral",
        "color": "#888",
    }


def _fetch_news_ideas():
    """Fetch global news from multiple RSS feeds and generate market analysis."""
    import urllib.request
    import time as _time

    now = _time.time()
    if _NEWS_IDEAS_CACHE["ideas"] and (now - _NEWS_IDEAS_CACHE["ts"]) < _NEWS_IDEAS_TTL:
        return _NEWS_IDEAS_CACHE["ideas"]

    feeds = [
        # Financial feeds (reuse existing)
        ("https://feeds.marketwatch.com/marketwatch/topstories/", "MarketWatch"),
        ("https://www.cnbc.com/id/100003114/device/rss/rss.html", "CNBC"),
        ("https://finance.yahoo.com/news/rssindex", "Yahoo Finance"),
        # Global news feeds
        ("https://feeds.reuters.com/reuters/topNews", "Reuters"),
        ("https://feeds.bbci.co.uk/news/world/rss.xml", "BBC World"),
        ("https://rsshub.app/apnews/topics/apf-topnews", "AP News"),
    ]

    all_stories = []
    for url, source_name in feeds:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=8) as resp:
                raw = resp.read()
            root = ET.fromstring(raw)
            for item in root.findall(".//item")[:8]:
                title = item.findtext("title", "").strip()
                link = item.findtext("link", "").strip()
                pub = item.findtext("pubDate", "").strip()
                if title and link:
                    pub_iso = ""
                    if pub:
                        try:
                            from email.utils import parsedate_to_datetime
                            dt = parsedate_to_datetime(pub)
                            pub_iso = dt.isoformat()
                        except Exception:
                            pub_iso = pub
                    all_stories.append({
                        "headline": html_unescape(title),
                        "link": link,
                        "source": source_name,
                        "published": pub_iso,
                    })
        except Exception:
            continue

    # Sort by published date descending
    def _sort_key(s):
        try:
            return datetime.datetime.fromisoformat(s["published"].replace("Z", "+00:00"))
        except Exception:
            return datetime.datetime.min
    all_stories.sort(key=_sort_key, reverse=True)

    # Deduplicate by similar headlines
    seen_titles = []
    unique_stories = []
    for s in all_stories:
        dupe = False
        for seen in seen_titles:
            if SequenceMatcher(None, s["headline"].lower(), seen).ratio() > 0.6:
                dupe = True
                break
        if not dupe:
            seen_titles.append(s["headline"].lower())
            unique_stories.append(s)

    # Take top 10 and classify
    ideas = []
    for s in unique_stories[:10]:
        rule = _classify_headline(s["headline"])
        ideas.append({
            "headline": s["headline"],
            "source": s["source"],
            "link": s["link"],
            "published": s["published"],
            "category": rule["category"],
            "market_take": rule["market_take"],
            "profit_angle": rule["profit_angle"],
            "sentiment": rule.get("sentiment", "neutral"),
            "color": rule.get("color", "#888"),
        })

    _NEWS_IDEAS_CACHE["ideas"] = ideas
    _NEWS_IDEAS_CACHE["ts"] = now
    return ideas


@app.route("/news-ideas")
def news_ideas_endpoint():
    """Return top 10 global news stories with market analysis."""
    try:
        ideas = _fetch_news_ideas()
        if not ideas:
            return jsonify({"ideas": [], "error": "News ideas temporarily unavailable."})
        return jsonify({"ideas": ideas, "cached_at": _NEWS_IDEAS_CACHE["ts"]})
    except Exception as e:
        return jsonify({"ideas": [], "error": f"News ideas unavailable: {str(e)}"})


@app.route("/news-ideas/refresh")
def news_ideas_refresh():
    """Force refresh news ideas cache."""
    _NEWS_IDEAS_CACHE["ideas"] = []
    _NEWS_IDEAS_CACHE["ts"] = 0
    try:
        ideas = _fetch_news_ideas()
        return jsonify({"ideas": ideas, "cached_at": _NEWS_IDEAS_CACHE["ts"]})
    except Exception as e:
        return jsonify({"ideas": [], "error": str(e)})


_PORTFOLIO_CACHE = {"data": None, "ts": 0}
_PORTFOLIO_CACHE_TTL = 15  # seconds — serve cached data between refreshes

@app.route("/portfolio-summary")
def portfolio_summary():
    """Return cached portfolio data. Background loop keeps it fresh."""
    if _PORTFOLIO_CACHE["data"]:
        return jsonify(_PORTFOLIO_CACHE["data"])
    # No cache yet — return empty shell so frontend shows zeros instead of spinning
    return jsonify({
        "balance_usd": 0, "portfolio_value_usd": 0, "positions_value_usd": 0,
        "open_positions": [], "open_count": 0, "total_invested_usd": 0,
        "total_unrealized_usd": 0, "wins": 0, "losses": 0, "breakeven": 0,
        "win_rate": 0, "win_rate_7d": 0, "total_realized_usd": 0, "settled_history": [],
    })


# ---------------------------------------------------------------------------
# Ticker proxy — avoids CORS issues fetching stock/crypto prices client-side
# ---------------------------------------------------------------------------

@app.route("/ticker-prices")
def ticker_prices():
    """Proxy for CoinGecko + Yahoo Finance quotes."""
    import requests as _req
    result = {}
    # Crypto — try CoinGecko first, fallback to Coinbase
    try:
        cg = _req.get(
            "https://api.coingecko.com/api/v3/simple/price",
            params={"ids": "bitcoin,ethereum", "vs_currencies": "usd", "include_24hr_change": "true"},
            timeout=5,
        ).json()
        result["btc"] = {"price": cg["bitcoin"]["usd"], "change": cg["bitcoin"].get("usd_24h_change")}
        result["eth"] = {"price": cg["ethereum"]["usd"], "change": cg["ethereum"].get("usd_24h_change")}
    except Exception as e:
        print(f"[TICKER] CoinGecko failed: {e}, trying Coinbase fallback")
        # Fallback: Coinbase public API (no auth needed)
        for coin, key in [("BTC", "btc"), ("ETH", "eth")]:
            try:
                cb = _req.get(f"https://api.coinbase.com/v2/prices/{coin}-USD/spot", timeout=5).json()
                price = float(cb["data"]["amount"])
                result[key] = {"price": price, "change": None}
            except Exception:
                pass
    # Stocks via Yahoo v8 chart endpoint (v7 quote requires auth now)
    for sym in ("VOO", "TSLA", "GOOG"):
        try:
            chart = _req.get(
                f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}",
                params={"interval": "1d", "range": "2d"},
                headers={"User-Agent": "Mozilla/5.0"},
                timeout=5,
            ).json()
            meta = chart["chart"]["result"][0]["meta"]
            price = meta.get("regularMarketPrice", 0)
            prev = meta.get("chartPreviousClose", 0)
            chg = ((price - prev) / prev * 100) if prev else 0
            result[sym.lower()] = {"price": price, "change": round(chg, 2)}
        except Exception:
            pass
    return jsonify(result)


# ---------------------------------------------------------------------------
# Bot endpoints (NEW)
# ---------------------------------------------------------------------------

def _count_trades_today():
    """Count unique trades placed today (deduplicated by ticker+side).
    Uses the same logic as /trades-today to ensure both numbers match."""
    seen = set()
    count = 0
    for _tlist in [BOT_STATE.get("snipe_trades_today", []),
                   BOT_STATE.get("moonshark_trades_today", []),
                   BOT_STATE.get("closegame_trades_today", []),
                   BOT_STATE.get("manual_trades_today", [])]:
        for t in _tlist:
            tk = t.get("ticker", "")
            side = t.get("side", "")
            key = (tk, side)
            if key not in seen:
                seen.add(key)
                count += 1
    return count

@app.route("/status")
def status():
    markets = BOT_STATE["last_scan_markets"]
    mispriced = BOT_STATE["last_scan_mispriced"]
    quant = BOT_STATE.get("quant_stats", {})
    return jsonify({
        "bot_enabled": BOT_CONFIG["enabled"],
        "config": BOT_CONFIG,
        "last_scan": BOT_STATE["last_scan"],
        "last_scan_markets": markets,
        "last_scan_mispriced": mispriced,
        "trades_today": _count_trades_today(),
        "daily_spent_usd": BOT_STATE.get("snipe_daily_spent", 0) + BOT_STATE.get("moonshark_daily_spent", 0) + BOT_STATE.get("closegame_daily_spent", 0),
        "total_trades_all_time": len(BOT_STATE["all_trades"]),
        "recent_errors": BOT_STATE["errors"][-5:],
        "scheduler_running": scheduler.running,
        "sniper_trades_today": len(BOT_STATE.get("snipe_trades_today", [])),
        "sniper_daily_spent": BOT_STATE.get("snipe_daily_spent", 0),
        "quant_engine": {
            "strategies_active": quant.get("strategies_active", []),
            "momentum_signals": quant.get("momentum_signals", 0),
            "mean_reversion_signals": quant.get("mean_reversion_signals", 0),
            "news_signals": quant.get("news_signals", 0),
            "mm_positions": len(_market_maker_orders),
            "kelly_avg_size": quant.get("kelly_avg_size", 0),
            "ema_tracked": len(_price_averages),
            "momentum_tracked": len(_price_history),
        },
    })


@app.route("/bot-activity")
def bot_activity():
    return jsonify({
        "activity": BOT_STATE.get("activity_log", [])[-20:],
    })


@app.route("/category-stats")
def category_stats():
    """Category win rate stats for auto-adjustment display."""
    stats = {}
    for cat, data in _CATEGORY_STATS.items():
        total = data["wins"] + data["losses"]
        stats[cat] = {
            "wins": data["wins"],
            "losses": data["losses"],
            "total": total,
            "win_rate": round(data["wins"] / total * 100, 1) if total > 0 else 0,
            "pnl": round(data["pnl"], 2),
            "multiplier": _category_multiplier("", cat),
        }
    return jsonify(stats)


@app.route("/trades-today")
def trades_today_endpoint():
    """Return all trades placed today (sniper + moonshark + closegame + manual).
    NOTE: Excludes BOT_STATE['trades_today'] — that list is hydrated from Kalshi
    fills API and double-counts trades already in the per-strategy lists."""
    sniper_trades = BOT_STATE.get("snipe_trades_today", [])
    quant_trades = BOT_STATE.get("quant_trades", [])
    moonshark_trades = BOT_STATE.get("moonshark_trades_today", [])
    closegame_trades = BOT_STATE.get("closegame_trades_today", [])
    manual_trades = BOT_STATE.get("manual_trades_today", [])
    today_str = datetime.datetime.now(tz=_PACIFIC).strftime("%Y-%m-%d")

    def _is_today_pacific(ts_str):
        """Check if a UTC timestamp string falls on today in Pacific time."""
        if not ts_str or len(ts_str) < 10:
            return False
        try:
            dt = datetime.datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
            pacific_date = dt.astimezone(_PACIFIC).strftime("%Y-%m-%d")
            return pacific_date == today_str
        except Exception:
            return ts_str[:10] == today_str

    all_today = []
    # Helper: extract time from trade (handles both "time" and "timestamp" field names)
    def _get_time(t):
        return t.get("time", "") or t.get("timestamp", "") or ""
    # Helper: extract price (handles both "price" and "price_cents")
    def _get_price(t):
        return t.get("price", 0) or t.get("price_cents", 0)
    # Helper: extract cost (handles both "cost" and "cost_usd")
    def _get_cost(t):
        return t.get("cost", 0) or t.get("cost_usd", 0)

    for t in sniper_trades:
        all_today.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", t.get("question", t.get("ticker", ""))),
            "side": t.get("side", ""),
            "price_cents": _get_price(t),
            "count": t.get("count", 0),
            "cost_usd": round(_get_cost(t), 2),
            "time": _get_time(t),
            "strategy": "sniper",
            "success": True,
            "source": "bot",
            "edge_reasons": t.get("edge_reasons", []),
            "conviction": t.get("conviction", 0),
            "espn_edge": t.get("espn_edge"),
            "potential_profit": t.get("potential_profit", 0),
        })
    for t in quant_trades:
        all_today.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", t.get("question", t.get("ticker", ""))),
            "side": t.get("side", ""),
            "price_cents": _get_price(t),
            "count": t.get("count", 0),
            "cost_usd": round(_get_cost(t), 2),
            "time": _get_time(t),
            "strategy": "quant",
            "success": True,
            "source": "bot",
            "edge_reasons": t.get("edge_reasons", []),
            "conviction": t.get("conviction", 0),
            "espn_edge": t.get("espn_edge"),
            "potential_profit": t.get("potential_profit", 0),
        })

    for t in moonshark_trades:
        all_today.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", t.get("question", t.get("ticker", ""))),
            "side": t.get("side", ""),
            "price_cents": _get_price(t),
            "count": t.get("count", 0),
            "cost_usd": round(_get_cost(t), 2),
            "time": _get_time(t),
            "strategy": "moonshark",
            "success": True,
            "source": "bot",
            "edge_reasons": t.get("edge_reasons", []),
            "conviction": t.get("conviction", 0),
            "espn_edge": t.get("espn_edge"),
            "potential_profit": t.get("potential_profit", 0),
        })
    for t in closegame_trades:
        all_today.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", t.get("question", t.get("ticker", ""))),
            "side": t.get("side", ""),
            "price_cents": _get_price(t),
            "count": t.get("count", 0),
            "cost_usd": round(_get_cost(t), 2),
            "time": _get_time(t),
            "strategy": "closegame",
            "success": True,
            "source": "bot",
            "edge_reasons": t.get("edge_reasons", []),
            "conviction": t.get("conviction", 0),
            "espn_edge": t.get("espn_edge"),
            "potential_profit": t.get("potential_profit", 0),
        })
    for t in manual_trades:
        all_today.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", t.get("question", t.get("ticker", ""))),
            "side": t.get("side", ""),
            "price_cents": _get_price(t),
            "count": t.get("count", 0),
            "cost_usd": round(_get_cost(t), 2),
            "time": _get_time(t),
            "strategy": t.get("strategy", "manual"),
            "success": True,
            "source": "you",
        })

    # Fallback: also check all_trades for today's entries (survives redeploys via Kalshi hydration)
    seen_tickers = set(t.get("ticker", "") for t in all_today)
    # Build set of tickers the bot ACTUALLY placed (from in-memory daily arrays)
    _bot_placed_tickers = set()
    for _blist in [sniper_trades, moonshark_trades, closegame_trades, quant_trades]:
        for _bt in _blist:
            _bot_placed_tickers.add(_bt.get("ticker", ""))
    for t in BOT_STATE.get("all_trades", []):
        ticker = t.get("ticker", "")
        ts = t.get("timestamp", "")
        if ticker and ticker not in seen_tickers and _is_today_pacific(ts) and t.get("action") != "sell":
            # Only trust bot attribution if the ticker is in an actual bot trade array
            # Hydration infers "moonshark" for all sports tickers, which mislabels manual bets
            actually_bot = ticker in _bot_placed_tickers
            is_manual = t.get("manual") or not actually_bot
            strat = t.get("strategy") or ""
            source = "bot" if actually_bot else "you"
            display_strategy = strat if actually_bot else "manual"
            all_today.append({
                "ticker": ticker,
                "title": t.get("question", t.get("ticker", "")),
                "side": t.get("side", ""),
                "price_cents": t.get("price_cents", 0),
                "count": t.get("count", 0),
                "cost_usd": round(t.get("cost_usd", 0), 2),
                "time": ts,
                "strategy": display_strategy,
                "success": t.get("success", True),
                "source": source,
                "edge_reasons": t.get("edge_reasons", []),
                "conviction": t.get("conviction", 0),
                "espn_edge": t.get("espn_edge"),
                "potential_profit": t.get("potential_profit", 0),
            })
            seen_tickers.add(ticker)

    # Consolidate duplicate fills: group by ticker+side, sum count/cost
    _consolidated = {}
    for t in all_today:
        key = (t.get("ticker", ""), t.get("side", ""))
        if key in _consolidated:
            c = _consolidated[key]
            c["count"] += t.get("count", 0)
            c["cost_usd"] = round(c["cost_usd"] + t.get("cost_usd", 0), 2)
            c["potential_profit"] = round((c.get("potential_profit") or 0) + (t.get("potential_profit") or 0), 2)
            # Keep earliest time
            if t.get("time", "") and (not c.get("time") or t["time"] < c["time"]):
                c["time"] = t["time"]
            # Keep edge_reasons from the entry that has them
            if t.get("edge_reasons") and not c.get("edge_reasons"):
                c["edge_reasons"] = t["edge_reasons"]
                c["conviction"] = t.get("conviction", 0)
                c["espn_edge"] = t.get("espn_edge")
            # Weighted average price
            total_count = c["count"]
            if total_count > 0:
                c["price_cents"] = round(c["cost_usd"] * 100 / total_count)
        else:
            _consolidated[key] = dict(t)
    all_today = list(_consolidated.values())

    # Enrich with close_time and current price
    # 1) Try market cache first (fast, covers open markets)
    market_info = {}
    try:
        for m in _market_cache.get("data") or []:
            tid = m.get("ticker") or m.get("id") or ""
            if tid:
                yp = m.get("yes_ask_cents") or int(round(m.get("yes", 0.5) * 100))
                np = m.get("no_ask_cents") or int(round(m.get("no", 0.5) * 100))
                market_info[tid] = {
                    "close_time": m.get("close_time") or "",
                    "yes_price": yp,
                    "no_price": np,
                }
    except Exception:
        pass
    # 2) For tickers not in cache (live/closed markets), fetch from Kalshi API directly
    missing = [t.get("ticker", "") for t in all_today if t.get("ticker", "") and t.get("ticker", "") not in market_info]
    for ticker in set(missing):
        try:
            path = f"/markets/{ticker}"
            sh = signed_headers("GET", path)
            if sh:
                resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + path, headers=sh, timeout=3)
                if resp.ok:
                    mk = resp.json().get("market", {})
                    yp = int(round(float(mk.get("yes_ask", mk.get("last_price", 0.5))) * 100))
                    np = 100 - yp
                    market_info[ticker] = {
                        "close_time": mk.get("expected_expiration_time") or mk.get("close_time") or "",
                        "yes_price": yp,
                        "no_price": np,
                    }
        except Exception:
            pass
    # Check realized P&L for settled positions
    _settled_pnl = {}
    try:
        _sph = signed_headers("GET", "/portfolio/positions")
        if _sph:
            _spr = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/positions",
                headers=_sph, params={"limit": 200, "settlement_status": "settled"},
                timeout=8,
            )
            if _spr.ok:
                for _sp in _spr.json().get("market_positions", []):
                    _stk = _sp.get("ticker", "")
                    _spnl = _parse_kalshi_dollars(_sp.get("realized_pnl_dollars") or _sp.get("realized_pnl"))
                    if _stk:
                        _settled_pnl[_stk] = _spnl / 100  # in USD
    except Exception:
        pass

    for t in all_today:
        info = market_info.get(t.get("ticker", ""), {})
        t["close_time"] = info.get("close_time", "")
        side = t.get("side", "yes")
        entry = t.get("price_cents", 0)
        current = info.get("yes_price", 0) if side == "yes" else info.get("no_price", 0)
        t["current_price"] = current
        if entry and current:
            t["pnl_pct"] = round((current - entry) / entry * 100, 1)
        else:
            t["pnl_pct"] = 0
        # Add settlement result if available
        ticker = t.get("ticker", "")
        if ticker in _settled_pnl:
            pnl_usd = _settled_pnl[ticker]
            t["result"] = "win" if pnl_usd > 0.005 else ("loss" if pnl_usd < -0.005 else "push")
            t["result_pnl"] = round(pnl_usd, 2)
        else:
            t["result"] = None
            t["result_pnl"] = None

    # Normalize all timestamps to clean UTC format (strip microseconds, ensure Z)
    # Then filter to only trades that are actually TODAY in Pacific time
    filtered = []
    for t in all_today:
        _ts = t.get("time", "")
        if _ts:
            # Strip microseconds: "2026-03-23T17:07:32.123456" → "2026-03-23T17:07:32"
            if "." in _ts:
                _ts = _ts.split(".")[0]
            # Ensure Z suffix
            if not _ts.endswith("Z") and "+" not in _ts:
                _ts += "Z"
            t["time"] = _ts
        # Only keep trades that are actually today in Pacific time
        if _ts and _is_today_pacific(_ts):
            filtered.append(t)
        elif not _ts:
            filtered.append(t)  # keep trades with no timestamp (shouldn't happen)
    all_today = filtered

    # Sort by time descending
    all_today.sort(key=lambda x: x.get("time", ""), reverse=True)
    total_spent = sum(t["cost_usd"] for t in all_today if t["success"])
    return jsonify({"trades": all_today, "count": len(all_today), "total_spent": round(total_spent, 2)})


# ── Live Scores (ESPN) ────────────────────────────────────────────────
_live_scores_cache = {"data": {}, "ts": 0}
_LIVE_SCORES_TTL = 15  # seconds — fast refresh for close-game sniper

_ESPN_ENDPOINTS = {
    "nba": "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard",
    "mlb": "https://site.api.espn.com/apis/site/v2/sports/baseball/mlb/scoreboard",
    "nhl": "https://site.api.espn.com/apis/site/v2/sports/hockey/nhl/scoreboard",
    "ncaab": "https://site.api.espn.com/apis/site/v2/sports/basketball/mens-college-basketball/scoreboard",
    "ncaawb": "https://site.api.espn.com/apis/site/v2/sports/basketball/womens-college-basketball/scoreboard",
    "atp": "https://site.api.espn.com/apis/site/v2/sports/tennis/atp/scoreboard",
    "wta": "https://site.api.espn.com/apis/site/v2/sports/tennis/wta/scoreboard",
    "kbo": "https://site.api.espn.com/apis/site/v2/sports/baseball/kbo/scoreboard",
    "mls": "https://site.api.espn.com/apis/site/v2/sports/soccer/usa.1/scoreboard",
    "epl": "https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard",
}

# Common team name aliases: display name → ESPN short name / location variants
_TEAM_ALIASES = {
    # NBA
    "milwaukee": ["mil", "bucks"], "phoenix": ["phx", "suns"], "los angeles": ["la", "lal", "lac"],
    "golden state": ["gs", "gsw", "warriors"], "new york": ["ny", "nyk", "knicks"],
    "san antonio": ["sa", "sas", "spurs"], "oklahoma city": ["okc", "thunder"],
    "portland": ["por", "trail blazers", "blazers"], "minnesota": ["min", "timberwolves", "wolves"],
    "new orleans": ["no", "nop", "pelicans"], "sacramento": ["sac", "kings"],
    "indiana": ["ind", "pacers"], "cleveland": ["cle", "cavaliers", "cavs"],
    "boston": ["bos", "celtics"], "denver": ["den", "nuggets"], "miami": ["mia", "heat"],
    "dallas": ["dal", "mavericks", "mavs"], "memphis": ["mem", "grizzlies"],
    "philadelphia": ["phi", "phl", "76ers", "sixers"], "toronto": ["tor", "raptors"],
    "chicago": ["chi", "bulls"], "atlanta": ["atl", "hawks"], "brooklyn": ["bkn", "nets"],
    "detroit": ["det", "pistons"], "houston": ["hou", "rockets"], "charlotte": ["cha", "hornets"],
    "orlando": ["orl", "magic"], "washington": ["wsh", "was", "wizards"],
    "utah": ["uta", "jazz"], "lakers": ["lal", "la lakers"], "clippers": ["lac", "la clippers"],
    # NHL extras
    "pittsburgh": ["pit", "penguins"], "tampa bay": ["tb", "tbl", "lightning"],
    "colorado": ["col", "avalanche"], "carolina": ["car", "hurricanes"],
    "st. louis": ["stl", "blues"], "st louis": ["stl", "blues"],
    "vegas": ["vgk", "golden knights"], "las vegas": ["vgk", "golden knights"],
    "edmonton": ["edm", "oilers"], "winnipeg": ["wpg", "jets"],
    "vancouver": ["van", "canucks"], "calgary": ["cgy", "flames"],
    "ottawa": ["ott", "senators"], "montreal": ["mtl", "canadiens"],
    "seattle": ["sea", "kraken"], "nashville": ["nsh", "predators"],
    "florida": ["fla", "panthers"], "buffalo": ["buf", "sabres"],
    "columbus": ["cbj", "blue jackets"], "arizona": ["ari", "coyotes"],
    "anaheim": ["ana", "ducks"], "new jersey": ["nj", "njd", "devils"],
    "ny rangers": ["nyr", "rangers"], "ny islanders": ["nyi", "islanders"],
}


def _fetch_all_espn_scores():
    """Fetch today's scores from all ESPN endpoints. Returns dict of normalized_team_key -> game info."""
    games = {}
    for league, url in _ESPN_ENDPOINTS.items():
        try:
            resp = requests.get(url, timeout=5)
            if not resp.ok:
                continue
            data = resp.json()
            for event in data.get("events", []):
                competition = (event.get("competitions") or [{}])[0]
                competitors = competition.get("competitors", [])
                if len(competitors) < 2:
                    continue
                status_obj = competition.get("status") or event.get("status", {})
                status_type = (status_obj.get("type") or {})
                state = status_type.get("state", "")  # pre, in, post
                detail = status_obj.get("type", {}).get("shortDetail", "") or status_obj.get("type", {}).get("detail", "")
                # Get short detail from the status directly
                detail = status_obj.get("displayClock", "")
                period = status_obj.get("period", 0)

                teams = []
                for c in competitors:
                    team_obj = c.get("team", {})
                    teams.append({
                        "abbrev": team_obj.get("abbreviation", "").upper(),
                        "name": team_obj.get("displayName", ""),
                        "short": team_obj.get("shortDisplayName", ""),
                        "location": team_obj.get("location", ""),
                        "score": c.get("score", "0"),
                        "home": c.get("homeAway", "") == "home",
                    })

                if state == "pre":
                    clock_str = "Pregame"
                elif state == "post":
                    clock_str = "Final"
                else:
                    # In-progress
                    if league in ("nba", "ncaab", "ncaawb"):
                        qtr_names = {1: "Q1", 2: "Q2", 3: "Q3", 4: "Q4"}
                        if league == "ncaab":
                            qtr_names = {1: "1H", 2: "2H"}
                        # ncaawb plays quarters (Q1-Q4), same as NBA
                        clock_str = qtr_names.get(period, f"OT{period-4}" if period > 4 else f"Q{period}")
                        if detail:
                            clock_str = f"{detail} {clock_str}"
                    elif league == "nhl":
                        p_names = {1: "P1", 2: "P2", 3: "P3"}
                        clock_str = p_names.get(period, f"OT{period-3}" if period > 3 else f"P{period}")
                        if detail:
                            clock_str = f"{detail} {clock_str}"
                    elif league in ("mlb", "kbo"):
                        half = "Top" if status_obj.get("type", {}).get("shortDetail", "").lower().startswith("top") else "Bot"
                        clock_str = f"{half} {period}"
                    elif league in ("atp", "wta"):
                        # Tennis: use set score from detail
                        short_detail = status_obj.get("type", {}).get("shortDetail", "")
                        clock_str = short_detail or f"Set {period}"
                    elif league in ("mls", "epl"):
                        clock_str = f"{detail}'" if detail else f"{period}'"
                    else:
                        clock_str = detail or f"Period {period}"

                # away team is usually index 1, home index 0 — ESPN uses homeAway field
                away = next((t for t in teams if not t["home"]), teams[1] if len(teams) > 1 else teams[0])
                home = next((t for t in teams if t["home"]), teams[0])

                # Extract sportsbook odds if available
                odds_data = {}
                try:
                    _odds_list = competition.get("odds", [])
                    if _odds_list:
                        _odds = _odds_list[0]  # First provider (usually consensus)
                        _home_ml = _odds.get("homeTeamOdds", {}).get("moneyLine")
                        _away_ml = _odds.get("awayTeamOdds", {}).get("moneyLine")
                        if _home_ml is not None and _away_ml is not None:
                            # Convert moneyline to implied probability
                            def _ml_to_prob(ml):
                                ml = float(ml)
                                if ml > 0:
                                    return 100 / (ml + 100)
                                else:
                                    return abs(ml) / (abs(ml) + 100)
                            odds_data = {
                                "home_ml": int(_home_ml),
                                "away_ml": int(_away_ml),
                                "home_implied": round(_ml_to_prob(_home_ml), 3),
                                "away_implied": round(_ml_to_prob(_away_ml), 3),
                                "provider": _odds.get("provider", {}).get("name", "ESPN"),
                            }
                except Exception:
                    pass

                game_info = {
                    "away_abbrev": away["abbrev"],
                    "home_abbrev": home["abbrev"],
                    "away_score": away["score"],
                    "home_score": home["score"],
                    "away_name": away["name"],
                    "home_name": home["name"],
                    "away_location": away["location"],
                    "home_location": home["location"],
                    "away_short": away["short"],
                    "home_short": home["short"],
                    "clock": clock_str,
                    "state": state,
                    "league": league.upper(),
                    "odds": odds_data,
                }

                # Index by multiple keys for fuzzy matching
                for team in [away, home]:
                    for key in [team["abbrev"].lower(), team["name"].lower(),
                                team["short"].lower(), team["location"].lower()]:
                        if key:
                            games[key] = game_info
        except Exception:
            continue
    return games


def _extract_teams_from_title(title):
    """Extract team names from bet titles like 'Milwaukee at Phoenix Winner?' or 'MIL vs PHX'."""
    if not title:
        return []
    # Clean up title
    title_clean = title.replace("Winner?", "").replace("winner?", "").replace("Winner", "")
    title_clean = title_clean.replace("Over/Under", "").replace("Spread", "").strip()
    # Try "Team at/vs/v Team" pattern
    m = re.match(r'^(.+?)\s+(?:at|vs\.?|v\.?|@)\s+(.+?)(?:\s*[-\(].*)?$', title_clean, re.IGNORECASE)
    if m:
        return [m.group(1).strip().lower(), m.group(2).strip().lower()]
    # Try to find any known team name in the title
    title_lower = title.lower()
    found = []
    for team_name in _TEAM_ALIASES:
        if team_name in title_lower:
            found.append(team_name)
    return found[:2]


def _find_game_for_teams(team_names, scores_map):
    """Try to match extracted team names against the scores map."""
    for name in team_names:
        # Direct match
        if name in scores_map:
            return scores_map[name]
        # Check aliases
        if name in _TEAM_ALIASES:
            for alias in _TEAM_ALIASES[name]:
                if alias in scores_map:
                    return scores_map[alias]
        # Check if any alias maps to this name
        for canonical, aliases in _TEAM_ALIASES.items():
            if name in aliases and canonical in scores_map:
                return scores_map[canonical]
    return None


def _format_score_string(game):
    """Format game info into a display string like 'MIL 45 - PHX 52 Q3'."""
    if not game:
        return ""
    return f"{game['away_abbrev']} {game['away_score']} - {game['home_abbrev']} {game['home_score']} {game['clock']}"


# ---------------------------------------------------------------------------
# BLOWOUT DETECTION — Skip bets where underdog is getting destroyed
# ---------------------------------------------------------------------------

# Blowout thresholds by sport: max point deficit to still bet on the underdog
_BLOWOUT_THRESHOLDS = {
    "nba": 15,     # down by 15+ points
    "ncaab": 15,   # down by 15+ points
    "nhl": 3,      # down by 3+ goals
    "mlb": 4,      # down by 4+ runs
    "soccer": 2,   # down by 2+ goals (soccer is low-scoring)
}

# Late-game thresholds: stricter when game is almost over
_LATE_GAME_THRESHOLDS = {
    "nba": {"period": 4, "max_deficit": 8},      # Q4, down 8+
    "ncaab": {"period": 2, "max_deficit": 10},    # 2nd half, down 10+
    "nhl": {"period": 3, "max_deficit": 2},       # P3, down 2+
    "mlb": {"period": 7, "max_deficit": 3},       # 7th inning+, down 3+
}


def _check_blowout(ticker, title, bet_team_abbrev=None):
    """Check if the game is a blowout. Returns (is_blowout, reason, game_info).

    bet_team_abbrev: the team abbreviation we're betting ON (from ticker suffix).
    If the team we're betting on is getting crushed, skip.
    If the game is close or our team is winning, it's fine.
    """
    try:
        # Detect sport from ticker
        tk_upper = ticker.upper()
        sport = None
        if "NBA" in tk_upper or "NCAA" in tk_upper:
            sport = "ncaab" if "NCAA" in tk_upper else "nba"
        elif "NHL" in tk_upper:
            sport = "nhl"
        elif "MLB" in tk_upper:
            sport = "mlb"
        elif "SOCCER" in tk_upper or "EPL" in tk_upper or "MLS" in tk_upper:
            sport = "soccer"
        else:
            return False, "", None  # Can't check — allow the bet

        # Fetch live scores
        now = _time.time()
        if now - _live_scores_cache["ts"] > _LIVE_SCORES_TTL or not _live_scores_cache["data"]:
            _live_scores_cache["data"] = _fetch_all_espn_scores()
            _live_scores_cache["ts"] = now

        scores = _live_scores_cache["data"]
        if not scores:
            return False, "", None  # No scores available — allow the bet

        # Find the game
        team_names = _extract_teams_from_title(title)
        game = _find_game_for_teams(team_names, scores)
        if not game:
            # Try extracting from ticker suffix (e.g., KXNCAAMBGAME-26MAR22TENNUVA-UVA)
            parts = ticker.split("-")
            if len(parts) >= 2:
                suffix_team = parts[-1].lower()
                if suffix_team in scores:
                    game = scores[suffix_team]
            if not game:
                return False, "", None  # Can't find game — allow the bet

        # Game hasn't started yet — no blowout possible
        if game["state"] == "pre":
            return False, "pregame", game

        # Game is over — don't bet on finished games
        if game["state"] == "post":
            return True, "game over", game

        # Parse scores
        away_score = int(game.get("away_score", 0) or 0)
        home_score = int(game.get("home_score", 0) or 0)

        # Figure out which team we're betting on
        our_score = None
        their_score = None
        if bet_team_abbrev:
            bet_abbrev_upper = bet_team_abbrev.upper()
            if game["away_abbrev"] == bet_abbrev_upper:
                our_score = away_score
                their_score = home_score
            elif game["home_abbrev"] == bet_abbrev_upper:
                our_score = home_score
                their_score = away_score

        if our_score is not None and their_score is not None:
            deficit = their_score - our_score  # positive = we're losing

            # Check standard blowout
            threshold = _BLOWOUT_THRESHOLDS.get(sport, 15)
            if deficit >= threshold:
                score_str = _format_score_string(game)
                return True, f"blowout (down {deficit}, threshold {threshold}) {score_str}", game

            # Check late-game threshold (stricter)
            late = _LATE_GAME_THRESHOLDS.get(sport)
            if late:
                period = 0
                try:
                    # Extract period from clock string
                    clock = game.get("clock", "")
                    for p_match in re.findall(r'Q(\d)|P(\d)|OT|(\d+)(?:st|nd|rd|th)', clock):
                        for g in p_match:
                            if g:
                                period = int(g)
                                break
                        if period:
                            break
                except Exception:
                    pass
                if period >= late["period"] and deficit >= late["max_deficit"]:
                    score_str = _format_score_string(game)
                    return True, f"late-game deficit (period {period}, down {deficit}) {score_str}", game

            # Close game or we're winning — boost confidence
            if deficit <= 0:
                return False, f"winning/tied ({_format_score_string(game)})", game

        # Default: allow the bet
        return False, "", game

    except Exception as e:
        print(f"[BLOWOUT] Error checking {ticker}: {e}")
        return False, "", None  # Error — allow the bet


# ── Live Game Monitor ────────────────────────────────────────────────
_game_score_tracker = {}  # {ticker: {"last_score": "MIL 45 - PHX 52", "last_state": "in", "alerts": []}}

# ── Price Movement Tracker ────────────────────────────────────────────
_price_history = {}  # {ticker: [(timestamp, yes_price), ...]} — last 10 readings

def _track_prices():
    """Track Kalshi price movements for game markets. Detect sharp moves."""
    try:
        # Get markets from cache
        markets = _market_cache.get("data") or []
        if not markets:
            return
        now = _time.time()
        alerts = []
        for m in markets:
            ticker = m.get("ticker") or m.get("id") or ""
            if not ticker:
                continue
            # Only track game markets
            t_upper = ticker.upper()
            if not any(kw in t_upper for kw in ["GAME", "MATCH", "FIGHT"]):
                continue

            yes_price = 0
            try:
                ya = m.get("yes_ask_cents") or m.get("yes_ask") or m.get("yes", 0)
                if isinstance(ya, float) and ya < 1:
                    yes_price = int(round(ya * 100))
                else:
                    yes_price = int(ya)
            except Exception:
                continue

            if yes_price <= 0 or yes_price >= 100:
                continue

            # Add to history
            if ticker not in _price_history:
                _price_history[ticker] = []
            history = _price_history[ticker]
            history.append((now, yes_price))
            # Keep last 10 readings (~10 minutes at 60s intervals)
            _price_history[ticker] = history[-10:]

            # Need at least 3 readings to detect movement
            if len(history) < 3:
                continue

            # Check price change over last 5 minutes
            old_readings = [p for t, p in history if now - t >= 180]  # 3+ min ago
            if not old_readings:
                continue
            old_price = old_readings[0]
            price_change = yes_price - old_price

            # Alert on significant moves (10c+ in either direction)
            if abs(price_change) >= 10:
                title = m.get("title", ticker)[:40]
                direction = "📈" if price_change > 0 else "📉"
                _log_activity(
                    f"{direction} PRICE MOVE: {title} — {old_price}c → {yes_price}c ({price_change:+d}c in {len(history)} readings)",
                    "info"
                )
                alerts.append({"ticker": ticker, "change": price_change, "price": yes_price})

        # Cleanup old tickers (>1 hour stale)
        stale = [t for t, h in _price_history.items() if h and now - h[-1][0] > 3600]
        for t in stale:
            del _price_history[t]

        return alerts
    except Exception as e:
        print(f"[PRICE_TRACK] Error: {e}")
        return []


# ── Historical Win Rate Model ─────────────────────────────────────────
# Based on real sports data: probability of trailing team winning given margin and game phase
_WIN_PROB_MODEL = {
    # NBA: (max_deficit, period_keywords) -> win_probability
    "nba": [
        # Q4 comebacks
        (3, ["Q4", "4th"], 0.42),     # Down 1-3 in Q4: 42%
        (5, ["Q4", "4th"], 0.33),     # Down 4-5 in Q4: 33%
        (8, ["Q4", "4th"], 0.22),     # Down 6-8 in Q4: 22%
        (12, ["Q4", "4th"], 0.12),    # Down 9-12 in Q4: 12%
        (3, ["Q3", "3rd"], 0.48),     # Down 1-3 in Q3: 48%
        (8, ["Q3", "3rd"], 0.35),     # Down 4-8 in Q3: 35%
        (15, ["Q3", "3rd"], 0.20),    # Down 9-15 in Q3: 20%
        (3, ["OT"], 0.45),            # Down 1-3 in OT: 45%
    ],
    "ncaab": [
        (3, ["2H", "2nd"], 0.44),     # Down 1-3 in 2H: 44%
        (5, ["2H", "2nd"], 0.36),     # Down 4-5 in 2H: 36%
        (8, ["2H", "2nd"], 0.25),     # Down 6-8 in 2H: 25%
        (12, ["2H", "2nd"], 0.15),    # Down 9-12 in 2H: 15%
        (3, ["OT"], 0.45),
    ],
    "ncaawb": [
        (3, ["2H", "2nd"], 0.44),
        (5, ["2H", "2nd"], 0.36),
        (8, ["2H", "2nd"], 0.25),
    ],
    "nhl": [
        (1, ["P3", "3rd"], 0.28),     # Down 1 in P3: 28%
        (2, ["P3", "3rd"], 0.12),     # Down 2 in P3: 12%
        (1, ["OT"], 0.50),            # OT is 50/50
    ],
    "mlb": [
        (1, [], 0.35),                # Down 1 late: 35%
        (2, [], 0.22),                # Down 2 late: 22%
        (3, [], 0.14),                # Down 3 late: 14%
    ],
    "kbo": [
        (1, [], 0.33),
        (2, [], 0.20),
        (3, [], 0.12),
    ],
    "atp": [
        (1, [], 0.40),                # Down 1 set: 40%
    ],
    "wta": [
        (1, [], 0.42),                # WTA more volatile: 42%
    ],
    "mls": [
        (1, [], 0.25),                # Down 1 goal in 60th+: 25%
    ],
    "epl": [
        (1, [], 0.22),                # EPL tighter: 22%
    ],
}

def _lookup_win_prob(sport, deficit, period):
    """Look up estimated win probability for trailing team."""
    model = _WIN_PROB_MODEL.get(sport, [])
    best_prob = 0.15  # default fallback

    for max_def, period_kws, prob in model:
        if deficit <= max_def:
            if not period_kws:
                # No period requirement (baseball, tennis, soccer)
                best_prob = max(best_prob, prob)
            elif any(kw in period for kw in period_kws):
                best_prob = max(best_prob, prob)

    return best_prob


def _check_arbitrage():
    """Find markets where YES + NO < 100c (guaranteed profit).
    Buy both sides, guaranteed payout of $1, cost less than $1."""
    if not BOT_CONFIG.get("enabled"):
        return []

    markets = _market_cache.get("data") or []
    if not markets:
        return []

    arbs = []
    for m in markets:
        ticker = m.get("ticker") or m.get("id") or ""
        if not ticker:
            continue

        yes_ask = 0
        no_ask = 0
        try:
            ya = m.get("yes_ask_cents") or m.get("yes_ask") or 0
            na = m.get("no_ask_cents") or m.get("no_ask") or 0
            if isinstance(ya, float) and ya < 1:
                yes_ask = int(round(ya * 100))
            else:
                yes_ask = int(ya)
            if isinstance(na, float) and na < 1:
                no_ask = int(round(na * 100))
            else:
                no_ask = int(na)
        except Exception:
            continue

        if yes_ask <= 0 or no_ask <= 0:
            continue

        total = yes_ask + no_ask
        if total < 98:  # At least 2c profit guaranteed
            gap = 100 - total
            title = m.get("title", ticker)[:40]
            _log_activity(
                f"💰 ARBITRAGE: {title} — YES {yes_ask}c + NO {no_ask}c = {total}c (gap={gap}c FREE)",
                "success"
            )
            # Buy both sides
            max_contracts = min(50, int(BOT_CONFIG.get("max_bet_usd", 5) * 100 / total))
            if max_contracts > 0:
                try:
                    res_yes = place_kalshi_order(ticker, "yes", yes_ask, count=max_contracts)
                    res_no = place_kalshi_order(ticker, "no", no_ask, count=max_contracts)
                    yes_filled = int(float(str(res_yes.get("order", {}).get("filled_count_fp") or 0)))
                    no_filled = int(float(str(res_no.get("order", {}).get("filled_count_fp") or 0)))
                    filled = min(yes_filled, no_filled)
                    if filled > 0:
                        cost = (yes_ask + no_ask) * filled / 100.0
                        profit = gap * filled / 100.0
                        _log_activity(
                            f"💰 ARB HIT! {ticker} x{filled} — cost ${cost:.2f}, guaranteed profit ${profit:.2f}",
                            "success"
                        )
                        arbs.append({"ticker": ticker, "filled": filled, "profit": profit})
                except Exception as e:
                    print(f"[ARB] Order error: {e}")

    return arbs


def _blowout_exit():
    """Sell positions where our team is getting destroyed to salvage capital.
    Only sells game positions where deficit is severe in late game.
    Better to get 2-3c back than ride to guaranteed $0."""
    if not BOT_CONFIG.get("enabled"):
        return
    if not BOT_CONFIG.get("blowout_exit_enabled", True):
        return

    try:
        positions = check_position_prices()
    except Exception:
        return

    # Filter to game positions only
    game_positions = [p for p in positions if any(x in (p.get("ticker") or "").upper() for x in ["GAME", "MATCH", "FIGHT"])]
    if not game_positions:
        return

    scores = _fetch_all_espn_scores()
    if not scores:
        return

    for pos in game_positions:
        ticker = pos.get("ticker", "")
        title = pos.get("title", ticker)
        side = pos.get("side", "yes")
        count = pos.get("count", 0)
        current_price = pos.get("current_price", 0)

        if count <= 0:
            continue

        # Only consider selling if price has dropped significantly (under 8c)
        if current_price > 8:
            continue

        # Find the game score
        teams = _extract_teams_from_title(title)
        game = _find_game_for_teams(teams, scores)
        if not game:
            continue

        state = game.get("state", "")
        if state != "in":
            continue  # only sell during live games, not pre-game

        home_score = int(game.get("home_score", 0))
        away_score = int(game.get("away_score", 0))
        bet_team = ticker.split("-")[-1].upper() if "-" in ticker else ""

        our_score = home_score if game.get("home_abbrev", "").upper() == bet_team else away_score
        their_score = away_score if game.get("home_abbrev", "").upper() == bet_team else home_score
        deficit = their_score - our_score
        period = game.get("clock", "")

        # Define blowout thresholds by sport (more aggressive than buy filter)
        is_hopeless = False
        sport = ""
        for s in ["nba", "ncaab", "nhl", "mlb"]:
            if s in title.lower() or s in ticker.lower():
                sport = s
                break

        if "NBA" in ticker.upper() or "NBAGAME" in ticker.upper():
            # NBA: down 20+ in Q3/Q4, or down 15+ in Q4
            if deficit >= 20 and any(p in period for p in ["Q3", "Q4", "3rd", "4th"]):
                is_hopeless = True
            elif deficit >= 15 and any(p in period for p in ["Q4", "4th", "OT"]):
                is_hopeless = True
        elif "NCAA" in ticker.upper():
            # College BB: down 18+ in 2H, or down 12+ with <5 min
            if deficit >= 18 and any(p in period for p in ["2H", "2nd"]):
                is_hopeless = True
            elif deficit >= 12 and any(p in period for p in ["2H", "2nd"]):
                # Check if late in half (rough estimate)
                is_hopeless = True
        elif "NHL" in ticker.upper():
            # Hockey: down 4+ in P3
            if deficit >= 4 and any(p in period for p in ["P3", "3rd", "OT"]):
                is_hopeless = True
        elif "MLB" in ticker.upper():
            # Baseball: down 7+ in 7th+
            try:
                inning = int(''.join(c for c in period if c.isdigit()) or "0")
                if deficit >= 7 and inning >= 7:
                    is_hopeless = True
            except Exception:
                pass

        if not is_hopeless:
            continue

        # This position is hopeless — sell to salvage whatever we can
        score_str = _format_score_string(game)
        sell_side = "no" if side == "yes" else "yes"
        # Sell at market (1c) to guarantee exit
        sell_price = max(1, current_price - 1)

        _log_activity(
            f"💀 BLOWOUT EXIT: Selling {ticker} — down {deficit} in {period} | {score_str} | salvaging {count} contracts @ ~{current_price}c",
            "warning"
        )

        try:
            result = place_kalshi_order(ticker, side, sell_price, count=count, action="sell")
            if "error" not in result:
                order_data = result.get("order", {})
                filled = 0
                try:
                    filled = int(float(str(order_data.get("filled_count_fp") or order_data.get("filled_count") or 0)))
                except Exception:
                    pass
                if filled > 0:
                    salvaged = (sell_price * filled) / 100.0
                    _log_activity(
                        f"💀 BLOWOUT EXIT DONE: Sold {filled}x {ticker} — salvaged ${salvaged:.2f}",
                        "info"
                    )
                    _save_state()
        except Exception as e:
            print(f"[BLOWOUT_EXIT] Sell error: {e}")


def _monitor_live_games():
    """Monitor live scores for active game positions. Log momentum shifts."""
    try:
        positions = check_position_prices()
    except Exception:
        return
    # Filter to game positions only
    game_positions = [p for p in positions if any(x in (p.get("ticker") or "").upper() for x in ["GAME", "MATCH", "FIGHT"])]
    if not game_positions:
        return

    scores = _fetch_all_espn_scores()
    if not scores:
        return

    for pos in game_positions:
        ticker = pos.get("ticker", "")
        title = pos.get("title", ticker)
        bet_team = ticker.split("-")[-1].upper() if "-" in ticker else ""

        # Find the game
        teams = _extract_teams_from_title(title)
        game = _find_game_for_teams(teams, scores)
        if not game:
            continue

        score_str = _format_score_string(game)
        state = game.get("state", "")

        # Get previous state
        prev = _game_score_tracker.get(ticker, {})
        prev_score = prev.get("last_score", "")
        prev_state = prev.get("last_state", "")

        # Detect changes
        if score_str != prev_score and state == "in":
            # Check if our team took the lead or game got close
            home_score = int(game.get("home_score", 0))
            away_score = int(game.get("away_score", 0))
            our_score = home_score if game.get("home_abbrev", "").upper() == bet_team else away_score
            their_score = away_score if game.get("home_abbrev", "").upper() == bet_team else home_score
            deficit = their_score - our_score

            if prev.get("last_deficit") is not None:
                prev_deficit = prev["last_deficit"]
                # Our team made a run (deficit shrunk by 5+)
                if prev_deficit - deficit >= 5:
                    _log_activity(f"🔥 MOMENTUM: {title[:30]} — {score_str} (was down {prev_deficit}, now {deficit})", "info")
                # Our team took the lead!
                if prev_deficit > 0 and deficit <= 0:
                    _log_activity(f"🚀 LEAD CHANGE: {title[:30]} — {score_str} — our team leads!", "info")
                # Game is now close (within 3 points in Q4)
                if abs(deficit) <= 3 and game.get("clock", "").startswith(("Q4", "P3", "OT", "2H")):
                    _log_activity(f"⚡ CLOSE GAME: {title[:30]} — {score_str}", "info")

            _game_score_tracker[ticker] = {
                "last_score": score_str,
                "last_state": state,
                "last_deficit": deficit,
            }

        # Game just ended
        if state == "post" and prev_state == "in":
            home_score = int(game.get("home_score", 0))
            away_score = int(game.get("away_score", 0))
            our_score = home_score if game.get("home_abbrev", "").upper() == bet_team else away_score
            their_score = away_score if game.get("home_abbrev", "").upper() == bet_team else home_score
            won = our_score > their_score
            _log_activity(
                f"{'🎉 WIN' if won else '❌ LOSS'}: {title[:30]} — Final: {score_str}",
                "info"
            )
            _game_score_tracker[ticker] = {"last_score": score_str, "last_state": state, "last_deficit": 0}


@app.route("/live-scores")
def live_scores_endpoint():
    """Return live scores matched to active bet tickers."""
    now = _time.time()
    if now - _live_scores_cache["ts"] > _LIVE_SCORES_TTL or not _live_scores_cache["data"]:
        try:
            _live_scores_cache["data"] = _fetch_all_espn_scores()
            _live_scores_cache["ts"] = now
        except Exception:
            pass

    scores_map = _live_scores_cache["data"]
    tickers_param = request.args.get("tickers", "")
    titles_param = request.args.get("titles", "")
    tickers = [t.strip() for t in tickers_param.split("|") if t.strip()] if tickers_param else []
    titles = [t.strip() for t in titles_param.split("|") if t.strip()] if titles_param else []

    result = {}
    for i, title in enumerate(titles):
        ticker = tickers[i] if i < len(tickers) else title
        team_names = _extract_teams_from_title(title)
        game = _find_game_for_teams(team_names, scores_map)
        if game:
            result[ticker] = {
                "display": _format_score_string(game),
                "state": game["state"],
                "league": game["league"],
            }

    return jsonify({"scores": result, "game_count": len(scores_map) // 4})


@app.route("/quant-status")
def quant_status():
    """Real-time quant engine dashboard — shows all strategy performance."""
    stats = BOT_STATE.get("quant_stats", {})
    momentum = scan_momentum_opportunities()[:5]
    return jsonify({
        "active_strategies": stats.get("strategies_active", []),
        "ema_tracked": len(_price_averages),
        "momentum_tracked": len(_price_history),
        "mm_orders": len(_market_maker_orders),
        "volatility_tracked": len(_volatility_scores),
        "orderbooks_cached": len(_orderbook_cache),
        "settlements_known": len(_known_settled),
        "strategies": {
            "kelly_criterion": {
                "status": "active",
                "avg_bet_size": stats.get("kelly_avg_size", 0),
                "description": "Half-Kelly sizing — bets scale with bankroll + edge",
            },
            "mean_reversion": {
                "status": "active" if stats.get("mean_reversion_signals", 0) > 0 else "scanning",
                "signals": stats.get("mean_reversion_signals", 0),
                "tracked_tickers": len(_price_averages),
                "description": "Bets against extreme price spikes — reverts to mean",
            },
            "momentum": {
                "status": "active" if stats.get("momentum_signals", 0) > 0 else "scanning",
                "signals": stats.get("momentum_signals", 0),
                "tracked_tickers": len(_price_history),
                "top_movers": momentum,
                "description": "Rides strong price trends",
            },
            "market_making": {
                "status": "active" if _market_maker_orders else "scanning",
                "active_positions": len(_market_maker_orders),
                "fills": stats.get("mm_fills", 0),
                "description": "Captures bid-ask spread on liquid markets",
            },
            "news_sentiment": {
                "status": "active" if stats.get("news_signals", 0) > 0 else "scanning",
                "signals": stats.get("news_signals", 0),
                "description": "Trades on breaking news catalysts",
            },
            "orderbook_depth": {
                "status": "active" if _orderbook_cache else "scanning",
                "cached_books": len(_orderbook_cache),
                "description": "Confirms trades with bid/ask imbalance analysis",
            },
            "correlation_filter": {
                "status": "active",
                "max_per_category": BOT_CONFIG.get("max_category_exposure", 10),
                "description": "Limits category exposure for diversification",
            },
            "volatility_scoring": {
                "status": "active" if _volatility_scores else "scanning",
                "tracked_tickers": len(_volatility_scores),
                "description": "Prioritizes high-movement markets for bigger profits",
            },
            "economic_data": {
                "status": "active" if FRED_API_KEY else "needs_api_key",
                "signals": stats.get("econ_signals", 0),
                "description": "Trades on government data releases (CPI, GDP, jobs)",
            },
            "settlement_reinvest": {
                "status": "active",
                "known_settled": len(_known_settled),
                "description": "Auto-redeploys freed capital when positions settle",
            },
            "live_sniper": {
                "status": "active" if BOT_STATE.get("snipe_trades_today") else "scanning",
                "trades_today": len(BOT_STATE.get("snipe_trades_today", [])),
                "spent_today": BOT_STATE.get("snipe_daily_spent", 0),
                "description": "Buys 93-98c live game positions for guaranteed profit",
            },
            "twitter_sentiment": {
                "status": "active" if _twitter_cache else "scanning",
                "cached_queries": len(_twitter_cache),
                "description": "Scans social media trends for early market signals",
            },
            "parallel_execution": {
                "status": "active",
                "description": "Places multiple orders simultaneously for speed",
            },
        },
    })


@app.route("/orderbook/<ticker>")
def orderbook_view(ticker):
    """View order book depth for a specific market."""
    ob = fetch_orderbook(ticker)
    if not ob:
        return jsonify({"error": "Could not fetch orderbook", "ticker": ticker})
    analysis = analyze_orderbook(ticker)
    return jsonify({
        "ticker": ticker,
        "orderbook": {
            "yes_bids": ob.get("yes_bids", [])[:10],
            "yes_asks": ob.get("yes_asks", [])[:10],
            "spread": ob.get("spread", 0),
            "bid_depth": ob.get("bid_depth", 0),
            "ask_depth": ob.get("ask_depth", 0),
        },
        "analysis": analysis,
    })


@app.route("/category-exposure")
def category_exposure():
    """View current category exposure for correlation management."""
    positions = check_position_prices()
    exposure = get_category_exposure(positions)
    max_per_cat = BOT_CONFIG.get("max_category_exposure", 10)
    return jsonify({
        "exposure": exposure,
        "max_per_category": max_per_cat,
        "total_positions": len(positions),
        "categories_at_limit": [cat for cat, count in exposure.items() if count >= max_per_cat],
    })


@app.route("/volatility")
def volatility_view():
    """View volatility scores for tracked markets."""
    scored = [(t, s["score"]) for t, s in _volatility_scores.items() if s["score"] > 0]
    scored.sort(key=lambda x: x[1], reverse=True)
    return jsonify({
        "tracked": len(_volatility_scores),
        "high_volatility": [{"ticker": t, "score": s} for t, s in scored[:20]],
    })


@app.route("/trades")
def trades():
    # Build settlement lookup from trade journal AND Kalshi positions
    settle_map = {}
    for jt in _TRADE_JOURNAL:
        if jt.get("result"):
            settle_map[jt["ticker"]] = {
                "result": jt["result"],
                "pnl_usd": jt.get("pnl_usd", 0),
            }
    # Also check Kalshi positions for realized P&L (more reliable after restarts)
    try:
        for _status in ["settled", "unsettled"]:
            _ph = signed_headers("GET", "/portfolio/positions")
            if _ph:
                _pr = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/positions",
                    headers=_ph, params={"limit": 200, "settlement_status": _status},
                    timeout=8,
                )
                if _pr.ok:
                    for _pp in _pr.json().get("market_positions", []):
                        _ptk = _pp.get("ticker", "")
                        _ppnl = _parse_kalshi_dollars(_pp.get("realized_pnl_dollars") or _pp.get("realized_pnl"))
                        _ppnl_usd = _ppnl / 100
                        if _ptk and abs(_ppnl_usd) > 0.005 and _ptk not in settle_map:
                            settle_map[_ptk] = {
                                "result": "win" if _ppnl_usd > 0 else "loss",
                                "pnl_usd": round(_ppnl_usd, 2),
                            }
    except Exception:
        pass
    # Build buy/sell P&L from fills: group by ticker, match buys with sells
    _fill_pnl = {}
    _buys = {}
    _sells = {}
    for t in BOT_STATE["all_trades"]:
        tk = t.get("ticker", "")
        action = t.get("action", "buy")
        cost = t.get("cost_usd", 0) or 0
        if action == "sell":
            _sells[tk] = _sells.get(tk, 0) + cost
        else:
            _buys[tk] = _buys.get(tk, 0) + cost
    # If we have both buy and sell for a ticker, calculate P&L
    for tk in _sells:
        if tk in _buys:
            pnl = round(_sells[tk] - _buys[tk], 2)
            _fill_pnl[tk] = {"result": "win" if pnl > 0 else "loss", "pnl_usd": pnl}

    # Enrich all_trades with settlement outcome
    enriched = []
    for t in BOT_STATE["all_trades"]:
        tc = dict(t)
        ticker = tc.get("ticker", "")
        if ticker in settle_map:
            tc["outcome"] = settle_map[ticker]["result"]
            tc["pnl_usd"] = settle_map[ticker]["pnl_usd"]
        elif ticker in _fill_pnl:
            tc["outcome"] = _fill_pnl[ticker]["result"]
            tc["pnl_usd"] = _fill_pnl[ticker]["pnl_usd"]
        else:
            tc["outcome"] = None
        enriched.append(tc)
    # Sort by timestamp descending (most recent first)
    enriched.sort(key=lambda x: x.get("timestamp", ""), reverse=True)
    return jsonify({
        "total": len(enriched),
        "today": len(BOT_STATE["trades_today"]),
        "daily_spent_usd": BOT_STATE["daily_spent_usd"],
        "trades": enriched,
    })


@app.route("/mispriced")
def mispriced():
    all_markets = fetch_all_markets()
    mispricings = find_consensus_mispricings(all_markets)
    return jsonify({
        "total_markets_scanned": len(all_markets),
        "mispriced_count": len(mispricings),
        "mispricings": mispricings,
    })


_picks_cache = {"data": None, "time": None}
_EMPTY_PICKS = {"picks": [], "hero": [], "misc": [], "sports_count": 0, "nonsports_count": 0, "hero_count": 0, "misc_count": 0, "total_scanned": 0, "status": "scanning"}

@app.route("/top-picks")
def top_picks():
    now = datetime.datetime.utcnow()
    # ALWAYS serve cached data instantly — never block the page
    if _picks_cache["data"] is not None:
        return jsonify(_picks_cache["data"])
    # No cache yet — return empty with status so page shows "scanning"
    # Background thread will populate the cache within 30-60 seconds
    return jsonify(_EMPTY_PICKS)


# ---------------------------------------------------------------------------
# 75%'ers — High-probability live betting opportunities
# ---------------------------------------------------------------------------
_sf_cache = {"data": None, "ts": 0}
_SF_CACHE_TTL = 60  # seconds

BOT_STATE["sf_wins"] = 0
BOT_STATE["sf_losses"] = 0
BOT_STATE["sf_streak"] = 0
BOT_STATE["sf_best_streak"] = 0
BOT_STATE["sf_profit"] = 0.0
BOT_STATE["sf_bets"] = 0

# Line movement tracker — detect price drops for buy-the-dip opportunities
_line_history = {}  # ticker -> list of (timestamp, price_cents)

def _track_line(ticker, price_cents):
    """Record a price point for line movement tracking."""
    import time as _t
    now = _t.time()
    if ticker not in _line_history:
        _line_history[ticker] = []
    _line_history[ticker].append((now, price_cents))
    # Keep last 30 minutes of data
    _line_history[ticker] = [(t, p) for t, p in _line_history[ticker] if now - t < 1800]

def _get_line_movement(ticker, price_cents):
    """Get line movement info for a ticker. Returns (direction, drop_cents, trend)."""
    import time as _t
    now = _t.time()
    _track_line(ticker, price_cents)
    history = _line_history.get(ticker, [])
    if len(history) < 2:
        return {"direction": "new", "change": 0, "is_dip": False}
    # Compare to highest price in last 15 min
    recent = [(t, p) for t, p in history if now - t < 900]
    if not recent:
        return {"direction": "stable", "change": 0, "is_dip": False}
    high = max(p for _, p in recent)
    low = min(p for _, p in recent)
    change = price_cents - recent[0][1]  # vs first reading
    # A "dip" is when price dropped 3+ cents from recent high (buying opportunity)
    is_dip = (high - price_cents) >= 3 and price_cents >= 70
    return {
        "direction": "up" if change > 0 else "down" if change < 0 else "stable",
        "change": change,
        "high": high,
        "low": low,
        "is_dip": is_dip,
        "dip_size": high - price_cents if is_dip else 0,
    }


def _smart_bet_size(price_cents, bankroll=None, edge=0.05):
    """Edge-driven bet sizing using half-Kelly criterion.

    Only bets when edge > 1.5%. Sizes proportional to edge, not price.
    Bigger edge = bigger bet. Trust Kelly to size appropriately.
    """
    if bankroll is None:
        try:
            bankroll = (_PORTFOLIO_CACHE.get("data") or {}).get("balance_usd", 0)
        except Exception:
            bankroll = 0
    if bankroll <= 0:
        bankroll = 400

    if edge < 0.015:
        return 0  # No edge, no bet

    # Half-Kelly: bet size proportional to edge magnitude
    # Higher edge = bigger bet, but always conservative
    odds = (100 - price_cents) / max(1, price_cents)
    win_prob = min(price_cents / 100.0 + edge, 0.95)
    kelly_frac = (odds * win_prob - (1 - win_prob)) / max(0.01, odds)
    kelly_frac = max(0, kelly_frac) / 2  # half-Kelly for safety
    # Cap at 5% of bankroll per trade (risk management)
    kelly_frac = min(kelly_frac, 0.05)

    bet = bankroll * kelly_frac
    if bet < 1.0:
        return 0  # Kelly says not worth it
    bet = min(bet, BOT_CONFIG.get("max_bet_usd", 25.0))
    return round(bet, 2)


def _generate_seventy_fivers():
    """Find top 10 markets at 70-85c with cross-platform validation."""
    import time as _t
    now = _t.time()
    if _sf_cache["data"] and (now - _sf_cache["ts"]) < _SF_CACHE_TTL:
        return _sf_cache["data"]

    try:
        all_markets = fetch_all_markets()
    except Exception:
        return _sf_cache["data"] or {"picks": [], "count": 0}

    # Blocked keywords (weather etc)
    _BLOCKED = ["temperature", "weather", "highest temp", "lowest temp", "degrees",
                "fahrenheit", "celsius", "rainfall", "snow", "hurricane", "tornado"]

    def _blocked(q):
        ql = q.lower()
        return any(kw in ql for kw in _BLOCKED)

    # Build cross-platform price index for validation
    other_prices = {}  # normalized_question -> list of prices from other platforms
    for m in all_markets:
        if m["platform"] == "kalshi":
            continue
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        if nq not in other_prices:
            other_prices[nq] = []
        other_prices[nq].append({
            "platform": m["platform"],
            "yes": m.get("yes", 0.5),
        })

    candidates = []
    now_dt = datetime.datetime.utcnow()

    for m in all_markets:
        if m["platform"] != "kalshi":
            continue
        title = m.get("question", "")
        if _blocked(title):
            continue
        if _is_parlay_title(title):
            continue

        ticker = m.get("id", "")
        vol = m.get("volume", 0) or 0

        # Block minor leagues and esports
        _75_BLOCKED_PREFIXES = ["KXKHLGAME", "KXVTBGAME", "KXCS2GAME", "KXVALGAME",
                                "KXDOTAGAME", "KXLOLGAME", "KXCOD", "KXCRICKET", "KXKABADDI"]
        if any(ticker.upper().startswith(bp) for bp in _75_BLOCKED_PREFIXES):
            continue

        # Get prices in cents
        yes_cents = int(round(m.get("yes", 0.5) * 100))
        no_cents = int(round(m.get("no", 0.5) * 100))

        # Determine best side at 70-85c
        side = None
        price = 0
        if 70 <= yes_cents <= 85:
            side = "yes"
            price = yes_cents
        elif 70 <= no_cents <= 85:
            side = "no"
            price = no_cents
        else:
            continue

        # Check if live — ticker prefix OR closes within 24h
        is_live = False
        t_upper = ticker.upper()
        et = m.get("event_ticker", "")
        et_upper = (et or "").upper()
        for pfx in LIVE_GAME_SERIES:
            if t_upper.startswith(pfx) or et_upper.startswith(pfx):
                is_live = True
                break
        # Also mark as live if closes within 24h
        close_time = m.get("close_time", "")
        if close_time and not is_live:
            try:
                close_dt = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                hours_left = (close_dt - now_dt).total_seconds() / 3600
                if 0 < hours_left <= 24:
                    is_live = True
            except Exception:
                pass

        # 48h max close time — no long-dated junk, only markets settling soon
        if close_time:
            try:
                close_dt_chk = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                hours_to_close = (close_dt_chk - now_dt).total_seconds() / 3600
                if hours_to_close > 48:
                    continue  # Skip anything more than 48h out
            except Exception:
                pass
        else:
            continue  # No close time = skip (probably long-dated)

        # Volume filter: relaxed for live sports (they often have low volume)
        if vol < 10 and is_live:
            continue
        if vol < 100 and not is_live:
            continue

        # Cross-platform validation
        nq = normalize_question(title)
        matching_platforms = []
        for nq_other, prices in other_prices.items():
            # Simple keyword overlap check
            words_k = set(nq.split())
            words_o = set(nq_other.split())
            overlap = len(words_k & words_o)
            if overlap >= 3 or (overlap >= 2 and len(words_k) <= 5):
                for p in prices:
                    other_prob = p["yes"] if side == "yes" else (1 - p["yes"])
                    if other_prob >= 0.65:  # other platform also thinks 65%+
                        matching_platforms.append(p["platform"])

        # Time to close
        close_time = m.get("close_time", "")
        time_left = ""
        if close_time:
            try:
                close_dt = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                delta = close_dt - now_dt
                total_secs = int(delta.total_seconds())
                if total_secs <= 0:
                    continue  # already closed
                if total_secs < 3600:
                    time_left = f"{total_secs // 60}m"
                elif total_secs < 86400:
                    time_left = f"{total_secs // 3600}h {(total_secs % 3600) // 60}m"
                else:
                    days = total_secs // 86400
                    time_left = f"{days}d"
            except Exception:
                pass

        profit_cents = 100 - price
        bet_size = _smart_bet_size(price)
        count = max(1, int(bet_size * 100 / price))
        confidence = len(matching_platforms) + 1  # 1 for Kalshi itself

        # Line movement tracking
        line = _get_line_movement(ticker, price)

        # Closing time edge — markets in last 30 min rarely flip
        closing_soon = False
        if close_time:
            try:
                close_dt2 = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                mins_left = (close_dt2 - now_dt).total_seconds() / 60
                if 0 < mins_left <= 30:
                    closing_soon = True
            except Exception:
                pass

        candidates.append({
            "ticker": ticker,
            "title": title[:80],
            "side": side,
            "price_cents": price,
            "profit_cents": profit_cents,
            "volume": vol,
            "is_live": is_live,
            "close_time": close_time,
            "time_left": time_left,
            "platforms": list(set(matching_platforms))[:3],
            "platform_count": len(set(matching_platforms)) + 1,
            "bet_size": bet_size,
            "count": count,
            "url": m.get("url", f"https://kalshi.com/markets/{ticker}"),
            "confidence": confidence,
            "line_movement": line,
            "closing_soon": closing_soon,
            "is_dip": line.get("is_dip", False),
        })

    # Sort: closing soon first (huge edge), then live, then dips, then by score
    candidates.sort(key=lambda x: (
        -int(x.get("closing_soon", False)),
        -int(x["is_live"]),
        -int(x.get("is_dip", False)),
        -(x["platform_count"] * x["profit_cents"] * min(x["volume"], 10000)),
    ))

    result = {"picks": candidates[:10], "count": len(candidates)}
    _sf_cache["data"] = result
    _sf_cache["ts"] = _t.time()
    return result


@app.route("/seventy-fivers")
def seventy_fivers():
    data = _generate_seventy_fivers()
    return jsonify(data)


@app.route("/trade-patterns")
def trade_patterns():
    """Pattern analysis endpoint — what's winning and losing."""
    analysis = get_pattern_analysis()
    return jsonify(analysis)


@app.route("/trade-journal")
def trade_journal():
    """Full trade journal with all metadata."""
    return jsonify({"trades": _TRADE_JOURNAL[-50:], "total": len(_TRADE_JOURNAL)})


@app.route("/quick-bet", methods=["POST"])
def quick_bet():
    """One-click bet from the 75%'ers tab."""
    body = request.get_json(force=True)
    ticker = body.get("ticker", "")
    side = body.get("side", "")
    price_cents = body.get("price_cents", 0)

    if not ticker or not side or not price_cents:
        return jsonify({"error": "Missing ticker, side, or price_cents"}), 400

    # Smart bet sizing
    bet_size = _smart_bet_size(price_cents)
    count = max(1, int(bet_size * 100 / price_cents))
    cost_usd = (price_cents * count) / 100.0

    # Safety checks
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                            headers=bal_h, timeout=8)
        if bal_r.ok:
            balance = bal_r.json().get("balance", 0) / 100
            min_bal = BOT_CONFIG.get("min_balance_usd", 10.0)
            if balance - cost_usd < min_bal:
                return jsonify({"error": f"Would drop below ${min_bal:.0f} safety floor"}), 400
    except Exception:
        pass  # proceed anyway if balance check fails

    result = place_kalshi_order(ticker, side, price_cents, count=count)
    success = "error" not in result

    if success:
        _log_activity(f"QUICK BET: {side.upper()} {ticker} @ {price_cents}c x{count} (${cost_usd:.2f})", "success")
        BOT_STATE["sf_bets"] += 1
        # Track in trades-today feed so manual bets show up in Activity
        BOT_STATE.setdefault("manual_trades_today", []).append({
            "ticker": ticker, "title": ticker, "side": side,
            "price": price_cents, "count": count, "cost": round(cost_usd, 2),
            "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "strategy": "manual", "source": "you",
        })
        _journal_trade(ticker, ticker, side, price_cents, count, cost_usd, "manual", is_live=False)
    else:
        err = result.get("error", result.get("response_body", "Unknown"))
        _log_activity(f"QUICK BET FAILED: {ticker} — {str(err)[:60]}", "error")

    return jsonify({
        "success": success,
        "ticker": ticker,
        "side": side,
        "price_cents": price_cents,
        "count": count,
        "cost_usd": round(cost_usd, 2),
        "bet_size": bet_size,
        "result": result,
    })


@app.route("/seventy-fivers-stats")
def seventy_fivers_stats():
    return jsonify({
        "wins": BOT_STATE.get("sf_wins", 0),
        "losses": BOT_STATE.get("sf_losses", 0),
        "streak": BOT_STATE.get("sf_streak", 0),
        "best_streak": BOT_STATE.get("sf_best_streak", 0),
        "profit": round(BOT_STATE.get("sf_profit", 0), 2),
        "total_bets": BOT_STATE.get("sf_bets", 0),
        "win_rate": round(BOT_STATE.get("sf_wins", 0) / max(1, BOT_STATE.get("sf_wins", 0) + BOT_STATE.get("sf_losses", 0)) * 100, 1),
    })


# ---------------------------------------------------------------------------
# MOONSHARK API — Longshot underdog sniper stats
# ---------------------------------------------------------------------------

@app.route("/moonshark")
def moonshark_stats():
    """Return MoonShark strategy stats: today's trades, daily spend, lifetime stats, active positions, and full trade history including manually placed low-price bets."""
    today = datetime.datetime.utcnow().strftime("%Y-%m-%d")

    # Today's MoonShark trades
    todays_trades = BOT_STATE.get("moonshark_trades_today", [])
    daily_spent = BOT_STATE.get("moonshark_daily_spent", 0.0)

    # ── Gather ALL MoonShark-style trades ──
    # 1. Journal entries with strategy == "moonshark"
    moonshark_journal = [t for t in _TRADE_JOURNAL if t.get("strategy") == "moonshark"]

    # 2. Also include any journal entry where entry price was <= 30 cents (manual low-price bets)
    low_price_journal = [
        t for t in _TRADE_JOURNAL
        if t.get("strategy") != "moonshark"
        and (t.get("price_cents") or t.get("price_at_entry") or 999) <= 30
        and (t.get("price_cents") or t.get("price_at_entry") or 0) > 0
    ]

    # 3. Pull from Kalshi settled positions API for any trades <= 30 cents not already in journal
    kalshi_low_price_settled = []
    journal_tickers = {t.get("ticker") for t in _TRADE_JOURNAL if t.get("ticker")}
    try:
        path = "/portfolio/positions"
        positions_list = []
        cursor = None
        for _ in range(10):
            params = {"limit": 200, "settlement_status": "settled"}
            if cursor:
                params["cursor"] = cursor
            h = signed_headers("GET", path)
            if not h:
                break
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
                headers=h, params=params, timeout=15,
            )
            if not resp.ok:
                break
            page = resp.json()
            positions_list.extend(page.get("market_positions", []))
            cursor = page.get("cursor")
            if not cursor:
                break

        for pos in positions_list:
            ticker = pos.get("ticker", "")
            if ticker in journal_tickers:
                continue  # already covered by journal
            side = pos.get("side", "yes")
            try:
                if side == "yes":
                    entry_cents = int(round(float(str(
                        pos.get("average_yes_price_dollars") or pos.get("average_yes_price") or 0
                    )) * 100))
                else:
                    entry_cents = int(round(float(str(
                        pos.get("average_no_price_dollars") or pos.get("average_no_price") or 0
                    )) * 100))
            except Exception:
                entry_cents = 0
            if entry_cents <= 0 or entry_cents > 30:
                continue  # not a moonshark-style trade
            try:
                count = int(float(str(pos.get("total_count_fp") or pos.get("total_count") or 0)))
            except Exception:
                count = 0
            cost_usd = round((entry_cents * count) / 100, 2)
            pnl_cents = _parse_kalshi_dollars(pos.get("realized_pnl_dollars") or pos.get("realized_pnl"))
            pnl_usd = round(pnl_cents / 100, 2)
            won = pnl_usd > 0
            # Try to get title
            title = ticker
            trade_rec = {}
            for t in BOT_STATE.get("all_trades", []):
                if t.get("ticker") == ticker:
                    trade_rec = t
                    title = t.get("question", "") or t.get("ticker", ticker)
                    break
            kalshi_low_price_settled.append({
                "ticker": ticker,
                "title": title,
                "side": side,
                "price_cents": entry_cents,
                "count": count,
                "cost_usd": cost_usd,
                "result": "win" if won else ("loss" if pnl_usd < -0.005 else "even"),
                "pnl_usd": pnl_usd,
                "payout": round(cost_usd + pnl_usd, 2),
                "settlement_time": trade_rec.get("close_time", "") or "",
                "entry_time": trade_rec.get("timestamp", "") or "",
                "strategy": "moonshark_manual",
                "source": "kalshi_api",
            })
    except Exception as e:
        print(f"[MOONSHARK] Error fetching Kalshi settled for low-price: {e}")

    # ── Combine all moonshark-style trades ──
    all_moonshark = moonshark_journal + low_price_journal + kalshi_low_price_settled

    # Deduplicate by ticker (prefer journal entries)
    seen_tickers = set()
    deduped = []
    for t in all_moonshark:
        tk = t.get("ticker", "")
        if tk and tk in seen_tickers:
            continue
        seen_tickers.add(tk)
        deduped.append(t)
    all_moonshark = deduped

    settled = [t for t in all_moonshark if t.get("result") is not None]
    wins = [t for t in settled if t.get("result") == "win"]
    losses = [t for t in settled if t.get("result") in ("loss", "even")]
    total_pnl = sum(t.get("pnl_usd", 0) for t in settled)
    best_win = max((t.get("pnl_usd", 0) for t in wins), default=0)
    total_cost = sum(t.get("cost_usd", 0) for t in settled)
    roi = round(total_pnl / max(0.01, total_cost) * 100, 1) if total_cost > 0 else 0

    # Active MoonShark positions (unsettled journal entries)
    active = [t for t in all_moonshark if t.get("result") is None]

    avg_payout = round(sum(t.get("pnl_usd", 0) for t in wins) / max(1, len(wins)), 2) if wins else 0

    # Build settled trade history sorted by most recent
    trade_history = []
    for t in settled:
        close_time = t.get("settlement_time") or t.get("entry_time") or ""
        pnl = t.get("pnl_usd", 0)
        cost = t.get("cost_usd", 0)
        payout = t.get("payout") if t.get("payout") is not None else round(cost + pnl, 2)
        trade_history.append({
            "ticker": t.get("ticker", ""),
            "title": t.get("title", ""),
            "side": t.get("side", ""),
            "entry_price": t.get("price_cents") or t.get("price_at_entry") or 0,
            "count": t.get("count", 0),
            "cost": round(cost, 2),
            "result": t.get("result", ""),
            "payout": round(payout, 2),
            "pnl": round(pnl, 2),
            "close_time": close_time,
            "entry_time": t.get("entry_time", ""),
        })
    # Sort by close_time descending (most recent first)
    trade_history.sort(key=lambda x: x.get("close_time") or x.get("entry_time") or "", reverse=True)

    # Cumulative P&L timeline (chronological order for running total)
    cumulative_pnl = []
    running = 0.0
    for th in reversed(trade_history):
        running += th.get("pnl", 0)
        cumulative_pnl.append({
            "ticker": th.get("ticker", ""),
            "pnl": th.get("pnl", 0),
            "running_total": round(running, 2),
            "time": th.get("close_time") or th.get("entry_time") or "",
        })

    return jsonify({
        "today": {
            "trades": todays_trades,
            "trade_count": len(todays_trades),
            "daily_spent": round(daily_spent, 2),
            "daily_limit": MOONSHARK_MAX_DAILY,
            "trades_remaining": max(0, MOONSHARK_MAX_TRADES - len(todays_trades)),
            "budget_remaining": round(max(0, MOONSHARK_MAX_DAILY - daily_spent), 2),
        },
        "lifetime": {
            "total_trades": len(all_moonshark),
            "settled": len(settled),
            "wins": len(wins),
            "losses": len(losses),
            "win_rate": round(len(wins) / max(1, len(settled)) * 100, 1),
            "total_pnl": round(total_pnl, 2),
            "best_win": round(best_win, 2),
            "avg_payout_on_wins": avg_payout,
            "total_cost": round(total_cost, 2),
            "roi": roi,
        },
        "active_positions": [{
            "ticker": t.get("ticker"),
            "title": t.get("title", ""),
            "side": t.get("side"),
            "price": t.get("price_cents") or t.get("price_at_entry") or t.get("entry_price_cents"),
            "count": t.get("count"),
            "cost": t.get("cost_usd"),
            "potential_profit": round((100 - ((t.get("price_cents") or t.get("price_at_entry") or t.get("entry_price_cents")) or 0)) * (t.get("count") or 0) / 100.0, 2),
            "entry_time": t.get("entry_time"),
        } for t in active],
        "trade_history": trade_history,
        "cumulative_pnl": cumulative_pnl,
        "settings": {
            "min_price": MOONSHARK_MIN_PRICE,
            "max_price": MOONSHARK_MAX_PRICE,
            "bet_size": MOONSHARK_BET_USD,
            "max_daily": MOONSHARK_MAX_DAILY,
            "max_trades": MOONSHARK_MAX_TRADES,
        },
        "enabled": BOT_CONFIG.get("moonshark_enabled", True),
    })


@app.route("/moonshark-opportunities")
def moonshark_opportunities():
    """Return top 5 MoonShark-eligible markets for the wheel."""
    try:
        # Fetch Kalshi sport markets directly for MoonShark
        # fetch_kalshi() is too heavy (80+ API calls, 20s timeout) — instead we
        # fetch events, pick sport-relevant ones, then get their markets
        import time as _t
        _now = _t.time()
        if not hasattr(moonshark_opportunities, '_kalshi_cache'):
            moonshark_opportunities._kalshi_cache = {"data": [], "ts": 0}
        kc = moonshark_opportunities._kalshi_cache
        if kc["data"] and (_now - kc["ts"]) < 120:
            markets = kc["data"]
        else:
            markets = []
            _sport_prefixes = ["KXATP", "KXWTA", "KXKBL", "KXNCAA", "KXNBA",
                               "KXNHL", "KXMLB", "KXUFC", "KXMMA", "KXSOCCER",
                               "KXEPL", "KXNFL", "KXMLS", "KXWNBA", "KXPGA"]
            try:
                # Step 1: Get events
                _ev_tickers = []
                _ev_cursor = None
                for _evp in range(3):
                    _evh = signed_headers("GET", "/events")
                    _evparams = {"limit": 200, "status": "open"}
                    if _ev_cursor:
                        _evparams["cursor"] = _ev_cursor
                    _evr = requests.get(
                        KALSHI_BASE_URL + KALSHI_API_PREFIX + "/events",
                        headers=_evh, params=_evparams, timeout=10,
                    )
                    if _evr.ok:
                        for ev in _evr.json().get("events", []):
                            et = ev.get("event_ticker", "")
                            # Keep non-parlay events (sport + general)
                            if et and not et.upper().startswith("KXMVE"):
                                _ev_tickers.append(et)
                        _ev_cursor = _evr.json().get("cursor")
                        if not _ev_cursor:
                            break
                    else:
                        break
                # Step 2: Fetch markets for sport events first, then others
                # Prioritize sports (what MoonShark bets on)
                _sport_evts = [e for e in _ev_tickers if any(e.upper().startswith(p) for p in _sport_prefixes)]
                _other_evts = [e for e in _ev_tickers if e not in _sport_evts]
                _fetch_evts = _sport_evts + _other_evts[:30]  # all sports + up to 30 others
                for et in _fetch_evts:
                    try:
                        _mh = signed_headers("GET", "/markets")
                        _mr = requests.get(
                            KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                            headers=_mh,
                            params={"limit": 200, "event_ticker": et, "status": "open"},
                            timeout=5,
                        )
                        if _mr.ok:
                            markets.extend(_mr.json().get("markets", []))
                    except Exception:
                        continue
            except Exception as _ms_err:
                print(f"[MOONSHARK] Fetch error: {_ms_err}")
            if markets:
                kc["data"] = markets
                kc["ts"] = _now
            print(f"[MOONSHARK] Fetched {len(markets)} markets from {len(_fetch_evts) if '_fetch_evts' in dir() else 0} events")
        opps = []
        existing_tickers = set()
        try:
            positions = check_position_prices()
            existing_tickers = {p.get("ticker", "") for p in positions}
        except Exception:
            pass

        debug_total = len(markets)
        debug_in_range = 0
        debug_kalshi = 0
        debug_has_price = 0
        debug_in_position = 0
        # Debug: sample first 3 markets to see field names
        debug_samples = []
        for dm in markets[:3]:
            debug_samples.append({
                "ticker": dm.get("ticker", ""),
                "id": dm.get("id", ""),
                "platform": dm.get("platform", ""),
                "question": (dm.get("question") or dm.get("title") or "")[:30],
            })

        for m in markets:
            # Only Kalshi markets (tickers start with KX)
            ticker = m.get("ticker") or m.get("id") or ""
            if not ticker or not ticker.upper().startswith("KX"):
                continue
            # Only women's tennis (WTA) markets for the wheel
            _tk_upper = ticker.upper()
            if not _tk_upper.startswith("KXWTA"):
                continue
            # Must be a GAME/MATCH/FIGHT (binary outcome, not futures/props)
            if not any(kw in _tk_upper for kw in ["GAME", "MATCH", "FIGHT"]):
                continue
            # Must be LIVE right now — close_time within next 12h and game already started
            _ct = m.get("close_time") or m.get("expected_expiration_time") or ""
            if _ct:
                try:
                    _cd = datetime.datetime.fromisoformat(_ct.replace("Z", "+00:00")).replace(tzinfo=None)
                    _htc = (_cd - datetime.datetime.utcnow()).total_seconds() / 3600
                    if _htc > 12 or _htc < 0:
                        continue
                except Exception:
                    continue
            else:
                continue
            debug_kalshi += 1
            if ticker in existing_tickers:
                debug_in_position += 1
                continue
            # Try multiple price field names (raw Kalshi API uses _dollars string fields)
            yes_price = 0
            no_price = 0
            # First try dollar string fields (raw Kalshi v2 API)
            for yf in ["yes_ask_dollars", "last_price_dollars"]:
                v = m.get(yf)
                if v is not None:
                    try:
                        yes_price = max(0, int(round(float(v) * 100)))
                        break
                    except (ValueError, TypeError):
                        continue
            # Then try cents/numeric fields (normalized data)
            if not yes_price:
                for yf in ["yes_ask_cents", "yes_ask", "yes_price"]:
                    v = m.get(yf)
                    if v and isinstance(v, (int, float)) and v > 0:
                        yes_price = int(v) if v > 1 else int(v * 100)
                        break
            # Also check decimal "yes" field (0-1 range)
            if not yes_price:
                y = m.get("yes", 0)
                if y and 0 < y < 1:
                    yes_price = int(y * 100)
            no_price = 100 - yes_price if yes_price else 0
            title = m.get("question", "") or m.get("title", "") or ticker
            close_time = m.get("close_time") or m.get("expected_expiration_time") or ""

            if yes_price > 0:
                debug_has_price += 1
            # Check YES side (5-45c range for longshot opportunities)
            if 5 <= yes_price <= 45:
                debug_in_range += 1
                payout = round((100 - yes_price) / 100 * 5, 2)
                opps.append({
                    "ticker": ticker, "title": title, "side": "yes",
                    "price": yes_price, "win_prob": yes_price,
                    "payout": payout, "close_time": close_time,
                    "volume": m.get("volume", 0) or 0,
                })
            # Check NO side
            elif 5 <= no_price <= 45:
                debug_in_range += 1
                payout = round((100 - no_price) / 100 * 5, 2)
                opps.append({
                    "ticker": ticker, "title": title, "side": "no",
                    "price": no_price, "win_prob": no_price,
                    "payout": payout, "close_time": close_time,
                    "volume": m.get("volume", 0) or 0,
                })

        # Split into general and WTA tennis
        wta_opps = [o for o in opps if 'KXWTA' in (o.get('ticker') or '').upper() or
                    'KXWTAMATCH' in (o.get('ticker') or '').upper()]
        general_opps = [o for o in opps if o not in wta_opps]

        # Sort by volume (most liquid first), take top 10 each
        general_opps.sort(key=lambda x: -(x.get("volume") or 0))
        wta_opps.sort(key=lambda x: -(x.get("volume") or 0))
        return jsonify({
            "opportunities": general_opps[:10],
            "wta_opportunities": wta_opps[:10],
            "total_scanned": debug_total,
            "debug_kalshi": debug_kalshi,
            "debug_has_price": debug_has_price,
            "debug_in_position": debug_in_position,
            "in_range": debug_in_range,
            "debug_samples": debug_samples,
        })
    except Exception as e:
        import traceback
        return jsonify({"opportunities": [], "error": str(e), "trace": traceback.format_exc()})


@app.route("/moonshark/toggle", methods=["POST"])
def moonshark_toggle():
    """Toggle MoonShark enabled/disabled."""
    current = BOT_CONFIG.get("moonshark_enabled", True)
    BOT_CONFIG["moonshark_enabled"] = not current
    _save_state()
    return jsonify({"enabled": BOT_CONFIG["moonshark_enabled"]})


# ---------------------------------------------------------------------------
# MOONSHOT TAB — Underdog bets in close live games (high payout)
# ---------------------------------------------------------------------------
_moonshot_cache = {"data": None, "ts": 0}
_MOONSHOT_CACHE_TTL = 30  # refresh every 30s for live action

BOT_STATE["moonshot_fund"] = 0.0  # 10% of wins auto-allocated
BOT_STATE["moonshot_wins"] = 0
BOT_STATE["moonshot_losses"] = 0
BOT_STATE["moonshot_profit"] = 0.0
BOT_STATE["moonshot_bets"] = 0
BOT_STATE["moonshot_biggest_win"] = 0.0

def _generate_moonshots():
    """Find live sports underdogs in close games — high payout opportunities.
    Strategy: When a heavy pre-game favorite is in a close game, the underdog
    price is artificially low. The market is slow to adjust live odds."""
    import time as _t
    now = _t.time()
    if _moonshot_cache["data"] and (now - _moonshot_cache["ts"]) < _MOONSHOT_CACHE_TTL:
        return _moonshot_cache["data"]

    candidates = []
    now_dt = datetime.datetime.utcnow()

    # Scan all live game series for underdogs
    for series in LIVE_GAME_SERIES:
        try:
            mh = signed_headers("GET", "/markets")
            params = {"limit": 200, "status": "open", "series_ticker": series}
            resp = requests.get(
                KALSHI_BASE_URL + KALSHI_API_PREFIX + "/markets",
                headers=mh, params=params, timeout=8,
            )
            if not resp.ok:
                continue
            markets = resp.json().get("markets", [])

            for mkt in markets:
                ticker = mkt.get("ticker", "")
                title = mkt.get("title", "")
                vol = mkt.get("volume", 0) or 0

                # Need some volume
                if vol < 20:
                    continue

                # Must be closing soon (live game = within 12h)
                close_time = mkt.get("close_time", "")
                hours_left = 999
                if close_time:
                    try:
                        close_dt = datetime.datetime.fromisoformat(close_time.replace("Z", "+00:00")).replace(tzinfo=None)
                        hours_left = (close_dt - now_dt).total_seconds() / 3600
                        if hours_left > 12 or hours_left <= 0:
                            continue
                    except Exception:
                        continue

                # Parse prices
                yes_price = 50
                no_price = 50
                try:
                    ya = mkt.get("yes_ask_dollars") or mkt.get("yes_ask") or mkt.get("last_price")
                    if ya:
                        yes_price = int(round(float(str(ya)) * 100))
                    na = mkt.get("no_ask_dollars") or mkt.get("no_ask")
                    if na:
                        no_price = int(round(float(str(na)) * 100))
                    else:
                        no_price = 100 - yes_price
                except Exception:
                    continue

                # MOONSHOT ZONE: underdog at 15-45c (payout 2.2x to 6.7x)
                # This is the sweet spot — cheap enough for big payout,
                # but not so cheap that it's hopeless
                side = None
                price = 0
                payout_ratio = 0

                if 15 <= yes_price <= 45:
                    side = "yes"
                    price = yes_price
                    payout_ratio = round(100 / price, 1)
                elif 15 <= no_price <= 45:
                    side = "no"
                    price = no_price
                    payout_ratio = round(100 / price, 1)
                else:
                    continue

                # Calculate implied edge: if the game is close, real odds are
                # much better than market price suggests
                # Close game indicator: underdog at 30-45c suggests competitive game
                closeness = "unknown"
                edge_estimate = 0
                if price >= 35:
                    closeness = "TIGHT"
                    edge_estimate = 15  # market might be 10-15% behind reality
                elif price >= 25:
                    closeness = "COMPETITIVE"
                    edge_estimate = 10
                else:
                    closeness = "TRAILING"
                    edge_estimate = 5

                # Time pressure bonus: closer to end = more valuable
                time_bonus = 0
                time_label = ""
                if hours_left <= 1:
                    time_bonus = 10
                    time_label = "FINAL STRETCH"
                elif hours_left <= 3:
                    time_bonus = 5
                    time_label = "LATE GAME"
                else:
                    time_label = "MID GAME"

                # Determine sport type from series prefix
                sport = "Sports"
                t_upper = ticker.upper()
                if "NBA" in t_upper:
                    sport = "NBA"
                elif "NHL" in t_upper:
                    sport = "NHL"
                elif "MLB" in t_upper:
                    sport = "MLB"
                elif "NFL" in t_upper:
                    sport = "NFL"
                elif "ATP" in t_upper or "WTA" in t_upper:
                    sport = "Tennis"
                elif "SOCCER" in t_upper:
                    sport = "Soccer"

                # Suggested bet from moonshot fund
                fund = BOT_STATE.get("moonshot_fund", 0)
                suggested_bet = min(max(5, fund * 0.25), 25)  # 25% of fund, $5-$25 range
                potential_win = round(suggested_bet * (payout_ratio - 1), 2)

                # Time remaining string
                time_left = ""
                if hours_left < 1:
                    time_left = f"{int(hours_left * 60)}m"
                else:
                    time_left = f"{hours_left:.1f}h"

                # Score: higher = better moonshot
                score = (edge_estimate + time_bonus) * payout_ratio * min(vol, 500)

                candidates.append({
                    "ticker": ticker,
                    "title": title[:80],
                    "side": side,
                    "price_cents": price,
                    "payout_ratio": payout_ratio,
                    "sport": sport,
                    "closeness": closeness,
                    "time_label": time_label,
                    "time_left": time_left,
                    "hours_left": round(hours_left, 2),
                    "volume": vol,
                    "edge_estimate": edge_estimate,
                    "suggested_bet": round(suggested_bet, 2),
                    "potential_win": potential_win,
                    "score": score,
                    "url": f"https://kalshi.com/markets/{ticker}",
                })
        except Exception:
            continue

    # Sort by score (best moonshots first)
    candidates.sort(key=lambda x: -x["score"])

    result = {
        "picks": candidates[:10],
        "count": len(candidates),
        "fund_balance": round(BOT_STATE.get("moonshot_fund", 0), 2),
        "total_wins": BOT_STATE.get("moonshot_wins", 0),
        "total_losses": BOT_STATE.get("moonshot_losses", 0),
        "total_profit": round(BOT_STATE.get("moonshot_profit", 0), 2),
        "total_bets": BOT_STATE.get("moonshot_bets", 0),
        "biggest_win": round(BOT_STATE.get("moonshot_biggest_win", 0), 2),
    }
    _moonshot_cache["data"] = result
    _moonshot_cache["ts"] = _t.time()
    return result


@app.route("/moonshots")
def moonshots():
    data = _generate_moonshots()
    return jsonify(data)


@app.route("/moonshot-bet", methods=["POST"])
def moonshot_bet():
    """Place a moonshot bet from the fund."""
    body = request.get_json(force=True)
    ticker = body.get("ticker", "")
    side = body.get("side", "")
    price_cents = body.get("price_cents", 0)
    bet_usd = body.get("bet_usd", 5)
    bet_source = body.get("source", "manual")  # "wheel" or "manual"

    if not ticker or not side:
        return jsonify({"error": "Missing ticker or side"}), 400

    # Safety checks
    fund = BOT_STATE.get("moonshot_fund", 0)
    if bet_usd > fund + 5:  # allow $5 over fund for manual adds
        return jsonify({"error": f"Moonshot fund only has ${fund:.2f}"}), 400
    if bet_usd > 50:
        return jsonify({"error": "Max moonshot bet is $50"}), 400

    count = max(1, int(bet_usd * 100 / max(1, price_cents)))
    try:
        order_h = signed_headers("POST", "/portfolio/orders")
        order_body = {
            "ticker": ticker,
            "action": "buy",
            "type": "limit",
            "side": side,
            "count": count,
            "yes_price": price_cents if side == "yes" else (100 - price_cents),
            "expiration_ts": int((datetime.datetime.utcnow() + datetime.timedelta(minutes=2)).timestamp()),
        }
        resp = requests.post(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/orders",
            headers=order_h, json=order_body, timeout=10,
        )
        if resp.ok:
            actual_cost = (price_cents * count) / 100
            BOT_STATE["moonshot_fund"] = max(0, fund - actual_cost)
            BOT_STATE["moonshot_bets"] = BOT_STATE.get("moonshot_bets", 0) + 1
            payout = (100 * count) / 100
            _add_activity(
                f"MOONSHOT: {side.upper()} {ticker} {count}x @ {price_cents}c "
                f"(${actual_cost:.2f} for ${payout:.2f} payout)",
                "success",
            )
            # Track in trades-today feed so manual moonshot bets show up
            BOT_STATE.setdefault("manual_trades_today", []).append({
                "ticker": ticker, "title": ticker, "side": side,
                "price": price_cents, "count": count, "cost": round(actual_cost, 2),
                "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                "strategy": "wta_wheel" if bet_source == "wheel" else "moonshark_manual", "source": "you",
            })
            _strategy = "wta_wheel" if bet_source == "wheel" else "moonshark_manual"
            _journal_trade(ticker, ticker, side, price_cents, count, actual_cost, _strategy, is_live=True)
            return jsonify({"success": True, "cost": actual_cost, "count": count, "potential_payout": payout})
        else:
            return jsonify({"error": resp.text}), 400
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/moonshot-fund", methods=["POST"])
def moonshot_fund_add():
    """Manually add to the moonshot fund."""
    body = request.get_json(force=True)
    amount = body.get("amount", 0)
    if amount > 0:
        BOT_STATE["moonshot_fund"] = BOT_STATE.get("moonshot_fund", 0) + amount
        return jsonify({"success": True, "new_balance": round(BOT_STATE["moonshot_fund"], 2)})
    return jsonify({"error": "Amount must be positive"}), 400


@app.route("/wta-wheel-stats")
def wta_wheel_stats():
    """Stats for WTA wheel bets and all WTA tennis positions."""
    try:
        # Get all WTA trades from journal (wheel + bot)
        wta_all = [t for t in _TRADE_JOURNAL if "KXWTA" in (t.get("ticker") or "").upper()]
        wta_wheel = [t for t in _TRADE_JOURNAL if t.get("strategy") == "wta_wheel"]
        wta_settled = [t for t in wta_all if t.get("result") is not None]
        wheel_settled = [t for t in wta_wheel if t.get("result") is not None]

        wta_wins = sum(1 for t in wta_settled if t.get("result") == "win")
        wta_losses = sum(1 for t in wta_settled if t.get("result") == "loss")
        wta_pnl = sum(float(t.get("pnl") or 0) for t in wta_settled)

        wheel_wins = sum(1 for t in wheel_settled if t.get("result") == "win")
        wheel_losses = sum(1 for t in wheel_settled if t.get("result") == "loss")
        wheel_pnl = sum(float(t.get("pnl") or 0) for t in wheel_settled)

        # Also check open WTA positions
        wta_open = []
        try:
            positions = check_position_prices()
            for p in positions:
                tk = (p.get("ticker") or "").upper()
                if "KXWTA" in tk:
                    wta_open.append(p)
        except Exception:
            pass

        # Build bet list for wheel bets (settled + open)
        bets = []
        for t in wta_wheel:
            bets.append({
                "ticker": t.get("ticker", ""),
                "title": t.get("title", t.get("ticker", "")),
                "side": t.get("side", ""),
                "price": t.get("price_cents", 0),
                "count": t.get("count", 0),
                "cost": round(float(t.get("cost_usd") or 0), 2),
                "result": t.get("result"),
                "pnl": round(float(t.get("pnl") or 0), 2),
                "time": t.get("timestamp", ""),
            })
        # Also include any WTA bot trades
        for t in wta_all:
            if t.get("strategy") != "wta_wheel":
                bets.append({
                    "ticker": t.get("ticker", ""),
                    "title": t.get("title", t.get("ticker", "")),
                    "side": t.get("side", ""),
                    "price": t.get("price_cents", 0),
                    "count": t.get("count", 0),
                    "cost": round(float(t.get("cost_usd") or 0), 2),
                    "result": t.get("result"),
                    "pnl": round(float(t.get("pnl") or 0), 2),
                    "time": t.get("timestamp", ""),
                    "source": "bot",
                })

        total_bets = len(wta_settled)
        win_rate = round(wta_wins / max(1, wta_wins + wta_losses) * 100, 1) if total_bets > 0 else 0

        return jsonify({
            "total_bets": len(wta_all),
            "settled": len(wta_settled),
            "wins": wta_wins,
            "losses": wta_losses,
            "win_rate": win_rate,
            "pnl": round(wta_pnl, 2),
            "open_count": len(wta_open),
            "unrealized": round(sum(p.get("unrealized_pnl_cents", 0) for p in wta_open) / 100, 2),
            "wheel_bets": len(wta_wheel),
            "wheel_wins": wheel_wins,
            "wheel_losses": wheel_losses,
            "wheel_pnl": round(wheel_pnl, 2),
            "bets": bets[-20:],  # last 20
        })
    except Exception as e:
        return jsonify({"error": str(e), "total_bets": 0, "bets": []})


# ---------------------------------------------------------------------------
# QUANT TAB — Mispriced market trading (active quantitative approach)
# ---------------------------------------------------------------------------
_quant_cache = {"data": None, "ts": 0}
_QUANT_CACHE_TTL = 60

BOT_STATE["quant_wins"] = 0
BOT_STATE["quant_losses"] = 0
BOT_STATE["quant_profit"] = 0.0
BOT_STATE["quant_bets"] = 0
BOT_STATE["quant_trades"] = []  # Full trade history for Quant tab

def _generate_quant_picks():
    """Find top 10 mispriced markets with cross-platform edge."""
    import time as _t
    now = _t.time()
    if _quant_cache["data"] and (now - _quant_cache["ts"]) < _QUANT_CACHE_TTL:
        return _quant_cache["data"]

    try:
        all_markets = fetch_all_markets()
        mispricings = find_consensus_mispricings(all_markets)
    except Exception:
        return _quant_cache["data"] or {"picks": [], "count": 0}

    _BLOCKED = ["temperature", "weather", "highest temp", "lowest temp", "degrees",
                "fahrenheit", "celsius", "rainfall", "snow", "hurricane", "tornado"]

    candidates = []
    for opp in mispricings:
        title = opp.get("kalshi_question", "")
        ticker = opp.get("kalshi_ticker", "")

        # Skip blocked categories
        if any(kw in title.lower() for kw in _BLOCKED):
            continue
        if _is_parlay_title(title):
            continue

        # Quality filters
        plat_count = len(opp.get("matching_platforms", []))
        if plat_count < 1:
            continue
        deviation = opp.get("deviation", 0)
        if deviation < 0.10:
            continue  # need 10%+ edge
        pc = opp.get("price_cents", 0)
        if pc < 20 or pc > 80:
            continue  # no penny traps, no overpaying

        volume = 0
        # Try to get volume from the market data
        for m in all_markets:
            if m.get("id") == ticker and m.get("platform") == "kalshi":
                volume = m.get("volume", 0) or 0
                break
        if volume < 50:
            continue

        side = opp.get("signal", "").replace("buy_", "")
        consensus = opp.get("consensus_yes_price", 0.5)
        kalshi_price = opp.get("kalshi_yes_price", 0.5)
        edge_cents = int(round(deviation * 100))
        bet_size = _smart_bet_size(pc)
        count = max(1, int(bet_size * 100 / pc))
        ev_dollars = round(edge_cents * count / 100, 2)
        category = classify_market_category(title, ticker)
        line = _get_line_movement(ticker, pc)

        # Platform details
        platforms_detail = []
        for mp in opp.get("matching_platforms", [])[:3]:
            platforms_detail.append({
                "platform": mp.get("platform", ""),
                "price": int(round(mp.get("yes", 0.5) * 100)),
            })

        candidates.append({
            "ticker": ticker,
            "title": title[:80],
            "side": side,
            "price_cents": pc,
            "consensus_cents": int(round(consensus * 100)),
            "kalshi_cents": int(round(kalshi_price * 100)),
            "deviation_pct": round(deviation * 100, 1),
            "edge_cents": edge_cents,
            "volume": volume,
            "platforms": platforms_detail,
            "platform_count": plat_count + 1,
            "bet_size": bet_size,
            "count": count,
            "ev_dollars": ev_dollars,
            "category": category,
            "url": opp.get("kalshi_url", f"https://kalshi.com/markets/{ticker}"),
            "line_movement": line,
            "is_dip": line.get("is_dip", False),
        })

    # Sort by deviation * platform_count * volume (best edge first)
    candidates.sort(key=lambda x: -(x["deviation_pct"] * x["platform_count"] * min(x["volume"], 10000)))
    top = candidates[:10]
    result = {"picks": top, "count": len(candidates)}
    _quant_cache["data"] = result
    _quant_cache["ts"] = _t.time()
    return result


@app.route("/quant-picks")
def quant_picks():
    data = _generate_quant_picks()
    return jsonify(data)


@app.route("/quant-bet", methods=["POST"])
def quant_bet():
    """Place a quant trade from the Quant tab."""
    body = request.get_json(force=True) or {}
    ticker = body.get("ticker", "")
    side = body.get("side", "yes")
    price_cents = body.get("price_cents", 50)

    if not ticker:
        return jsonify({"success": False, "error": "Missing ticker"})

    # Safety checks
    try:
        bal_h = signed_headers("GET", "/portfolio/balance")
        bal_r = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + "/portfolio/balance",
                             headers=bal_h, timeout=TIMEOUT)
        if bal_r.ok:
            bal = bal_r.json().get("balance", 0) / 100
            if bal < BOT_CONFIG.get("min_balance_usd", 10):
                return jsonify({"success": False, "error": f"Balance too low: ${bal:.2f}"})
        else:
            bal = 500
    except Exception:
        bal = 500

    bet_size = _smart_bet_size(price_cents, bankroll=bal)
    count = max(1, int(bet_size * 100 / price_cents))
    cost = (price_cents * count) / 100.0

    result = place_kalshi_order(ticker, side, price_cents, count=count)
    success = "error" not in result

    if success:
        BOT_STATE["quant_bets"] = BOT_STATE.get("quant_bets", 0) + 1
        trade_record = {
            "ticker": ticker,
            "title": body.get("title", ticker),
            "side": side,
            "price_cents": price_cents,
            "count": count,
            "cost_usd": round(cost, 2),
            "time": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "category": classify_market_category(body.get("title", ticker), ticker),
            "deviation_pct": body.get("deviation_pct", 0),
            "status": "open",
        }
        BOT_STATE.setdefault("quant_trades", []).append(trade_record)
        # Keep last 50 trades
        BOT_STATE["quant_trades"] = BOT_STATE["quant_trades"][-50:]
        _log_activity(
            f"QUANT: {side.upper()} {ticker} @ {price_cents}c x{count} (${cost:.2f})",
            "success"
        )

    return jsonify({"success": success, "result": result, "cost": cost, "count": count})


@app.route("/quant-stats")
def quant_stats():
    trades = BOT_STATE.get("quant_trades", [])
    return jsonify({
        "wins": BOT_STATE.get("quant_wins", 0),
        "losses": BOT_STATE.get("quant_losses", 0),
        "profit": round(BOT_STATE.get("quant_profit", 0), 2),
        "total_bets": BOT_STATE.get("quant_bets", 0),
        "win_rate": round(BOT_STATE.get("quant_wins", 0) / max(1, BOT_STATE.get("quant_wins", 0) + BOT_STATE.get("quant_losses", 0)) * 100, 1),
        "trades": trades[-20:],  # Last 20 trades for display
    })


def _generate_picks():
    """Heavy lifting — called by background thread only, never by HTTP."""
    now = datetime.datetime.utcnow()
    all_markets = fetch_all_markets()
    picks = []

    # Build Kalshi and other-platform market lists
    # GLOBAL: filter out all parlays upfront — they can't cross-platform match
    kalshi_markets = []
    other_markets = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        # Skip parlays globally — titles with multiple "yes " are multi-leg combos
        if m["platform"] == "kalshi" and _is_parlay_title(m.get("question", "")):
            continue
        # Hard filter: ONLY markets settling in 2026 or sooner
        # Money locked in 2030+ bets can't compound toward our $1M goal
        if m["platform"] == "kalshi":
            ct = m.get("close_time", "")
            if ct:
                try:
                    exp_year = datetime.datetime.fromisoformat(ct.replace("Z", "")).year
                    if exp_year > 2026:
                        continue
                except Exception:
                    pass
            kalshi_markets.append((nq, m))
        else:
            other_markets.append((nq, m))

    # Build keyword index for other markets
    other_kw_index = {}
    for idx_o, (nq_o, om) in enumerate(other_markets):
        for word in set(nq_o.split()):
            if word not in other_kw_index:
                other_kw_index[word] = set()
            other_kw_index[word].add(idx_o)

    # Platform liquidity weights
    PLAT_WEIGHT = PLAT_WEIGHT_GLOBAL

    def _time_bonus(market):
        """Heavily favor markets that settle SOON — that's where we compound."""
        ct = market.get("close_time")
        if not ct:
            return 0.1
        try:
            exp = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00").replace("+00:00", ""))
        except Exception:
            return 0.1
        days_left = max(0, (exp - now).total_seconds() / 86400)
        if days_left <= 1:
            return 3.0      # settles TODAY — highest priority
        elif days_left <= 7:
            return 2.5      # this week
        elif days_left <= 30:
            return 2.0      # this month
        elif days_left <= 90:
            return 1.5      # this quarter
        elif days_left <= 365:
            return 0.8      # this year — ok
        elif days_left <= 730:
            return 0.3      # 1-2 years — deprioritize
        else:
            return 0.05     # 2+ years — basically ignore

    # ── Strategy 1: Cross-platform consensus picks ──
    for nq_k, km in kalshi_markets:
        matches = []
        candidate_counts = {}
        for w in set(nq_k.split()):
            for idx_o in other_kw_index.get(w, ()):
                candidate_counts[idx_o] = candidate_counts.get(idx_o, 0) + 1
        candidates = [idx_o for idx_o, cnt in candidate_counts.items() if cnt >= 2]
        for idx_o in candidates:
            nq_o, om = other_markets[idx_o]
            sim = similarity(nq_k, nq_o, km["question"], om["question"])
            if sim >= 0.75:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                details = getattr(similarity, '_last_match_details', {}).copy()
                quality = match_quality_score(sim, details)
                matches.append({
                    "platform": om["platform"], "yes": om["yes"], "no": om["no"],
                    "similarity": round(sim, 3), "volume": om.get("volume", 0),
                    "match_quality": quality,
                })
        if not matches:
            continue

        total_weight = sum(PLAT_WEIGHT.get(m["platform"], 1.0) for m in matches)
        consensus_yes = sum(m["yes"] * PLAT_WEIGHT.get(m["platform"], 1.0) for m in matches) / total_weight
        deviation = abs(km["yes"] - consensus_yes)
        if deviation < 0.02:
            continue
        if deviation > 0.40:
            continue

        kalshi_vol = km.get("volume", 0)
        plat_prices = [f"{p['platform'].title()} {p['yes']*100:.0f}¢" for p in matches]
        k_price = km["yes"] * 100
        c_price = consensus_yes * 100
        dev_pct = deviation * 100
        if km["yes"] < consensus_yes:
            signal = "buy_yes"
            price_cents = km.get("yes_ask_cents") or int(km["yes"] * 100)
            edge = f"Kalshi YES at {k_price:.0f}¢ vs consensus {c_price:.0f}¢"
            thesis = f"Cross-platform consensus ({', '.join(plat_prices)}) prices this {dev_pct:.0f}% higher than Kalshi. "
            thesis += f"Buy YES at {k_price:.0f}¢ — consensus expects ~{c_price:.0f}¢."
            edge_reason = f"{len(matches)} other platform{'s' if len(matches)>1 else ''} price this at {c_price:.0f}¢ but Kalshi is selling at {k_price:.0f}¢ — that {dev_pct:.0f}% gap is our edge."
            potential = round((c_price - k_price) / 100, 2)
        else:
            signal = "buy_no"
            price_cents = km.get("no_ask_cents") or int(km["no"] * 100)
            edge = f"Kalshi YES at {k_price:.0f}¢ but consensus only {c_price:.0f}¢"
            thesis = f"Cross-platform consensus ({', '.join(plat_prices)}) prices this {dev_pct:.0f}% lower than Kalshi. "
            thesis += f"Buy NO at {price_cents}¢ — consensus expects YES to drop toward {c_price:.0f}¢."
            edge_reason = f"{len(matches)} other platform{'s' if len(matches)>1 else ''} say YES is only worth {c_price:.0f}¢ but Kalshi has it at {k_price:.0f}¢ — we profit on NO when it corrects."
            potential = round((k_price - c_price) / 100, 2)

        win_prob = min(0.95, consensus_yes if signal == "buy_yes" else 1 - consensus_yes)

        if deviation >= 0.20 and len(matches) >= 2 and kalshi_vol > 0:
            confidence = "HIGH"
        elif deviation >= 0.10 or len(matches) >= 2:
            confidence = "MEDIUM"
        else:
            confidence = "LOW"

        plat_bonus = 1 + 0.25 * (len(matches) - 1)
        time_b = _time_bonus(km)
        vol_bonus = 1.3 if kalshi_vol > 100 else 1.0 if kalshi_vol > 0 else 0.5
        score = win_prob * (1 + deviation) * plat_bonus * time_b * vol_bonus

        # Real win likelihood: consensus-validated probability, discounted by uncertainty
        # Cross-platform agreement = more reliable than single source
        real_win = win_prob * (0.85 + 0.05 * min(len(matches), 3))  # 85-100% of market prob depending on matches
        if kalshi_vol < 50:
            real_win *= 0.85  # low volume = less reliable price
        real_win = min(0.95, real_win)

        picks.append({
            "type": "consensus",
            "kalshi_ticker": km["id"],
            "kalshi_question": km["question"],
            "kalshi_yes_price": km["yes"],
            "kalshi_url": km["url"],
            "yes_label": km.get("yes_label", "Yes"),
            "no_label": km.get("no_label", "No"),
            "close_time": km.get("close_time"),
            "consensus_yes_price": round(consensus_yes, 4),
            "deviation": round(deviation, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": matches,
            "edge_summary": edge,
            "edge_reason": edge_reason,
            "thesis": thesis,
            "potential_profit_usd": potential,
            "confidence": confidence,
            "platform_count": len(matches),
            "match_quality": int(sum(m.get("match_quality", 50) for m in matches) / len(matches)) if matches else 0,
            "win_probability": round(win_prob, 4),
            "real_win_likelihood": round(real_win, 4),
            "score": round(score, 4),
            "volume": kalshi_vol,
            "is_sports": km.get("is_sports", False),
            "prices": {
                "kalshi": round(k_price, 1),
                **{p["platform"]: round(p["yes"] * 100, 1) for p in matches}
            },
        })

    # ── Strategy 2: Arbitrage pairs ──
    existing_tickers = {p["kalshi_ticker"] for p in picks}
    opps = find_opportunities(all_markets, min_similarity=0.85, max_cost=1.0)
    for opp in opps[:20]:
        buy_yes = opp["buy_yes"]
        buy_no = opp["buy_no"]
        kalshi_side = None
        matched_km = None
        if buy_yes["platform"] == "kalshi":
            kalshi_side = buy_yes
            other_side = buy_no
            signal = "buy_yes"
        elif buy_no["platform"] == "kalshi":
            kalshi_side = buy_no
            other_side = buy_yes
            signal = "buy_no"
        if not kalshi_side:
            continue
        # Find matching Kalshi market ticker
        ticker = ""
        for nq_k, km in kalshi_markets:
            if similarity(nq_k, normalize_question(opp["question_a"]), km["question"], opp["question_a"]) > 0.75:
                ticker = km["id"]; matched_km = km; break
            if similarity(nq_k, normalize_question(opp["question_b"]), km["question"], opp["question_b"]) > 0.75:
                ticker = km["id"]; matched_km = km; break
        if not ticker or ticker in existing_tickers:
            continue
        existing_tickers.add(ticker)
        price_cents = int(kalshi_side["price"] * 100)
        spread = abs(buy_yes["price"] - (1 - buy_no["price"]))
        kalshi_title = matched_km["question"] if matched_km else opp["question_a"]
        other_price = other_side["price"]
        edge = f"Arbitrage: buy {signal.replace('buy_','')} on Kalshi at {price_cents}¢, hedge on {other_side['platform'].title()}"
        thesis = f"Price spread of {opp['profit_pct']:.1f}% between Kalshi and {other_side['platform'].title()}. "
        thesis += f"Estimated profit: ${opp['estimated_profit']:.4f} per contract after fees."
        edge_reason = f"Price gap of {opp['profit_pct']:.1f}% between Kalshi and {other_side['platform'].title()} — buy here at {price_cents}¢ and profit when the gap closes."
        # Better win probability for arbitrage — use the consensus side price
        if signal == "buy_yes":
            win_prob = min(0.95, max(other_price, kalshi_side["price"]))
        else:
            win_prob = min(0.95, max(1 - other_price, 1 - kalshi_side["price"]))
        # Arbitrage: cross-platform validated, apply 90% confidence to market prob
        real_win = min(0.95, win_prob * 0.90)
        picks.append({
            "type": "arbitrage",
            "kalshi_ticker": ticker,
            "kalshi_question": kalshi_title,
            "kalshi_yes_price": buy_yes["price"] if buy_yes["platform"] == "kalshi" else 1 - buy_no["price"],
            "kalshi_url": kalshi_side["url"],
            "yes_label": matched_km.get("yes_label", "Yes") if matched_km else "Yes",
            "no_label": matched_km.get("no_label", "No") if matched_km else "No",
            "close_time": matched_km.get("close_time") if matched_km else None,
            "consensus_yes_price": buy_yes["price"] if buy_yes["platform"] != "kalshi" else 1 - buy_no["price"],
            "deviation": round(spread, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": [{"platform": other_side["platform"], "yes": round(1 - other_price, 4) if signal == "buy_no" else round(other_price, 4), "similarity": opp["similarity"]}],
            "edge_summary": edge,
            "edge_reason": edge_reason,
            "thesis": thesis,
            "potential_profit_usd": round(opp["estimated_profit"], 2),
            "confidence": "HIGH" if opp["estimated_profit"] > 0.05 else "MEDIUM" if opp["estimated_profit"] > 0.02 else "LOW",
            "platform_count": 1,
            "win_probability": round(win_prob, 4),
            "real_win_likelihood": round(real_win, 4),
            "score": round(opp["estimated_profit"] * 10 + 0.5, 4),
            "is_sports": matched_km.get("is_sports", False) if matched_km else False,
            "prices": {
                "kalshi": round(kalshi_side["price"] * 100, 1),
                other_side["platform"]: round(other_price * 100, 1),
            },
        })

    # ── Strategy 3: Kalshi picks with cross-platform validation ──
    # Every pick gets checked against other platforms for independent confirmation
    existing_tickers = {p["kalshi_ticker"] for p in picks}

    # Sort by volume (highest volume = most important markets)
    sorted_kalshi = sorted(kalshi_markets, key=lambda x: x[1].get("volume", 0), reverse=True)
    for nq_k, km in sorted_kalshi:
        if km["id"] in existing_tickers:
            continue
        if _is_parlay_title(km["question"]):
            continue
        kalshi_vol = km.get("volume", 0)

        # Tier A: Strong directional with volume >= 10
        # Tier B: High-volume (>=500) at any price
        if kalshi_vol >= 500:
            pass
        elif kalshi_vol >= 10 and (km["yes"] > 0.70 or km["yes"] < 0.30):
            pass
        else:
            continue

        # ── Cross-platform check for EVERY pick ──
        xplat_matches = []
        candidate_counts = {}
        for w in set(nq_k.split()):
            for idx_o in other_kw_index.get(w, ()):
                candidate_counts[idx_o] = candidate_counts.get(idx_o, 0) + 1
        candidates = [idx_o for idx_o, cnt in candidate_counts.items() if cnt >= 2]
        for idx_o in candidates:
            nq_o, om = other_markets[idx_o]
            sim = similarity(nq_k, nq_o, km["question"], om["question"])
            if sim >= 0.75:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                details = getattr(similarity, '_last_match_details', {}).copy()
                quality = match_quality_score(sim, details)
                xplat_matches.append({
                    "platform": om["platform"], "yes": om["yes"],
                    "similarity": round(sim, 3), "match_quality": quality,
                })

        has_xplat = len(xplat_matches) > 0

        # Determine signal
        if km["yes"] >= 0.55:
            signal = "buy_yes"
            win_prob = km["yes"]
            price_cents = km.get("yes_ask_cents") or int(km["yes"] * 100)
        else:
            signal = "buy_no"
            win_prob = 1 - km["yes"]
            price_cents = km.get("no_ask_cents") or int(km["no"] * 100)

        side_label = "YES" if signal == "buy_yes" else "NO"
        k_price = km["yes"] * 100

        # If we have cross-platform data, use it for better probability estimate
        if has_xplat:
            total_w = sum(PLAT_WEIGHT.get(m["platform"], 1.0) for m in xplat_matches)
            xplat_consensus = sum(m["yes"] * PLAT_WEIGHT.get(m["platform"], 1.0) for m in xplat_matches) / total_w
            xplat_price = xplat_consensus * 100
            plat_names = [f"{m['platform'].title()} {m['yes']*100:.0f}¢" for m in xplat_matches]
            pick_type = "cross_validated"
            platform_count = len(xplat_matches)

            # Use cross-platform consensus for win probability
            if signal == "buy_yes":
                win_prob = max(km["yes"], xplat_consensus)
            else:
                win_prob = max(1 - km["yes"], 1 - xplat_consensus)

            deviation = abs(km["yes"] - xplat_consensus)
            edge = f"Kalshi {k_price:.0f}¢ vs {', '.join(plat_names)}"
            if deviation >= 0.05:
                edge_reason = f"Checked {platform_count} other platform{'s' if platform_count > 1 else ''}: they price this at {xplat_price:.0f}¢ vs Kalshi's {k_price:.0f}¢ — {deviation*100:.0f}% edge in our favor."
            else:
                edge_reason = f"Checked {platform_count} other platform{'s' if platform_count > 1 else ''}: they agree at ~{xplat_price:.0f}¢ (Kalshi {k_price:.0f}¢). Prices align — strong confidence in market price."
        else:
            pick_type = "kalshi_only"
            platform_count = 0
            xplat_matches = []
            deviation = abs(km["yes"] - 0.5)
            edge = f"{win_prob*100:.0f}% on Kalshi — buy {side_label} at {price_cents}¢"
            if kalshi_vol >= 1000:
                edge += f" ({kalshi_vol:,} vol)"
            edge_reason = f"No match found on other platforms. Kalshi-only at {price_cents}¢ with {kalshi_vol:,} trades — use caution, no independent validation."

        # Score: cross-platform validated picks score much higher
        time_b = _time_bonus(km)
        if kalshi_vol >= 10000:
            vol_bonus = 2.0
        elif kalshi_vol >= 1000:
            vol_bonus = 1.5
        elif kalshi_vol >= 100:
            vol_bonus = 1.2
        else:
            vol_bonus = 1.0

        xplat_bonus = 1.5 + 0.25 * platform_count if has_xplat else 0.5
        directional_strength = abs(km["yes"] - 0.5) * 2
        score = win_prob * time_b * vol_bonus * xplat_bonus * (0.3 + directional_strength * 0.3)

        if has_xplat and win_prob >= 0.70:
            confidence = "HIGH"
        elif has_xplat or (win_prob >= 0.80 and kalshi_vol >= 100):
            confidence = "MEDIUM"
        elif win_prob >= 0.65 and kalshi_vol >= 50:
            confidence = "MEDIUM"
        else:
            confidence = "LOW"

        thesis = f"Kalshi at {km['yes']*100:.0f}¢ YES / {km['no']*100:.0f}¢ NO ({kalshi_vol:,} vol)."
        if has_xplat:
            thesis += f" Cross-checked with {platform_count} platform{'s' if platform_count > 1 else ''}."
        thesis += f" Buy {side_label} at {price_cents}¢ for {(100-price_cents)}¢ profit if correct."

        # Trust level based on validation
        if has_xplat and platform_count >= 2:
            real_win = min(0.95, win_prob * 0.90)
        elif has_xplat:
            real_win = min(0.92, win_prob * 0.85)
        else:
            vol_trust = 0.70 if kalshi_vol >= 5000 else 0.60 if kalshi_vol >= 1000 else 0.50 if kalshi_vol >= 100 else 0.40
            real_win = min(0.90, win_prob * vol_trust)

        prices_dict = {"kalshi": round(k_price, 1)}
        for xm in xplat_matches:
            prices_dict[xm["platform"]] = round(xm["yes"] * 100, 1)

        picks.append({
            "type": pick_type,
            "kalshi_ticker": km["id"],
            "kalshi_question": km["question"],
            "kalshi_yes_price": km["yes"],
            "kalshi_url": km["url"],
            "yes_label": km.get("yes_label", "Yes"),
            "no_label": km.get("no_label", "No"),
            "close_time": km.get("close_time"),
            "consensus_yes_price": round(win_prob, 4),
            "deviation": round(deviation, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": xplat_matches,
            "edge_summary": edge,
            "edge_reason": edge_reason,
            "thesis": thesis,
            "potential_profit_usd": round((100 - price_cents) / 100, 2),
            "confidence": confidence,
            "platform_count": platform_count,
            "win_probability": round(win_prob, 4),
            "real_win_likelihood": round(real_win, 4),
            "score": round(score, 4),
            "volume": kalshi_vol,
            "is_sports": km.get("is_sports", False),
            "prices": prices_dict,
        })
        existing_tickers.add(km["id"])

    MAX_SETTLE_DAYS = 365 * 5  # No limit — we sell positions for profit, don't wait for settlement

    def _days_to_settle(p):
        ct = p.get("close_time")
        if not ct:
            return 9999
        try:
            exp = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00").replace("+00:00", ""))
            return max(0, (exp - now).total_seconds() / 86400)
        except Exception:
            return 9999

    # ── Filter ALL picks to 90-day max settlement ──
    # Filter: must settle in the future AND within MAX_SETTLE_DAYS
    picks = [p for p in picks if 0 < _days_to_settle(p) <= MAX_SETTLE_DAYS]
    # Filter: skip terrible risk/reward globally (not just hero)
    # Min 15c: avoid illiquid penny markets that can't be sold
    # Max 90c: avoid expensive low-upside markets
    picks = [p for p in picks if 15 <= p.get("price_cents", 50) <= 90]
    # Deduplicate: only 1 pick per base event question
    seen_base_q = set()
    deduped_picks = []
    for p in picks:
        import re as _re
        base = _re.sub(r'\s*(q[1-4]\s*20\d{2}|before\s+20\d{2}|by\s+20\d{2})$', '', p.get("kalshi_question", "").lower().strip())[:60]
        event_prefix = p.get("kalshi_ticker", "")[:10]
        key = base + "|" + event_prefix
        if key not in seen_base_q:
            seen_base_q.add(key)
            deduped_picks.append(p)
    picks = deduped_picks

    # ── Split into sports & non-sports, return exactly 10 each ──
    sports_picks = sorted([p for p in picks if p.get("is_sports")], key=lambda x: x["score"], reverse=True)[:10]
    nonsports_picks = sorted([p for p in picks if not p.get("is_sports")], key=lambda x: x["score"], reverse=True)[:10]

    # ── Top 5 hero picks: ranked by cross-platform confidence ──

    def _days_to_settle(p):
        ct = p.get("close_time")
        if not ct:
            return 9999
        try:
            exp = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00").replace("+00:00", ""))
            return max(0, (exp - now).total_seconds() / 86400)
        except Exception:
            return 9999

    def _is_hero_worthy(p):
        # 90-day filter already applied globally above
        # Must have SOME volume (people actually trading)
        if (p.get("volume") or 0) < 10:
            return False
        # Must have some edge — at least 5% deviation
        if p.get("deviation", 0) < 0.05:
            return False
        # Filter out terrible risk/reward — if you pay 90¢+ to win $1,
        # the profit is tiny but the loss is huge. Skip these.
        price = p.get("price_cents", 50)
        if price > 90:
            return False
        # Also skip super cheap (<5¢) — usually longshots with no edge
        if price < 5:
            return False
        return True

    hero_candidates = [p for p in picks if _is_hero_worthy(p)]
    # Rank by: edge size * platform validation * volume (liquidity)
    # This finds the biggest money-making opportunities
    def _hero_sort_key(p):
        # Cross-platform = much more trustworthy
        is_xplat = 3.0 if p.get("type") in ("consensus", "arbitrage") else 1.5 if p.get("type") == "cross_validated" else 1.0
        # More platforms = more confidence
        plat_count = 1 + p.get("platform_count", 0) * 0.5
        # Edge size = how mispriced it is = our profit opportunity
        deviation = p.get("deviation", 0)
        # Volume = liquidity = can we actually get in and out
        vol = min(3.0, 1.0 + (p.get("volume", 0) / 5000))
        # Profit potential per contract (sweet spot is 20-70c cost)
        price = p.get("price_cents", 50)
        profit_ratio = (100 - price) / max(1, price)  # e.g. 30c cost = 2.33x
        return is_xplat * plat_count * (1 + deviation * 3) * vol * (1 + profit_ratio * 0.3)
    all_sorted = sorted(hero_candidates, key=_hero_sort_key, reverse=True)
    # Deduplicate hero: only 1 pick per base event (avoid 4x recession variants)
    seen_events = set()
    hero_picks = []
    for p in all_sorted:
        # Normalize: strip trailing date/quarter suffixes for grouping
        q = p.get("kalshi_question", "").lower().strip()
        # Remove common suffixes that create duplicates
        import re as _re
        base_q = _re.sub(r'\s*(q[1-4]\s*20\d{2}|before\s+20\d{2}|by\s+20\d{2}|in\s+20\d{2}|on\s+dec\s+\d+.*|20\d{2})$', '', q).strip()
        # Also use event_ticker prefix as grouping key
        event_key = p.get("kalshi_ticker", "")[:12]  # first 12 chars of ticker
        group_key = base_q[:50] + "|" + event_key
        if group_key not in seen_events:
            seen_events.add(group_key)
            hero_picks.append(p)
        if len(hero_picks) >= 5:
            break
    for i, p in enumerate(hero_picks):
        p["hero_rank"] = i + 1

    # ── Miscellaneous: interesting picks not in sports/nonsports top 10 ──
    top_tickers = {p["kalshi_ticker"] for p in sports_picks + nonsports_picks}
    misc_candidates = [p for p in picks if p["kalshi_ticker"] not in top_tickers]
    misc_picks = sorted(misc_candidates, key=lambda x: x["score"], reverse=True)[:10]

    # Re-rank within each category
    for i, p in enumerate(sports_picks):
        p["rank"] = i + 1
    for i, p in enumerate(nonsports_picks):
        p["rank"] = i + 1
    for i, p in enumerate(misc_picks):
        p["rank"] = i + 1

    all_ranked = hero_picks + sports_picks + nonsports_picks + misc_picks
    # Deduplicate for news enrichment
    seen_tickers_ranked = set()
    unique_ranked = []
    for p in all_ranked:
        if p["kalshi_ticker"] not in seen_tickers_ranked:
            seen_tickers_ranked.add(p["kalshi_ticker"])
            unique_ranked.append(p)
    all_ranked = unique_ranked

    # ── Enrich top picks with news research (parallel, fast) ──
    def _add_news(pick):
        try:
            research = research_market(pick["kalshi_question"])
            pick["news"] = research["headlines"][:3]  # top 3 headlines
            pick["news_sentiment"] = research["sentiment"]
            pick["news_count"] = research["news_count"]
            # Boost/penalize score based on news sentiment alignment
            if research["sentiment"] == "bullish" and pick["signal"] == "buy_yes":
                pick["news_confirms"] = True
            elif research["sentiment"] == "bearish" and pick["signal"] == "buy_no":
                pick["news_confirms"] = True
            else:
                pick["news_confirms"] = False
        except Exception:
            pick["news"] = []
            pick["news_sentiment"] = "neutral"
            pick["news_count"] = 0
            pick["news_confirms"] = False

    with ThreadPoolExecutor(max_workers=8) as pool:
        pool.map(_add_news, all_ranked)

    # ── Save pick history for win/loss tracking ──
    existing_hist_tickers = {ph["ticker"] for ph in BOT_STATE.get("pick_history", [])}
    for p in all_ranked:
        tk = p.get("kalshi_ticker", "")
        if tk and tk not in existing_hist_tickers:
            BOT_STATE.setdefault("pick_history", []).append({
                "ticker": tk,
                "type": p.get("type", "unknown"),
                "signal": p.get("signal", ""),
                "price_cents": p.get("price_cents", 0),
                "win_probability": p.get("win_probability", 0),
                "platform_count": p.get("platform_count", 0),
                "confidence": p.get("confidence", ""),
                "timestamp": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            })
            existing_hist_tickers.add(tk)
    # Trim to last 500
    BOT_STATE["pick_history"] = BOT_STATE.get("pick_history", [])[-500:]
    _save_state()

    result = {"picks": all_ranked, "hero": [p["kalshi_ticker"] for p in hero_picks], "misc": [p["kalshi_ticker"] for p in misc_picks], "sports_count": len(sports_picks), "nonsports_count": len(nonsports_picks), "hero_count": len(hero_picks), "misc_count": len(misc_picks), "total_scanned": len(all_markets)}
    _picks_cache["data"] = result
    _picks_cache["time"] = datetime.datetime.utcnow()
    return result


@app.route("/today-picks")
def today_picks():
    """Return Kalshi markets that settle today — quick win/loss opportunities."""
    all_markets = fetch_all_markets()
    now = datetime.datetime.utcnow()
    today_end = now.replace(hour=23, minute=59, second=59)
    tomorrow_end = today_end + datetime.timedelta(hours=12)  # include early morning settles

    today_markets = []
    seen_tickers = set()
    for m in all_markets:
        if m["platform"] != "kalshi":
            continue
        # Skip parlays (multi-outcome markets)
        if _is_parlay_title(m.get("question", "")):
            continue
        # Skip duplicates
        if m["id"] in seen_tickers:
            continue
        seen_tickers.add(m["id"])
        # Must have some volume (real market)
        if (m.get("volume") or 0) < 5:
            continue
        ct = m.get("close_time")
        if not ct:
            continue
        try:
            close_dt = datetime.datetime.fromisoformat(ct.replace("Z", "+00:00").replace("+00:00", ""))
        except Exception:
            try:
                close_dt = datetime.datetime.strptime(ct[:19], "%Y-%m-%dT%H:%M:%S")
            except Exception:
                continue
        if close_dt < now or close_dt > tomorrow_end:
            continue
        # Calculate time remaining
        diff = close_dt - now
        hrs = int(diff.total_seconds() // 3600)
        mins = int((diff.total_seconds() % 3600) // 60)
        if hrs > 0:
            time_left = f"{hrs}h {mins}m"
        else:
            time_left = f"{mins}m"

        # Don't show 50/50 markets — must have some directional signal
        if 0.40 <= m["yes"] <= 0.60:
            continue

        price_cents = min(int(m["yes"] * 100), int(m["no"] * 100))
        cheaper_side = "buy_yes" if m["yes"] <= m["no"] else "buy_no"
        potential = round((100 - price_cents) / 100, 2)

        today_markets.append({
            "kalshi_ticker": m["id"],
            "kalshi_question": m["question"],
            "kalshi_url": m["url"],
            "kalshi_yes_price": m["yes"],
            "signal": cheaper_side,
            "price_cents": price_cents,
            "close_time": ct,
            "time_left": time_left,
            "time_left_seconds": int(diff.total_seconds()),
            "potential_profit_usd": potential,
            "yes_price": round(m["yes"] * 100),
            "no_price": round(m["no"] * 100),
            "is_sports": m.get("is_sports", False),
        })

    # Sort by soonest to settle
    today_markets.sort(key=lambda x: x["time_left_seconds"])
    return jsonify({"picks": today_markets[:20], "total": len(today_markets)})


@app.route("/scan", methods=["POST"])
def manual_scan():
    """Trigger an immediate bot scan + quant strategy run."""
    import threading
    def _do_scan():
        try:
            _log_activity("🔍 Manual scan triggered from dashboard")
            run_bot_scan()
            all_mkts = fetch_all_markets()
            if all_mkts:
                run_quant_strategies(all_mkts)
            _log_activity("✅ Manual scan completed")
        except Exception as e:
            _log_activity(f"❌ Manual scan error: {e}")
    t = threading.Thread(target=_do_scan, daemon=True)
    t.start()
    return jsonify({"status": "scan_started", "message": "Manual scan triggered — check /trades for results"})


@app.route("/config", methods=["POST"])
def config():
    data = request.get_json(force=True)
    allowed = {"enabled", "max_bet_usd", "max_daily_usd", "min_balance_usd", "min_deviation",
                "min_platforms", "min_volume", "min_cash_reserve_pct", "max_open_positions",
                "scan_interval_seconds"}
    updated = {}
    for key in allowed:
        if key in data:
            BOT_CONFIG[key] = data[key]
            updated[key] = data[key]
    return jsonify({"updated": updated, "config": BOT_CONFIG})


@app.route("/execute-trade", methods=["POST"])
def execute_trade():
    data = request.get_json(force=True)
    ticker = data.get("ticker")
    side = data.get("side")
    price_cents = data.get("price_cents")
    if not all([ticker, side, price_cents]):
        return jsonify({"error": "Missing ticker, side, or price_cents"}), 400
    pc = int(price_cents)
    count = max(1, 500 // pc) if pc > 0 else 1  # target $5 per trade
    result = place_kalshi_order(ticker, side, pc, count=count)
    trade_record = {
        "timestamp": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        "ticker": ticker,
        "question": data.get("question", ""),
        "side": side,
        "price_cents": pc,
        "count": count,
        "cost_usd": (pc * count) / 100.0,
        "deviation": data.get("deviation", 0),
        "consensus_price": data.get("consensus_price", 0),
        "kalshi_price": data.get("kalshi_price", 0),
        "matching_platforms": data.get("matching_platforms", []),
        "result": result,
        "success": "error" not in result,
        "manual": True,
    }
    BOT_STATE["all_trades"].append(trade_record)
    BOT_STATE["trades_today"].append(trade_record)
    if trade_record["success"]:
        BOT_STATE["daily_spent_usd"] += trade_record["cost_usd"]
    _save_state()
    return jsonify(trade_record)


@app.route("/sell-position", methods=["POST"])
def sell_position():
    """Sell an open position."""
    data = request.get_json(force=True)
    ticker = data.get("ticker")
    side = data.get("side")
    price_cents = data.get("price_cents")
    count = data.get("count", 1)
    if not all([ticker, side, price_cents]):
        return jsonify({"error": "Missing ticker, side, or price_cents"}), 400
    result = sell_kalshi_position(ticker, side, int(price_cents), int(count))
    trade_record = {
        "timestamp": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        "ticker": ticker,
        "side": side,
        "action": "sell",
        "price_cents": int(price_cents),
        "count": int(count),
        "result": result,
        "success": "error" not in result,
    }
    BOT_STATE["all_trades"].append(trade_record)
    _save_state()
    return jsonify(trade_record)


@app.route("/sell-all-losers", methods=["POST"])
def sell_all_losers():
    """Sell all positions that are currently underwater."""
    positions = check_position_prices()
    sold = []
    skipped = []
    errors = []
    for p in positions:
        count = p.get("count", 0)
        if count <= 0:
            continue
        pnl_pct = p.get("pnl_pct")
        entry_price = p.get("entry_price")
        current_price = p.get("current_price")
        ticker = p.get("ticker", "")
        side = p.get("side", "")
        title = p.get("title", ticker)

        # Skip positions we can't price
        if current_price is None or entry_price is None:
            skipped.append({"ticker": ticker, "title": title[:40], "reason": "no price data"})
            continue

        # Only sell losers (negative P&L)
        if pnl_pct is not None and pnl_pct >= 0:
            skipped.append({"ticker": ticker, "title": title[:40], "reason": "winning/flat"})
            continue

        # Sell at current market price (1c below to ensure fill)
        sell_price = max(1, current_price - 1)
        try:
            result = sell_kalshi_position(ticker, side, sell_price, count)
            if "error" not in result:
                sold.append({
                    "ticker": ticker, "title": title[:40], "side": side,
                    "count": count, "price": sell_price, "pnl_pct": pnl_pct,
                })
                _log_activity(
                    f"SOLD LOSER: {side.upper()} {ticker} x{count} @ {sell_price}c ({pnl_pct:+.1f}%) | {title[:30]}",
                    "warning"
                )
            else:
                errors.append({"ticker": ticker, "title": title[:40], "error": str(result.get("error", ""))[:60]})
        except Exception as e:
            errors.append({"ticker": ticker, "title": title[:40], "error": str(e)[:60]})

    _save_state()
    return jsonify({
        "sold": len(sold),
        "skipped": len(skipped),
        "errors": len(errors),
        "sold_details": sold,
        "skipped_details": skipped,
        "error_details": errors,
    })


@app.route("/position-monitor")
def position_monitor():
    """Get all open positions with current prices and P&L."""
    positions = check_position_prices()
    return jsonify({
        "positions": positions,
        "auto_exit_enabled": BOT_CONFIG.get("enabled", False),
        "take_profit_pct": TAKE_PROFIT_PCT,
        "stop_loss_pct": STOP_LOSS_PCT,
    })


@app.route("/")
def dashboard():
    return DASHBOARD_HTML


# ---------------------------------------------------------------------------
# Dashboard HTML
# ---------------------------------------------------------------------------

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>TradeShark</title>
<link rel="icon" href="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'><text y='.9em' font-size='90'>🦈</text></svg>">
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #0d0d0d; color: #e0e0e0; overflow-x: hidden; -webkit-font-smoothing: antialiased; }
.container { max-width: 1100px; margin: 0 auto; padding: 0 20px 40px; }
/* Ticker bar */
.ticker-bar { display: flex; align-items: center; justify-content: center; gap: 24px; padding: 6px 20px; background: #0a0a0a; border-bottom: 1px solid #1a1a1a; font-size: 12px; overflow-x: auto; }
.ticker-item { display: flex; align-items: center; gap: 6px; white-space: nowrap; }
.ticker-symbol { color: #666; font-weight: 600; font-size: 11px; letter-spacing: 0.5px; }
.ticker-price { color: #ccc; font-weight: 600; font-variant-numeric: tabular-nums; }
.ticker-chg { font-size: 11px; font-weight: 600; }
.ticker-chg.up { color: #00dc5a; }
.ticker-chg.down { color: #ff5000; }
/* Portfolio breakdown */
.portfolio-breakdown { display: flex; align-items: center; justify-content: center; gap: 16px; margin-top: 12px; }
.breakdown-item { display: flex; flex-direction: column; align-items: center; gap: 2px; }
.breakdown-label { font-size: 11px; color: #666; font-weight: 500; text-transform: uppercase; letter-spacing: 0.5px; }
.breakdown-val { font-size: 16px; color: #ccc; font-weight: 600; }
.breakdown-dot { width: 3px; height: 3px; border-radius: 50%; background: #333; }
.header { display: flex; align-items: center; justify-content: space-between; padding: 12px 24px; position: sticky; top: 28px; z-index: 100; background: rgba(13,13,13,0.95); backdrop-filter: blur(12px); border-bottom: 1px solid #1a1a1a; margin: 0 -20px 0; overflow: visible; }
.header-left { display: flex; align-items: center; gap: 12px; padding-left: 20px; }
.logo { width: 44px; height: 44px; filter: drop-shadow(0 0 8px rgba(200,160,50,0.6)); flex-shrink: 0; }
h1 { font-size: 24px; color: #fff; font-weight: 800; letter-spacing: -0.5px; margin: 0; }
h1 span { background: linear-gradient(135deg, #8b5e28, #c9963a, #dab060, #a87530); -webkit-background-clip: text; -webkit-text-fill-color: transparent; background-clip: text; }
.subtitle { display: none; }
/* Toggle switch */
.switch { position: relative; width: 48px; height: 26px; flex-shrink: 0; }
.switch input { opacity: 0; width: 0; height: 0; }
.slider { position: absolute; cursor: pointer; top: 0; left: 0; right: 0; bottom: 0; background: #333; border-radius: 26px; transition: 0.3s; }
.slider:before { content: ''; position: absolute; height: 20px; width: 20px; left: 3px; bottom: 3px; background: #888; border-radius: 50%; transition: 0.3s; }
input:checked + .slider { background: #00dc5a; }
input:checked + .slider:before { transform: translateX(22px); background: #fff; }
.toggle-label { font-size: 13px; color: #999; font-weight: 500; }
.toggle-label.active { color: #00dc5a; }

/* Big portfolio value */
.portfolio-hero { text-align: center; padding: 40px 20px 8px; }
.portfolio-value { font-size: 28px; font-weight: 700; color: #fff; letter-spacing: -0.5px; line-height: 1; }
.portfolio-change { font-size: 16px; font-weight: 600; margin-top: 6px; }
.portfolio-change.up { color: #00dc5a; }
.portfolio-change.down { color: #ff5000; }
.portfolio-change.flat { color: #666; }

/* Chart */
.chart-section { padding: 0 20px 20px; }
.chart-canvas { width: 100%; height: 180px; position: relative; }
.chart-canvas canvas { width: 100%; height: 100%; }

/* Quick stats row */
.stats-row { display: grid; grid-template-columns: repeat(auto-fit, minmax(100px, 1fr)); gap: 1px; background: #1a1a1a; border-radius: 12px; overflow: hidden; margin: 0 0 20px; }
.stat-card { background: #141414; padding: 14px 8px; text-align: center; }
.stat-label { font-size: 10px; color: #555; font-weight: 600; margin-bottom: 6px; text-transform: uppercase; letter-spacing: 0.5px; }
.stat-value { font-size: 18px; font-weight: 700; color: #fff; }
.stat-value.green { color: #00dc5a; }
.stat-value.red { color: #ff5000; }

/* Tabs */
.tabs { display: flex; gap: 0; border-bottom: 1px solid #222; margin-bottom: 24px; }
.tab { flex: 1; padding: 14px 0; font-size: 14px; font-weight: 600; color: #555; cursor: pointer; border-bottom: 2px solid transparent; transition: all 0.2s; white-space: nowrap; background: none; border-top: none; border-left: none; border-right: none; font-family: inherit; text-align: center; }
.tab:hover { color: #aaa; }
.tab.active { color: #fff; border-bottom-color: #00dc5a; }
.tab-content { display: none; }
.tab-content.active { display: block; }

/* Section headers */
.section { margin-bottom: 28px; }
.section-title { font-size: 15px; font-weight: 700; color: #eee; margin-bottom: 14px; display: flex; align-items: center; gap: 10px; letter-spacing: -0.2px; }
.badge { background: #1f1f1f; padding: 2px 10px; border-radius: 20px; font-size: 12px; color: #999; font-weight: 600; }
.refresh-btn { background: none; border: 1px solid #333; color: #666; padding: 6px 14px; border-radius: 8px; cursor: pointer; font-size: 12px; margin-left: auto; font-family: inherit; font-weight: 500; transition: all 0.2s; }
.refresh-btn:hover { border-color: #555; color: #aaa; }

/* Tables */
table { width: 100%; border-collapse: collapse; }
th { text-align: left; padding: 10px 12px; font-size: 11px; color: #666; font-weight: 600; text-transform: uppercase; letter-spacing: 0.5px; border-bottom: 1px solid #1f1f1f; }
td { padding: 12px; border-bottom: 1px solid #141414; font-size: 13px; color: #ccc; }
tr:hover { background: rgba(255,255,255,0.02); }
.confidence { display: inline-block; padding: 3px 10px; border-radius: 20px; font-size: 11px; font-weight: 600; }
.conf-high { background: rgba(0,220,90,0.1); color: #00dc5a; }
.conf-med { background: rgba(255,180,0,0.1); color: #ffb400; }
.conf-low { background: rgba(255,80,0,0.1); color: #ff5000; }
.trade-btn { background: none; color: #00dc5a; border: 1px solid #00dc5a; padding: 6px 14px; border-radius: 8px; cursor: pointer; font-size: 12px; font-weight: 600; font-family: inherit; transition: all 0.2s; }
.trade-btn:hover { background: #00dc5a; color: #000; }
.trade-btn:disabled { border-color: #333; color: #444; cursor: not-allowed; background: none; }
.side-yes { color: #00dc5a; font-weight: 600; }
.side-no { color: #ff5000; font-weight: 600; }
.result-win { color: #00dc5a; }
.result-loss { color: #ff5000; }
.result-pending { color: #ffb400; }
.empty { text-align: center; padding: 40px; color: #444; font-size: 14px; }
.loading { text-align: center; padding: 24px; color: #444; font-size: 14px; }
a { color: #5b8def; text-decoration: none; }
a:hover { color: #7da5f5; }

/* Activity feed */
.activity-bar { max-height: 300px; overflow-y: auto; }
.activity-bar::-webkit-scrollbar { width: 4px; }
.activity-bar::-webkit-scrollbar-thumb { background: #333; border-radius: 4px; }
.activity-line { display: flex; gap: 10px; padding: 8px 0; border-bottom: 1px solid #141414; align-items: center; }
.activity-line .time { color: #555; font-size: 12px; min-width: 70px; flex-shrink: 0; font-variant-numeric: tabular-nums; }
.activity-line .dot { width: 6px; height: 6px; border-radius: 50%; flex-shrink: 0; }
.activity-line .dot.info { background: #5b8def; }
.activity-line .dot.success { background: #00dc5a; }
.activity-line .dot.error { background: #ff5000; }
.activity-line .msg { color: #999; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; font-size: 13px; }
.activity-line .msg.success { color: #00dc5a; }
.activity-line .msg.error { color: #ff5000; }
@keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.3; } }

/* Portfolio positions */
.portfolio-tile { display: none; }
.portfolio-stats { display: none; }
.pos-scroll { max-height: 600px; overflow-y: auto; border-radius: 12px; }
.pos-scroll::-webkit-scrollbar { width: 6px; }
.pos-scroll::-webkit-scrollbar-thumb { background: #333; border-radius: 3px; }
.pos-table-compact { width: 100%; border-collapse: collapse; }
.pos-table-compact thead { position: sticky; top: 0; z-index: 1; }
.pos-table-compact th { text-align: left; padding: 10px 12px; font-size: 11px; color: #666; font-weight: 600; text-transform: uppercase; letter-spacing: 0.5px; border-bottom: 1px solid #1f1f1f; background: #141414; }
.pos-table-compact td { padding: 10px 12px; font-size: 13px; color: #ccc; border-bottom: 1px solid #1a1a1a; }
.pos-table-compact tr:hover { background: rgba(255,255,255,0.02); }
.pos-count { font-size: 13px; color: #999; }
.wr-bar { height: 4px; background: #1a1a1a; margin-top: 4px; border-radius: 4px; overflow: hidden; }
.wr-bar .fill { height: 100%; border-radius: 4px; }

/* Top Picks cards */
.top-picks { margin-bottom: 20px; }
.picks-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(280px, 1fr)); gap: 12px; }
.pick-card { background: #141414; border: 1px solid #1f1f1f; padding: 16px; border-radius: 12px; position: relative; display: flex; flex-direction: column; transition: border-color 0.2s; }
.pick-card:hover { border-color: #333; }
.pick-rank { position: absolute; top: 12px; right: 14px; font-size: 16px; font-weight: 800; color: #222; }
.pick-header { display: flex; align-items: center; gap: 6px; margin-bottom: 8px; flex-wrap: wrap; }
.pick-signal { font-size: 11px; font-weight: 700; padding: 3px 8px; border-radius: 6px; }
.pick-signal.yes { background: rgba(0,220,90,0.12); color: #00dc5a; }
.pick-signal.no { background: rgba(255,80,0,0.12); color: #ff5000; }
.pick-conf { font-size: 10px; padding: 2px 8px; border-radius: 6px; font-weight: 600; }
.pick-conf.high { color: #00dc5a; background: rgba(0,220,90,0.08); }
.pick-conf.medium { color: #ffb400; background: rgba(255,180,0,0.08); }
.pick-conf.low { color: #ff5000; background: rgba(255,80,0,0.08); }
.pick-question { font-size: 13px; color: #e0e0e0; margin-bottom: 6px; font-weight: 600; line-height: 1.4; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; }
.pick-question a { color: #e0e0e0; }
.pick-question a:hover { color: #fff; }
.pick-edge { font-size: 12px; color: #888; margin-bottom: 4px; font-weight: 500; overflow: hidden; white-space: nowrap; text-overflow: ellipsis; }
.pick-thesis { display: none; }
.pick-chart { width: 100%; height: 60px; margin: 6px 0; position: relative; flex-shrink: 0; }
.pick-chart canvas { width: 100%; height: 100%; }
.pick-footer { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; margin-top: auto; padding-top: 8px; }
.pick-meta { font-size: 11px; color: #666; }
.pick-meta b { color: #999; }
.pick-profit { font-size: 13px; color: #00dc5a; font-weight: 700; }
.pick-execute { background: none; color: #00dc5a; border: 1px solid #00dc5a; padding: 8px 12px; border-radius: 8px; cursor: pointer; font-size: 12px; font-weight: 600; font-family: inherit; width: 100%; margin-top: 8px; transition: all 0.2s; }
.pick-execute:hover { background: #00dc5a; color: #000; }
.pick-execute:disabled { border-color: #333; color: #444; cursor: not-allowed; background: none; }

/* Hero picks */
.hero-section { margin-bottom: 24px; }
.hero-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 12px; width: 100%; }
.hero-card { background: #141414; border: 1px solid #1f1f1f; padding: 16px; border-radius: 12px; position: relative; display: flex; flex-direction: column; min-width: 0; overflow: hidden; word-break: break-word; transition: border-color 0.2s; }
.hero-card:hover { border-color: #00dc5a; }
.hero-rank { position: absolute; top: 8px; right: 12px; font-size: 18px; font-weight: 800; color: #1f1f1f; }
.hero-prob { font-size: 28px; font-weight: 800; color: #00dc5a; line-height: 1; }
.hero-label { font-size: 10px; color: #666; text-transform: uppercase; letter-spacing: 0.5px; margin-top: 2px; font-weight: 500; }
.hero-question { font-size: 13px; color: #e0e0e0; margin: 8px 0; font-weight: 600; line-height: 1.4; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; }
.hero-question a { color: #e0e0e0; }
.hero-question a:hover { color: #fff; }
.hero-edge-reason { font-size: 11px; color: #888; line-height: 1.4; margin: 2px 0 8px; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; font-style: italic; }
.hero-signal { font-size: 10px; font-weight: 700; padding: 2px 8px; border-radius: 6px; display: inline-block; }
.hero-signal.yes { background: rgba(0,220,90,0.12); color: #00dc5a; }
.hero-signal.no { background: rgba(255,80,0,0.12); color: #ff5000; }
.hero-footer { display: flex; align-items: center; justify-content: space-between; gap: 6px; margin-top: auto; padding-top: 8px; }
.hero-execute { background: rgba(0,220,90,0.08); color: #00dc5a; border: 1px solid rgba(0,220,90,0.3); padding: 6px 12px; border-radius: 8px; cursor: pointer; font-size: 12px; font-weight: 600; font-family: inherit; white-space: nowrap; transition: all 0.2s; }
.hero-execute:hover { background: #00dc5a; color: #000; border-color: #00dc5a; }
.hero-execute:disabled { border-color: #333; color: #444; cursor: not-allowed; background: none; }

/* Two column layout */
.two-col { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; margin-bottom: 20px; }
@media (max-width: 900px) { .two-col { grid-template-columns: 1fr; } }

/* Toast */
.toast-container { position: fixed; top: 80px; right: 20px; z-index: 9999; display: flex; flex-direction: column; gap: 8px; pointer-events: none; }
.toast { pointer-events: auto; padding: 14px 20px; border-radius: 12px; font-size: 13px; font-family: inherit; max-width: 380px; animation: toastIn 0.3s ease, toastOut 0.4s ease 4.6s; opacity: 0; word-break: break-word; backdrop-filter: blur(8px); }
.toast.success { background: rgba(0,220,90,0.15); border: 1px solid rgba(0,220,90,0.3); color: #00dc5a; }
.toast.error { background: rgba(255,80,0,0.15); border: 1px solid rgba(255,80,0,0.3); color: #ff5000; }
.toast.info { background: rgba(91,141,239,0.15); border: 1px solid rgba(91,141,239,0.3); color: #5b8def; }
@keyframes toastIn { from { opacity: 0; transform: translateY(-10px); } to { opacity: 1; transform: translateY(0); } }
@keyframes toastOut { from { opacity: 1; } to { opacity: 0; } }

/* Progress bar */
.progress-section { margin-top: 32px; padding: 20px; background: #141414; border-radius: 12px; border: 1px solid #1f1f1f; }
.progress-bar-bg { background: #1f1f1f; height: 8px; border-radius: 8px; overflow: hidden; margin-top: 8px; }
.progress-bar-fill { height: 100%; border-radius: 8px; background: linear-gradient(90deg, #00dc5a, #5b8def); transition: width 0.5s; }

/* P&L Flash animation */
@keyframes plFlashGreen { 0% { color: #fff; } 50% { color: #00ff6a; text-shadow: 0 0 12px rgba(0,220,90,0.6); } 100% { color: #fff; } }
@keyframes plFlashRed { 0% { color: #fff; } 50% { color: #ff4040; text-shadow: 0 0 12px rgba(255,80,0,0.6); } 100% { color: #fff; } }
.pl-flash-green { animation: plFlashGreen 0.6s ease; }
.pl-flash-red { animation: plFlashRed 0.6s ease; }

/* Sparkline */
.sparkline { display: inline-block; vertical-align: middle; margin-left: 6px; }

/* Touch-friendly tap targets */
@media (pointer: coarse) {
  .tab { min-height: 44px; display: flex; align-items: center; }
  .trade-btn, .pick-execute, .hero-execute, .refresh-btn, #scan-btn { min-height: 44px; }
  .switch { width: 52px; height: 28px; }
  .slider:before { height: 22px; width: 22px; }
  input:checked + .slider:before { transform: translateX(24px); }
}

/* Responsive */
/* ===== TABLET (max 900px) ===== */
@media (max-width: 900px) {
  .container { padding: 0 8px; }
  .portfolio-value { font-size: 24px; }
  .stats-row { grid-template-columns: repeat(2, 1fr); gap: 1px; }
  .stat-value { font-size: 14px; }
  .stat-card { padding: 10px 8px; }
  .hero-grid { grid-template-columns: 1fr 1fr; }
  .picks-grid { grid-template-columns: 1fr; }
  .tab { padding: 8px 14px; font-size: 12px; }
  .header { padding: 10px 12px; flex-wrap: wrap; gap: 8px; }
  .tabs { overflow-x: auto; white-space: nowrap; -webkit-overflow-scrolling: touch; scrollbar-width: none; }
  .tabs::-webkit-scrollbar { display: none; }
  table { font-size: 11px; }
  table th, table td { padding: 6px 4px; }
  .section-title { font-size: 13px; }
  .chart-section { padding: 0 8px 12px; }
  .chart-canvas { height: 120px; }
  #tab-activity > div { grid-template-columns: 1fr !important; }
  .pos-table-compact th, .pos-table-compact td { font-size: 10px; padding: 6px 4px; }
  .breakdown-item { font-size: 10px; }
  .two-col { grid-template-columns: 1fr; }
  .portfolio-hero { padding: 24px 12px 6px; }
  .portfolio-breakdown { gap: 10px; flex-wrap: wrap; }
  .breakdown-val { font-size: 14px; }
  .progress-section { padding: 8px 12px; }
  .pick-card { padding: 12px; }
  .hero-card { padding: 12px; }
  .toast-container { top: 60px; right: 8px; left: 8px; }
  .toast { max-width: 100%; font-size: 12px; padding: 10px 14px; }
  /* Positions winning/losing columns stack on tablet */
  #pos-split { grid-template-columns: 1fr !important; }
}

/* ===== MOBILE (max 480px) ===== */
@media (max-width: 480px) {
  body { font-size: 13px; }
  .portfolio-value { font-size: 20px; letter-spacing: -0.5px; }
  .portfolio-change { font-size: 12px; }
  .portfolio-hero { padding: 16px 8px 4px; }
  .stats-row { grid-template-columns: 1fr 1fr; gap: 1px; border-radius: 8px; }
  .stat-card { padding: 8px 4px; }
  .stat-value { font-size: 13px; }
  .stat-label { font-size: 7px; letter-spacing: 0.3px; }
  .tab { padding: 8px 12px; font-size: 11px; }
  .tabs { gap: 0; padding: 0 4px; }
  .ticker-bar { font-size: 9px; gap: 12px; padding: 4px 8px; justify-content: flex-start; }
  .ticker-item { gap: 3px; }
  .header { padding: 8px 10px; top: 22px; margin: 0 -8px 0; }
  .header h1 { font-size: 16px; }
  .logo { width: 26px; height: 26px; }
  h1 { font-size: 16px; }
  #scan-btn { padding: 4px 10px; font-size: 11px; }
  #scan-btn svg { width: 12px; height: 12px; }
  .switch { width: 40px; height: 22px; }
  .slider:before { height: 16px; width: 16px; }
  input:checked + .slider:before { transform: translateX(18px); }
  .toggle-label { font-size: 10px; }
  .container { padding: 0 6px 20px; }
  .chart-section { display: none; }
  .progress-section { padding: 6px 10px; margin: 0 0 6px; }
  .progress-section span { font-size: 9px !important; }
  .section-title { font-size: 12px; flex-wrap: wrap; }
  .badge { font-size: 10px; padding: 1px 8px; }
  .refresh-btn { padding: 4px 10px; font-size: 10px; }
  /* Tables — card-like on mobile */
  table { font-size: 10px; }
  table th { padding: 6px 4px; font-size: 8px; }
  table td { padding: 8px 4px; font-size: 10px; }
  .pos-table-compact th { font-size: 8px; padding: 4px 3px; }
  .pos-table-compact td { font-size: 9px; padding: 6px 3px; }
  .pos-scroll { max-height: 400px; }
  /* Cards */
  .pick-card { padding: 10px; border-radius: 8px; }
  .pick-question { font-size: 12px; -webkit-line-clamp: 2; }
  .pick-edge { font-size: 10px; }
  .pick-execute { padding: 6px 10px; font-size: 11px; }
  .pick-footer { gap: 4px; }
  .pick-meta { font-size: 9px; }
  .hero-grid { grid-template-columns: 1fr; gap: 8px; }
  .hero-card { padding: 10px; border-radius: 8px; }
  .hero-prob { font-size: 22px; }
  .hero-question { font-size: 12px; }
  .hero-execute { padding: 5px 10px; font-size: 11px; }
  /* Activity */
  .activity-line { gap: 6px; padding: 6px 0; }
  .activity-line .time { font-size: 10px; min-width: 55px; }
  .activity-line .msg { font-size: 11px; }
  .activity-bar { max-height: 250px; }
  /* Breakdown */
  .portfolio-breakdown { gap: 8px; margin-top: 8px; }
  .breakdown-val { font-size: 13px; }
  .breakdown-label { font-size: 9px; }
  .breakdown-dot { display: none; }
  /* Today trades dropdown */
  #today-trades-dropdown { min-width: 280px !important; left: -100px !important; right: auto !important; }
  /* Quant/75ers cards on mobile */
  .sf-card { padding: 10px !important; }
  /* Hide less critical info on mobile */
  .pos-count { font-size: 11px; }
  .empty { padding: 20px; font-size: 12px; }
}
@keyframes spin { from { transform: rotate(0deg); } to { transform: rotate(360deg); } }
#scan-btn:hover:not(:disabled) { background: #00dc5a !important; color: #000 !important; }
#scan-btn:disabled { cursor: wait; }
</style>
</head>
<body>
<!-- Ticker bar -->
<div class="ticker-bar" id="ticker-bar">
  <div class="ticker-item"><span class="ticker-symbol">BTC</span> <span class="ticker-price" id="tk-btc">--</span> <span class="ticker-chg" id="tk-btc-chg"></span></div>
  <div class="ticker-item"><span class="ticker-symbol">ETH</span> <span class="ticker-price" id="tk-eth">--</span> <span class="ticker-chg" id="tk-eth-chg"></span></div>
  <div class="ticker-item"><span class="ticker-symbol">VOO</span> <span class="ticker-price" id="tk-voo">--</span> <span class="ticker-chg" id="tk-voo-chg"></span></div>
  <div class="ticker-item"><span class="ticker-symbol">TSLA</span> <span class="ticker-price" id="tk-tsla">--</span> <span class="ticker-chg" id="tk-tsla-chg"></span></div>
  <div class="ticker-item"><span class="ticker-symbol">GOOG</span> <span class="ticker-price" id="tk-goog">--</span> <span class="ticker-chg" id="tk-goog-chg"></span></div>
</div>

<div class="header">
  <div class="header-left">
    <svg class="logo" viewBox="0 0 64 64" xmlns="http://www.w3.org/2000/svg" style="filter:drop-shadow(0 2px 6px rgba(180,130,60,0.35))">
      <defs>
        <linearGradient id="sharkG" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" style="stop-color:#5a3a1a"/>
          <stop offset="18%" style="stop-color:#c9963a"/>
          <stop offset="35%" style="stop-color:#a87530"/>
          <stop offset="50%" style="stop-color:#dab060"/>
          <stop offset="65%" style="stop-color:#8b5e28"/>
          <stop offset="80%" style="stop-color:#c9963a"/>
          <stop offset="100%" style="stop-color:#4a2e14"/>
        </linearGradient>
        <linearGradient id="sharkFin" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" style="stop-color:#8b5e28"/>
          <stop offset="50%" style="stop-color:#c9963a"/>
          <stop offset="100%" style="stop-color:#5a3a1a"/>
        </linearGradient>
        <linearGradient id="sharkHL" x1="0%" y1="0%" x2="50%" y2="100%">
          <stop offset="0%" style="stop-color:#dab060" stop-opacity="0.6"/>
          <stop offset="100%" style="stop-color:#8b5e28" stop-opacity="0"/>
        </linearGradient>
      </defs>
      <path d="M8 38c0 0 4-18 20-22c2-6 8-12 14-14c-2 6-1 10 0 14c6 3 12 8 14 16c1 4 0 8-2 11l-6 3l2-6l-4 5l-8 2l3-4l-6 3c-4 1-10 1-14-1l4-3l-7 1c-4-1-7-3-9-6" fill="url(#sharkG)" stroke="#3d2510" stroke-width="0.5"/>
      <path d="M8 38c0 0 4-18 20-22c2-6 8-12 14-14c-2 6-1 10 0 14c6 3 12 8 14 16" fill="url(#sharkHL)"/>
      <circle cx="44" cy="28" r="2" fill="#1a0e05"/>
      <circle cx="44.5" cy="27.3" r="0.7" fill="#dab060" opacity="0.8"/>
      <path d="M28 40l-4 10l6-8l5 12l4-11l6 8l-2-11" fill="url(#sharkFin)" stroke="#3d2510" stroke-width="0.3" opacity="0.85"/>
    </svg>
    <h1><span>Trade</span><span style="background:linear-gradient(135deg,#c9963a,#dab060,#8b5e28,#c9963a);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text">Shark</span></h1>
  </div>
  <div style="display:flex;align-items:center;gap:12px">
    <!-- Notification Bell -->
    <div id="notif-bell-wrapper" style="position:relative;cursor:pointer" onclick="toggleNotifPanel()">
      <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="#888" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" id="notif-bell-icon">
        <path d="M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9"/><path d="M13.73 21a2 2 0 0 1-3.46 0"/>
      </svg>
      <span id="notif-badge" style="display:none;position:absolute;top:-4px;right:-6px;background:#ff3333;color:#fff;font-size:9px;font-weight:800;border-radius:50%;min-width:16px;height:16px;line-height:16px;text-align:center;padding:0 3px">0</span>
    </div>
    <!-- Notification Dropdown -->
    <div id="notif-panel" style="display:none;position:absolute;top:60px;right:100px;width:380px;max-height:450px;overflow-y:auto;background:#1a1a1a;border:1px solid #333;border-radius:12px;box-shadow:0 8px 32px rgba(0,0,0,0.6);z-index:1000;padding:0">
      <div style="padding:12px 16px;border-bottom:1px solid #333;display:flex;justify-content:space-between;align-items:center">
        <span style="font-size:13px;font-weight:700;color:#fff">Notifications</span>
        <span style="font-size:10px;color:#00dc5a;cursor:pointer" onclick="clearNotifs()">Mark all read</span>
      </div>
      <div id="notif-list" style="padding:4px 0">
        <div style="padding:20px;text-align:center;color:#555;font-size:11px">No notifications yet</div>
      </div>
    </div>
    <button id="scan-btn" onclick="triggerScan()" style="background:none;border:1px solid #00dc5a;color:#00dc5a;padding:6px 16px;border-radius:8px;cursor:pointer;font-size:13px;font-weight:600;font-family:inherit;transition:all 0.2s;display:flex;align-items:center;gap:6px">
      <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg>
      Scan Now
    </button>
    <span class="toggle-label" id="toggle-label">Auto-Trade</span>
    <label class="switch">
      <input type="checkbox" id="auto-trade-toggle" onchange="toggleAutoTrade()">
      <span class="slider"></span>
    </label>
  </div>
</div>

<!-- Progress bar hidden until meaningful -->

<div class="container">

<!-- Hidden elements needed by JS -->
<div style="display:none">
  <span id="balance">--</span>
  <span id="markets-scanned">--</span>
  <span id="mispriced-count">--</span>
  <span id="auto-trade-btn">--</span>
  <div id="pf-value">$0.00</div>
  <div id="pf-change">$0.00</div>
  <span id="pf-cash-hero">--</span>
  <span id="pf-invested-hero">--</span>
  <span id="chart-pl"></span>
  <canvas id="pl-chart"></canvas>
</div>

<!-- Slim stat bar -->
<div class="stats-row" style="margin-bottom:8px">
  <div class="stat-card" style="flex:1.5"><div class="stat-label">Portfolio</div><div class="stat-value" id="pf-total" style="color:#fff;font-size:18px">--</div></div>
  <div class="stat-card"><div class="stat-label">Cash</div><div class="stat-value" id="pf-cash">--</div></div>
  <div class="stat-card"><div class="stat-label">Invested</div><div class="stat-value" id="pf-invested">--</div></div>
  <div class="stat-card"><div class="stat-label">Daily P&L</div><div class="stat-value" id="pf-daily-pl">--</div></div>
  <div class="stat-card"><div class="stat-label">P&amp;L Since Day 1</div><div class="stat-value" id="pf-total-pl">--</div></div>
  <div class="stat-card"><div class="stat-label">Win Rate</div><div class="stat-value" id="pf-winrate">--</div></div>
  <div class="stat-card"><div class="stat-label">W / L</div><div class="stat-value" id="pf-winrate-7d">--</div></div>
  <div class="stat-card" style="cursor:pointer;position:relative" onclick="toggleTodayTrades()"><div class="stat-label">Trades Today</div><div class="stat-value" id="trades-today" style="text-decoration:underline;text-decoration-style:dotted">--</div><div id="today-trades-dropdown" style="display:none;position:absolute;top:100%;left:0;right:0;min-width:350px;max-width:500px;background:#111;border:1px solid #333;border-radius:10px;padding:12px;z-index:100;box-shadow:0 8px 24px rgba(0,0,0,0.6);max-height:400px;overflow-y:auto;font-size:10px"></div></div>
</div>

<!-- Hidden portfolio elements needed by JS -->
<div style="display:none">
  <span id="pf-unrealized">--</span>
  <span id="pf-realized">--</span>
  <span id="pf-wrbar"></span>
  <span id="pf-wl">--</span>
  <span id="daily-spent">--</span>
</div>

<!-- Tabs -->
<div class="tabs">
  <button class="tab active" onclick="switchTab('positions')">Dashboard</button>
  <button class="tab" onclick="switchTab('performance')">Performance</button>
  <button class="tab" onclick="switchTab('trends')" style="color:#e040fb">Trends</button>
  <button class="tab" onclick="switchTab('moonshark')" style="color:#00d4ff;margin-left:auto">&#x1F988; MoonShark</button>
</div>

<!-- Positions Tab -->
<div class="tab-content active" id="tab-positions">
  <!-- Live Feed + Bets Placed Today + Closing Soon -->
  <div style="display:grid;grid-template-columns:1fr 1.2fr 1fr;gap:12px;margin-bottom:16px;min-width:0">
    <div class="section" style="min-width:0;overflow:hidden">
      <div class="section-title">Live Feed <span style="width:8px;height:8px;border-radius:50%;background:#00dc5a;display:inline-block;animation:pulse 2s infinite" id="activity-pulse-dash"></span></div>
      <div class="activity-bar" id="activity-feed-dash" style="max-height:300px;overflow-y:auto">
        <div id="activity-lines-dash"><div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg">Waiting for first scan...</span></div></div>
      </div>
    </div>
    <div class="section" style="min-width:0;overflow:hidden">
      <div class="section-title">Bets Placed Today <span class="badge" id="bets-today-count-dash">0</span> <span style="width:8px;height:8px;border-radius:50%;background:#ffb400;display:inline-block" id="bets-pulse-dash"></span></div>
      <div class="activity-bar" id="bets-feed-dash" style="max-height:300px;overflow-y:auto">
        <div id="bets-lines-dash"><div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg">Loading trade history...</span></div></div>
      </div>
    </div>
    <div class="section" style="min-width:0;overflow:hidden">
      <div class="section-title">Closing Soon <span class="badge" id="closing-soon-count">0</span> <span style="width:8px;height:8px;border-radius:50%;background:#ff5000;display:inline-block;animation:pulse 2s infinite"></span></div>
      <div class="activity-bar" id="closing-soon-feed" style="max-height:300px;overflow-y:auto">
        <div id="closing-soon-lines"><div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg">Loading positions...</span></div></div>
      </div>
    </div>
  </div>
  <div style="display:flex;justify-content:flex-end;align-items:center;gap:12px;margin-bottom:6px">
    <button onclick="sellAllLosers()" style="background:#1a1a1a;border:1px solid #333;color:#888;padding:3px 10px;border-radius:6px;font-size:9px;cursor:pointer">Sell Losers</button>
    <label style="font-size:10px;color:#888;cursor:pointer"><input type="checkbox" id="hide-bot-trades" checked onchange="loadPortfolio();loadPositions()" style="margin-right:4px">Hide old bot trades &amp; penny positions</label>
  </div>
  <div id="portfolio-positions"><div class="loading">Loading positions...</div></div>
  <div class="section" style="margin-top:20px">
    <div class="section-title">All Positions <span class="badge" id="pos-badge">0</span><button class="refresh-btn" onclick="loadPositions()">Refresh</button></div>
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px" id="pos-split-container">
      <div>
        <div style="font-size:11px;font-weight:700;color:#00dc5a;margin-bottom:6px">Open <span id="pos-open-count" style="color:#888;font-weight:400">(0)</span> <span id="pos-open-pnl" style="font-size:10px;color:#888"></span></div>
        <div id="pos-table-open"><div class="loading">Loading...</div></div>
      </div>
      <div>
        <div style="font-size:11px;font-weight:700;color:#888;margin-bottom:6px">Closed <span id="pos-closed-count" style="color:#888;font-weight:400">(0)</span> <span id="pos-closed-pnl" style="font-size:10px;color:#888"></span></div>
        <div id="pos-table-closed"><div class="loading">Loading...</div></div>
      </div>
    </div>
  </div>
  <!-- Mispriced Markets hidden — consensus strategy disabled -->
  <div class="section" style="display:none">
    <div class="section-title">Mispriced Markets <span class="badge" id="opp-badge">0</span><button class="refresh-btn" onclick="loadMispriced()">Refresh</button></div>
    <div id="opp-table"></div>
  </div>
  <!-- Activity section merged into Dashboard — REMOVED from bottom, now at top -->
</div>

<!-- Picks Tab — Goldman Sachs Style Research Desk -->
<div class="tab-content" id="tab-picks">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">
    <div>
      <div style="font-size:16px;font-weight:800;color:#fff;letter-spacing:0.5px">TradeShark Research Desk</div>
      <div style="font-size:9px;color:#888;margin-top:2px">Quantitative Analysis | Cross-Platform Validated | Updated Every 60s</div>
    </div>
    <button class="refresh-btn" onclick="loadTopPicks()" style="font-size:10px">Refresh Analysis</button>
  </div>
  <div id="gs-picks-grid" style="display:grid;grid-template-columns:1fr 1fr;gap:12px">
    <div class="loading" style="grid-column:1/-1;padding:40px;text-align:center;color:#888">Scanning 3,000+ markets across 6 platforms...</div>
  </div>
  <!-- Hidden elements for backward compatibility -->
  <div style="display:none">
    <span id="hero-badge">0</span>
    <div id="hero-picks"></div>
    <span id="picks-badge-sports">0</span>
    <div id="top-picks-list-sports"></div>
    <span id="picks-badge-nonsports">0</span>
    <div id="top-picks-list-nonsports"></div>
    <span id="today-badge-sports">0</span>
    <div id="today-table-sports"></div>
    <span id="today-badge-nonsports">0</span>
    <div id="today-table-nonsports"></div>
    <span id="misc-badge">0</span>
    <div id="misc-picks"></div>
  </div>
</div>

<!-- Activity Tab -->
<div class="tab-content" id="tab-activity">
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px">
    <div class="section">
      <div class="section-title">Live Feed <span style="width:8px;height:8px;border-radius:50%;background:#00dc5a;display:inline-block;animation:pulse 2s infinite" id="activity-pulse"></span></div>
      <div class="activity-bar" id="activity-feed">
        <div id="activity-lines"><div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg">Waiting for first scan...</span></div></div>
      </div>
    </div>
    <div class="section">
      <div class="section-title">Bets Placed Today <span class="badge" id="bets-today-count">0</span> <span style="width:8px;height:8px;border-radius:50%;background:#ffb400;display:inline-block" id="bets-pulse"></span></div>
      <div class="activity-bar" id="bets-feed" style="max-height:400px;overflow-y:auto">
        <div id="bets-lines"><div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg">Loading trade history...</span></div></div>
      </div>
    </div>
  </div>
  <div class="section" style="margin-top:16px">
    <div class="section-title">All Bets <span class="badge" id="all-bets-count">0</span> <button class="refresh-btn" onclick="loadAllBets()">Refresh</button></div>
    <div id="all-bets-table"><div class="loading">Loading all bets...</div></div>
  </div>
</div>

<!-- History Tab -->
<div class="tab-content" id="tab-performance">
  <!-- Row 1: Core KPIs -->
  <div style="display:grid;grid-template-columns:repeat(5,1fr);gap:6px;margin-bottom:12px" id="perf-kpis">
    <span style="color:#666">Loading...</span>
  </div>

  <!-- Row 2: P&L Chart + Strategy Breakdown side by side -->
  <div style="display:grid;grid-template-columns:1.5fr 1fr;gap:12px;margin-bottom:12px">
    <!-- P&L Equity Curve -->
    <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">Equity Curve</div>
      <div style="position:relative;height:140px">
        <canvas id="perf-pl-chart" style="width:100%;height:100%"></canvas>
      </div>
    </div>
    <!-- Strategy Breakdown -->
    <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">By Strategy</div>
      <div id="perf-strategies"></div>
    </div>
  </div>

  <!-- Row 3: Category + Price Range + Time of Day -->
  <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:12px;margin-bottom:12px">
    <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">By Sport</div>
      <div id="perf-by-sport"></div>
    </div>
    <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">By Price Range</div>
      <div id="perf-by-price"></div>
    </div>
    <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">By Time of Day</div>
      <div id="perf-by-time"></div>
    </div>
  </div>

  <!-- Row 4: Daily Insights -->
  <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px;margin-bottom:12px">
    <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:8px">Daily Insights</div>
    <div id="daily-insights-feed" style="display:flex;flex-direction:column;gap:6px">
      <div class="loading">Generating insights...</div>
    </div>
  </div>

  <!-- Row 5: Recent Trades -->
  <div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">
      <div style="color:#888;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px">Trade Journal <span class="badge" id="trade-badge" style="margin-left:6px">0</span> <span style="color:#444;font-size:8px;font-weight:400;margin-left:4px">click any trade for edge details</span></div>
      <div style="display:flex;align-items:center;gap:8px">
        <label style="font-size:10px;color:#666;cursor:pointer"><input type="checkbox" id="hide-history-junk" checked onchange="loadPerformance()" style="margin-right:3px;accent-color:#00dc5a"> Hide old bot trades</label>
        <button class="refresh-btn" onclick="loadPerformance()">Refresh</button>
      </div>
    </div>
    <div id="settled-table"></div>
  </div>
</div>

<!-- Legacy hidden tab-content for backward compat -->
<div class="tab-content" id="tab-history" style="display:none"></div>
<div class="tab-content" id="tab-analytics" style="display:none"></div>

<!-- 75%'ers Tab -->
<div class="tab-content" id="tab-seventyfivers">
  <div class="section">
    <div id="sf-stats-banner" style="display:flex;align-items:center;gap:16px;padding:10px 14px;background:#1a1a2e;border-radius:10px;margin-bottom:14px;flex-wrap:wrap">
      <span style="font-size:16px;font-weight:700;color:#00dc5a" id="sf-streak-text">Loading...</span>
      <span style="font-size:12px;color:#888" id="sf-winrate-text"></span>
      <span style="font-size:12px;color:#888" id="sf-profit-text"></span>
      <div style="margin-left:auto;display:flex;align-items:center;gap:8px">
        <label style="font-size:11px;color:#888;cursor:pointer;display:flex;align-items:center;gap:4px">
          <input type="checkbox" id="sf-live-only" checked onchange="loadSeventyFivers()" style="accent-color:#00dc5a"> Live Only
        </label>
        <button class="refresh-btn" onclick="loadSeventyFivers()">Refresh</button>
      </div>
    </div>
    <div id="sf-cards" style="display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:12px">
      <div class="loading">Scanning for 75%'ers...</div>
    </div>
  </div>
</div>

<!-- Quant Tab -->
<div class="tab-content" id="tab-quant">
  <div class="section">
    <div id="quant-stats-banner" style="display:flex;align-items:center;gap:16px;padding:10px 14px;background:#0d1a2e;border:1px solid #1a3050;border-radius:10px;margin-bottom:14px;flex-wrap:wrap">
      <span style="font-size:14px;font-weight:700;color:#00d4ff" id="quant-banner-text">Mispriced Markets</span>
      <span style="font-size:12px;color:#888" id="quant-winrate-text"></span>
      <span style="font-size:12px;color:#888" id="quant-profit-text"></span>
      <div style="margin-left:auto;display:flex;align-items:center;gap:8px">
        <label style="font-size:11px;color:#888;cursor:pointer;display:flex;align-items:center;gap:4px">
          <input type="checkbox" id="quant-strong-only" onchange="loadQuantPicks()" style="accent-color:#00d4ff"> Strong Only (25%+)
        </label>
        <button class="refresh-btn" onclick="loadQuantPicks()">Refresh</button>
      </div>
    </div>
    <div id="quant-cards" style="display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:12px">
      <div class="loading">Scanning for mispriced markets...</div>
    </div>
  </div>
</div>

<div class="tab-content" id="tab-moonshark">
  <div class="section">
    <!-- Header -->
    <div style="display:flex;align-items:center;gap:16px;padding:14px 18px;background:linear-gradient(135deg,#001a2a,#002a3a);border:1px solid #004a6a;border-radius:12px;margin-bottom:14px;flex-wrap:wrap">
      <div>
        <div style="font-size:22px;font-weight:800;color:#00d4ff">&#x1F988; MoonShark</div>
        <div style="font-size:11px;color:#0099bb;font-weight:500">Longshot Sniper &bull; 10-30&cent; Underdogs</div>
      </div>
      <div style="margin-left:auto;display:flex;align-items:center;gap:8px">
        <button id="mshark-toggle-btn" onclick="toggleMoonshark()" style="background:none;border:2px solid #00dc5a;color:#00dc5a;padding:6px 14px;border-radius:8px;cursor:pointer;font-size:11px;font-weight:700;font-family:inherit">&#x1F988; ENABLED</button>
        <button class="refresh-btn" onclick="loadMoonshark()" style="border-color:#004a6a;color:#00d4ff">&#x1F504; Refresh</button>
      </div>
    </div>

    <!-- Wheel + Opportunities -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:16px">
      <!-- Spin Wheel -->
      <div style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:12px;padding:16px;text-align:center">
        <div style="color:#00d4ff;font-size:13px;font-weight:700;margin-bottom:12px">&#x1F3B0; Spin the Wheel</div>
        <div style="position:relative;width:280px;height:280px;margin:0 auto">
          <canvas id="moonshark-wheel" width="280" height="280" style="border-radius:50%"></canvas>
          <div id="wheel-pointer" style="position:absolute;top:-10px;left:50%;transform:translateX(-50%);font-size:24px;z-index:10">&#x25BC;</div>
        </div>
        <button id="spin-btn" onclick="spinWheel()" style="margin-top:14px;background:linear-gradient(135deg,#00d4ff,#0088aa);border:none;color:#000;padding:10px 28px;border-radius:8px;font-size:14px;font-weight:800;cursor:pointer;font-family:inherit;letter-spacing:1px">&#x1F988; SPIN!</button>
        <div id="wheel-result" style="margin-top:10px;min-height:40px;font-size:12px;color:#ccc"></div>
      </div>
      <!-- WTA Wheel Stats -->
      <div style="background:#0a1a22;border:1px solid #e040fb;border-radius:12px;padding:16px">
        <div style="color:#e040fb;font-size:15px;font-weight:800;margin-bottom:14px">&#x1F3BE; Ladies Tennis Tracker</div>
        <div id="wta-wheel-stats" style="display:flex;flex-direction:column;gap:10px">
          <div class="loading">Loading stats...</div>
        </div>
        <div style="color:#e040fb;font-size:12px;font-weight:700;margin-top:16px;margin-bottom:8px">Wheel Bets</div>
        <div id="wta-wheel-bets" style="display:flex;flex-direction:column;gap:6px;max-height:300px;overflow-y:auto">
          <div style="color:#555;font-size:10px">No wheel bets yet — spin to play!</div>
        </div>
      </div>
    </div>

    <!-- Stats Bar -->
    <div id="mshark-stats-bar" style="display:grid;grid-template-columns:repeat(auto-fill,minmax(100px,1fr));gap:8px;margin-bottom:16px">
      <div class="loading">Loading stats...</div>
    </div>

    <!-- Active Positions -->
    <div style="margin-bottom:20px">
      <div style="color:#00d4ff;font-size:14px;font-weight:700;margin-bottom:10px">&#x1F988; Active Positions <span id="mshark-active-badge" style="background:#004a6a;color:#00d4ff;padding:2px 8px;border-radius:10px;font-size:11px;font-weight:600">0</span></div>
      <div id="mshark-positions" style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:10px;padding:12px;min-height:40px">
        <div class="loading">Loading...</div>
      </div>
    </div>

    <!-- Trade History -->
    <div style="margin-bottom:20px">
      <div style="color:#00d4ff;font-size:14px;font-weight:700;margin-bottom:10px">Trade History <span id="mshark-history-badge" style="background:#004a6a;color:#00d4ff;padding:2px 8px;border-radius:10px;font-size:11px;font-weight:600">0</span></div>
      <div id="mshark-history" style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:10px;padding:12px;min-height:40px;overflow-x:auto">
        <div class="loading">Loading...</div>
      </div>
    </div>

    <!-- Cumulative P&L -->
    <div style="margin-bottom:20px">
      <div style="color:#00d4ff;font-size:14px;font-weight:700;margin-bottom:10px">Cumulative P&amp;L</div>
      <div id="mshark-cumulative" style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:10px;padding:12px;min-height:40px;max-height:300px;overflow-y:auto">
        <div class="loading">Loading...</div>
      </div>
    </div>

    <!-- Settings -->
    <div style="margin-bottom:10px">
      <div style="color:#00d4ff;font-size:14px;font-weight:700;margin-bottom:10px">Settings</div>
      <div id="mshark-settings" style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:10px;padding:14px">
        <div class="loading">Loading...</div>
      </div>
    </div>
  </div>
</div>

<!-- Analytics Tab -->
<!-- Analytics tab removed — merged into Performance tab -->

<!-- News Feed Tab (was Trends) -->
<div class="tab-content" id="tab-trends">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:16px">
    <div>
      <div style="color:#e040fb;font-size:18px;font-weight:800;letter-spacing:0.5px">&#x1F30D; Global Markets Brief</div>
      <div style="color:#666;font-size:10px;margin-top:2px">Top 10 stories moving markets today</div>
    </div>
    <div style="display:flex;align-items:center;gap:8px">
      <span id="news-updated-time" style="color:#555;font-size:10px"></span>
      <button class="refresh-btn" onclick="loadNewsFeed(true)">Refresh</button>
    </div>
  </div>
  <div id="global-news-feed" style="display:flex;flex-direction:column;gap:12px">
    <div class="loading">Loading global markets brief...</div>
  </div>
</div>

<!-- News Tab -->
<div class="tab-content" id="tab-news">
  <div class="section">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:14px">
      <div>
        <div style="color:#ccc;font-size:16px;font-weight:700">&#x1F4F0; Market News</div>
        <div style="color:#666;font-size:11px;margin-top:2px">Top financial stories</div>
      </div>
      <div style="display:flex;align-items:center;gap:10px">
        <span id="news-updated" style="color:#555;font-size:10px"></span>
        <button onclick="loadNews(true)" style="background:#1a1a2e;border:1px solid #333;color:#ccc;padding:4px 10px;border-radius:6px;font-size:11px;cursor:pointer">Refresh</button>
      </div>
    </div>
    <div id="news-feed" style="display:flex;flex-direction:column;gap:10px">
      <div class="loading">Loading news...</div>
    </div>
  </div>
  <div class="section" style="margin-top:20px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:14px">
      <div>
        <div style="color:#e6b800;font-size:16px;font-weight:700">&#x1F4A1; News Ideas</div>
        <div style="color:#666;font-size:11px;margin-top:2px">Market signals from today's headlines</div>
      </div>
      <div style="display:flex;align-items:center;gap:10px">
        <span id="newsideas-updated" style="color:#555;font-size:10px"></span>
        <button onclick="loadNewsIdeas(true)" style="background:#1a1a20;border:1px solid #3a3520;color:#e6b800;padding:4px 10px;border-radius:6px;font-size:11px;cursor:pointer">Refresh</button>
      </div>
    </div>
    <div id="newsideas-feed" style="display:flex;flex-direction:column;gap:10px">
      <div class="loading">Analyzing headlines...</div>
    </div>
  </div>
</div>

</div><!-- end container -->

<div class="toast-container" id="toast-container"></div>

<!-- Hidden portfolio tile for compatibility -->
<div class="portfolio-tile" id="portfolio-tile" style="display:none">
  <div class="portfolio-stats" id="portfolio-stats"></div>
</div>

<script>
// Parse any UTC timestamp to local Date — handles microseconds, missing Z, etc.
function parseUTC(ts) {
  if (!ts) return null;
  // Strip microseconds (keep max 3 decimal places for JS compatibility)
  ts = ts.replace(/(\.\d{3})\d+/, '$1');
  // Ensure Z suffix for UTC interpretation
  if (ts.indexOf('Z') < 0 && ts.indexOf('+') < 0 && ts.indexOf('-', 10) < 0) ts += 'Z';
  var d = new Date(ts);
  return isNaN(d.getTime()) ? null : d;
}
function fmtTime(ts) {
  var d = parseUTC(ts);
  return d ? d.toLocaleTimeString([], {hour:'2-digit', minute:'2-digit'}) : '--:--';
}
function fmtTimeSec(ts) {
  var d = parseUTC(ts);
  return d ? d.toLocaleTimeString([], {hour:'2-digit', minute:'2-digit', second:'2-digit'}) : '--:--:--';
}
function switchTab(name) {
  document.querySelectorAll('.tab').forEach(function(t) { t.classList.remove('active'); });
  document.querySelectorAll('.tab-content').forEach(function(t) { t.classList.remove('active'); });
  document.getElementById('tab-' + name).classList.add('active');
  var tabs = document.querySelectorAll('.tab');
  tabs.forEach(function(t) { if (t.getAttribute('onclick').indexOf(name) >= 0) t.classList.add('active'); });
  // Lazy-load tab data
  if (name === 'positions') { loadActivityDash(); loadBetsFeedDash(); }
  if (name === 'moonshark') loadMoonshark();
  if (name === 'performance') { loadPerformance(); }
  if (name === 'history') { loadPerformance(); }  // legacy redirect
  if (name === 'analytics') { loadPerformance(); }  // legacy redirect
  if (name === 'trends') { loadNewsFeed(); }
  // Legacy support for hidden tabs
  if (name === 'activity') { loadActivity(); loadBetsFeed(); loadAllBets(); }
}

const API = window.location.origin;

// Safe DOM helpers — prevent null reference crashes when elements are missing
function _el(id) { return document.getElementById(id); }
function _setText(id, val) { var e = document.getElementById(id); if (e) e.textContent = val; }
function _setHTML(id, val) { var e = document.getElementById(id); if (e) e.innerHTML = val; }

// Sports classification is now done server-side via is_sports field
function isSports(pick) {
  return !!pick.is_sports;
}

function formatSettleTime(closeTime) {
  if (!closeTime) return 'TBD';
  try {
    var close = new Date(closeTime);
    var now = new Date();
    var diff = close - now;
    if (diff <= 0) return 'Settling now';
    var mins = Math.floor(diff / 60000);
    var hrs = Math.floor(mins / 60);
    var days = Math.floor(hrs / 24);
    if (days > 365) return Math.floor(days/365) + 'y+';
    if (days > 30) return Math.floor(days/30) + 'mo';
    if (days > 0) return days + 'd ' + (hrs % 24) + 'h';
    if (hrs > 0) return hrs + 'h ' + (mins % 60) + 'm';
    return mins + 'm';
  } catch(e) { return 'TBD'; }
}

function renderHeroCard(p, idx) {
  var sigClass = p.signal === 'buy_yes' ? 'yes' : 'no';
  var sigLabel = p.signal === 'buy_yes' ? 'YES' : 'NO';
  var winPct = (p.win_probability || 0.5) * 100;
  var ct = Math.max(1, Math.floor(500 / p.price_cents));
  var cost = (p.price_cents * ct / 100).toFixed(2);
  var sideWord = p.signal === 'buy_yes' ? 'YES' : 'NO';
  var isConsensus = p.type === 'consensus' || p.type === 'arbitrage' || p.type === 'cross_validated';
  var settleTime = formatSettleTime(p.close_time);
  var platCount = (p.platform_count || 0) + 1;

  var h = '<div class="hero-card">';
  h += '<div class="hero-rank">#' + (idx + 1) + '</div>';

  // Main stat: win probability (market-derived)
  var pctColor = winPct >= 75 ? '#00dc5a' : winPct >= 55 ? '#ffb400' : '#ffcc00';
  h += '<div class="hero-prob" style="color:' + pctColor + '">' + winPct.toFixed(0) + '%</div>';
  h += '<div class="hero-label">Market Probability</div>';

  // Compact info line
  h += '<div style="display:flex;gap:5px;font-size:7px;color:#888;margin:2px 0;flex-wrap:wrap;align-items:center">';
  if (isConsensus) {
    h += '<span style="color:#00dc5a;font-weight:700">' + platCount + ' PLATFORMS</span>';
  } else {
    h += '<span style="color:#555">KALSHI ONLY</span>';
  }
  h += '<span>⏱' + settleTime + '</span>';
  h += '<span>' + (p.volume || 0).toLocaleString() + ' vol</span>';
  h += '<span>' + p.price_cents + '¢→$1</span>';
  h += '</div>';

  // Question
  h += '<div class="hero-question"><a href="' + p.kalshi_url + '" target="_blank">' + p.kalshi_question + '</a></div>';

  // Edge reason — single sentence explaining WHY
  var edgeReason = p.edge_reason || p.edge_summary || '';
  if (edgeReason) {
    h += '<div class="hero-edge-reason">' + edgeReason + '</div>';
  }

  // Signal + bet meaning
  var yesL = p.yes_label || 'Yes';
  var noL = p.no_label || 'No';
  var betMeaning = p.signal === 'buy_yes' ? yesL : noL;
  h += '<div style="display:flex;gap:4px;align-items:center;flex-wrap:wrap;margin-bottom:2px">';
  h += '<span class="hero-signal ' + sigClass + '">' + sigLabel + '</span>';
  if (betMeaning !== 'Yes' && betMeaning !== 'No') {
    h += '<span style="font-size:8px;color:#ffcc00;font-weight:600">→ ' + betMeaning + '</span>';
  }
  h += '</div>';

  h += '<div class="hero-footer">';
  h += '<button class="hero-execute" onclick="executePickTrade(this, ' + p._globalIdx + ')">Buy ' + sideWord + ' · $' + cost + '</button>';
  h += '</div>';
  h += '</div>';
  return h;
}

function showToast(msg, type) {
  const c = document.getElementById('toast-container');
  const t = document.createElement('div');
  t.className = 'toast ' + type;
  t.textContent = msg;
  c.appendChild(t);
  requestAnimationFrame(() => t.style.opacity = '1');
  setTimeout(() => { t.remove(); }, 5000);
}

async function toggleTodayTrades() {
  var dd = document.getElementById('today-trades-dropdown');
  if (dd.style.display !== 'none') {
    dd.style.display = 'none';
    return;
  }
  dd.innerHTML = '<div style="color:#888;padding:8px">Loading...</div>';
  dd.style.display = 'block';
  try {
    var data = await fetch(API + '/trades-today').then(r => r.json());
    var trades = data.trades || [];
    if (trades.length === 0) {
      dd.innerHTML = '<div style="color:#666;padding:8px;text-align:center">No trades placed today</div>';
      return;
    }
    var h = '<div style="color:#00dc5a;font-weight:700;font-size:12px;margin-bottom:8px">' + trades.length + ' trades today ($' + data.total_spent.toFixed(2) + ' spent)</div>';
    h += '<table style="width:100%;border-collapse:collapse">';
    h += '<tr style="color:#888;border-bottom:1px solid #222"><th style="padding:4px;text-align:left">Time</th><th style="padding:4px;text-align:left">Market</th><th style="padding:4px">Side</th><th style="padding:4px">Price</th><th style="padding:4px">Cost</th><th style="padding:4px">Source</th></tr>';
    trades.forEach(function(t) {
      var sideC = t.side === 'yes' ? '#00dc5a' : '#ff5000';
      var timeStr = fmtTime(t.time);
      var stratColors = {sniper:'#ffb400', quant:'#00d4ff', bot:'#888', consensus_mispricing:'#888'};
      var stratLabels = {sniper:'Sniper', quant:'Quant', bot:'Bot', consensus_mispricing:'Bot'};
      var sc = stratColors[t.strategy] || '#888';
      var sl = stratLabels[t.strategy] || t.strategy;
      h += '<tr style="border-bottom:1px solid #1a1a1a">';
      h += '<td style="padding:4px;color:#666">' + timeStr + '</td>';
      h += '<td style="padding:4px;color:#ccc;max-width:150px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (t.title || t.ticker) + '</td>';
      h += '<td style="padding:4px;color:' + sideC + ';font-weight:700;text-align:center">' + (t.side || '').toUpperCase() + '</td>';
      h += '<td style="padding:4px;color:#fff;text-align:center">' + t.price_cents + '&#162; x' + t.count + '</td>';
      h += '<td style="padding:4px;color:#ffb400;text-align:center">$' + t.cost_usd.toFixed(2) + '</td>';
      h += '<td style="padding:4px;color:' + sc + ';text-align:center;font-weight:600">' + sl + '</td>';
      h += '</tr>';
    });
    h += '</table>';
    dd.innerHTML = h;
  } catch(e) {
    dd.innerHTML = '<div style="color:#ff5000;padding:8px">Error: ' + e.message + '</div>';
  }
}

// Close dropdown when clicking outside
document.addEventListener('click', function(e) {
  var dd = document.getElementById('today-trades-dropdown');
  if (dd && dd.style.display !== 'none' && !e.target.closest('.stat-card')) {
    dd.style.display = 'none';
  }
});

async function loadStatus() {
  try {
    const [status, bal] = await Promise.all([
      fetch(API + '/status').then(r => r.json()),
      fetch(API + '/balance').then(r => r.json()),
    ]);
    window._currentBalance = bal.balance_usd || 0;
    _setText('balance', '$' + (bal.balance_usd || 0).toFixed(2));
    _setText('markets-scanned', status.last_scan_markets || 0);
    _setText('mispriced-count', status.last_scan_mispriced || 0);
    // Use trades-today endpoint count (consolidated, matches "Bets Placed Today" badge)
    try {
      var ttData = await fetch(API + '/trades-today').then(function(r){ return r.json(); });
      _setText('trades-today', (ttData.trades || []).length);
    } catch(e) {
      _setText('trades-today', status.trades_today || 0);
    }
    _setText('daily-spent', '$' + (status.daily_spent_usd || 0).toFixed(2));
    // Update toggle switch
    var tog = document.getElementById('auto-trade-toggle');
    var togLabel = document.getElementById('toggle-label');
    if (tog) tog.checked = !!status.bot_enabled;
    if (togLabel) {
      togLabel.textContent = status.bot_enabled ? 'Auto-Trade On' : 'Auto-Trade';
      togLabel.className = 'toggle-label' + (status.bot_enabled ? ' active' : '');
    }
    // Keep hidden btn in sync for any legacy references
    var atBtn = document.getElementById('auto-trade-btn');
    if (atBtn) atBtn.textContent = status.bot_enabled ? 'ON' : 'OFF';
    window._botEnabled = status.bot_enabled;
  } catch(e) { console.error(e); }
}

async function toggleBot() {
  const enable = !window._botEnabled;
  await fetch(API + '/config', { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify({enabled: enable}) });
  loadStatus();
}

async function triggerScan() {
  var btn = _el('scan-btn');
  if (!btn) return;
  btn.disabled = true;
  btn.innerHTML = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" style="animation:spin 1s linear infinite"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg> Scanning...';
  btn.style.borderColor = '#555';
  btn.style.color = '#888';
  try {
    await fetch(API + '/scan', { method: 'POST' });
    showToast('Scan started — finding opportunities...', 'success');
    // Wait a bit then refresh data
    setTimeout(() => {
      loadAll();
      btn.disabled = false;
      btn.innerHTML = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg> Scan Now';
      btn.style.borderColor = '#00dc5a';
      btn.style.color = '#00dc5a';
    }, 15000);
  } catch(e) {
    showToast('Scan failed: ' + e.message, 'error');
    btn.disabled = false;
    btn.innerHTML = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg> Scan Now';
    btn.style.borderColor = '#00dc5a';
    btn.style.color = '#00dc5a';
  }
}

async function toggleAutoTrade() {
  var tog = document.getElementById('auto-trade-toggle');
  var enable = tog ? tog.checked : !window._botEnabled;
  try {
    await fetch(API + '/config', { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify({enabled: enable}) });
    showToast(enable ? 'Auto-trading enabled' : 'Auto-trading disabled', enable ? 'success' : 'info');
  } catch(e) {
    showToast('Failed to toggle: ' + e.message, 'error');
  }
  loadStatus();
}

async function loadPortfolio() {
  try {
    const data = await fetch(API + '/portfolio-summary').then(r => r.json());
    if (data.error) { console.error(data.error); return; }

    // Skip update if server cache not warmed yet (all zeros) — keep previous values
    if ((data.portfolio_value_usd || 0) === 0 && (data.balance_usd || 0) === 0 && window._lastPortfolioData) {
      return;
    }
    // Save last good data
    if ((data.portfolio_value_usd || 0) > 0 || (data.balance_usd || 0) > 0) {
      window._lastPortfolioData = data;
    }

    // Big portfolio value at top — flash green/red on change
    var pfVal = data.portfolio_value_usd || 0;
    var pfValEl = _el('pf-value');
    if (pfValEl) {
      var prevVal = parseFloat(pfValEl.getAttribute('data-prev') || '0');
      pfValEl.textContent = '$' + pfVal.toFixed(2);
      pfValEl.style.color = '#fff';
      if (prevVal > 0 && Math.abs(pfVal - prevVal) > 0.01) {
        pfValEl.classList.remove('pl-flash-green', 'pl-flash-red');
        void pfValEl.offsetWidth; // force reflow
        pfValEl.classList.add(pfVal > prevVal ? 'pl-flash-green' : 'pl-flash-red');
      }
      pfValEl.setAttribute('data-prev', pfVal.toFixed(2));
    }

    // Update progress bar to $1M — pfVal already includes cash + invested
    var totalVal = pfVal;
    var prog = Math.min(100, (totalVal / 1000000) * 100);
    var progLbl = prog < 0.01 ? '<0.01%' : prog.toFixed(3) + '%';
    var progFill = document.getElementById('progress-fill');
    var progLabel = document.getElementById('progress-label');
    var progBalance = document.getElementById('progress-balance');
    if (progFill) progFill.style.width = Math.max(0.3, prog) + '%';
    if (progLabel) progLabel.textContent = progLbl;
    if (progBalance) progBalance.textContent = '$' + totalVal.toFixed(2);

    // All-time P&L — Day 1 = March 16, 2026
    var DAY1_BALANCE = 733.92;  // Portfolio value on March 16 (fresh start)
    var totalPnl = pfVal - DAY1_BALANCE;
    var changeEl = document.getElementById('pf-change');
    if (changeEl) {
      var daysSinceStart = Math.max(1, Math.floor((Date.now() - new Date('2026-03-16T00:00:00').getTime()) / 86400000));
      changeEl.textContent = (totalPnl >= 0 ? '+' : '-') + '$' + Math.abs(totalPnl).toFixed(2) + ' all time (Day ' + daysSinceStart + ')';
      changeEl.className = 'portfolio-change ' + (totalPnl > 0 ? 'up' : totalPnl < 0 ? 'down' : 'flat');
    }

    // Hero breakdown (cash + invested under big number)
    var cashHero = document.getElementById('pf-cash-hero');
    var invHero = document.getElementById('pf-invested-hero');
    if (cashHero) cashHero.textContent = '$' + (data.balance_usd || 0).toFixed(2);
    // Show positions market value (what they're worth now, not what you paid)
    var investedVal = data.positions_value_usd || data.total_invested_usd || 0;
    // Portfolio should match Kalshi: cash + positions = total
    // If portfolio_value_usd is available and > cash, derive invested from it
    if (pfVal > 0 && (data.balance_usd || 0) > 0) {
      investedVal = pfVal - (data.balance_usd || 0);
    }
    if (invHero) invHero.textContent = '$' + Math.max(0, investedVal).toFixed(2);

    // Quick stats
    var totalEl = document.getElementById('pf-total');
    if (totalEl) totalEl.textContent = '$' + pfVal.toFixed(2);
    _setText('pf-cash', '$' + (data.balance_usd || 0).toFixed(2));
    _setText('pf-invested', '$' + Math.max(0, investedVal).toFixed(2));

    // Daily P&L (today's settled + current unrealized)
    var dailyPl = (data.daily_pnl_usd !== undefined) ? data.daily_pnl_usd : (data.total_unrealized_usd || 0);
    var dailyEl = document.getElementById('pf-daily-pl');
    if (dailyEl) {
      dailyEl.textContent = (dailyPl >= 0 ? '+' : '') + '$' + Math.abs(dailyPl).toFixed(2);
      dailyEl.style.color = dailyPl >= 0 ? '#00dc5a' : '#ff5000';
    }
    // Total P&L — use /settled endpoint for Day 1+ accuracy (fetched below for win rate)
    var totalPl = data.total_realized_usd || 0;
    var totalPlEl = document.getElementById('pf-total-pl');
    // Will be updated below with settled data if available

    var uPnl = data.total_unrealized_usd || 0;
    var uEl = document.getElementById('pf-unrealized');
    uEl.textContent = (uPnl >= 0 ? '+$' : '-$') + Math.abs(uPnl).toFixed(2);
    uEl.style.color = uPnl >= 0 ? '#00dc5a' : '#ff5000';

    var rPnl = data.total_realized_usd || 0;
    var rEl = document.getElementById('pf-realized');
    rEl.textContent = (rPnl >= 0 ? '+$' : '-$') + Math.abs(rPnl).toFixed(2);
    rEl.style.color = rPnl >= 0 ? '#00dc5a' : '#ff5000';

    // Use /settled endpoint for accurate win rate (same source as scorecard)
    // Use AbortController for 5s timeout so header doesn't show "--" forever
    var wr = data.win_rate || 0;
    var w = data.wins || 0, l = data.losses || 0;
    try {
      var _ac = new AbortController();
      var _to = setTimeout(function(){ _ac.abort(); }, 5000);
      var settledData = await fetch(API + '/settled', {signal: _ac.signal}).then(function(r){return r.json();});
      clearTimeout(_to);
      if (settledData && settledData.win_rate !== undefined) {
        wr = settledData.win_rate || 0;
        w = settledData.wins || 0;
        l = settledData.losses || 0;
      }
      // Use settled P&L for Day 1+ total (more accurate than portfolio-summary journal)
      if (settledData && settledData.total_pnl_usd !== undefined) {
        totalPl = settledData.total_pnl_usd || 0;
      }
    } catch(e) { /* keep fallback values from portfolio-summary */ }
    // Now render P&L Since Day 1 (after settled data is available)
    if (totalPlEl) {
      totalPlEl.textContent = (totalPl >= 0 ? '+$' : '-$') + Math.abs(totalPl).toFixed(2);
      totalPlEl.style.color = totalPl >= 0 ? '#00dc5a' : '#ff5000';
    }
    var wrEl = document.getElementById('pf-winrate');
    wrEl.textContent = wr.toFixed(0) + '%';
    wrEl.style.color = wr >= 60 ? '#00dc5a' : wr >= 40 ? '#ffb400' : '#ff5000';
    var wr7d = document.getElementById('pf-winrate-7d');
    if (wr7d) {
      // Show Day 1+ wins/losses from /settled (already fetched above)
      if (w + l > 0) {
        wr7d.innerHTML = '<span style="color:#00dc5a">' + w + 'W</span> / <span style="color:#ff5000">' + l + 'L</span>';
      } else {
        wr7d.textContent = '0W / 0L';
        wr7d.style.color = '#555';
      }
    }
    var wrBar = document.getElementById('pf-wrbar');
    if (wrBar) {
      wrBar.style.width = Math.max(2, wr) + '%';
      wrBar.style.background = wr >= 60 ? '#00dc5a' : wr >= 40 ? '#ffb400' : '#ff5000';
    }

    var wlEl = document.getElementById('pf-wl');
    wlEl.innerHTML = '<span style="color:#00dc5a">' + w + 'W</span> / <span style="color:#ff5000">' + l + 'L</span>';

    // Positions table (filter out old bot junk)
    var allPos = data.open_positions || [];
    var hidePenny = document.getElementById('hide-bot-trades') && document.getElementById('hide-bot-trades').checked;
    var _botJunk = ['netflix', 'spotify', 'billboard', 'title holder', 'nuclear fusion', 'truth social', 'top song', 'top artist', 'featherweight', 'bantamweight', 'flyweight', 'middleweight', 'welterweight', 'lightweight', 'heavyweight', 'pga tour major', 'ballon d', 'gas prices'];
    var positions = allPos;
    if (hidePenny) {
      positions = allPos.filter(function(p) {
        // Hide any position currently worth 1c or less (dead money, can't sell)
        var nowPrice = p.current_price || p.entry_price || 0;
        if (nowPrice <= 1) return false;
        // Hide penny bot bets under 5c entry
        if (p.placed_by !== 'you' && (p.entry_price || 0) < 5) return false;
        var t = ((p.title || p.ticker) + '').toLowerCase();
        for (var i = 0; i < _botJunk.length; i++) { if (t.indexOf(_botJunk[i]) >= 0) return false; }
        return true;
      });
    }
    var hiddenCount = allPos.length - positions.length;
    var posEl = document.getElementById('portfolio-positions');
    if (positions.length === 0) {
      posEl.innerHTML = '<div style="color:#555;font-size:10px;padding:6px">No open positions</div>';
      return;
    }
    // Sort: biggest P&L movers first, then alphabetical
    positions.sort(function(a, b) {
      var aPnl = Math.abs(a.pnl_pct || 0);
      var bPnl = Math.abs(b.pnl_pct || 0);
      return bPnl - aPnl;
    });
    // Expiry breakdown
    var now = new Date();
    var nowMs = now.getTime();
    var midnight = new Date(now.getFullYear(), now.getMonth(), now.getDate() + 1, 0, 0, 0).getTime();
    var weekEnd = nowMs + (7 * 86400000);
    var monthEnd = nowMs + (30 * 86400000);
    var settlingNow = 0, closingToday = 0, thisWeek = 0, thisMonth = 0, later = 0;
    positions.forEach(function(p) {
      if (!p.close_time) { later++; return; }
      var close = new Date(p.close_time).getTime();
      if (close <= nowMs) settlingNow++;
      else if (close <= midnight) closingToday++;
      else if (close <= weekEnd) thisWeek++;
      else if (close <= monthEnd) thisMonth++;
      else later++;
    });

    var totalUp = positions.filter(function(p) { return (p.pnl_pct || 0) > 0; }).length;
    var totalDown = positions.filter(function(p) { return (p.pnl_pct || 0) < 0; }).length;
    var totalFlat = positions.length - totalUp - totalDown;

    var html = '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:2px">';
    html += '<span class="pos-count" style="font-size:10px;color:#ccc;font-weight:700">' + positions.length + ' open positions</span>';
    html += '<span class="pos-count"><span style="color:#00dc5a">' + totalUp + ' up</span> · <span style="color:#ff5000">' + totalDown + ' down</span> · <span style="color:#555">' + totalFlat + ' flat</span></span>';
    html += '</div>';
    html += '<div style="display:flex;gap:8px;margin-bottom:6px;flex-wrap:wrap">';
    if (settlingNow > 0) html += '<span style="font-size:8px;padding:2px 6px;background:#1a1a1a;border:1px solid #ffb400;border-radius:3px;color:#ffb400">' + settlingNow + ' settling now</span>';
    if (closingToday > 0) html += '<span style="font-size:8px;padding:2px 6px;background:#1a1a1a;border:1px solid #ffcc00;border-radius:3px;color:#ffcc00">' + closingToday + ' closing today</span>';
    if (thisWeek > 0) html += '<span style="font-size:8px;padding:2px 6px;background:#1a1a1a;border:1px solid #00bfff;border-radius:3px;color:#00bfff">' + thisWeek + ' this week</span>';
    if (thisMonth > 0) html += '<span style="font-size:8px;padding:2px 6px;background:#1a1a1a;border:1px solid #888;border-radius:3px;color:#888">' + thisMonth + ' this month</span>';
    if (later > 0) html += '<span style="font-size:8px;padding:2px 6px;background:#1a1a1a;border:1px solid #444;border-radius:3px;color:#555">' + later + ' later</span>';
    html += '</div>';
    // Split into winning and losing
    var winning = positions.filter(function(p) { return (p.pnl_pct || 0) > 0; });
    var losing = positions.filter(function(p) { return (p.pnl_pct || 0) <= 0; });
    // Sort each: biggest movers first
    winning.sort(function(a, b) { return (b.pnl_pct || 0) - (a.pnl_pct || 0); });
    losing.sort(function(a, b) { return (a.pnl_pct || 0) - (b.pnl_pct || 0); });

    var winPnl = winning.reduce(function(s, p) { return s + (p.unrealized_pnl_cents || 0); }, 0);
    var losePnl = losing.reduce(function(s, p) { return s + (p.unrealized_pnl_cents || 0); }, 0);

    function buildPosTable(arr, label, color, totalCents) {
      var t = '<div style="flex:1;min-width:300px">';
      t += '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px">';
      t += '<span style="font-size:11px;font-weight:700;color:' + color + '">' + label + ' (' + arr.length + ')</span>';
      t += '<span style="font-size:10px;font-weight:700;color:' + color + '">' + (totalCents >= 0 ? '+' : '') + '$' + (Math.abs(totalCents) / 100).toFixed(2) + '</span>';
      t += '</div>';
      if (arr.length === 0) {
        t += '<div style="color:#555;font-size:9px;padding:8px;text-align:center;background:#0a0a0a;border-radius:8px">None</div>';
        t += '</div>';
        return t;
      }
      t += '<div class="pos-scroll" style="max-height:350px"><table class="pos-table-compact"><thead><tr><th>Market</th><th>Side</th><th>Now</th><th>P&L</th><th>Exp</th><th></th></tr></thead><tbody>';
      arr.forEach(function(p) {
        var sideColor = p.side === 'yes' ? '#00dc5a' : '#ff5000';
        var pnlText = '--';
        var pnlColor = '#555';
        if (p.pnl_pct !== null && p.pnl_pct !== undefined) {
          pnlColor = p.pnl_pct > 0 ? '#00dc5a' : p.pnl_pct < 0 ? '#ff5000' : '#555';
          var cents = p.unrealized_pnl_cents || 0;
          pnlText = (p.pnl_pct >= 0 ? '+' : '') + p.pnl_pct + '%';
          if (Math.abs(cents) >= 1) pnlText += ' ($' + (cents >= 0 ? '+' : '-') + (Math.abs(cents) / 100).toFixed(2) + ')';
        }
        var timeLeft = formatSettleTime(p.close_time);
        var sellPrice = p.current_price ? Math.max(1, p.current_price - 1) : 0;
        var sparkColor = (p.pnl_pct || 0) >= 0 ? '#00dc5a' : '#ff5000';
        var entry = p.entry_price || 50;
        var curr = p.current_price || entry;
        var sparkY1 = Math.max(2, Math.min(14, 16 - (entry / 100 * 14)));
        var sparkY2 = Math.max(2, Math.min(14, 16 - (curr / 100 * 14)));
        var spark = '<svg class="sparkline" width="24" height="14" viewBox="0 0 24 14"><line x1="1" y1="' + sparkY1 + '" x2="22" y2="' + sparkY2 + '" stroke="' + sparkColor + '" stroke-width="1.5" stroke-linecap="round"/><circle cx="22" cy="' + sparkY2 + '" r="1.5" fill="' + sparkColor + '"/></svg>';
        t += '<tr>';
        var placedTag = p.placed_by === 'bot' ? '<span style="font-size:7px;padding:1px 3px;background:#1a1a2e;border:1px solid #4a4ae0;border-radius:3px;color:#7a7aff;margin-right:4px;vertical-align:middle" title="Placed by TradeShark bot">BOT</span>' : p.placed_by === 'unknown' ? '<span style="font-size:7px;padding:1px 3px;background:#2e2e1a;border:1px solid #8a8a3a;border-radius:3px;color:#bfbf5a;margin-right:4px;vertical-align:middle" title="Source unknown — placed before last restart">?</span>' : '<span style="font-size:7px;padding:1px 3px;background:#1a2e1a;border:1px solid #3a8a3a;border-radius:3px;color:#5abf5a;margin-right:4px;vertical-align:middle" title="Placed by you">YOU</span>';
        var _sc = (window._positionScores || {})[p.ticker];
        var _scoreHtml = '';
        if (_sc && _sc.display) {
          var _scColor = _sc.state === 'in' ? '#ffb400' : _sc.state === 'post' ? '#888' : '#555';
          _scoreHtml = '<div style="font-size:8px;color:' + _scColor + ';margin-top:1px">&#9889; ' + _sc.display + '</div>';
        }
        t += '<td style="max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + placedTag + '<a href="https://kalshi.com/markets/' + p.ticker + '" target="_blank" style="color:#ddd;font-size:9px">' + (p.title || p.ticker) + '</a>' + _scoreHtml + '</td>';
        t += '<td style="color:' + sideColor + ';font-weight:700;font-size:8px">' + p.side.toUpperCase() + '</td>';
        t += '<td style="font-weight:700;font-size:8px">' + (p.current_price || '?') + 'c' + spark + '</td>';
        t += '<td style="color:' + pnlColor + ';font-weight:700;font-size:8px">' + pnlText + '</td>';
        t += '<td style="color:#ffb400;font-size:8px">' + timeLeft + '</td>';
        if (sellPrice > 0) {
          t += '<td><button class="hero-execute" style="font-size:7px;padding:1px 5px" onclick="sellPosition(&quot;' + p.ticker + '&quot;,&quot;' + p.side + '&quot;,' + sellPrice + ',' + p.count + ')">SELL</button></td>';
        } else {
          t += '<td></td>';
        }
        t += '</tr>';
      });
      t += '</tbody></table></div></div>';
      return t;
    }

    html += '<div style="display:grid;grid-template-columns:1fr 1fr;gap:16px">';
    html += buildPosTable(winning, 'Winning', '#00dc5a', winPnl);
    html += buildPosTable(losing, 'Losing', '#ff5000', losePnl);
    html += '</div>';
    if (hiddenCount > 0) {
      html += '<div style="margin-top:6px;font-size:9px;color:#555">' + hiddenCount + ' old bot positions hidden (uncheck toggle to show all)</div>';
    }

    // Split by placed_by: YOU vs BOT
    var myBets = positions.filter(function(p) { return p.placed_by === 'you'; });
    var botBets = positions.filter(function(p) { return p.placed_by === 'bot'; });
    var legacyBets = positions.filter(function(p) { return p.placed_by === 'legacy'; });
    if (legacyBets.length > 0) {
      hiddenCount += legacyBets.length;
    }
    var myPnl = myBets.reduce(function(s, p) { return s + (p.unrealized_pnl_cents || 0); }, 0);
    var botPnl = botBets.reduce(function(s, p) { return s + (p.unrealized_pnl_cents || 0); }, 0);
    html += '<div style="margin-top:16px;display:grid;grid-template-columns:1fr 1fr;gap:16px">';
    html += buildPosTable(myBets, '👤 My Bets', '#5abf5a', myPnl);
    html += buildPosTable(botBets, '🤖 Bot Bets', '#7a7aff', botPnl);
    html += '</div>';

    posEl.innerHTML = html;
  } catch(e) {
    console.error('Portfolio load error:', e);
  }
}

async function loadActivity() {
  try {
    const data = await fetch(API + '/bot-activity').then(r => r.json());
    const items = data.activity || [];
    if (items.length === 0) return;
    const el = document.getElementById('activity-lines');
    let html = '';
    items.slice().reverse().forEach(a => {
      var msg = a.msg || '';
      // Filter out noisy repeated messages
      if (msg.indexOf('failed:') >= 0 && msg.indexOf('409') >= 0) return;  // 409 order rejections
      if (msg.indexOf('Scanning all platforms') >= 0) return;  // redundant scan start
      var t = fmtTimeSec(a.time);
      var lvl = a.level || 'info';
      html += '<div class="activity-line">';
      html += '<span class="time">' + t + '</span>';
      html += '<span class="dot ' + lvl + '"></span>';
      html += '<span class="msg ' + lvl + '">' + msg.substring(0, 80) + (msg.length > 80 ? '...' : '') + '</span>';
      html += '</div>';
    });
    el.innerHTML = html;
    // Also update dashboard version
    var dashEl = document.getElementById('activity-lines-dash');
    if (dashEl) dashEl.innerHTML = html;
  } catch(e) {}
}

async function loadActivityDash() { loadActivity(); }
async function loadBetsFeedDash() { loadBetsFeed(); }

async function loadBetsFeed() {
  try {
    var data = await fetch(API + '/trades-today').then(r => r.json());
    var trades = data.trades || [];
    var el = document.getElementById('bets-lines');
    // Update both old and dashboard badge counts
    var countEl = document.getElementById('bets-today-count');
    var countElDash = document.getElementById('bets-today-count-dash');
    if (countEl) countEl.textContent = trades.length;
    if (countElDash) countElDash.textContent = trades.length;
    if (trades.length === 0) {
      el.innerHTML = '<div class="activity-line"><span class="time">--:--</span><span class="dot info"></span><span class="msg" style="color:#666">No bets placed today</span></div>';
      return;
    }
    // Fetch live scores for all trades in parallel
    var scoreMap = {};
    try {
      var tickers = trades.map(function(t){ return t.ticker || ''; }).join('|');
      var titles = trades.map(function(t){ return t.title || t.ticker || ''; }).join('|');
      var scData = await fetch(API + '/live-scores?tickers=' + encodeURIComponent(tickers) + '&titles=' + encodeURIComponent(titles)).then(function(r){ return r.json(); });
      scoreMap = scData.scores || {};
    } catch(e) {}
    var h = '';
    trades.forEach(function(t) {
      var timeStr = fmtTime(t.time);
      var sideC = t.side === 'yes' ? '#00dc5a' : '#ff5000';
      var stratColors = {sniper:'#ffb400', quant:'#00d4ff', bot:'#888', moonshark:'#e040fb', closegame:'#00d4ff', manual:'#5abf5a', moonshark_manual:'#5abf5a', live_sniper:'#ffb400'};
      var stratLabels = {sniper:'SNIPER', quant:'QUANT', bot:'BOT', moonshark:'MOONSHARK', closegame:'CLOSEGAME', manual:'MANUAL', moonshark_manual:'MOONSHOT', live_sniper:'SNIPER'};
      var sc = stratColors[t.strategy] || '#888';
      var sl = stratLabels[t.strategy] || (t.strategy || 'bot').toUpperCase();
      var title = (t.title || t.ticker || '').substring(0, 40);
      var sourceTag = t.source === 'you' ? '<span style="font-size:7px;padding:1px 3px;background:#1a2e1a;border:1px solid #3a8a3a;border-radius:3px;color:#5abf5a;margin-right:4px">YOU</span>' : '<span style="font-size:7px;padding:1px 3px;background:#1a1a2e;border:1px solid #4a4ae0;border-radius:3px;color:#7a7aff;margin-right:4px">BOT</span>';
      // Build tooltip with edge reasoning
      var tooltipLines = [];
      if (t.edge_reasons && t.edge_reasons.length > 0) {
        tooltipLines.push('WHY THIS BET:');
        t.edge_reasons.forEach(function(r) { tooltipLines.push('  ' + r); });
      }
      if (t.conviction) tooltipLines.push('Conviction: ' + t.conviction + '/5');
      if (t.espn_edge) tooltipLines.push('ESPN Edge: +' + (t.espn_edge * 100).toFixed(1) + '%');
      if (t.potential_profit) tooltipLines.push('Potential Profit: +$' + t.potential_profit.toFixed(2));
      tooltipLines.push('Entry: ' + (t.price_cents || 0) + '\u00A2 x' + (t.count || 0));
      tooltipLines.push('Cost: $' + (t.cost_usd || 0).toFixed(2));
      var tooltipText = tooltipLines.join('\\n');
      h += '<div class="activity-line" style="cursor:pointer;position:relative" title="' + tooltipText.replace(/"/g, '&quot;') + '">';
      h += '<span class="time">' + timeStr + '</span>';
      h += '<span class="dot" style="background:' + sc + '"></span>';
      h += '<span class="msg">' + sourceTag + '<span style="color:' + sc + ';font-weight:700;font-size:8px;margin-right:4px">' + sl + '</span>';
      h += '<span style="color:' + sideC + ';font-weight:700">' + (t.side || '').toUpperCase() + '</span> ';
      h += '<span style="color:#fff;font-weight:700;margin-right:4px">$' + (t.cost_usd || 0).toFixed(2) + '</span> ';
      h += '<span style="color:#ccc">' + title + '</span> ';
      // Result / P&L indicator
      var pnl = t.pnl_pct || 0;
      var isSettling = t.close_time && new Date(t.close_time) <= new Date();
      if (t.result === 'win') {
        h += '<span style="color:#00dc5a;font-size:10px;font-weight:700;margin-left:4px;padding:1px 6px;background:#0a2a0a;border:1px solid #00dc5a;border-radius:4px">✓ WON +$' + Math.abs(t.result_pnl || 0).toFixed(2) + '</span> ';
      } else if (t.result === 'loss') {
        h += '<span style="color:#ff5000;font-size:10px;font-weight:700;margin-left:4px;padding:1px 6px;background:#2a0a0a;border:1px solid #ff5000;border-radius:4px">✗ LOST -$' + Math.abs(t.result_pnl || 0).toFixed(2) + '</span> ';
      } else if (isSettling && t.current_price === 50) {
        h += '<span style="color:#ffb400;font-size:10px;margin-left:4px">⏳ Awaiting result</span> ';
      } else if (t.current_price && t.price_cents && t.current_price !== 50) {
        var pnlColor = pnl > 0 ? '#00dc5a' : (pnl < 0 ? '#ff5000' : '#888');
        var pnlArrow = pnl > 0 ? '▲' : (pnl < 0 ? '▼' : '–');
        h += '<span style="color:' + pnlColor + ';font-size:10px;font-weight:700;margin-left:4px">' + pnlArrow + ' ' + (pnl > 0 ? '+' : '') + pnl + '% (' + t.current_price + '¢)</span> ';
      }
      // Time until settlement
      var settleStr = '';
      if (t.close_time) {
        try {
          var ct = new Date(t.close_time);
          var diff = ct - new Date();
          if (diff <= 0) { settleStr = 'Settling now'; }
          else if (diff < 3600000) { settleStr = Math.ceil(diff/60000) + 'm'; }
          else if (diff < 86400000) { settleStr = Math.floor(diff/3600000) + 'h ' + Math.floor((diff%3600000)/60000) + 'm'; }
          else { settleStr = Math.floor(diff/86400000) + 'd ' + Math.floor((diff%86400000)/3600000) + 'h'; }
        } catch(e) {}
      }
      if (settleStr) h += '<span style="color:#555;font-size:10px;margin-left:4px">⏱ ' + settleStr + '</span>';
      // Live score display
      var scoreInfo = scoreMap[t.ticker];
      if (scoreInfo && scoreInfo.display) {
        var scoreColor = scoreInfo.state === 'in' ? '#00d4ff' : (scoreInfo.state === 'post' ? '#888' : '#ffb400');
        var scoreIcon = scoreInfo.state === 'in' ? '⚡' : (scoreInfo.state === 'post' ? '✓' : '🏀');
        h += '<span style="color:' + scoreColor + ';font-size:10px;margin-left:4px">' + scoreIcon + ' ' + scoreInfo.display + '</span>';
      }
      h += '</span>';
      // Expandable edge detail row (hidden by default, toggles on click)
      if (t.edge_reasons && t.edge_reasons.length > 0) {
        var edgeId = 'edge-' + (t.ticker || '').replace(/[^a-zA-Z0-9]/g, '_') + '-' + (t.side || '');
        h += '<div id="' + edgeId + '" style="display:none;margin:4px 0 2px 24px;padding:6px 10px;background:#0d1117;border:1px solid #1f2937;border-radius:6px;font-size:10px;line-height:1.6">';
        h += '<div style="color:#ffb400;font-weight:700;margin-bottom:3px">WHY THIS BET</div>';
        t.edge_reasons.forEach(function(r) {
          h += '<div style="color:#aaa">• ' + r + '</div>';
        });
        if (t.conviction) h += '<div style="color:#00d4ff;margin-top:3px">Conviction: ' + t.conviction + '/5</div>';
        if (t.potential_profit) h += '<div style="color:#00dc5a;margin-top:2px">Potential profit: +$' + t.potential_profit.toFixed(2) + '</div>';
        h += '</div>';
      }
      h += '</div>';
    });
    el.innerHTML = h;
    // Add click handlers to toggle edge detail
    el.querySelectorAll('.activity-line').forEach(function(line) {
      line.addEventListener('click', function() {
        var detail = line.querySelector('[id^="edge-"]');
        if (detail) {
          detail.style.display = detail.style.display === 'none' ? 'block' : 'none';
        }
      });
    });
    // Also update dashboard version
    var dashBetsEl = document.getElementById('bets-lines-dash');
    if (dashBetsEl) {
      dashBetsEl.innerHTML = h;
      dashBetsEl.querySelectorAll('.activity-line').forEach(function(line) {
        line.addEventListener('click', function() {
          var detail = line.querySelector('[id^="edge-"]');
          if (detail) {
            detail.style.display = detail.style.display === 'none' ? 'block' : 'none';
          }
        });
      });
    }
    // Pulse the dot
    var pulse = document.getElementById('bets-pulse');
    if (pulse && trades.length > 0) pulse.style.background = '#ffb400';
  } catch(e) {}
}

async function loadAllBets() {
  try {
    const data = await fetch(API + '/trades').then(r => r.json());
    const trades = data.trades || [];
    _setText('all-bets-count', trades.length);
    if (trades.length === 0) {
      _setHTML('all-bets-table', '<div class="empty">No bets yet</div>');
      return;
    }
    let html = '<table><tr><th>Date</th><th>Market</th><th>Side</th><th>Qty</th><th>Entry</th><th>Cost</th><th>Result</th><th>Source</th></tr>';
    trades.slice().reverse().forEach(t => {
      var time = '--';
      if (t.timestamp) {
        try {
          var ts = t.timestamp;
          if (ts.indexOf('Z') < 0 && ts.indexOf('+') < 0 && ts.indexOf('-', 10) < 0) ts += 'Z';
          var d = new Date(ts);
          time = isNaN(d.getTime()) ? ts.substring(0, 10) : d.toLocaleDateString();
        } catch(e) { time = t.timestamp.substring(0, 10); }
      }
      var sideClass = t.side === 'yes' ? 'side-yes' : 'side-no';
      var resultClass, resultLabel;
      if (t.outcome === 'win') {
        resultClass = 'result-win';
        resultLabel = 'WON' + (t.pnl_usd ? ' +$' + Math.abs(t.pnl_usd).toFixed(2) : '');
      } else if (t.outcome === 'loss') {
        resultClass = 'result-loss';
        resultLabel = 'LOST' + (t.pnl_usd ? ' -$' + Math.abs(t.pnl_usd).toFixed(2) : '');
      } else if (t.outcome === 'even') {
        resultClass = '';
        resultLabel = 'EVEN';
      } else {
        resultClass = '';
        resultLabel = 'Open';
      }
      var source = t.source === 'kalshi_fill' ? 'Kalshi' : (t.manual ? 'YOU' : 'BOT');
      var sourceColor = t.manual ? '#5abf5a' : '#7a7aff';
      var qty = t.count || 1;
      var title = (t.question || t.title || t.ticker || '').substring(0, 45);
      html += '<tr>';
      html += '<td>' + time + '</td>';
      html += '<td>' + title + '</td>';
      html += '<td class="' + sideClass + '">' + qty + 'x ' + (t.side || '').toUpperCase() + '</td>';
      html += '<td>' + qty + '</td>';
      html += '<td>' + (t.price_cents || '--') + 'c</td>';
      html += '<td>$' + (t.cost_usd || (t.price_cents || 0)/100).toFixed(2) + '</td>';
      html += '<td class="' + resultClass + '">' + resultLabel + '</td>';
      html += '<td style="color:' + sourceColor + '">' + source + '</td>';
      html += '</tr>';
    });
    html += '</table>';
    _setHTML('all-bets-table', html);
  } catch(e) {
    _setHTML('all-bets-table', '<div class="empty">Error loading bets</div>');
  }
}

let _mispricedFirstLoad = true;
async function loadMispriced() {
  if (_mispricedFirstLoad) _setHTML('opp-table', '<div class="loading">Scanning markets...</div>');
  try {
    const data = await fetch(API + '/mispriced').then(r => r.json());
    _mispricedFirstLoad = false;
    _setText('opp-badge', data.mispriced_count);
    if (!data.mispricings || data.mispricings.length === 0) {
      _setHTML('opp-table', '<div class="empty">No mispriced markets found right now. The bot scans every 10 minutes.</div>');
      return;
    }
    let html = '<table><tr><th>Market</th><th>Signal</th><th>Kalshi</th><th>Consensus</th><th>Deviation</th><th>Confidence</th><th>Platforms</th><th>Action</th></tr>';
    data.mispricings.forEach(m => {
      const dev = (m.deviation * 100).toFixed(1);
      const conf = m.deviation >= 0.25 ? 'high' : m.deviation >= 0.18 ? 'med' : 'low';
      const confLabel = conf === 'high' ? 'Strong' : conf === 'med' ? 'Medium' : 'Weak';
      const sideClass = m.signal === 'buy_yes' ? 'side-yes' : 'side-no';
      const sideLabel = m.signal === 'buy_yes' ? 'BUY YES' : 'BUY NO';
      const plats = m.matching_platforms.map(p => p.platform).join(', ');
      html += '<tr>';
      html += '<td><a href="' + m.kalshi_url + '" target="_blank">' + m.kalshi_question.substring(0, 60) + '</a></td>';
      html += '<td class="' + sideClass + '">' + sideLabel + '</td>';
      html += '<td>' + (m.kalshi_yes_price * 100).toFixed(0) + '¢</td>';
      html += '<td>' + (m.consensus_yes_price * 100).toFixed(0) + '¢</td>';
      html += '<td>' + dev + '%</td>';
      html += '<td><span class="confidence conf-' + conf + '">' + confLabel + '</span></td>';
      html += '<td>' + plats + '</td>';
      var mSide = m.signal === 'buy_yes' ? 'YES' : 'NO';
      var mCt = Math.max(1, Math.floor(500 / m.price_cents));
      var mCost = (m.price_cents * mCt / 100).toFixed(2);
      html += '<td><button class="trade-btn" onclick="executeTrade(this, ' + JSON.stringify(JSON.stringify(m)) + ')">Buy ' + mSide + ' · $' + mCost + '</button></td>';
      html += '</tr>';
    });
    html += '</table>';
    _setHTML('opp-table', html);
  } catch(e) {
    _setHTML('opp-table', '<div class="empty">Error loading: ' + e.message + '</div>');
  }
}

async function executeTrade(btn, mJson) {
  const m = JSON.parse(mJson);
  btn.disabled = true;
  btn.textContent = 'Placing...';
  try {
    const res = await fetch(API + '/execute-trade', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({
        ticker: m.kalshi_ticker,
        side: m.signal.replace('buy_', ''),
        price_cents: m.price_cents,
        question: m.kalshi_question,
        deviation: m.deviation,
        consensus_price: m.consensus_yes_price,
        kalshi_price: m.kalshi_yes_price,
        matching_platforms: m.matching_platforms,
      })
    });
    const data = await res.json();
    if (data.success) {
      btn.textContent = 'Done!';
      btn.style.background = '#00d4aa';
      showToast('Order filled: ' + m.kalshi_ticker, 'success');
    } else {
      btn.textContent = 'Failed';
      btn.style.background = '#ef4444';
      const errMsg = data.result && data.result.response_body ? data.result.response_body : (data.result && data.result.error ? data.result.error : 'Unknown error');
      showToast('Trade failed: ' + errMsg, 'error');
    }
    loadStatus();
    loadTrades();
  } catch(e) {
    btn.textContent = 'Error';
    btn.style.background = '#ef4444';
    showToast('Network error: ' + e.message, 'error');
  }
}

function drawPickChart(canvasId, prices, signal) {
  const canvas = document.getElementById(canvasId);
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.parentElement.getBoundingClientRect();
  canvas.width = rect.width * dpr;
  canvas.height = rect.height * dpr;
  ctx.scale(dpr, dpr);
  const w = rect.width, h = rect.height;
  ctx.clearRect(0, 0, w, h);

  const entries = Object.entries(prices);
  if (entries.length === 0) return;
  const barW = Math.min(60, (w - 40) / entries.length - 10);
  const maxVal = 100;
  const padTop = 14, padBot = 18;
  const chartH = h - padTop - padBot;
  const startX = (w - (entries.length * (barW + 10) - 10)) / 2;

  entries.forEach(([plat, price], i) => {
    const x = startX + i * (barW + 10);
    const barH = (price / maxVal) * chartH;
    const y = padTop + chartH - barH;

    // Bar color: Kalshi in orange, others in teal
    const isKalshi = plat.toLowerCase().includes('kalshi');
    const grad = ctx.createLinearGradient(x, y, x, y + barH);
    if (isKalshi) {
      grad.addColorStop(0, '#ffb400');
      grad.addColorStop(1, '#cc7000');
    } else {
      grad.addColorStop(0, '#00d4aa');
      grad.addColorStop(1, '#0891b2');
    }
    ctx.fillStyle = grad;
    ctx.fillRect(x, y, barW, barH);

    // Highlight border
    ctx.strokeStyle = isKalshi ? '#ffaa33' : '#00ffcc';
    ctx.lineWidth = 1;
    ctx.strokeRect(x, y, barW, barH);

    // Price label on top
    ctx.fillStyle = '#fff';
    ctx.font = '10px Courier New';
    ctx.textAlign = 'center';
    ctx.fillText(price.toFixed(0) + '¢', x + barW/2, y - 3);

    // Platform label below
    ctx.fillStyle = '#888';
    ctx.font = '8px Courier New';
    const label = plat.replace('kalshi_yes','KALSHI Y').replace('kalshi_no','KALSHI N').replace('kalshi','KALSHI').replace('polymarket','POLY').replace('predictit','PREDIT').replace('manifold','MANIFD').toUpperCase();
    ctx.fillText(label.substring(0, 7), x + barW/2, h - 4);
  });

  // Dashed 50¢ reference line
  const midY = padTop + chartH * 0.5;
  ctx.strokeStyle = '#333';
  ctx.setLineDash([3, 3]);
  ctx.beginPath();
  ctx.moveTo(10, midY);
  ctx.lineTo(w - 10, midY);
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = '#444';
  ctx.font = '8px Courier New';
  ctx.textAlign = 'left';
  ctx.fillText('50¢', 2, midY - 2);
}

let _picksFirstLoad = true;
let _picksData = [];

function renderPickCard(p, idx, prefix) {
  const sigClass = p.signal === 'buy_yes' ? 'yes' : 'no';
  const sigLabel = p.signal === 'buy_yes' ? 'BET YES' : 'BET NO';
  const confClass = p.confidence.toLowerCase();
  const typeLabels = {consensus: 'CROSS-PLATFORM', arbitrage: 'ARBITRAGE', cross_validated: 'VERIFIED', kalshi_only: 'KALSHI ONLY', news_researched: 'NEWS + DATA', high_probability: 'HIGH PROB'};
  const typeLabel = typeLabels[p.type] || 'PICK';
  const typeColors = {consensus: '#00dc5a', arbitrage: '#ffb400', cross_validated: '#00d4ff', kalshi_only: '#666', news_researched: '#c084fc', high_probability: '#4a9eff'};
  const typeColor = typeColors[p.type] || '#888';
  let h = '<div class="pick-card">';
  h += '<div class="pick-rank">#' + (idx + 1) + '</div>';
  h += '<div class="pick-header">';
  h += '<span class="pick-signal ' + sigClass + '">' + sigLabel + '</span>';
  h += '<span class="pick-conf ' + confClass + '">' + p.confidence + '</span>';
  h += '<span class="pick-meta" style="color:' + typeColor + '">' + typeLabel + '</span>';
  var winPct = (p.win_probability || 0.5) * 100;
  var wpColor = winPct >= 75 ? '#00dc5a' : winPct >= 55 ? '#ffb400' : '#ffcc00';
  h += '<span class="pick-meta" style="color:' + wpColor + ';font-weight:700;font-size:1.2em">' + winPct.toFixed(0) + '%</span>';
  var pickSettle = formatSettleTime(p.close_time);
  h += '<span class="pick-meta" style="color:#ffb400;font-weight:600">⏱ ' + pickSettle + '</span>';
  if (p.platform_count > 0) h += '<span class="pick-meta">' + (p.platform_count + 1) + ' platforms</span>';
  if (p.volume > 0) h += '<span class="pick-meta" style="color:#666">' + p.volume.toLocaleString() + ' vol</span>';
  h += '</div>';
  h += '<div class="pick-question"><a href="' + p.kalshi_url + '" target="_blank">' + p.kalshi_question + '</a></div>';
  var pickYL = p.yes_label || 'Yes';
  var pickNL = p.no_label || 'No';
  var pickBetMeaning = p.signal === 'buy_yes' ? pickYL : pickNL;
  if (pickBetMeaning !== 'Yes' && pickBetMeaning !== 'No') {
    h += '<div style="font-size:9px;color:#ffcc00;font-weight:600;margin-bottom:2px">→ Betting: ' + pickBetMeaning + '</div>';
  }
  // Edge reason — single sentence explaining why
  var pickEdgeReason = p.edge_reason || '';
  if (pickEdgeReason) {
    h += '<div style="font-size:8px;color:#aaa;font-style:italic;line-height:1.3;margin:2px 0 4px">' + pickEdgeReason + '</div>';
  }
  h += '<div class="pick-edge">' + p.edge_summary + '</div>';
  // News headlines
  if (p.news && p.news.length > 0) {
    var sentColor = p.news_sentiment === 'bullish' ? '#00dc5a' : p.news_sentiment === 'bearish' ? '#ff5000' : '#888';
    var confirmIcon = p.news_confirms ? '✓' : '';
    h += '<div class="pick-news" style="margin:4px 0;padding:4px 6px;background:#111;border-left:2px solid ' + sentColor + ';font-size:8px;max-height:48px;overflow:hidden">';
    h += '<div style="color:' + sentColor + ';font-weight:700;margin-bottom:2px;text-transform:uppercase;letter-spacing:0.5px">📰 ' + p.news_sentiment + ' ' + confirmIcon + '</div>';
    p.news.forEach(function(n) {
      h += '<div style="color:#999;line-height:1.3;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">';
      h += '<span style="color:#666">' + n.source + '</span> ' + n.title;
      if (n.age) h += ' <span style="color:#555">' + n.age + '</span>';
      h += '</div>';
    });
    h += '</div>';
  }
  h += '<div class="pick-chart"><canvas id="' + prefix + '-chart-' + idx + '"></canvas></div>';
  h += '<div class="pick-thesis">' + p.thesis + '</div>';
  h += '<div class="pick-footer">';
  h += '<span class="pick-meta">COST <b>' + p.price_cents + '¢</b></span>';
  h += '<span class="pick-profit">+$' + p.potential_profit_usd.toFixed(2) + ' potential</span>';
  var ct = Math.max(1, Math.floor(500 / p.price_cents));
  var cost = (p.price_cents * ct / 100).toFixed(2);
  var sideWord = p.signal === 'buy_yes' ? 'YES' : 'NO';
  h += '<button class="pick-execute" onclick="executePickTrade(this, ' + p._globalIdx + ')">Buy ' + sideWord + ' · $' + cost + '</button>';
  h += '</div>';
  h += '</div>';
  return h;
}

function _gsConviction(p) {
  var score = 0;
  // Cross-platform validation is the strongest signal
  var platCount = (p.platform_count || 0) + 1;
  if (platCount >= 4) score += 3;
  else if (platCount >= 3) score += 2;
  else if (platCount >= 2) score += 1;
  // High win probability
  var wp = (p.win_probability || 0.5) * 100;
  if (wp >= 80) score += 3;
  else if (wp >= 70) score += 2;
  else if (wp >= 60) score += 1;
  // Volume = institutional interest
  var vol = p.volume || 0;
  if (vol >= 5000) score += 2;
  else if (vol >= 1000) score += 1;
  // News confirms thesis
  if (p.news_confirms) score += 1;
  // Deviation = edge size
  if ((p.deviation || 0) >= 0.3) score += 1;
  // Map to conviction
  if (score >= 8) return {label: 'STRONG BUY', color: '#00dc5a', stars: 5};
  if (score >= 6) return {label: 'BUY', color: '#00dc5a', stars: 4};
  if (score >= 4) return {label: 'OVERWEIGHT', color: '#ffb400', stars: 3};
  if (score >= 2) return {label: 'MARKET WEIGHT', color: '#888', stars: 2};
  return {label: 'SPECULATIVE', color: '#ff5000', stars: 1};
}

function _gsThesis(p) {
  var parts = [];
  var platCount = (p.platform_count || 0) + 1;
  var wp = ((p.win_probability || 0.5) * 100).toFixed(0);
  var dev = ((p.deviation || 0) * 100).toFixed(0);
  var side = p.signal === 'buy_yes' ? 'YES' : 'NO';
  // Primary thesis
  if (platCount >= 3) {
    parts.push('Cross-platform consensus across ' + platCount + ' independent exchanges confirms ' + side + ' at ' + wp + '% probability.');
  } else if (platCount >= 2) {
    parts.push('Dual-platform validation supports ' + side + ' position with ' + wp + '% implied probability.');
  } else {
    parts.push('Single-platform signal at ' + wp + '% implied probability on the ' + side + ' side.');
  }
  // Edge
  if ((p.deviation || 0) > 0.15) {
    parts.push('Kalshi is mispriced by ' + dev + '% vs consensus, creating an exploitable edge.');
  }
  // News
  if (p.news_confirms) {
    parts.push('Recent news flow confirms directional bias.');
  }
  // Risk
  var vol = p.volume || 0;
  if (vol < 500) {
    parts.push('Liquidity risk: low volume (' + vol + ') may impact exit.');
  }
  return parts.join(' ');
}

function _gsRiskLevel(p) {
  var wp = (p.win_probability || 0.5) * 100;
  var vol = p.volume || 0;
  if (wp >= 80 && vol >= 1000) return {label: 'LOW', color: '#00dc5a'};
  if (wp >= 65 && vol >= 500) return {label: 'MODERATE', color: '#ffb400'};
  return {label: 'ELEVATED', color: '#ff5000'};
}

function renderGSTile(p, idx) {
  var conv = _gsConviction(p);
  var thesis = _gsThesis(p);
  var risk = _gsRiskLevel(p);
  var side = p.signal === 'buy_yes' ? 'YES' : 'NO';
  var sideColor = p.signal === 'buy_yes' ? '#00dc5a' : '#ff5000';
  var wp = ((p.win_probability || 0.5) * 100).toFixed(0);
  var platCount = (p.platform_count || 0) + 1;
  var settleTime = formatSettleTime(p.close_time);
  var ct = Math.max(1, Math.floor(500 / p.price_cents));
  var cost = (p.price_cents * ct / 100).toFixed(2);
  var profit = ((100 - p.price_cents) * ct / 100).toFixed(2);
  var stars = '';
  for (var s = 0; s < 5; s++) stars += '<span style="color:' + (s < conv.stars ? '#ffb400' : '#333') + '">&#9733;</span>';

  var h = '<div style="background:#0d0d0d;border:1px solid #1a1a1a;border-radius:10px;padding:14px;position:relative;border-left:3px solid ' + conv.color + '">';
  // Header row
  h += '<div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:8px">';
  h += '<div style="flex:1">';
  h += '<div style="font-size:7px;font-weight:700;color:' + conv.color + ';letter-spacing:1px;margin-bottom:2px">' + conv.label + '</div>';
  h += '<div style="font-size:8px;color:#666">' + stars + '</div>';
  h += '</div>';
  h += '<div style="text-align:right">';
  h += '<div style="font-size:20px;font-weight:800;color:' + sideColor + '">' + side + ' ' + wp + '%</div>';
  h += '<div style="font-size:8px;color:#666">' + p.price_cents + '&#162; entry | ' + settleTime + '</div>';
  h += '</div>';
  h += '</div>';

  // Market question
  h += '<div style="font-size:11px;color:#ddd;font-weight:600;margin-bottom:6px;line-height:1.3"><a href="' + (p.kalshi_url || '#') + '" target="_blank" style="color:#ddd;text-decoration:none">' + (p.kalshi_question || p.ticker || 'Unknown Market') + '</a></div>';

  // Investment thesis
  h += '<div style="font-size:9px;color:#999;line-height:1.4;margin-bottom:8px;border-left:2px solid #222;padding-left:8px">' + thesis + '</div>';

  // News headlines
  var news = p.news || [];
  if (news.length > 0) {
    h += '<div style="margin-bottom:8px">';
    h += '<div style="font-size:7px;color:#555;font-weight:700;letter-spacing:0.5px;margin-bottom:3px">CATALYST</div>';
    news.slice(0, 2).forEach(function(n) {
      h += '<div style="font-size:8px;color:#888;margin-bottom:1px">&#x2022; ' + (n.title || n).toString().substring(0, 70) + '</div>';
    });
    h += '</div>';
  }

  // Metrics row
  h += '<div style="display:flex;gap:10px;margin-bottom:8px;flex-wrap:wrap">';
  h += '<div style="text-align:center"><div style="font-size:7px;color:#555;font-weight:600">PLATFORMS</div><div style="font-size:12px;font-weight:800;color:#00d4ff">' + platCount + '</div></div>';
  h += '<div style="text-align:center"><div style="font-size:7px;color:#555;font-weight:600">VOLUME</div><div style="font-size:12px;font-weight:800;color:#ccc">' + (p.volume || 0).toLocaleString() + '</div></div>';
  h += '<div style="text-align:center"><div style="font-size:7px;color:#555;font-weight:600">EDGE</div><div style="font-size:12px;font-weight:800;color:#ffb400">' + ((p.deviation || 0) * 100).toFixed(0) + '%</div></div>';
  h += '<div style="text-align:center"><div style="font-size:7px;color:#555;font-weight:600">RISK</div><div style="font-size:12px;font-weight:800;color:' + risk.color + '">' + risk.label + '</div></div>';
  h += '<div style="text-align:center"><div style="font-size:7px;color:#555;font-weight:600">POTENTIAL</div><div style="font-size:12px;font-weight:800;color:#00dc5a">+$' + profit + '</div></div>';
  h += '</div>';

  // Action button
  h += '<button class="hero-execute" style="width:100%;padding:8px;font-size:10px;font-weight:700" onclick="executePickTrade(this, ' + p._globalIdx + ')">EXECUTE ' + side + ' &#x2022; $' + cost + ' &#x2022; +$' + profit + ' potential</button>';
  h += '</div>';
  return h;
}

async function loadTopPicks() {
  var gsGrid = document.getElementById('gs-picks-grid');
  if (_picksFirstLoad && gsGrid) {
    gsGrid.innerHTML = '<div class="loading" style="grid-column:1/-1;padding:40px;text-align:center;color:#888">Scanning 3,000+ markets across 6 platforms...</div>';
  }
  try {
    const data = await fetch(API + '/top-picks').then(r => r.json());
    _picksFirstLoad = false;
    const picks = data.picks || [];
    picks.forEach((p, i) => { p._globalIdx = i; });
    _picksData = picks;

    // Deduplicate and take top 10 by score
    var seen = {};
    var top10 = [];
    picks.forEach(function(p) {
      var tk = p.kalshi_ticker || '';
      if (!seen[tk] && tk) {
        seen[tk] = true;
        top10.push(p);
      }
    });
    top10 = top10.slice(0, 10);

    if (gsGrid) {
      if (top10.length === 0) {
        gsGrid.innerHTML = '<div class="empty" style="grid-column:1/-1;padding:40px;text-align:center">Market scan in progress. Analysis will appear shortly.</div>';
      } else {
        var html = '';
        top10.forEach(function(p, idx) { html += renderGSTile(p, idx); });
        gsGrid.innerHTML = html;
      }
    }

    // Also update hidden elements for backward compat
    _setText('hero-badge', top10.length);
  } catch(e) {
    if (gsGrid) gsGrid.innerHTML = '<div class="empty" style="grid-column:1/-1">Analysis error: ' + e.message + '</div>';
  }
}

async function executePickTrade(btn, idx) {
  const m = _picksData[idx];
  btn.disabled = true;
  btn.textContent = 'PLACING...';
  btn.style.borderColor = '#ffb400';
  btn.style.color = '#ffb400';
  try {
    const res = await fetch(API + '/execute-trade', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({
        ticker: m.kalshi_ticker,
        side: m.signal.replace('buy_', ''),
        price_cents: m.price_cents,
        question: m.kalshi_question,
        deviation: m.deviation,
        consensus_price: m.consensus_yes_price,
        kalshi_price: m.kalshi_yes_price,
        matching_platforms: m.matching_platforms,
      })
    });
    const data = await res.json();
    if (data.success) {
      btn.textContent = 'FILLED';
      btn.style.borderColor = '#00dc5a';
      btn.style.color = '#00dc5a';
      btn.style.background = 'rgba(0,255,136,0.15)';
      showToast('Order filled: ' + m.kalshi_ticker + ' ' + m.signal.replace('buy_','').toUpperCase() + ' @ ' + (m.price_cents/100).toFixed(2), 'success');
    } else {
      btn.textContent = 'FAILED';
      btn.style.borderColor = '#ff5000';
      btn.style.color = '#ff5000';
      const errMsg = data.result && data.result.response_body ? data.result.response_body : (data.result && data.result.error ? data.result.error : 'Unknown error');
      showToast('Trade failed: ' + errMsg, 'error');
      var retrySide = m.signal === 'buy_yes' ? 'YES' : 'NO';
      setTimeout(() => { btn.disabled = false; btn.textContent = 'Retry ' + retrySide; btn.style.borderColor = '#ffb400'; btn.style.color = '#ffb400'; }, 3000);
    }
    loadStatus();
    loadTrades();
  } catch(e) {
    btn.textContent = 'ERROR';
    btn.style.borderColor = '#ff5000';
    btn.style.color = '#ff5000';
    showToast('Network error: ' + e.message, 'error');
  }
}

async function loadTrades() {
  try {
    const data = await fetch(API + '/trades').then(r => r.json());
    var _tradeBadge = document.getElementById('trade-badge');
    if (_tradeBadge) _tradeBadge.textContent = data.total;
    drawPLChart(data.trades || []);
    var _tradeTable = document.getElementById('trade-table');
    if (!_tradeTable) return; // element removed — skip rendering
    if (!data.trades || data.trades.length === 0) {
      _tradeTable.innerHTML = '<div class="empty">No trades yet. Enable the bot or click Trade on an opportunity.</div>';
      return;
    }
    let html = '<table><tr><th>Time</th><th>Market</th><th>Side</th><th>Qty</th><th>Cost</th><th>Deviation</th><th>Result</th><th>Source</th></tr>';
    data.trades.forEach(t => {
      var time = '--';
      if (t.timestamp) {
        try {
          var ts = t.timestamp;
          if (ts.indexOf('Z') < 0 && ts.indexOf('+') < 0 && ts.indexOf('-', 10) < 0) ts += 'Z';
          var d = new Date(ts);
          time = isNaN(d.getTime()) ? t.timestamp.substring(0, 16).replace('T', ' ') : d.toLocaleString();
        } catch(e) { time = t.timestamp.substring(0, 16); }
      }
      var sideClass = t.side === 'yes' ? 'side-yes' : 'side-no';
      // Show settlement outcome: win/loss/pending
      var resultClass, resultLabel;
      if (t.outcome === 'win') {
        resultClass = 'result-win';
        resultLabel = 'WON' + (t.pnl_usd ? ' +$' + Math.abs(t.pnl_usd).toFixed(2) : '');
      } else if (t.outcome === 'loss') {
        resultClass = 'result-loss';
        resultLabel = 'LOST' + (t.pnl_usd ? ' -$' + Math.abs(t.pnl_usd).toFixed(2) : '');
      } else if (t.outcome === 'even') {
        resultClass = '';
        resultLabel = 'EVEN';
      } else {
        // Not yet settled
        var isSuccess = t.source === 'kalshi_fill' ? true : (t.success || false);
        resultClass = isSuccess ? '' : 'result-loss';
        resultLabel = isSuccess ? 'Open' : 'Failed';
      }
      var source = t.source === 'kalshi_fill' ? 'Kalshi' : (t.manual ? 'Manual' : 'Bot');
      var actionLabel = (t.action === 'sell') ? 'SELL' : '';
      var qty = t.count || 1;
      var title = (t.question || t.title || t.ticker || '').substring(0, 50);
      var devText = t.deviation ? ((t.deviation * 100).toFixed(1) + '%') : '--';
      html += '<tr>';
      html += '<td>' + time + '</td>';
      html += '<td>' + title + '</td>';
      html += '<td class="' + sideClass + '">' + (actionLabel ? actionLabel + ' ' : '') + qty + 'x ' + (t.side || '').toUpperCase() + '</td>';
      html += '<td>' + qty + '</td>';
      html += '<td>$' + (t.cost_usd || (t.price_cents || 0)/100).toFixed(2) + '</td>';
      html += '<td>' + devText + '</td>';
      html += '<td class="' + resultClass + '">' + resultLabel + '</td>';
      html += '<td>' + source + '</td>';
      html += '</tr>';
    });
    html += '</table>';
    if (_tradeTable) _tradeTable.innerHTML = html;
  } catch(e) {
    var _tt2 = document.getElementById('trade-table');
    if (_tt2) _tt2.innerHTML = '<div class="empty">Error loading trades</div>';
  }
}

// P/L Chart
function drawPLChart(trades) {
  const canvas = document.getElementById('pl-chart');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.parentElement.getBoundingClientRect();
  canvas.width = rect.width * dpr;
  canvas.height = rect.height * dpr;
  ctx.scale(dpr, dpr);
  const w = rect.width, h = rect.height;
  ctx.clearRect(0, 0, w, h);

  // Build cumulative P/L from actual settled data
  let points = [{x: 0, y: 0}];
  let cumPL = 0;
  if (window._settledData && window._settledData.length > 0) {
    window._settledData.forEach((s, i) => {
      cumPL += s.pnl_usd || 0;
      points.push({x: i + 1, y: cumPL});
    });
  } else if (trades && trades.length > 0) {
    // No settled data yet — show cost spent as negative until settled
    trades.forEach((t, i) => {
      if (t.success) {
        cumPL -= (t.cost_usd || 0);
      }
      points.push({x: i + 1, y: cumPL});
    });
  } else {
    for (let i = 1; i <= 20; i++) points.push({x: i, y: 0});
  }

  const plEl = document.getElementById('chart-pl');
  if (plEl) {
    if (cumPL > 0) { plEl.style.display = 'none'; }
    else if (cumPL < 0) { plEl.style.display = 'none'; }
    else { plEl.style.display = 'none'; }
  }

  const maxX = points.length - 1 || 1;
  const ys = points.map(p => p.y);
  let minY = Math.min(...ys, 0);
  let maxY = Math.max(...ys, 0);
  if (minY === maxY) { minY -= 1; maxY += 1; }
  const pad = 10;

  function px(i) { return pad + (i / maxX) * (w - pad * 2); }
  function py(v) { return h - pad - ((v - minY) / (maxY - minY)) * (h - pad * 2); }

  // Grid lines
  ctx.strokeStyle = '#1f1f1f';
  ctx.lineWidth = 0.5;
  for (let i = 0; i < 5; i++) {
    const yy = pad + i * (h - pad * 2) / 4;
    ctx.beginPath(); ctx.moveTo(pad, yy); ctx.lineTo(w - pad, yy); ctx.stroke();
  }

  // Zero line
  const zeroY = py(0);
  ctx.strokeStyle = '#333';
  ctx.setLineDash([4, 4]);
  ctx.beginPath(); ctx.moveTo(pad, zeroY); ctx.lineTo(w - pad, zeroY); ctx.stroke();
  ctx.setLineDash([]);

  // P/L area fill
  ctx.beginPath();
  ctx.moveTo(px(0), zeroY);
  points.forEach((p, i) => ctx.lineTo(px(i), py(p.y)));
  ctx.lineTo(px(points.length - 1), zeroY);
  ctx.closePath();
  const grad = ctx.createLinearGradient(0, 0, 0, h);
  if (cumPL >= 0) { grad.addColorStop(0, 'rgba(0,220,90,0.2)'); grad.addColorStop(1, 'rgba(0,220,90,0)'); }
  else { grad.addColorStop(0, 'rgba(255,80,0,0)'); grad.addColorStop(1, 'rgba(255,80,0,0.2)'); }
  ctx.fillStyle = grad;
  ctx.fill();

  // P/L line
  ctx.beginPath();
  points.forEach((p, i) => { if (i === 0) ctx.moveTo(px(i), py(p.y)); else ctx.lineTo(px(i), py(p.y)); });
  ctx.strokeStyle = cumPL >= 0 ? '#00dc5a' : '#ff5000';
  ctx.lineWidth = 2;
  ctx.stroke();

  // Current dot
  const last = points[points.length - 1];
  ctx.beginPath();
  ctx.arc(px(points.length - 1), py(last.y), 4, 0, Math.PI * 2);
  ctx.fillStyle = cumPL >= 0 ? '#00dc5a' : '#ff5000';
  ctx.fill();
}

let _todayData = [];

function renderTodayTable(picks, containerId, badgeId) {
  document.getElementById(badgeId).textContent = picks.length;
  if (picks.length === 0) {
    document.getElementById(containerId).innerHTML = '<div class="empty">No markets settling today.</div>';
    return;
  }
  let html = '<table><tr><th>Market</th><th>YES</th><th>NO</th><th>Signal</th><th>Settles In</th><th>Potential</th><th>Action</th></tr>';
  picks.forEach((p) => {
    const sigClass = p.signal === 'buy_yes' ? 'side-yes' : 'side-no';
    const sigLabel = p.signal === 'buy_yes' ? 'BUY YES' : 'BUY NO';
    var ct = Math.max(1, Math.floor(500 / p.price_cents));
    var cost = (p.price_cents * ct / 100).toFixed(2);
    html += '<tr>';
    html += '<td><a href="' + p.kalshi_url + '" target="_blank">' + p.kalshi_question.substring(0, 55) + '</a></td>';
    html += '<td>' + p.yes_price + '¢</td>';
    html += '<td>' + p.no_price + '¢</td>';
    html += '<td class="' + sigClass + '">' + sigLabel + '</td>';
    html += '<td style="color:#ffb400;font-weight:700">' + p.time_left + '</td>';
    html += '<td class="result-win">+$' + p.potential_profit_usd.toFixed(2) + '</td>';
    var todaySide = p.signal === 'buy_yes' ? 'YES' : 'NO';
    html += '<td><button class="trade-btn" onclick="executeTodayTrade(this,' + p._globalIdx + ')">Buy ' + todaySide + ' · $' + cost + '</button></td>';
    html += '</tr>';
  });
  html += '</table>';
  document.getElementById(containerId).innerHTML = html;
}

async function loadTodayPicks() {
  try {
    const data = await fetch(API + '/today-picks').then(r => r.json());
    const picks = data.picks || [];
    picks.forEach((p, i) => { p._globalIdx = i; });
    _todayData = picks;
    const sports = picks.filter(p => isSports(p));
    const nonSports = picks.filter(p => !isSports(p));
    renderTodayTable(sports, 'today-table-sports', 'today-badge-sports');
    renderTodayTable(nonSports, 'today-table-nonsports', 'today-badge-nonsports');
  } catch(e) {
    _setHTML('today-table-sports', '<div class="empty">Error: ' + e.message + '</div>');
    _setHTML('today-table-nonsports', '<div class="empty">Error: ' + e.message + '</div>');
  }
}

async function executeTodayTrade(btn, idx) {
  const m = _todayData[idx];
  btn.disabled = true;
  btn.textContent = 'PLACING...';
  try {
    const res = await fetch(API + '/execute-trade', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({
        ticker: m.kalshi_ticker,
        side: m.signal.replace('buy_', ''),
        price_cents: m.price_cents,
        question: m.kalshi_question,
      })
    });
    const data = await res.json();
    if (data.success) {
      btn.textContent = 'PLACED';
      btn.style.background = '#00d4aa';
      showToast('Order placed: ' + m.kalshi_ticker + ' settles in ' + m.time_left, 'success');
    } else {
      btn.textContent = 'FAILED';
      btn.style.background = '#ef4444';
      const errMsg = data.result && data.result.response_body ? data.result.response_body : 'Unknown error';
      showToast('Trade failed: ' + errMsg, 'error');
    }
    loadStatus();
    loadPositions();
    loadTrades();
  } catch(e) {
    btn.textContent = 'ERROR';
    showToast('Network error: ' + e.message, 'error');
  }
}

async function loadPositions() {
  try {
    // Use position-monitor for enriched data with current prices
    const data = await fetch(API + '/position-monitor').then(r => r.json());
    const allPositions = data.positions || [];
    // Fetch live scores for game positions
    var _gameTickers = allPositions.map(function(p){ return p.ticker || ''; }).filter(function(t){ return /GAME|MATCH|FIGHT/.test(t.toUpperCase()); });
    var _gameScores = {};
    if (_gameTickers.length > 0) {
      try {
        var _titles = allPositions.filter(function(p){ return /GAME|MATCH|FIGHT/.test((p.ticker||'').toUpperCase()); }).map(function(p){ return p.title || p.ticker || ''; });
        var _scResp = await fetch(API + '/live-scores?tickers=' + encodeURIComponent(_gameTickers.join(',')) + '&titles=' + encodeURIComponent(_titles.join(','))).then(function(r){ return r.json(); });
        (_scResp.scores || []).forEach(function(s){ _gameScores[s.ticker] = s; });
      } catch(e) {}
    }
    window._positionScores = _gameScores;
    var hidePenny = document.getElementById('hide-bot-trades') && document.getElementById('hide-bot-trades').checked;
    var botJunk = ['netflix', 'spotify', 'billboard', 'title holder', 'nuclear fusion', 'truth social', 'top song', 'top artist', 'featherweight', 'bantamweight', 'flyweight', 'middleweight', 'welterweight', 'lightweight', 'heavyweight', 'pga tour major', 'ballon d'];
    var positions = allPositions;
    if (hidePenny) {
      positions = allPositions.filter(function(p) {
        // Hide any position currently worth 1c or less (dead money, can't sell)
        var nowPrice = p.current_price || p.entry_price || 0;
        if (nowPrice <= 1) return false;
        // Hide penny bot bets under 5c entry
        if (p.placed_by !== 'you' && (p.entry_price || 0) < 5) return false;
        var t = ((p.title || p.ticker) + '').toLowerCase();
        for (var i = 0; i < botJunk.length; i++) { if (t.indexOf(botJunk[i]) >= 0) return false; }
        return true;
      });
    }
    var hiddenCount = allPositions.length - positions.length;
    _setText('pos-badge', positions.length);

    // Build open positions table
    function buildPosRows(arr) {
      if (arr.length === 0) return '<div style="color:#555;font-size:9px;padding:8px;text-align:center">None</div>';
      var h = '<table style="font-size:10px"><tr><th>Market</th><th>Side</th><th>Qty</th><th>Entry</th><th>Now</th><th>P&L</th><th>EXP</th><th></th></tr>';
      arr.forEach(function(p) {
        var timeLeft = formatSettleTime(p.close_time);
        var pnlText = '--';
        var pnlColor = '#888';
        if (p.pnl_pct !== null && p.pnl_pct !== undefined) {
          pnlColor = p.pnl_pct >= 0 ? '#00dc5a' : '#ff5000';
          var pnlCents = p.unrealized_pnl_cents || 0;
          pnlText = (p.pnl_pct >= 0 ? '+' : '') + p.pnl_pct + '% (' + (pnlCents >= 0 ? '+' : '') + (pnlCents / 100).toFixed(2) + ')';
        }
        var sideColor = p.side === 'yes' ? '#00dc5a' : '#ff5000';
        var sellPrice = p.current_price ? Math.max(1, p.current_price - 1) : 0;
        h += '<tr>';
        var _sc2 = (window._positionScores || {})[p.ticker];
        var _scoreHtml2 = '';
        if (_sc2 && _sc2.display) {
          var _scC2 = _sc2.state === 'in' ? '#ffb400' : _sc2.state === 'post' ? '#888' : '#555';
          _scoreHtml2 = '<div style="font-size:8px;color:' + _scC2 + '">&#9889; ' + _sc2.display + '</div>';
        }
        h += '<td style="max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (p.title || p.ticker) + _scoreHtml2 + '</td>';
        h += '<td style="color:' + sideColor + ';font-weight:700">' + p.side.toUpperCase() + '</td>';
        h += '<td>' + p.count + '</td>';
        h += '<td>' + (p.entry_price || '?') + 'c</td>';
        h += '<td style="font-weight:700">' + (p.current_price || '?') + 'c</td>';
        h += '<td style="color:' + pnlColor + ';font-weight:700">' + pnlText + '</td>';
        h += '<td style="color:#ffb400;font-size:9px">' + timeLeft + '</td>';
        if (sellPrice > 0) {
          h += '<td><button class="hero-execute" style="font-size:8px;padding:2px 6px" onclick="sellPosition(&quot;' + p.ticker + '&quot;,&quot;' + p.side + '&quot;,' + sellPrice + ',' + p.count + ')">SELL</button></td>';
        } else {
          h += '<td></td>';
        }
        h += '</tr>';
      });
      h += '</table>';
      return h;
    }

    // Calculate open P&L
    var openPnl = positions.reduce(function(s, p) { return s + (p.unrealized_pnl_cents || 0); }, 0);
    var openPnlColor = openPnl >= 0 ? '#00dc5a' : '#ff5000';
    _setText('pos-open-count', '(' + positions.length + ')');
    _setHTML('pos-open-pnl', '<span style="color:' + openPnlColor + '">' + (openPnl >= 0 ? '+' : '') + '$' + (Math.abs(openPnl) / 100).toFixed(2) + '</span>');
    _setHTML('pos-table-open', buildPosRows(positions));
    if (hiddenCount > 0) {
      document.getElementById('pos-table-open').innerHTML += '<div style="font-size:8px;color:#555;margin-top:4px">' + hiddenCount + ' old bot positions hidden</div>';
    }

    // Fetch closed/settled positions
    try {
      var settledData = await fetch(API + '/settled').then(function(r) { return r.json(); });
      var settled = settledData.settled || [];
      var closedPnl = settled.reduce(function(s, p) { return s + (p.pnl_usd || 0); }, 0);
      var closedPnlColor = closedPnl >= 0 ? '#00dc5a' : '#ff5000';
      _setText('pos-closed-count', '(' + settled.length + ')');
      _setHTML('pos-closed-pnl', '<span style="color:' + closedPnlColor + '">' + (closedPnl >= 0 ? '+' : '') + '$' + Math.abs(closedPnl).toFixed(2) + '</span>');
      if (settled.length === 0) {
        _setHTML('pos-table-closed', '<div style="color:#555;font-size:9px;padding:8px;text-align:center">No settled positions yet</div>');
      } else {
        // Sort newest first by trade_date (when we bought), then settle_time as tiebreaker
        settled.sort(function(a, b) {
          var aDate = a.trade_date || '2000-01-01';
          var bDate = b.trade_date || '2000-01-01';
          if (aDate !== bDate) return bDate > aDate ? 1 : -1;
          var aTime = a.settle_time || '';
          var bTime = b.settle_time || '';
          return bTime > aTime ? 1 : (bTime < aTime ? -1 : 0);
        });
        var ch = '<table style="font-size:10px"><tr><th>Settled</th><th>Market</th><th>Side</th><th>Result</th><th>P&L</th></tr>';
        settled.forEach(function(s) {
          var resultColor = s.won ? '#00dc5a' : '#ff5000';
          var resultText = s.won ? 'WON' : 'LOST';
          var pnlUsd = s.pnl_usd || 0;
          var settleDate = '--';
          if (s.settle_time) {
            try {
              var sd = new Date(s.settle_time);
              if (!isNaN(sd.getTime())) settleDate = sd.toLocaleDateString('en-US', {month:'short', day:'numeric'});
            } catch(e) {}
          } else if (s.trade_date) {
            settleDate = s.trade_date.substring(5);
          }
          ch += '<tr>';
          ch += '<td style="color:#888;font-size:9px">' + settleDate + '</td>';
          ch += '<td style="max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (s.title || s.ticker || '') + '</td>';
          ch += '<td style="color:' + (s.side === 'yes' ? '#00dc5a' : '#ff5000') + '">' + (s.side || '').toUpperCase() + '</td>';
          ch += '<td style="color:' + resultColor + ';font-weight:700">' + resultText + '</td>';
          ch += '<td style="color:' + resultColor + ';font-weight:700">' + (pnlUsd >= 0 ? '+$' : '-$') + Math.abs(pnlUsd).toFixed(2) + '</td>';
          ch += '</tr>';
        });
        ch += '</table>';
        _setHTML('pos-table-closed', ch);
      }
    } catch(e) {
      _setHTML('pos-table-closed', '<div style="color:#555;font-size:9px">Error loading settled</div>');
    }
  } catch(e) {
    _setHTML('pos-table', '<div class="empty">Error: ' + e.message + '</div>');
  }
}

async function sellPosition(ticker, side, priceCents, count) {
  if (!confirm('Sell ' + count + ' ' + side.toUpperCase() + ' contracts of ' + ticker + ' at ' + priceCents + 'c?')) return;
  try {
    const resp = await fetch(API + '/sell-position', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ticker: ticker, side: side, price_cents: priceCents, count: count})
    });
    const data = await resp.json();
    if (data.success) {
      showToast('Sold ' + count + ' contracts at ' + priceCents + 'c', 'success');
    } else {
      showToast('Sell failed: ' + (data.result ? data.result.error || data.result.response_body : 'Unknown'), 'error');
    }
    loadPositions();
  } catch(e) {
    showToast('Sell error: ' + e.message, 'error');
  }
}

async function sellAllLosers() {
  if (!confirm('⚠️ This will sell ALL losing positions at market price. Are you sure?')) return;
  showToast('Selling all losers... this may take a minute', 'info');
  try {
    const resp = await fetch(API + '/sell-all-losers', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
    });
    const data = await resp.json();
    var msg = '💣 Sold ' + data.sold + ' losing positions';
    if (data.skipped > 0) msg += ' | ' + data.skipped + ' kept (winning/no data)';
    if (data.errors > 0) msg += ' | ' + data.errors + ' errors';
    showToast(msg, data.sold > 0 ? 'success' : 'info');
    // Show details
    if (data.sold_details && data.sold_details.length > 0) {
      var detail = data.sold_details.map(function(s) {
        return s.side.toUpperCase() + ' ' + s.title + ' x' + s.count + ' @ ' + s.price + 'c (' + s.pnl_pct.toFixed(1) + '%)';
      }).join('\\n');
      console.log('Sold losers:\\n' + detail);
    }
    loadPositions();
    loadPortfolio();
  } catch(e) {
    showToast('Error: ' + e.message, 'error');
  }
}

async function loadSettled() {
  try {
    const data = await fetch(API + '/settled').then(r => r.json());
    var allSettled = data.settled || [];
    var hideJunk = document.getElementById('hide-history-junk') && document.getElementById('hide-history-junk').checked;

    // Filter: only show bets from Day 1 onwards (March 16, 2026)
    var filtered = allSettled;
    if (hideJunk) {
      // Backend already filters to Day 1+ trades only
      filtered = allSettled;
    }
    window._settledData = filtered;

    // Recalculate stats from filtered data
    var w = 0, l = 0, totalPnlCalc = 0, totalWagered = 0, bigW = 0, bigL = 0;
    filtered.forEach(function(s) {
      if (s.won === true) { w++; bigW = Math.max(bigW, s.pnl_usd); }
      else if (s.won === false) { l++; bigL = Math.min(bigL, s.pnl_usd); }
      totalPnlCalc += s.pnl_usd;
      totalWagered += s.total_traded || 0;
    });

    const el = document.getElementById('settled-stats');
    const wr = (w + l) > 0 ? Math.round(w / (w + l) * 100) : 0;
    const pnl = totalPnlCalc;
    const roi = totalWagered > 0 ? Math.round(pnl / totalWagered * 1000) / 10 : 0;
    const streak = data.streak || 0;
    const streakType = data.streak_type || 'none';
    const totalBets = filtered.length;
    const balance = window._currentBalance || 73.61;
    const pnlColor = pnl >= 0 ? '#00dc5a' : '#ff5000';
    const wrColor = wr >= 60 ? '#00dc5a' : wr >= 40 ? '#ffb400' : '#ff5000';
    const roiColor = roi >= 0 ? '#00dc5a' : '#ff5000';
    const streakColor = streakType === 'win' ? '#00dc5a' : streakType === 'loss' ? '#ff5000' : '#888';
    const streakLabel = streakType === 'win' ? streak + 'W' : streakType === 'loss' ? streak + 'L' : '-';

    // Progress bar to $1M
    const progress = Math.min(100, (balance / 1000000) * 100);
    const progressLabel = progress < 0.01 ? '<0.01%' : progress.toFixed(3) + '%';

    function statBox(label, value, color) {
      return '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:8px;padding:6px 10px;text-align:center;flex:1;min-width:80px">' +
        '<div style="color:#666;font-size:9px;font-weight:500;margin-bottom:1px">' + label + '</div>' +
        '<div style="color:' + color + ';font-size:15px;font-weight:700">' + value + '</div></div>';
    }

    var html = '';
    html += statBox('Wins', w, '#00dc5a');
    html += statBox('Losses', l, '#ff5000');
    html += statBox('Win Rate', wr.toFixed(0) + '%', wrColor);
    html += statBox('P&L', (pnl >= 0 ? '+$' : '-$') + Math.abs(pnl).toFixed(2), pnlColor);
    html += statBox('ROI', roi.toFixed(1) + '%', roiColor);
    html += statBox('Streak', streakLabel, streakColor);
    html += statBox('Best Win', '+$' + bigW.toFixed(2), '#00dc5a');
    html += statBox('Worst Loss', '-$' + Math.abs(bigL).toFixed(2), '#ff5000');
    html += statBox('Total Bets', totalBets, '#ffb400');
    el.innerHTML = html;

    // Update bottom progress bar
    var progFill = document.getElementById('progress-fill');
    var progLabel = document.getElementById('progress-label');
    var progBalance = document.getElementById('progress-balance');
    if (progFill) progFill.style.width = Math.max(0.3, progress) + '%';
    if (progLabel) progLabel.textContent = progressLabel;
    if (progBalance) progBalance.textContent = '$' + balance.toFixed(2);

    // Category breakdown — recalculate from filtered data
    var catEl = document.getElementById('settled-categories');
    var cats = {};
    filtered.forEach(function(s) {
      var cat = s.category || 'other';
      if (!cats[cat]) cats[cat] = {wins: 0, losses: 0, pnl_usd: 0, bets: 0, win_rate: 0};
      cats[cat].bets++;
      if (s.won === true) cats[cat].wins++;
      else if (s.won === false) cats[cat].losses++;
      cats[cat].pnl_usd += s.pnl_usd || 0;
    });
    Object.keys(cats).forEach(function(k) {
      var c = cats[k];
      c.win_rate = (c.wins + c.losses) > 0 ? Math.round(c.wins / (c.wins + c.losses) * 100) : 0;
      c.pnl_usd = Math.round(c.pnl_usd * 100) / 100;
    });
    // Only show categories with actual settled bets (filter out 0W/0L noise)
    var catKeys = Object.keys(cats).filter(function(k){ var c = cats[k]; return (c.wins + c.losses) > 0; }).sort(function(a,b){ return (cats[b].pnl_usd || 0) - (cats[a].pnl_usd || 0); });
    if (catKeys.length > 0 && catEl) {
      var catHtml = '<div style="padding:10px;background:#141414;border:1px solid #1f1f1f;border-radius:10px">';
      catHtml += '<div style="color:#999;font-size:11px;font-weight:600;margin-bottom:6px">Win Rate by Category</div>';
      catHtml += '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(80px,1fr));gap:4px">';
      catKeys.forEach(function(cat) {
        var c = cats[cat];
        var cwr = c.win_rate || 0;
        var cc = cwr >= 60 ? '#00dc5a' : cwr >= 40 ? '#ffb400' : '#ff5000';
        var pnlC = c.pnl_usd >= 0 ? '#00dc5a' : '#ff5000';
        catHtml += '<div style="background:#0d0d0d;border:1px solid #222;border-radius:8px;padding:6px 8px;text-align:center">';
        catHtml += '<div style="font-size:10px;color:#888;text-transform:capitalize">' + cat + '</div>';
        catHtml += '<div style="font-size:16px;font-weight:700;color:' + cc + '">' + cwr.toFixed(0) + '%</div>';
        catHtml += '<div style="font-size:9px;color:#666">' + c.wins + 'W/' + c.losses + 'L</div>';
        catHtml += '<div style="font-size:9px;color:' + pnlC + '">' + (c.pnl_usd >= 0 ? '+' : '') + '$' + c.pnl_usd.toFixed(2) + '</div>';
        catHtml += '</div>';
      });
      catHtml += '</div></div>';
      catEl.innerHTML = catHtml;
    } else if (catEl) {
      catEl.innerHTML = '<div style="padding:12px;background:#141414;border:1px solid #1f1f1f;border-radius:10px;color:#555;font-size:11px">No category data yet</div>';
    }

    // Settled positions table
    var tableEl = document.getElementById('settled-table');
    var settled = filtered;
    var hiddenCount = allSettled.length - filtered.length;
    if (settled.length === 0) {
      tableEl.innerHTML = '<div style="color:#555;font-size:10px;padding:8px">No settled positions yet. Place some bets and we will track every result here.</div>';
    } else {
      // Server already sorts: past close_times first (newest), future at bottom
      // No client-side re-sort needed
      var tbl = '<div style="display:flex;flex-direction:column;gap:6px">';
      settled.forEach(function(s) {
        var isWin = s.won === true;
        var isLoss = s.won === false;
        var pnlAbs = Math.abs(s.pnl_usd).toFixed(2);
        var borderColor = isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#555';
        var pnlColor = isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#888';
        var pnlSign = isWin ? '+$' : '-$';
        var resultLabel = isWin ? 'WON' : isLoss ? 'LOST' : 'EVEN';
        var bgColor = isWin ? 'rgba(0,220,90,0.05)' : isLoss ? 'rgba(255,80,0,0.05)' : 'rgba(50,50,50,0.2)';
        // Use trade_date for when the bet was placed
        var dateStr = '';
        var tdRaw = s.trade_date || '';
        if (tdRaw) {
          try {
            var parts = tdRaw.split('-');
            var months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
            dateStr = months[parseInt(parts[1])-1] + ' ' + parseInt(parts[2]);
          } catch(e) { dateStr = tdRaw; }
        }
        var costStr = s.total_traded ? '$' + s.total_traded.toFixed(2) : '';
        var catLabel = s.category ? s.category.charAt(0).toUpperCase() + s.category.slice(1) : '';
        tbl += '<div style="background:' + bgColor + ';border-left:3px solid ' + borderColor + ';padding:10px 14px;border-radius:6px;display:flex;justify-content:space-between;align-items:center">';
        tbl += '<div style="flex:1;min-width:0">';
        tbl += '<div style="color:#eee;font-size:12px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + s.title + '</div>';
        tbl += '<div style="color:#777;font-size:10px;margin-top:3px">';
        if (dateStr) tbl += dateStr;
        if (costStr) tbl += ' · Bet ' + costStr;
        if (catLabel) tbl += ' · ' + catLabel;
        if (s.side) tbl += ' · ' + s.side.toUpperCase();
        tbl += '</div>';
        tbl += '</div>';
        tbl += '<div style="text-align:right;margin-left:16px;flex-shrink:0">';
        tbl += '<div style="color:' + pnlColor + ';font-size:15px;font-weight:800">' + pnlSign + pnlAbs + '</div>';
        tbl += '<div style="color:' + pnlColor + ';font-size:10px;font-weight:600;letter-spacing:0.5px">' + resultLabel + '</div>';
        tbl += '</div></div>';
      });
      tbl += '</div>';
      if (hiddenCount > 0) {
        tbl += '<div style="color:#555;font-size:9px;padding:6px 4px">' + hiddenCount + ' old penny bot trades hidden (uncheck toggle to show all)</div>';
      }
      tableEl.innerHTML = tbl;
    }
  } catch(e) {
    var ss = document.getElementById('settled-stats');
    if (ss) ss.innerHTML = '<span style="color:#ff5000">Error: ' + e.message + '</span>';
  }
}

// === COMBINED PERFORMANCE TAB ===
async function loadPerformance() {
  try {
    // Fetch all data in parallel
    var [settledData, analyticsData, tradesData, insightsData] = await Promise.all([
      fetch(API + '/settled').then(r => r.json()),
      fetch(API + '/analytics').then(r => r.json()),
      fetch(API + '/trades').then(r => r.json()),
      fetch(API + '/insights').then(r => r.json()).catch(function() { return {insights:[]}; })
    ]);

    var allSettled = settledData.settled || [];
    var hideJunk = document.getElementById('hide-history-junk') && document.getElementById('hide-history-junk').checked;
    var settled = hideJunk ? allSettled : allSettled;
    window._settledData = settled;

    // === COMPUTE ALL KPIs ===
    var wins = 0, losses = 0, totalPnl = 0, totalWagered = 0, bigWin = 0, bigLoss = 0;
    var winPnls = [], lossPnls = [], allPnls = [];
    var streak = 0, streakType = 'none', maxStreak = 0, maxDrawdown = 0, peak = 0, cumPnl = 0;
    var dailyPnls = {};

    settled.forEach(function(s) {
      var pnl = s.pnl_usd || 0;
      allPnls.push(pnl);
      totalPnl += pnl;
      totalWagered += s.total_traded || 0;
      cumPnl += pnl;
      if (cumPnl > peak) peak = cumPnl;
      var dd = peak - cumPnl;
      if (dd > maxDrawdown) maxDrawdown = dd;

      if (s.won === true) {
        wins++;
        winPnls.push(pnl);
        bigWin = Math.max(bigWin, pnl);
      } else if (s.won === false) {
        losses++;
        lossPnls.push(pnl);
        bigLoss = Math.min(bigLoss, pnl);
      }

      // Daily P&L tracking
      var day = s.trade_date || 'unknown';
      if (!dailyPnls[day]) dailyPnls[day] = 0;
      dailyPnls[day] += pnl;
    });

    var total = wins + losses;
    var winRate = total > 0 ? (wins / total * 100) : 0;
    var roi = totalWagered > 0 ? (totalPnl / totalWagered * 100) : 0;
    var avgWin = winPnls.length > 0 ? winPnls.reduce(function(a,b){return a+b;},0) / winPnls.length : 0;
    var avgLoss = lossPnls.length > 0 ? Math.abs(lossPnls.reduce(function(a,b){return a+b;},0) / lossPnls.length) : 0;
    var profitFactor = avgLoss > 0 ? (avgWin * wins) / (avgLoss * losses) : 0;
    var expectancy = total > 0 ? totalPnl / total : 0;
    var payoffRatio = avgLoss > 0 ? avgWin / avgLoss : 0;

    // Sharpe-like ratio (daily P&L volatility)
    var dailyVals = Object.values(dailyPnls);
    var dailyMean = dailyVals.length > 0 ? dailyVals.reduce(function(a,b){return a+b;},0) / dailyVals.length : 0;
    var dailyVar = dailyVals.length > 1 ? dailyVals.reduce(function(a,b){return a + Math.pow(b - dailyMean, 2);},0) / (dailyVals.length - 1) : 0;
    var dailyStd = Math.sqrt(dailyVar);
    var sharpe = dailyStd > 0 ? (dailyMean / dailyStd).toFixed(2) : '--';

    // Streak
    var currStreak = settledData.streak || 0;
    var currStreakType = settledData.streak_type || 'none';

    // === RENDER KPIs ===
    var kpiEl = document.getElementById('perf-kpis');
    function kpi(label, value, color, sub) {
      return '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:10px 12px;text-align:center">' +
        '<div style="color:#555;font-size:9px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:2px">' + label + '</div>' +
        '<div style="color:' + color + ';font-size:20px;font-weight:800">' + value + '</div>' +
        (sub ? '<div style="color:#444;font-size:9px;margin-top:1px">' + sub + '</div>' : '') +
        '</div>';
    }
    var wrColor = winRate >= 50 ? '#00dc5a' : winRate >= 30 ? '#ffb400' : '#ff5000';
    var pnlColor = totalPnl >= 0 ? '#00dc5a' : '#ff5000';
    var roiColor = roi >= 0 ? '#00dc5a' : '#ff5000';
    var pfColor = profitFactor >= 1.5 ? '#00dc5a' : profitFactor >= 1.0 ? '#ffb400' : '#ff5000';
    var expColor = expectancy >= 0 ? '#00dc5a' : '#ff5000';
    var streakColor = currStreakType === 'win' ? '#00dc5a' : currStreakType === 'loss' ? '#ff5000' : '#888';
    var streakLabel = currStreakType === 'win' ? currStreak + 'W' : currStreakType === 'loss' ? currStreak + 'L' : '--';

    var khtml = '';
    // Row 1: Core trading metrics
    khtml += kpi('Total P&L', (totalPnl >= 0 ? '+$' : '-$') + Math.abs(totalPnl).toFixed(2), pnlColor, wins + 'W / ' + losses + 'L');
    khtml += kpi('Win Rate', winRate.toFixed(1) + '%', wrColor, total + ' trades');
    khtml += kpi('ROI', roi.toFixed(1) + '%', roiColor, '$' + totalWagered.toFixed(0) + ' wagered');
    khtml += kpi('Profit Factor', profitFactor.toFixed(2), pfColor, avgWin > 0 ? '$' + avgWin.toFixed(2) + ' avg W' : '');
    khtml += kpi('Expectancy', (expectancy >= 0 ? '+$' : '-$') + Math.abs(expectancy).toFixed(2), expColor, 'per trade');

    // Row 2
    khtml += kpi('Max Drawdown', '-$' + maxDrawdown.toFixed(2), maxDrawdown > 20 ? '#ff5000' : '#ffb400', 'from peak');
    khtml += kpi('Avg Win', '+$' + avgWin.toFixed(2), '#00dc5a', bigWin > 0 ? 'best +$' + bigWin.toFixed(2) : '');
    khtml += kpi('Avg Loss', '-$' + avgLoss.toFixed(2), '#ff5000', bigLoss < 0 ? 'worst -$' + Math.abs(bigLoss).toFixed(2) : '');
    khtml += kpi('Payoff Ratio', payoffRatio.toFixed(2) + 'x', payoffRatio >= 1 ? '#00dc5a' : '#ff5000', 'win/loss size');
    khtml += kpi('Streak', streakLabel, streakColor, 'Sharpe: ' + sharpe);

    kpiEl.innerHTML = khtml;

    // === EQUITY CURVE ===
    var canvas = document.getElementById('perf-pl-chart');
    if (canvas) {
      var ctx = canvas.getContext('2d');
      var dpr = window.devicePixelRatio || 1;
      var rect = canvas.parentElement.getBoundingClientRect();
      canvas.width = rect.width * dpr;
      canvas.height = rect.height * dpr;
      ctx.scale(dpr, dpr);
      var w = rect.width, h = rect.height;
      ctx.clearRect(0, 0, w, h);

      var points = [{x: 0, y: 0}];
      var cum = 0;
      settled.forEach(function(s, i) {
        cum += s.pnl_usd || 0;
        points.push({x: i + 1, y: cum});
      });

      if (points.length > 1) {
        var minY = Math.min.apply(null, points.map(function(p){return p.y;}));
        var maxY = Math.max.apply(null, points.map(function(p){return p.y;}));
        var range = Math.max(maxY - minY, 1);
        var pad = 16;

        // Zero line
        var zeroY = h - pad - ((0 - minY) / range) * (h - 2 * pad);
        ctx.strokeStyle = '#333';
        ctx.lineWidth = 1;
        ctx.setLineDash([4, 4]);
        ctx.beginPath();
        ctx.moveTo(0, zeroY);
        ctx.lineTo(w, zeroY);
        ctx.stroke();
        ctx.setLineDash([]);

        // Equity line
        ctx.beginPath();
        points.forEach(function(p, i) {
          var px = (p.x / (points.length - 1)) * (w - 2 * pad) + pad;
          var py = h - pad - ((p.y - minY) / range) * (h - 2 * pad);
          if (i === 0) ctx.moveTo(px, py);
          else ctx.lineTo(px, py);
        });
        ctx.strokeStyle = cum >= 0 ? '#00dc5a' : '#ff5000';
        ctx.lineWidth = 2;
        ctx.stroke();

        // Gradient fill
        var lastPt = points[points.length - 1];
        var lastPx = (lastPt.x / (points.length - 1)) * (w - 2 * pad) + pad;
        ctx.lineTo(lastPx, h - pad);
        ctx.lineTo(pad, h - pad);
        ctx.closePath();
        var grad = ctx.createLinearGradient(0, 0, 0, h);
        if (cum >= 0) {
          grad.addColorStop(0, 'rgba(0,220,90,0.15)');
          grad.addColorStop(1, 'rgba(0,220,90,0)');
        } else {
          grad.addColorStop(0, 'rgba(255,80,0,0.15)');
          grad.addColorStop(1, 'rgba(255,80,0,0)');
        }
        ctx.fillStyle = grad;
        ctx.fill();

        // End label
        ctx.fillStyle = cum >= 0 ? '#00dc5a' : '#ff5000';
        ctx.font = '11px Inter';
        ctx.textAlign = 'right';
        ctx.fillText((cum >= 0 ? '+$' : '-$') + Math.abs(cum).toFixed(2), w - 4, 14);
      }
    }

    // === STRATEGY BREAKDOWN ===
    var stratEl = document.getElementById('perf-strategies');
    var strategies = {};
    settled.forEach(function(s) {
      var strat = s.strategy || s.source || 'unknown';
      if (strat === 'kalshi_fill') strat = 'manual';
      if (!strategies[strat]) strategies[strat] = {wins:0, losses:0, pnl:0};
      if (s.won === true) strategies[strat].wins++;
      else if (s.won === false) strategies[strat].losses++;
      strategies[strat].pnl += s.pnl_usd || 0;
    });
    var stratKeys = Object.keys(strategies).sort(function(a,b) { return strategies[b].pnl - strategies[a].pnl; });
    if (stratKeys.length > 0) {
      var shtml = '';
      stratKeys.forEach(function(k) {
        var s = strategies[k];
        var st = s.wins + s.losses;
        var swr = st > 0 ? Math.round(s.wins / st * 100) : 0;
        var swrc = swr >= 50 ? '#00dc5a' : swr >= 30 ? '#ffb400' : '#ff5000';
        var spnlc = s.pnl >= 0 ? '#00dc5a' : '#ff5000';
        var barW = st > 0 ? Math.round(s.wins / st * 100) : 0;
        shtml += '<div style="margin-bottom:8px">';
        shtml += '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:3px">';
        shtml += '<span style="color:#ccc;font-size:11px;font-weight:600;text-transform:capitalize">' + k + '</span>';
        shtml += '<span style="color:' + spnlc + ';font-size:11px;font-weight:700">' + (s.pnl >= 0 ? '+' : '') + '$' + Math.abs(s.pnl).toFixed(2) + '</span>';
        shtml += '</div>';
        shtml += '<div style="display:flex;align-items:center;gap:6px">';
        shtml += '<div style="flex:1;height:6px;background:#222;border-radius:3px;overflow:hidden">';
        shtml += '<div style="width:' + barW + '%;height:100%;background:' + swrc + ';border-radius:3px"></div>';
        shtml += '</div>';
        shtml += '<span style="color:#888;font-size:9px;white-space:nowrap">' + swr + '% (' + s.wins + 'W/' + s.losses + 'L)</span>';
        shtml += '</div></div>';
      });
      stratEl.innerHTML = shtml;
    } else {
      stratEl.innerHTML = '<div style="color:#555;font-size:11px">No strategy data yet</div>';
    }

    // === BY SPORT ===
    var sportEl = document.getElementById('perf-by-sport');
    var cats = {};
    settled.forEach(function(s) {
      var cat = s.category || 'other';
      if (!cats[cat]) cats[cat] = {wins:0, losses:0, pnl:0};
      if (s.won === true) cats[cat].wins++;
      else if (s.won === false) cats[cat].losses++;
      cats[cat].pnl += s.pnl_usd || 0;
    });
    var catKeys = Object.keys(cats).filter(function(k) { var c = cats[k]; return (c.wins + c.losses) > 0; })
      .sort(function(a,b) { return cats[b].pnl - cats[a].pnl; });
    if (catKeys.length > 0) {
      var chtml = '';
      catKeys.forEach(function(k) {
        var c = cats[k];
        var ct = c.wins + c.losses;
        var cwr = Math.round(c.wins / ct * 100);
        var cwrc = cwr >= 50 ? '#00dc5a' : cwr >= 30 ? '#ffb400' : '#ff5000';
        var cpnlc = c.pnl >= 0 ? '#00dc5a' : '#ff5000';
        chtml += '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 0;border-bottom:1px solid #1a1a1a">';
        chtml += '<span style="color:#ccc;font-size:11px;text-transform:capitalize">' + k + '</span>';
        chtml += '<div style="display:flex;gap:10px;align-items:center">';
        chtml += '<span style="color:' + cwrc + ';font-size:11px;font-weight:700">' + cwr + '%</span>';
        chtml += '<span style="color:#666;font-size:10px">' + c.wins + 'W/' + c.losses + 'L</span>';
        chtml += '<span style="color:' + cpnlc + ';font-size:10px;font-weight:600;min-width:50px;text-align:right">' + (c.pnl >= 0 ? '+' : '') + '$' + Math.abs(c.pnl).toFixed(2) + '</span>';
        chtml += '</div></div>';
      });
      sportEl.innerHTML = chtml;
    } else {
      sportEl.innerHTML = '<div style="color:#555;font-size:11px">No data yet</div>';
    }

    // === BY PRICE RANGE ===
    var priceEl = document.getElementById('perf-by-price');
    var byPrice = analyticsData.by_price || {};
    // Fallback: compute from settled
    if (Object.keys(byPrice).length === 0 && settled.length > 0) {
      var pMap = {};
      settled.forEach(function(s) {
        var pc = s.entry_cents || 0;
        var bk = pc >= 90 ? '90-100' : pc >= 80 ? '80-89' : pc >= 70 ? '70-79' : pc >= 50 ? '50-69' : '<50';
        if (!pMap[bk]) pMap[bk] = {wins:0, losses:0, pnl:0, total:0};
        pMap[bk].total++;
        if (s.won === true) pMap[bk].wins++;
        else if (s.won === false) pMap[bk].losses++;
        pMap[bk].pnl += s.pnl_usd || 0;
      });
      Object.keys(pMap).forEach(function(k) {
        var b = pMap[k];
        b.win_rate = Math.round(b.wins / Math.max(1, b.wins + b.losses) * 100 * 10) / 10;
      });
      byPrice = pMap;
    }
    var priceKeys = Object.keys(byPrice).filter(function(k) { return (byPrice[k].total || 0) > 0; })
      .sort(function(a,b) { return (byPrice[b].win_rate || 0) - (byPrice[a].win_rate || 0); });
    if (priceKeys.length > 0) {
      var phtml = '';
      priceKeys.forEach(function(k) {
        var b = byPrice[k];
        var bwr = b.win_rate || 0;
        var bwrc = bwr >= 50 ? '#00dc5a' : bwr >= 30 ? '#ffb400' : '#ff5000';
        var bpnlc = (b.pnl || 0) >= 0 ? '#00dc5a' : '#ff5000';
        phtml += '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 0;border-bottom:1px solid #1a1a1a">';
        phtml += '<span style="color:#ccc;font-size:11px">' + k + String.fromCharCode(162) + '</span>';
        phtml += '<div style="display:flex;gap:10px;align-items:center">';
        phtml += '<span style="color:' + bwrc + ';font-size:11px;font-weight:700">' + bwr.toFixed(0) + '%</span>';
        phtml += '<span style="color:#666;font-size:10px">' + (b.wins||0) + 'W/' + (b.losses||0) + 'L</span>';
        phtml += '<span style="color:' + bpnlc + ';font-size:10px;font-weight:600;min-width:50px;text-align:right">' + ((b.pnl||0) >= 0 ? '+' : '') + '$' + Math.abs(b.pnl||0).toFixed(2) + '</span>';
        phtml += '</div></div>';
      });
      priceEl.innerHTML = phtml;
    } else {
      priceEl.innerHTML = '<div style="color:#555;font-size:11px">No data yet</div>';
    }

    // === BY TIME OF DAY ===
    var timeEl = document.getElementById('perf-by-time');
    var byTime = analyticsData.by_time || {};
    var timeKeys = Object.keys(byTime).filter(function(k) { return (byTime[k].total || 0) > 0; })
      .sort(function(a,b) { return (byTime[b].pnl || 0) - (byTime[a].pnl || 0); });
    if (timeKeys.length > 0) {
      var thtml = '';
      timeKeys.forEach(function(k) {
        var t = byTime[k];
        var twr = t.win_rate || 0;
        var twrc = twr >= 50 ? '#00dc5a' : twr >= 30 ? '#ffb400' : '#ff5000';
        var tpnlc = (t.pnl || 0) >= 0 ? '#00dc5a' : '#ff5000';
        // Shorten label
        var shortLabel = k.replace(' (6am-12pm)','').replace(' (12pm-6pm)','').replace(' (6pm-12am)','').replace(' (12am-6am)','');
        thtml += '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 0;border-bottom:1px solid #1a1a1a">';
        thtml += '<span style="color:#ccc;font-size:11px">' + shortLabel + '</span>';
        thtml += '<div style="display:flex;gap:10px;align-items:center">';
        thtml += '<span style="color:' + twrc + ';font-size:11px;font-weight:700">' + twr.toFixed(0) + '%</span>';
        thtml += '<span style="color:#666;font-size:10px">' + (t.wins||0) + 'W/' + (t.losses||0) + 'L</span>';
        thtml += '<span style="color:' + tpnlc + ';font-size:10px;font-weight:600;min-width:50px;text-align:right">' + ((t.pnl||0) >= 0 ? '+' : '') + '$' + Math.abs(t.pnl||0).toFixed(2) + '</span>';
        thtml += '</div></div>';
      });
      timeEl.innerHTML = thtml;
    } else {
      timeEl.innerHTML = '<div style="color:#555;font-size:11px">No data yet</div>';
    }

    // === DAILY INSIGHTS ===
    var insData = insightsData.insights || [];
    var feedEl = document.getElementById('daily-insights-feed');
    if (insData.length > 0) {
      var ihtml = '';
      insData.forEach(function(ins) {
        var icon = ins.trend === 'positive' ? String.fromCodePoint(0x1F4C8) : ins.trend === 'negative' ? String.fromCodePoint(0x1F4C9) : String.fromCodePoint(0x27A1);
        var borderColor = ins.trend === 'positive' ? '#00dc5a' : ins.trend === 'negative' ? '#ff5000' : '#333';
        ihtml += '<div style="border-left:3px solid ' + borderColor + ';padding:8px 12px;border-radius:6px;background:#0d0d0d">';
        ihtml += '<div style="display:flex;align-items:center;gap:6px;margin-bottom:2px">';
        ihtml += '<span style="font-size:14px">' + icon + '</span>';
        ihtml += '<span style="color:#ddd;font-size:12px;font-weight:700">' + ins.title + '</span>';
        ihtml += '</div>';
        ihtml += '<div style="color:#888;font-size:10px;line-height:1.4">' + ins.detail + '</div>';
        ihtml += '</div>';
      });
      feedEl.innerHTML = ihtml;
    } else {
      feedEl.innerHTML = '<div style="color:#555;font-size:11px">No insights yet</div>';
    }

    // === TRADE JOURNAL (all bets with edge reasoning) ===
    var tableEl = document.getElementById('settled-table');
    var hiddenCount = allSettled.length - settled.length;
    // Combine settled + open positions for full journal
    var allBets = [];
    // Add settled trades
    settled.forEach(function(s) {
      allBets.push({
        title: s.title || s.ticker || '',
        ticker: s.ticker || '',
        side: s.side || '',
        entry_cents: s.entry_cents || 0,
        count: s.count || 0,
        cost: s.total_traded || 0,
        pnl: s.pnl_usd || 0,
        won: s.won,
        status: s.won === true ? 'WON' : s.won === false ? 'LOST' : 'EVEN',
        date: s.trade_date || '',
        category: s.category || '',
        strategy: s.strategy || '',
        edge_reasons: s.edge_reasons || [],
        espn_edge: s.espn_edge,
        conviction: s.conviction || 0,
        game_state: s.game_state_at_entry || '',
        entry_time: s.entry_time || '',
        settle_time: s.settle_time || '',
      });
    });
    // Also add today's open trades (not yet settled)
    try {
      var todayData = await fetch(API + '/trades-today').then(function(r){ return r.json(); });
      (todayData.trades || []).forEach(function(t) {
        // Skip if already in settled
        var isDup = settled.some(function(s) { return s.ticker === t.ticker; });
        if (!isDup) {
          allBets.push({
            title: t.title || t.ticker || '',
            ticker: t.ticker || '',
            side: t.side || '',
            entry_cents: t.price_cents || 0,
            count: t.count || 0,
            cost: t.cost_usd || 0,
            pnl: null,
            won: null,
            status: 'OPEN',
            date: (t.time || '').substring(0, 10),
            category: '',
            strategy: t.strategy || '',
            edge_reasons: t.edge_reasons || [],
            espn_edge: t.espn_edge,
            conviction: t.conviction || 0,
            game_state: '',
            entry_time: t.time || '',
            settle_time: '',
          });
        }
      });
    } catch(e) {}

    if (allBets.length === 0) {
      tableEl.innerHTML = '<div style="color:#555;font-size:11px;padding:8px">No trades yet. Place some bets and every trade will be tracked here with full reasoning.</div>';
    } else {
      // Sort: open first, then by date descending
      allBets.sort(function(a, b) {
        if (a.status === 'OPEN' && b.status !== 'OPEN') return -1;
        if (b.status === 'OPEN' && a.status !== 'OPEN') return 1;
        return (b.date || '').localeCompare(a.date || '');
      });

      var tbl = '<div style="display:flex;flex-direction:column;gap:4px">';
      allBets.forEach(function(s, idx) {
        var isWin = s.won === true;
        var isLoss = s.won === false;
        var isOpen = s.status === 'OPEN';
        var borderColor = isOpen ? '#ffb400' : isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#555';
        var pnlColor = isOpen ? '#ffb400' : isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#888';
        var resultLabel = s.status;
        var pnlStr = isOpen ? 'PENDING' : (s.pnl >= 0 ? '+$' : '-$') + Math.abs(s.pnl).toFixed(2);

        // Format date
        var dateStr = '';
        if (s.date) {
          try {
            var parts = s.date.split('-');
            var months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
            dateStr = months[parseInt(parts[1])-1] + ' ' + parseInt(parts[2]);
          } catch(e) { dateStr = s.date; }
        }

        // Strategy label
        var stratLabels = {live_sniper:'SNIPER', sniper:'SNIPER', moonshark:'MOONSHARK', closegame:'CLOSEGAME', manual:'MANUAL', unknown:''};
        var stratColors = {live_sniper:'#ffb400', sniper:'#ffb400', moonshark:'#e040fb', closegame:'#00d4ff', manual:'#5abf5a', unknown:'#555'};
        var stratLabel = stratLabels[s.strategy] || (s.strategy || '').toUpperCase();
        var stratColor = stratColors[s.strategy] || '#888';

        var detailId = 'journal-' + idx;

        tbl += '<div style="border-left:3px solid ' + borderColor + ';border-radius:4px;background:rgba(20,20,20,0.5);cursor:pointer" onclick="var d=document.getElementById(&#39;' + detailId + '&#39;);d.style.display=d.style.display===&#39;none&#39;?&#39;block&#39;:&#39;none&#39;">';
        // Main row
        tbl += '<div style="padding:8px 12px;display:flex;justify-content:space-between;align-items:center">';
        tbl += '<div style="flex:1;min-width:0">';
        tbl += '<div style="display:flex;align-items:center;gap:6px">';
        if (stratLabel) tbl += '<span style="font-size:8px;padding:1px 5px;background:' + stratColor + '22;border:1px solid ' + stratColor + '44;border-radius:3px;color:' + stratColor + ';font-weight:700">' + stratLabel + '</span>';
        tbl += '<span style="color:#ddd;font-size:11px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + s.title + '</span>';
        tbl += '</div>';
        tbl += '<div style="color:#666;font-size:9px;margin-top:3px">';
        if (dateStr) tbl += dateStr;
        tbl += ' &middot; ' + (s.side || '').toUpperCase() + ' ' + s.entry_cents + '&cent; x' + s.count;
        tbl += ' &middot; $' + s.cost.toFixed(2);
        if (s.category) tbl += ' &middot; ' + s.category;
        tbl += ' <span style="color:#444">&#9660; click for details</span>';
        tbl += '</div></div>';
        tbl += '<div style="text-align:right;margin-left:12px;flex-shrink:0">';
        tbl += '<div style="color:' + pnlColor + ';font-size:14px;font-weight:800">' + pnlStr + '</div>';
        tbl += '<div style="color:' + pnlColor + ';font-size:9px;font-weight:600;letter-spacing:0.5px">' + resultLabel + '</div>';
        tbl += '</div></div>';

        // Expandable edge detail (hidden by default)
        tbl += '<div id="' + detailId + '" style="display:none;padding:0 12px 10px 12px;border-top:1px solid #1a1a1a">';
        tbl += '<div style="padding-top:8px">';
        // Edge reasoning section
        if (s.edge_reasons && s.edge_reasons.length > 0) {
          tbl += '<div style="color:#ffb400;font-size:10px;font-weight:700;margin-bottom:4px">WHY THIS BET</div>';
          s.edge_reasons.forEach(function(r) {
            tbl += '<div style="color:#aaa;font-size:10px;line-height:1.5;padding-left:8px">&bull; ' + r + '</div>';
          });
        } else {
          tbl += '<div style="color:#555;font-size:10px;font-style:italic">No edge data recorded (pre-tracking trade)</div>';
        }
        // Additional details
        tbl += '<div style="display:flex;gap:16px;margin-top:8px;flex-wrap:wrap">';
        if (s.espn_edge) {
          var edgeColor = s.espn_edge > 0.05 ? '#00dc5a' : s.espn_edge > 0 ? '#ffb400' : '#ff5000';
          tbl += '<div style="background:#0d1117;border:1px solid #1f2937;border-radius:6px;padding:6px 10px;text-align:center"><div style="color:#555;font-size:8px;text-transform:uppercase">ESPN Edge</div><div style="color:' + edgeColor + ';font-size:13px;font-weight:800">+' + (s.espn_edge * 100).toFixed(1) + '%</div></div>';
        }
        if (s.conviction) {
          var convColor = s.conviction >= 4 ? '#00dc5a' : s.conviction >= 2 ? '#ffb400' : '#ff5000';
          tbl += '<div style="background:#0d1117;border:1px solid #1f2937;border-radius:6px;padding:6px 10px;text-align:center"><div style="color:#555;font-size:8px;text-transform:uppercase">Conviction</div><div style="color:' + convColor + ';font-size:13px;font-weight:800">' + s.conviction + '/5</div></div>';
        }
        if (s.entry_cents) {
          var potentialProfit = ((100 - s.entry_cents) * s.count / 100).toFixed(2);
          tbl += '<div style="background:#0d1117;border:1px solid #1f2937;border-radius:6px;padding:6px 10px;text-align:center"><div style="color:#555;font-size:8px;text-transform:uppercase">Max Profit</div><div style="color:#00dc5a;font-size:13px;font-weight:800">+$' + potentialProfit + '</div></div>';
        }
        if (s.game_state) {
          var gsColor = s.game_state === 'live' ? '#00d4ff' : '#888';
          var gsLabel = s.game_state === 'live' ? 'LIVE' : 'POST';
          tbl += '<div style="background:#0d1117;border:1px solid #1f2937;border-radius:6px;padding:6px 10px;text-align:center"><div style="color:#555;font-size:8px;text-transform:uppercase">Game State</div><div style="color:' + gsColor + ';font-size:13px;font-weight:800">' + gsLabel + '</div></div>';
        }
        tbl += '</div>'; // end detail flex
        // Outcome analysis for settled trades
        if (!isOpen && s.pnl !== null) {
          var outcomeColor = isWin ? '#0a2a0a' : '#2a0a0a';
          var outcomeBorder = isWin ? '#00dc5a' : '#ff5000';
          var outcomeIcon = isWin ? '&#10003;' : '&#10007;';
          var outcomeText = isWin ? 'Edge was real — bet paid off' : 'Edge didn\'t hold — market moved against us';
          if (isLoss && s.espn_edge && s.espn_edge > 0.10) outcomeText = 'Had strong ESPN edge (+' + (s.espn_edge*100).toFixed(0) + '%) but market disagreed';
          if (isLoss && s.entry_cents && s.entry_cents < 40) outcomeText = 'Underdog bet at ' + s.entry_cents + '&cent; — high risk/high reward didn\'t pay off this time';
          if (isWin && s.entry_cents && s.entry_cents >= 65) outcomeText = 'Favorite at ' + s.entry_cents + '&cent; held as expected';
          tbl += '<div style="margin-top:8px;padding:6px 10px;background:' + outcomeColor + ';border:1px solid ' + outcomeBorder + '44;border-radius:4px;font-size:10px;color:' + outcomeBorder + '">';
          tbl += '<span style="font-weight:700">' + outcomeIcon + ' ' + resultLabel + '</span> &middot; ' + outcomeText;
          tbl += '</div>';
        }
        tbl += '</div></div>'; // end expandable
        tbl += '</div>'; // end card
      });
      tbl += '</div>';
      if (allBets.length > 50) {
        tbl += '<div style="color:#555;font-size:9px;padding:6px 4px;text-align:center">Showing all ' + allBets.length + ' trades</div>';
      }
      tableEl.innerHTML = tbl;
    }

    // Update trade badge
    var badge = document.getElementById('trade-badge');
    if (badge) badge.textContent = settled.length;

  } catch(e) {
    console.error('Performance tab error', e);
    var kpiEl = document.getElementById('perf-kpis');
    if (kpiEl) kpiEl.innerHTML = '<span style="color:#ff5000">Error loading: ' + e.message + '</span>';
  }
}

// --- 75%'ers Tab ---
async function loadSeventyFivers() {
  try {
    var data = await fetch(API + '/seventy-fivers').then(r => r.json());
    var stats = await fetch(API + '/seventy-fivers-stats').then(r => r.json());

    // Stats banner
    var streakEl = document.getElementById('sf-streak-text');
    var wrEl = document.getElementById('sf-winrate-text');
    var profEl = document.getElementById('sf-profit-text');
    if (stats.streak > 0) {
      streakEl.textContent = String.fromCodePoint(0x1F525) + ' ' + stats.streak + ' in a row!';
    } else if (stats.total_bets === 0) {
      streakEl.textContent = 'No bets yet - find your first 75% pick!';
    } else {
      streakEl.textContent = 'Best streak: ' + stats.best_streak;
    }
    wrEl.textContent = stats.total_bets > 0 ? stats.win_rate + '% win rate (' + stats.wins + 'W/' + stats.losses + 'L)' : '';
    var pf = stats.profit || 0;
    profEl.textContent = stats.total_bets > 0 ? ((pf >= 0 ? '+$' : '-$') + Math.abs(pf).toFixed(2) + ' profit') : '';
    profEl.style.color = pf >= 0 ? '#00dc5a' : '#ff5000';

    // Filter
    var _sfEl = _el('sf-live-only'); var liveOnly = _sfEl ? _sfEl.checked : false;
    var picks = (data.picks || []).filter(function(p) { return liveOnly ? p.is_live : true; });

    var cardsEl = document.getElementById('sf-cards');
    if (picks.length === 0) {
      cardsEl.innerHTML = '<div style="color:#666;text-align:center;padding:40px;grid-column:1/-1">' +
        (liveOnly ? 'No live 75% picks right now. Try turning off "Live Only" or check back during game time.' : 'No 75% picks found. Markets may be quiet right now.') + '</div>';
      return;
    }

    var html = '';
    picks.forEach(function(p) {
      var sideColor = p.side === 'yes' ? '#00dc5a' : '#ff5000';
      var sideLabel = p.side.toUpperCase();
      var liveBadge = p.is_live ? '<span style="background:#ff0040;color:#fff;font-size:9px;padding:2px 6px;border-radius:4px;font-weight:700;animation:pulse 2s infinite">&#x25CF; LIVE</span>' : '';
      var closingSoonBadge = p.closing_soon ? '<span style="background:#ff8c00;color:#fff;font-size:9px;padding:2px 6px;border-radius:4px;font-weight:700">CLOSING SOON</span>' : '';
      var dipBadge = p.is_dip ? '<span style="background:#00d4ff;color:#000;font-size:9px;padding:2px 6px;border-radius:4px;font-weight:700">DIP -' + (p.line_movement ? p.line_movement.dip_size : 0) + '&#162;</span>' : '';
      var platforms = '';
      if (p.platforms && p.platforms.length > 0) {
        platforms = '<span style="font-size:10px;color:#888;margin-left:4px">' + (p.platform_count) + ' platforms agree</span>';
      }
      // Line movement indicator
      var lineInfo = '';
      if (p.line_movement && p.line_movement.direction !== 'new') {
        var lc = p.line_movement.change;
        if (lc !== 0) {
          var lineColor = lc > 0 ? '#00dc5a' : '#ff5000';
          var arrow = lc > 0 ? '&#x2191;' : '&#x2193;';
          lineInfo = '<span style="color:' + lineColor + ';font-size:10px;font-weight:600"> ' + arrow + Math.abs(lc) + '&#162;</span>';
        }
      }
      var cardBorder = p.closing_soon ? '#ff8c00' : (p.is_dip ? '#00d4ff' : '#222');
      html += '<div style="background:#111;border:1px solid ' + cardBorder + ';border-radius:12px;padding:16px;position:relative">';
      html += '<div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:10px">';
      html += '<div style="flex:1;min-width:0"><div style="font-size:12px;color:#ccc;line-height:1.3;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + p.title + '</div></div>';
      html += '<div style="margin-left:8px;display:flex;gap:4px;align-items:center;flex-wrap:wrap">' + closingSoonBadge + liveBadge + dipBadge + '</div>';
      html += '</div>';
      html += '<div style="display:flex;align-items:baseline;gap:12px;margin-bottom:8px">';
      html += '<span style="font-size:28px;font-weight:800;color:#fff">' + p.price_cents + '&#162;</span>';
      html += lineInfo;
      html += '<span style="background:' + sideColor + ';color:#000;font-size:11px;font-weight:700;padding:2px 8px;border-radius:4px">' + sideLabel + '</span>';
      html += '<span style="color:#00dc5a;font-size:13px;font-weight:600">+' + p.profit_cents + '&#162;</span>';
      html += '</div>';
      html += '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">';
      html += '<div style="font-size:11px;color:#666">';
      html += 'Vol: ' + (p.volume >= 1000 ? (p.volume/1000).toFixed(1) + 'K' : p.volume);
      html += ' &#x2022; ' + (p.time_left || 'TBD');
      html += platforms;
      html += '</div>';
      html += '</div>';
      html += '<div style="display:flex;gap:8px">';
      html += '<button onclick="quickBet(&quot;' + p.ticker + '&quot;,&quot;' + p.side + '&quot;,' + p.price_cents + ')" style="flex:1;background:' + (p.closing_soon ? '#ff8c00' : '#00dc5a') + ';color:#000;border:none;padding:10px;border-radius:8px;font-weight:700;font-size:13px;cursor:pointer">' + (p.closing_soon ? 'LOCK IN $' : 'Bet $') + p.bet_size.toFixed(0) + '</button>';
      html += '<a href="' + p.url + '" target="_blank" style="display:flex;align-items:center;padding:10px 12px;background:#222;border-radius:8px;color:#888;text-decoration:none;font-size:11px">&#x2197;</a>';
      html += '</div>';
      html += '</div>';
    });
    cardsEl.innerHTML = html;
  } catch(e) {
    console.error('75%ers error', e);
    _setHTML('sf-cards', '<div style="color:#ff5000;text-align:center;padding:40px;grid-column:1/-1">Error loading picks</div>');
  }
}

async function quickBet(ticker, side, priceCents) {
  if (!confirm('Place ' + side.toUpperCase() + ' bet on ' + ticker + ' @ ' + priceCents + '&#162;?')) return;
  try {
    var resp = await fetch(API + '/quick-bet', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ticker: ticker, side: side, price_cents: priceCents})
    });
    var data = await resp.json();
    if (data.success) {
      showToast('Bet placed! ' + side.toUpperCase() + ' ' + ticker + ' @ ' + priceCents + '&#162; x' + data.count + ' ($' + data.cost_usd.toFixed(2) + ')', 'success');
      loadSeventyFivers();
      loadPortfolio();
    } else {
      showToast('Bet failed: ' + (data.error || 'Unknown error'), 'error');
    }
  } catch(e) {
    showToast('Bet error: ' + e.message, 'error');
  }
}

// --- Quant Tab ---
async function loadQuantPicks() {
  try {
    var data = await fetch(API + '/quant-picks').then(r => r.json());
    var stats = await fetch(API + '/quant-stats').then(r => r.json());
    var picks = data.picks || [];
    var strongOnly = document.getElementById('quant-strong-only');
    if (strongOnly && strongOnly.checked) {
      picks = picks.filter(function(p) { return p.deviation_pct >= 25; });
    }

    // Update banner
    var bannerEl = document.getElementById('quant-banner-text');
    bannerEl.textContent = data.count + ' mispriced markets found';
    var wrEl = document.getElementById('quant-winrate-text');
    wrEl.textContent = stats.total_bets > 0 ? stats.win_rate + '% win rate (' + stats.wins + 'W/' + stats.losses + 'L)' : '';
    var prEl = document.getElementById('quant-profit-text');
    if (stats.total_bets > 0) {
      var pc = stats.profit >= 0 ? '#00dc5a' : '#ff5000';
      prEl.innerHTML = '<span style="color:' + pc + '">' + (stats.profit >= 0 ? '+' : '') + '$' + stats.profit.toFixed(2) + ' profit</span>';
    }

    var cardsEl = document.getElementById('quant-cards');
    if (picks.length === 0) {
      cardsEl.innerHTML = '<div style="color:#555;text-align:center;padding:40px;grid-column:1/-1">No strong mispricings right now. Check back soon.</div>';
      return;
    }

    var html = '';
    picks.forEach(function(p) {
      var sideColor = p.side === 'yes' ? '#00dc5a' : '#ff5000';
      var sideLabel = p.side.toUpperCase();
      var catColors = {sports:'#00dc5a',politics:'#ff8c00',crypto:'#f7931a',economics:'#00d4ff',entertainment:'#e040fb',science:'#76ff03',finance:'#ffb400',other:'#888'};
      var catColor = catColors[p.category] || '#888';
      var catBadge = '<span style="background:' + catColor + '22;color:' + catColor + ';font-size:9px;padding:2px 6px;border-radius:4px;font-weight:600;text-transform:uppercase">' + p.category + '</span>';

      // Line movement
      var lineInfo = '';
      if (p.line_movement && p.line_movement.direction !== 'new') {
        var lc = p.line_movement.change;
        if (lc !== 0) {
          var lineColor = lc > 0 ? '#00dc5a' : '#ff5000';
          var arrow = lc > 0 ? '&#x2191;' : '&#x2193;';
          lineInfo = '<span style="color:' + lineColor + ';font-size:10px;font-weight:600"> ' + arrow + Math.abs(lc) + '&#162;</span>';
        }
      }

      // Platform detail
      var platHtml = '';
      if (p.platforms && p.platforms.length > 0) {
        p.platforms.forEach(function(pl) {
          var pn = pl.platform.charAt(0).toUpperCase() + pl.platform.slice(1,3);
          platHtml += '<span style="background:#1a1a2e;color:#aaa;font-size:9px;padding:2px 5px;border-radius:3px">' + pn + ' ' + pl.price + '&#162;</span> ';
        });
      }

      var dipBadge = p.is_dip ? '<span style="background:#00d4ff;color:#000;font-size:9px;padding:2px 6px;border-radius:4px;font-weight:700">DIP</span>' : '';
      var edgeStrength = p.deviation_pct >= 25 ? 'STRONG' : p.deviation_pct >= 18 ? 'GOOD' : 'MODERATE';
      var edgeColor = p.deviation_pct >= 25 ? '#00d4ff' : p.deviation_pct >= 18 ? '#00dc5a' : '#ffb400';

      html += '<div style="background:#0d1117;border:1px solid #1a3050;border-radius:12px;padding:16px;position:relative">';
      // Title row
      html += '<div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:10px">';
      html += '<div style="flex:1;min-width:0"><div style="font-size:12px;color:#ccc;line-height:1.3;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + p.title + '</div></div>';
      html += '<div style="margin-left:8px;display:flex;gap:4px;align-items:center">' + catBadge + dipBadge + '</div>';
      html += '</div>';
      // Edge hero
      html += '<div style="display:flex;align-items:baseline;gap:12px;margin-bottom:8px">';
      html += '<span style="font-size:28px;font-weight:800;color:' + edgeColor + '">' + p.deviation_pct.toFixed(0) + '%</span>';
      html += '<span style="font-size:11px;color:#888">edge</span>';
      html += '<span style="background:' + edgeColor + '22;color:' + edgeColor + ';font-size:10px;padding:2px 6px;border-radius:4px;font-weight:600">' + edgeStrength + '</span>';
      html += '</div>';
      // Price comparison
      html += '<div style="display:flex;align-items:center;gap:8px;margin-bottom:8px;font-size:12px">';
      html += '<span style="color:#888">Kalshi:</span><span style="color:#fff;font-weight:700">' + p.price_cents + '&#162;</span>';
      html += lineInfo;
      html += '<span style="color:#888;margin-left:8px">Consensus:</span><span style="color:#00d4ff;font-weight:700">' + p.consensus_cents + '&#162;</span>';
      html += '<span style="background:' + sideColor + ';color:#000;font-size:10px;font-weight:700;padding:1px 6px;border-radius:3px;margin-left:4px">' + sideLabel + '</span>';
      html += '</div>';
      // Platforms + volume
      html += '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">';
      html += '<div style="display:flex;gap:4px;flex-wrap:wrap">' + platHtml + '</div>';
      html += '</div>';
      html += '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">';
      html += '<div style="font-size:11px;color:#666">Vol: ' + (p.volume >= 1000 ? (p.volume/1000).toFixed(1) + 'K' : p.volume) + ' &#x2022; ' + p.platform_count + ' platforms</div>';
      html += '<div style="font-size:12px;color:#00dc5a;font-weight:600">EV: +$' + p.ev_dollars.toFixed(2) + '</div>';
      html += '</div>';
      // Action buttons
      html += '<div style="display:flex;gap:8px">';
      html += '<button onclick="quantBet(&quot;' + p.ticker + '&quot;,&quot;' + p.side + '&quot;,' + p.price_cents + ',&quot;' + p.title.replace(/'/g, '') + '&quot;,' + p.deviation_pct + ')" style="flex:1;background:#00d4ff;color:#000;border:none;padding:10px;border-radius:8px;font-weight:700;font-size:13px;cursor:pointer">Trade $' + p.bet_size.toFixed(0) + '</button>';
      html += '<a href="' + p.url + '" target="_blank" style="display:flex;align-items:center;padding:10px 12px;background:#1a2030;border-radius:8px;color:#888;text-decoration:none;font-size:11px">&#x2197;</a>';
      html += '</div>';
      html += '</div>';
    });
    cardsEl.innerHTML = html;

    // Render trade history below cards
    var trades = stats.trades || [];
    if (trades.length > 0) {
      var histHtml = '<div style="margin-top:20px;background:#0d1117;border:1px solid #1a3050;border-radius:10px;padding:14px">';
      histHtml += '<div style="color:#00d4ff;font-size:13px;font-weight:700;margin-bottom:10px">Quant Trade History</div>';
      histHtml += '<table style="width:100%;border-collapse:collapse;font-size:10px">';
      histHtml += '<tr style="color:#888;border-bottom:1px solid #1a3050;text-align:left">';
      histHtml += '<th style="padding:6px">Time</th><th style="padding:6px">Market</th><th style="padding:6px">Side</th><th style="padding:6px">Price</th><th style="padding:6px">Cost</th><th style="padding:6px">Edge</th><th style="padding:6px">Status</th>';
      histHtml += '</tr>';
      trades.slice().reverse().forEach(function(t) {
        var sideC = t.side === 'yes' ? '#00dc5a' : '#ff5000';
        var timeStr = fmtTime(t.time);
        var statusC = t.status === 'won' ? '#00dc5a' : t.status === 'lost' ? '#ff5000' : '#888';
        var statusL = t.status === 'won' ? 'WON' : t.status === 'lost' ? 'LOST' : 'OPEN';
        histHtml += '<tr style="border-bottom:1px solid #0d1a2e">';
        histHtml += '<td style="padding:5px;color:#666">' + timeStr + '</td>';
        histHtml += '<td style="padding:5px;color:#ccc;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (t.title || t.ticker) + '</td>';
        histHtml += '<td style="padding:5px;color:' + sideC + ';font-weight:700">' + (t.side || '').toUpperCase() + '</td>';
        histHtml += '<td style="padding:5px;color:#fff">' + (t.price_cents || 0) + '&#162; x' + (t.count || 0) + '</td>';
        histHtml += '<td style="padding:5px;color:#ffb400">$' + (t.cost_usd || 0).toFixed(2) + '</td>';
        histHtml += '<td style="padding:5px;color:#00d4ff">' + (t.deviation_pct || 0).toFixed(0) + '%</td>';
        histHtml += '<td style="padding:5px;color:' + statusC + ';font-weight:600">' + statusL + '</td>';
        histHtml += '</tr>';
      });
      histHtml += '</table></div>';
      cardsEl.innerHTML += histHtml;
    }
  } catch(e) {
    console.error('Quant error', e);
    _setHTML('quant-cards', '<div style="color:#ff5000;text-align:center;padding:40px;grid-column:1/-1">Error loading quant picks</div>');
  }
}

async function quantBet(ticker, side, priceCents, title, deviationPct) {
  if (!confirm('Place QUANT trade: ' + side.toUpperCase() + ' ' + ticker + ' @ ' + priceCents + 'c?')) return;
  try {
    var resp = await fetch(API + '/quant-bet', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ticker: ticker, side: side, price_cents: priceCents, title: title || ticker, deviation_pct: deviationPct || 0})
    });
    var data = await resp.json();
    if (data.success) {
      showToast('Quant trade placed! ' + side.toUpperCase() + ' ' + ticker + ' @ ' + priceCents + 'c x' + data.count + ' ($' + data.cost.toFixed(2) + ')', 'success');
      loadQuantPicks();
      loadPortfolio();
    } else {
      showToast('Trade failed: ' + (data.error || JSON.stringify(data.result).substring(0, 80)), 'error');
    }
  } catch(e) {
    showToast('Trade error: ' + e.message, 'error');
  }
}

// --- MoonShark Tab ---
// MoonShark Wheel
var _wheelOpps = [];
var _wheelSpinning = false;

function drawWheel(opps, highlightIdx) {
  var canvas = document.getElementById('moonshark-wheel');
  if (!canvas) return;
  var ctx = canvas.getContext('2d');
  var cx = 140, cy = 140, r = 130;
  ctx.clearRect(0, 0, 280, 280);
  var n = opps.length || 1;
  var colors = ['#003a5a','#004a2a','#3a2a00','#2a003a','#003a3a','#3a0a0a','#1a3a00','#2a2a3a'];
  for (var i = 0; i < n; i++) {
    var startAngle = (i * 2 * Math.PI / n) - Math.PI / 2;
    var endAngle = ((i + 1) * 2 * Math.PI / n) - Math.PI / 2;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.arc(cx, cy, r, startAngle, endAngle);
    ctx.closePath();
    ctx.fillStyle = i === highlightIdx ? '#00d4ff' : colors[i % colors.length];
    ctx.fill();
    ctx.strokeStyle = '#0a1a22';
    ctx.lineWidth = 2;
    ctx.stroke();
    // Label
    var midAngle = (startAngle + endAngle) / 2;
    var labelR = r * 0.65;
    var lx = cx + Math.cos(midAngle) * labelR;
    var ly = cy + Math.sin(midAngle) * labelR;
    ctx.save();
    ctx.translate(lx, ly);
    ctx.rotate(midAngle + Math.PI / 2);
    ctx.fillStyle = i === highlightIdx ? '#000' : '#fff';
    ctx.font = 'bold 9px sans-serif';
    ctx.textAlign = 'center';
    var label = opps[i] ? (opps[i].title || '').substring(0, 18) : '';
    ctx.fillText(label, 0, 0);
    ctx.font = '8px sans-serif';
    ctx.fillStyle = i === highlightIdx ? '#000' : '#ffb400';
    var priceLabel = opps[i] ? opps[i].price + '¢ → $' + opps[i].payout : '';
    ctx.fillText(priceLabel, 0, 12);
    ctx.restore();
  }
  // Center circle
  ctx.beginPath();
  ctx.arc(cx, cy, 22, 0, 2 * Math.PI);
  ctx.fillStyle = '#0a1a22';
  ctx.fill();
  ctx.strokeStyle = '#00d4ff';
  ctx.lineWidth = 2;
  ctx.stroke();
  ctx.fillStyle = '#00d4ff';
  ctx.font = 'bold 16px sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText('🦈', cx, cy + 6);
}

function skipWheelPick() {
  _setHTML('wheel-result', '<div style="color:#888;font-size:11px;padding:8px">Skipped — spin again!</div>');
}

function spinWheel() {
  if (_wheelSpinning || _wheelOpps.length === 0) return;
  _wheelSpinning = true;
  var btn = document.getElementById('spin-btn');
  btn.disabled = true;
  btn.textContent = 'Spinning...';
  var n = _wheelOpps.length;
  var winner = Math.floor(Math.random() * n);
  var totalSteps = 40 + Math.floor(Math.random() * 20) + winner;
  var step = 0;
  function spinStep() {
    var idx = step % n;
    drawWheel(_wheelOpps, idx);
    step++;
    if (step >= totalSteps) {
      drawWheel(_wheelOpps, winner);
      var pick = _wheelOpps[winner];
      var resultEl = document.getElementById('wheel-result');
      resultEl.innerHTML = '<div style="background:#002a3a;border:1px solid #00d4ff;border-radius:8px;padding:12px;margin-top:4px">' +
        '<div style="color:#00d4ff;font-weight:700;font-size:14px">🎯 ' + pick.title + '</div>' +
        '<div style="color:#ffb400;font-size:12px;margin-top:6px">' + pick.side.toUpperCase() + ' @ ' + pick.price + '¢ · ' + pick.win_prob + '% implied · $' + pick.payout + ' potential payout</div>' +
        '<div style="display:flex;gap:12px;justify-content:center;margin-top:10px">' +
        '<button onclick="placeMoonsharkBet(&quot;' + pick.ticker + '&quot;,&quot;' + pick.side + '&quot;,' + pick.price + ',true)" style="background:#00dc5a;border:none;color:#000;padding:10px 30px;border-radius:8px;font-size:14px;font-weight:800;cursor:pointer;min-width:100px">✅ YES</button>' +
        '<button onclick="skipWheelPick()" style="background:#ff3030;border:none;color:#fff;padding:10px 30px;border-radius:8px;font-size:14px;font-weight:800;cursor:pointer;min-width:100px">❌ NO</button>' +
        '</div></div>';
      btn.disabled = false;
      btn.textContent = '🦈 SPIN AGAIN!';
      _wheelSpinning = false;
      return;
    }
    // Decelerate: start fast, slow down near the end
    var remaining = totalSteps - step;
    var delay = remaining > 20 ? 50 : remaining > 10 ? 100 : remaining > 5 ? 180 : 300;
    setTimeout(spinStep, delay);
  }
  spinStep();
}

async function loadMoonsharkOpps() {
  try {
    var data = await fetch(API + '/moonshark-opportunities').then(r => r.json());
    var opps = data.opportunities || [];
    // Wheel uses WTA tennis only
    var wtaForWheel = data.wta_opportunities || opps;
    _wheelOpps = wtaForWheel.slice(0, 8);
    if (_wheelOpps.length > 0) {
      drawWheel(_wheelOpps, -1);
    } else {
      var canvas = document.getElementById('moonshark-wheel');
      if (canvas) {
        var ctx = canvas.getContext('2d');
        ctx.clearRect(0, 0, 280, 280);
        ctx.fillStyle = '#0a1a22';
        ctx.fillRect(0, 0, 280, 280);
        ctx.fillStyle = '#555';
        ctx.font = '13px sans-serif';
        ctx.textAlign = 'center';
        ctx.fillText('No live WTA matches right now', 140, 130);
        ctx.fillText('Check back during match hours!', 140, 150);
      }
    }
    var el = document.getElementById('moonshark-opps');
    if (!el) return;
    if (opps.length === 0) {
      el.innerHTML = '<div style="color:#555;font-size:10px;padding:8px;text-align:center">No opportunities right now — markets are tight. Check back soon!</div>';
      return;
    }
    var h = '';
    opps.slice(0, 5).forEach(function(o, i) {
      var probColor = o.win_prob >= 30 ? '#ffb400' : o.win_prob >= 20 ? '#ff8800' : '#ff5000';
      h += '<div style="display:flex;align-items:center;gap:10px;padding:8px 10px;background:#0d2230;border:1px solid #1a3a4a;border-radius:8px">';
      h += '<div style="color:#00d4ff;font-size:16px;font-weight:800;min-width:20px">' + (i+1) + '</div>';
      h += '<div style="flex:1">';
      h += '<div style="color:#ddd;font-size:11px;font-weight:600">' + (o.title || '').substring(0, 40) + '</div>';
      h += '<div style="display:flex;gap:8px;margin-top:3px;font-size:10px">';
      h += '<span style="color:#ffb400">' + o.price + '¢ entry</span>';
      h += '<span style="color:' + probColor + '">' + o.win_prob + '% chance</span>';
      h += '<span style="color:#00dc5a">$' + o.payout + ' payout</span>';
      h += '</div></div>';
      h += '<button onclick="placeMoonsharkBet(&quot;' + o.ticker + '&quot;,&quot;' + o.side + '&quot;,' + o.price + ')" style="background:#002a3a;border:1px solid #00d4ff;color:#00d4ff;padding:4px 10px;border-radius:6px;font-size:9px;font-weight:700;cursor:pointer;white-space:nowrap">BET</button>';
      h += '</div>';
    });
    el.innerHTML = h;
    // WTA Tennis column
    var wtaOpps = data.wta_opportunities || [];
    var wtaEl = document.getElementById('wta-opps');
    if (!wtaEl) return;
    if (wtaOpps.length === 0) {
      wtaEl.innerHTML = '<div style="color:#555;font-size:10px;padding:8px;text-align:center">No live WTA matches right now. Check back during match hours!</div>';
      return;
    }
    var wh = '';
    wtaOpps.slice(0, 5).forEach(function(o, i) {
      var probColor = o.win_prob >= 30 ? '#e040fb' : o.win_prob >= 20 ? '#ff8800' : '#ff5000';
      wh += '<div style="display:flex;align-items:center;gap:10px;padding:8px 10px;background:#1a0a22;border:1px solid #3a1a4a;border-radius:8px">';
      wh += '<div style="color:#e040fb;font-size:16px;font-weight:800;min-width:20px">🎾</div>';
      wh += '<div style="flex:1">';
      wh += '<div style="color:#ddd;font-size:11px;font-weight:600">' + (o.title || '').substring(0, 40) + '</div>';
      wh += '<div style="display:flex;gap:8px;margin-top:3px;font-size:10px">';
      wh += '<span style="color:#e040fb">' + o.price + '¢ entry</span>';
      wh += '<span style="color:' + probColor + '">' + o.win_prob + '% chance</span>';
      wh += '<span style="color:#00dc5a">$' + o.payout + ' payout</span>';
      wh += '</div></div>';
      wh += '<button onclick="placeMoonsharkBet(&quot;' + o.ticker + '&quot;,&quot;' + o.side + '&quot;,' + o.price + ')" style="background:#2a0a3a;border:1px solid #e040fb;color:#e040fb;padding:4px 10px;border-radius:6px;font-size:9px;font-weight:700;cursor:pointer;white-space:nowrap">BET</button>';
      wh += '</div>';
    });
    wtaEl.innerHTML = wh;
  } catch(e) {
    var el = document.getElementById('moonshark-opps');
    if (el) el.innerHTML = '<div style="color:#555;font-size:10px;padding:8px">Error loading opportunities</div>';
    var wtaEl = document.getElementById('wta-opps');
    if (wtaEl) wtaEl.innerHTML = '<div style="color:#555;font-size:10px;padding:8px">Error loading WTA</div>';
  }
}

async function placeMoonsharkBet(ticker, side, price, fromWheel) {
  if (!confirm('Place MoonShark bet on ' + ticker + '?')) return;
  try {
    var resp = await fetch(API + '/moonshot-bet', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ticker: ticker, side: side, source: fromWheel ? 'wheel' : 'manual'})
    }).then(r => r.json());
    if (resp.error) { alert('Error: ' + resp.error); }
    else { alert('Bet placed! 🎾🦈'); loadMoonshark(); loadBetsFeed(); loadWtaWheelStats(); }
  } catch(e) { alert('Error placing bet'); }
}

async function loadWtaWheelStats() {
  try {
    var data = await fetch(API + '/wta-wheel-stats').then(function(r) { return r.json(); });
    var statsEl = document.getElementById('wta-wheel-stats');
    var betsEl = document.getElementById('wta-wheel-bets');
    if (!statsEl) return;

    var pnl = data.pnl || 0;
    var unrealized = data.unrealized || 0;
    var totalPnl = pnl + unrealized;
    var pnlColor = totalPnl >= 0 ? '#00dc5a' : '#ff5000';
    var pnlSign = totalPnl >= 0 ? '+' : '-';

    var sh = '';
    sh += '<div style="display:grid;grid-template-columns:1fr 1fr;gap:8px">';
    sh += '<div style="background:#1a0a22;border-radius:8px;padding:10px;text-align:center">';
    sh += '<div style="font-size:9px;color:#888">Total Bets</div>';
    sh += '<div style="font-size:20px;font-weight:800;color:#e040fb">' + (data.total_bets || 0) + '</div>';
    sh += '</div>';
    sh += '<div style="background:#1a0a22;border-radius:8px;padding:10px;text-align:center">';
    sh += '<div style="font-size:9px;color:#888">Win Rate</div>';
    sh += '<div style="font-size:20px;font-weight:800;color:' + (data.win_rate > 0 ? '#00dc5a' : '#888') + '">' + (data.win_rate || 0) + '%</div>';
    sh += '</div>';
    sh += '<div style="background:#1a0a22;border-radius:8px;padding:10px;text-align:center">';
    sh += '<div style="font-size:9px;color:#888">W / L</div>';
    sh += '<div style="font-size:20px;font-weight:800"><span style="color:#00dc5a">' + (data.wins || 0) + 'W</span> / <span style="color:#ff5000">' + (data.losses || 0) + 'L</span></div>';
    sh += '</div>';
    sh += '<div style="background:#1a0a22;border-radius:8px;padding:10px;text-align:center">';
    sh += '<div style="font-size:9px;color:#888">P&L</div>';
    sh += '<div style="font-size:20px;font-weight:800;color:' + pnlColor + '">' + pnlSign + '$' + Math.abs(totalPnl).toFixed(2) + '</div>';
    sh += '</div>';
    sh += '</div>';

    // Open positions
    if (data.open_count > 0) {
      var uColor = unrealized >= 0 ? '#00dc5a' : '#ff5000';
      sh += '<div style="margin-top:10px;padding:8px 10px;background:#1a0a22;border-radius:8px;display:flex;justify-content:space-between">';
      sh += '<span style="color:#888;font-size:10px">' + data.open_count + ' open positions</span>';
      sh += '<span style="color:' + uColor + ';font-size:10px;font-weight:700">' + (unrealized >= 0 ? '+' : '-') + '$' + Math.abs(unrealized).toFixed(2) + ' unrealized</span>';
      sh += '</div>';
    }

    // Wheel-specific stats
    if (data.wheel_bets > 0) {
      var wPnlColor = data.wheel_pnl >= 0 ? '#00dc5a' : '#ff5000';
      sh += '<div style="margin-top:8px;padding:8px 10px;background:#002a3a;border:1px solid #004a6a;border-radius:8px;display:flex;justify-content:space-between">';
      sh += '<span style="color:#00d4ff;font-size:10px;font-weight:600">Wheel Bets: ' + data.wheel_bets + '</span>';
      sh += '<span style="color:' + wPnlColor + ';font-size:10px;font-weight:700">' + (data.wheel_pnl >= 0 ? '+' : '-') + '$' + Math.abs(data.wheel_pnl).toFixed(2) + '</span>';
      sh += '</div>';
    }

    statsEl.innerHTML = sh;

    // Bet list
    var bets = data.bets || [];
    if (bets.length === 0) {
      betsEl.innerHTML = '<div style="color:#555;font-size:10px;text-align:center;padding:8px">No WTA bets yet — spin the wheel!</div>';
    } else {
      var bh = '';
      bets.reverse().forEach(function(b) {
        var isWin = b.result === 'win';
        var isLoss = b.result === 'loss';
        var isPending = b.result === null || b.result === undefined;
        var borderColor = isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#e040fb';
        var resultText = isWin ? 'WON' : isLoss ? 'LOST' : 'OPEN';
        var resultColor = isWin ? '#00dc5a' : isLoss ? '#ff5000' : '#e040fb';
        var pnlText = isPending ? '$' + b.cost.toFixed(2) + ' bet' : ((b.pnl >= 0 ? '+$' : '-$') + Math.abs(b.pnl).toFixed(2));
        var title = (b.title || b.ticker || '').substring(0, 35);
        var isWheel = b.source !== 'bot';
        bh += '<div style="display:flex;align-items:center;gap:8px;padding:6px 8px;border-left:3px solid ' + borderColor + ';background:rgba(224,64,251,0.03);border-radius:4px">';
        bh += '<div style="flex:1;min-width:0">';
        bh += '<div style="font-size:10px;color:#ddd;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">' + (isWheel ? '🎡 ' : '🤖 ') + title + '</div>';
        bh += '<div style="font-size:9px;color:#888">' + (b.side || '').toUpperCase() + ' @ ' + b.price + 'c x' + b.count + '</div>';
        bh += '</div>';
        bh += '<div style="text-align:right;flex-shrink:0">';
        bh += '<div style="font-size:11px;font-weight:700;color:' + resultColor + '">' + pnlText + '</div>';
        bh += '<div style="font-size:8px;color:' + resultColor + '">' + resultText + '</div>';
        bh += '</div></div>';
      });
      betsEl.innerHTML = bh;
    }
  } catch(e) {
    console.log('wta-wheel-stats error', e);
  }
}

async function loadMoonshark() {
  loadMoonsharkOpps();
  loadWtaWheelStats();
  try {
    var data = await fetch(API + '/moonshark').then(r => r.json());
    var today = data.today || {};
    var lifetime = data.lifetime || {};
    var positions = data.active_positions || [];
    var history = data.trade_history || [];
    var cumPnl = data.cumulative_pnl || [];
    var settings = data.settings || {};
    var enabled = data.enabled !== false;

    // Toggle button in header
    var toggleBtn = document.getElementById('mshark-toggle-btn');
    if (toggleBtn) {
      var tc = enabled ? '#00dc5a' : '#ff5000';
      toggleBtn.style.borderColor = tc;
      toggleBtn.style.color = tc;
      toggleBtn.innerHTML = '&#x1F988; ' + (enabled ? 'ENABLED' : 'DISABLED');
    }

    // Stats Bar
    var statsBar = document.getElementById('mshark-stats-bar');
    var pnl = lifetime.total_pnl || 0;
    var pnlColor = pnl >= 0 ? '#00dc5a' : '#ff5000';
    var pnlSign = pnl >= 0 ? '+' : '';
    var roi = lifetime.roi || 0;
    var roiColor = roi >= 0 ? '#00dc5a' : '#ff5000';
    function statBox(label, value, color) {
      return '<div style="background:#0a1a22;border:1px solid #1a3a4a;border-radius:10px;padding:10px 8px;text-align:center">'
        + '<div style="font-size:9px;color:#006688;text-transform:uppercase;letter-spacing:0.5px">' + label + '</div>'
        + '<div style="font-size:18px;font-weight:800;color:' + (color || '#00d4ff') + '">' + value + '</div></div>';
    }
    statsBar.innerHTML = ''
      + statBox('Total Trades', lifetime.total_trades || 0)
      + statBox('Wins', '<span style="color:#00dc5a">' + (lifetime.wins || 0) + '</span>')
      + statBox('Losses', '<span style="color:#ff5000">' + (lifetime.losses || 0) + '</span>')
      + statBox('Win Rate', (lifetime.win_rate || 0) + '%')
      + statBox('Total P&amp;L', pnlSign + '$' + Math.abs(pnl).toFixed(2), pnlColor)
      + statBox('Best Win', '+$' + (lifetime.best_win || 0).toFixed(2), '#00dc5a')
      + statBox('ROI', (roi >= 0 ? '+' : '') + roi + '%', roiColor);

    // Active Positions
    var posContainer = document.getElementById('mshark-positions');
    var activeBadge = document.getElementById('mshark-active-badge');
    if (activeBadge) activeBadge.textContent = positions.length;
    if (positions.length === 0) {
      posContainer.innerHTML = '<div class="empty" style="color:#006688">No active MoonShark positions &mdash; shark is hunting</div>';
    } else {
      var posHtml = '<table style="width:100%;border-collapse:collapse;font-size:12px"><thead><tr style="color:#006688;font-size:10px;text-transform:uppercase;letter-spacing:0.5px">'
        + '<th style="text-align:left;padding:6px 8px">Ticker</th>'
        + '<th style="text-align:right;padding:6px 8px">Buy Price</th>'
        + '<th style="text-align:right;padding:6px 8px">Contracts</th>'
        + '<th style="text-align:right;padding:6px 8px">Cost</th>'
        + '<th style="text-align:right;padding:6px 8px">Potential Payout</th>'
        + '<th style="text-align:right;padding:6px 8px">Time Held</th>'
        + '</tr></thead><tbody>';
      positions.forEach(function(p) {
        var payout = (p.potential_profit || 0) + (p.cost || 0);
        var held = '';
        if (p.entry_time) {
          try {
            var entryMs = new Date(p.entry_time).getTime();
            var nowMs = Date.now();
            var diffMin = Math.floor((nowMs - entryMs) / 60000);
            if (diffMin < 60) held = diffMin + 'm';
            else if (diffMin < 1440) held = Math.floor(diffMin/60) + 'h ' + (diffMin%60) + 'm';
            else held = Math.floor(diffMin/1440) + 'd ' + Math.floor((diffMin%1440)/60) + 'h';
          } catch(e) { held = ''; }
        }
        posHtml += '<tr style="border-top:1px solid #1a2a33">'
          + '<td style="padding:8px;color:#e0e0e0;font-weight:600">' + (p.ticker || '') + '<div style="font-size:10px;color:#666;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (p.title || '') + '</div></td>'
          + '<td style="text-align:right;padding:8px;color:#00d4ff;font-weight:700">' + (p.price || 0) + String.fromCharCode(162) + ' <span style="font-size:10px;color:#888">' + (p.side || '').toUpperCase() + '</span></td>'
          + '<td style="text-align:right;padding:8px;color:#ccc">' + (p.count || 0) + '</td>'
          + '<td style="text-align:right;padding:8px;color:#ccc">$' + (p.cost || 0).toFixed(2) + '</td>'
          + '<td style="text-align:right;padding:8px;color:#00dc5a;font-weight:700">$' + payout.toFixed(2) + '</td>'
          + '<td style="text-align:right;padding:8px;color:#888;font-size:11px">' + held + '</td>'
          + '</tr>';
      });
      posHtml += '</tbody></table>';
      posContainer.innerHTML = posHtml;
    }

    // Trade History
    var histContainer = document.getElementById('mshark-history');
    var histBadge = document.getElementById('mshark-history-badge');
    if (histBadge) histBadge.textContent = history.length;
    if (history.length === 0) {
      histContainer.innerHTML = '<div class="empty" style="color:#006688">No settled MoonShark trades yet</div>';
    } else {
      var hHtml = '<table style="width:100%;border-collapse:collapse;font-size:12px"><thead><tr style="color:#006688;font-size:10px;text-transform:uppercase;letter-spacing:0.5px">'
        + '<th style="text-align:left;padding:6px 8px">Date</th>'
        + '<th style="text-align:left;padding:6px 8px">Ticker</th>'
        + '<th style="text-align:right;padding:6px 8px">Entry</th>'
        + '<th style="text-align:right;padding:6px 8px">Contracts</th>'
        + '<th style="text-align:right;padding:6px 8px">Cost</th>'
        + '<th style="text-align:center;padding:6px 8px">Result</th>'
        + '<th style="text-align:right;padding:6px 8px">Payout</th>'
        + '<th style="text-align:right;padding:6px 8px">P&amp;L</th>'
        + '</tr></thead><tbody>';
      history.forEach(function(t) {
        var dateStr = '';
        try { dateStr = t.close_time ? new Date(t.close_time).toLocaleDateString() + ' ' + new Date(t.close_time).toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'}) : (t.entry_time ? new Date(t.entry_time).toLocaleDateString() : ''); } catch(e) { dateStr = ''; }
        var isWin = t.result === 'win';
        var resultBadge = isWin
          ? '<span style="background:#00dc5a22;color:#00dc5a;padding:2px 8px;border-radius:6px;font-size:10px;font-weight:700">WIN</span>'
          : '<span style="background:#ff500022;color:#ff5000;padding:2px 8px;border-radius:6px;font-size:10px;font-weight:700">LOSS</span>';
        var pnlVal = t.pnl || 0;
        var pnlCol = pnlVal >= 0 ? '#00dc5a' : '#ff5000';
        var pnlStr = (pnlVal >= 0 ? '+' : '') + '$' + Math.abs(pnlVal).toFixed(2);
        var titleShort = (t.title || t.ticker || '').substring(0, 40);
        if ((t.title || '').length > 40) titleShort += '...';
        hHtml += '<tr style="border-top:1px solid #1a2a33">'
          + '<td style="padding:8px;color:#888;font-size:11px;white-space:nowrap">' + dateStr + '</td>'
          + '<td style="padding:8px;color:#e0e0e0;font-weight:600;max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap" title="' + (t.title || '') + '">' + titleShort + '</td>'
          + '<td style="text-align:right;padding:8px;color:#00d4ff;font-weight:700">' + (t.entry_price || 0) + String.fromCharCode(162) + '</td>'
          + '<td style="text-align:right;padding:8px;color:#ccc">' + (t.count || 0) + '</td>'
          + '<td style="text-align:right;padding:8px;color:#ccc">$' + (t.cost || 0).toFixed(2) + '</td>'
          + '<td style="text-align:center;padding:8px">' + resultBadge + '</td>'
          + '<td style="text-align:right;padding:8px;color:#ccc">$' + (t.payout || 0).toFixed(2) + '</td>'
          + '<td style="text-align:right;padding:8px;color:' + pnlCol + ';font-weight:700">' + pnlStr + '</td>'
          + '</tr>';
      });
      hHtml += '</tbody></table>';
      histContainer.innerHTML = hHtml;
    }

    // Cumulative P&L
    var cumContainer = document.getElementById('mshark-cumulative');
    if (cumPnl.length === 0) {
      cumContainer.innerHTML = '<div class="empty" style="color:#006688">No settled trades for P&amp;L tracking</div>';
    } else {
      var cHtml = '<table style="width:100%;border-collapse:collapse;font-size:11px"><thead><tr style="color:#006688;font-size:9px;text-transform:uppercase;letter-spacing:0.5px">'
        + '<th style="text-align:left;padding:4px 8px">#</th>'
        + '<th style="text-align:left;padding:4px 8px">Ticker</th>'
        + '<th style="text-align:right;padding:4px 8px">Trade P&amp;L</th>'
        + '<th style="text-align:right;padding:4px 8px">Running Total</th>'
        + '</tr></thead><tbody>';
      cumPnl.forEach(function(c, i) {
        var tPnlCol = (c.pnl || 0) >= 0 ? '#00dc5a' : '#ff5000';
        var rCol = (c.running_total || 0) >= 0 ? '#00dc5a' : '#ff5000';
        cHtml += '<tr style="border-top:1px solid #1a2a33">'
          + '<td style="padding:4px 8px;color:#444">' + (i+1) + '</td>'
          + '<td style="padding:4px 8px;color:#aaa;max-width:150px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + (c.ticker || '') + '</td>'
          + '<td style="text-align:right;padding:4px 8px;color:' + tPnlCol + '">' + ((c.pnl||0) >= 0 ? '+' : '') + '$' + Math.abs(c.pnl||0).toFixed(2) + '</td>'
          + '<td style="text-align:right;padding:4px 8px;color:' + rCol + ';font-weight:700">' + ((c.running_total||0) >= 0 ? '+' : '') + '$' + Math.abs(c.running_total||0).toFixed(2) + '</td>'
          + '</tr>';
      });
      cHtml += '</tbody></table>';
      cumContainer.innerHTML = cHtml;
    }

    // Settings
    var setContainer = document.getElementById('mshark-settings');
    setContainer.innerHTML = ''
      + '<div style="display:flex;align-items:center;gap:20px;flex-wrap:wrap">'
      + '<div style="display:flex;gap:16px;flex-wrap:wrap">'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Bet Size</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">$' + (settings.bet_size || 2.5).toFixed(2) + '</div></div>'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Daily Cap</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">$' + (settings.max_daily || 20) + '</div></div>'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Price Range</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">' + (settings.min_price || 10) + '-' + (settings.max_price || 30) + String.fromCharCode(162) + '</div></div>'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Max Trades/Day</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">' + (settings.max_trades || 8) + '</div></div>'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Today Spent</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">$' + (today.daily_spent || 0).toFixed(2) + ' / $' + (today.daily_limit || 20) + '</div></div>'
      + '<div><span style="font-size:10px;color:#006688;text-transform:uppercase">Today Trades</span><div style="font-size:14px;font-weight:700;color:#e0e0e0">' + (today.trade_count || 0) + ' / ' + (settings.max_trades || 8) + '</div></div>'
      + '</div>'
      + '</div>';

  } catch(e) {
    _setHTML('mshark-stats-bar', '<div class="empty" style="color:#ff5000">Error loading MoonShark: ' + e.message + '</div>');
  }
}

async function toggleMoonshark() {
  try {
    var resp = await fetch(API + '/moonshark/toggle', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
    });
    var data = await resp.json();
    showToast('MoonShark ' + (data.enabled ? 'ENABLED' : 'DISABLED'), data.enabled ? 'success' : 'info');
    loadMoonshark();
  } catch(e) {
    showToast('Toggle error: ' + e.message, 'error');
  }
}

// --- Ticker bar: live prices via server proxy ---
async function loadTicker() {
  try {
    var data = await fetch(API + '/ticker-prices').then(r => r.json());
    ['btc','eth','voo','tsla','goog'].forEach(function(sym) {
      if (data[sym]) setTicker(sym, data[sym].price, data[sym].change);
    });
  } catch(e) { console.warn('Ticker error', e); }
}

function setTicker(sym, price, changePct) {
  var priceEl = document.getElementById('tk-' + sym);
  var chgEl = document.getElementById('tk-' + sym + '-chg');
  if (!priceEl) return;
  if (price >= 1000) priceEl.textContent = '$' + price.toLocaleString(undefined, {maximumFractionDigits: 0});
  else if (price >= 1) priceEl.textContent = '$' + price.toFixed(2);
  else priceEl.textContent = '$' + price.toFixed(4);
  if (chgEl && changePct !== undefined && changePct !== null) {
    var sign = changePct >= 0 ? '+' : '';
    chgEl.textContent = sign + changePct.toFixed(2) + '%';
    chgEl.className = 'ticker-chg ' + (changePct >= 0 ? 'up' : 'down');
  }
}

// Browser notifications
var _notifEnabled = false;
if ('Notification' in window) {
  if (Notification.permission === 'granted') {
    _notifEnabled = true;
  } else if (Notification.permission !== 'denied') {
    Notification.requestPermission().then(function(p) { _notifEnabled = p === 'granted'; });
  }
}
function sendNotif(title, body, tag) {
  if (!_notifEnabled) return;
  try { new Notification(title, {body: body, icon: '/favicon.ico', tag: tag || 'tradeshark', silent: false}); } catch(e) {}
}

// Track last activity count for new trade notifications
var _lastActivityCount = 0;
var _lastSettledCount = 0;

async function checkForNotifications() {
  try {
    // Check for new trades
    var data = await fetch(API + '/bot-activity').then(function(r){return r.json();});
    var items = data.activity || [];
    if (items.length > _lastActivityCount && _lastActivityCount > 0) {
      var newest = items[items.length - 1];
      // Check all new messages since last poll
      var newItems = items.slice(_lastActivityCount);
      newItems.forEach(function(item) {
        if (!item || !item.msg) return;
        var msg = item.msg;
        if (msg.indexOf('SNIPE') >= 0 || msg.indexOf('SNIPED') >= 0 || msg.indexOf('MOONSHARK HIT') >= 0) {
          sendNotif('🦈 TradeShark Trade', msg, 'trade-' + Date.now());
        }
        if (msg.indexOf('WIN!') >= 0) {
          sendNotif('🦈 MoonShark WIN!', msg, 'win-' + Date.now());
        }
        if (msg.indexOf('LOSS:') >= 0) {
          sendNotif('TradeShark Loss', msg, 'loss-' + Date.now());
        }
        if (msg.indexOf('Settlements:') >= 0) {
          sendNotif('💰 Settlement Summary', msg, 'settle-' + Date.now());
        }
      });
    }
    _lastActivityCount = items.length;
  } catch(e) {}
}

// --- Daily Insights Feed ---
async function loadInsights() {
  try {
    var data = await fetch(API + '/insights').then(r => r.json());
    var feed = document.getElementById('daily-insights-feed');
    if (data.error || !data.insights || data.insights.length === 0) {
      feed.innerHTML = '<div style="color:#555;font-size:11px;padding:8px">No insights available yet.</div>';
      return;
    }
    var html = '';
    if (data.generated_at) {
      html += '<div style="color:#555;font-size:10px;margin-bottom:8px;text-align:right">Updated: ' + data.generated_at + '</div>';
    }
    data.insights.forEach(function(ins) {
      var icon = ins.trend === 'positive' ? '📈' : ins.trend === 'negative' ? '📉' : '➡️';
      var borderColor = ins.trend === 'positive' ? '#00dc5a' : ins.trend === 'negative' ? '#ff5000' : '#333';
      html += '<div style="background:#141414;border:1px solid #1f1f1f;border-left:3px solid ' + borderColor + ';border-radius:10px;padding:12px 14px">';
      html += '<div style="display:flex;align-items:center;gap:8px;margin-bottom:4px">';
      html += '<span style="font-size:16px">' + icon + '</span>';
      html += '<span style="color:#eee;font-size:13px;font-weight:700">' + ins.title + '</span>';
      html += '</div>';
      html += '<div style="color:#aaa;font-size:11px;line-height:1.4;margin-bottom:4px">' + ins.detail + '</div>';
      html += '<div style="color:#666;font-size:10px;font-style:italic">' + ins.action + '</div>';
      html += '</div>';
    });
    feed.innerHTML = html;
  } catch(e) {
    console.error('Insights load error', e);
    _setHTML('daily-insights-feed', '<div style="color:#ff5000;font-size:12px">Error loading insights: ' + e.message + '</div>');
  }
}

// --- Trends Tab ---
// === GLOBAL NEWS FEED ===
async function loadNewsFeed(forceRefresh) {
  try {
    var url = forceRefresh ? API + '/news/refresh' : API + '/news';
    var data = await fetch(url).then(function(r) { return r.json(); });
    var stories = data.stories || [];
    var feedEl = document.getElementById('global-news-feed');
    var timeEl = document.getElementById('news-updated-time');

    if (timeEl && data.cached_at) {
      try {
        var d = new Date(data.cached_at * 1000);
        timeEl.textContent = 'Updated ' + d.toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'});
      } catch(e) { timeEl.textContent = ''; }
    }

    if (stories.length === 0) {
      feedEl.innerHTML = '<div style="color:#555;font-size:12px;padding:20px;text-align:center">No stories available right now. Try refreshing.</div>';
      return;
    }

    var html = '';
    stories.slice(0, 10).forEach(function(story, idx) {
      var borderColor = story.color || '#888';
      var sentIcon = story.sentiment === 'bullish' ? String.fromCodePoint(0x1F7E2) : story.sentiment === 'bearish' ? String.fromCodePoint(0x1F534) : String.fromCodePoint(0x26AA);
      var catLabel = (story.category || 'general').replace('-', ' ');
      var timeAgo = '';
      if (story.published) {
        try {
          var pubDate = new Date(story.published);
          var now = new Date();
          var diffH = Math.round((now - pubDate) / 3600000);
          if (diffH < 1) timeAgo = 'Just now';
          else if (diffH < 24) timeAgo = diffH + 'h ago';
          else timeAgo = Math.round(diffH / 24) + 'd ago';
        } catch(e) {}
      }

      html += '<div style="background:#141414;border:1px solid #1f1f1f;border-left:4px solid ' + borderColor + ';border-radius:10px;padding:16px">';

      // Header: number + title + meta
      html += '<div style="display:flex;align-items:flex-start;gap:10px;margin-bottom:10px">';
      html += '<div style="color:' + borderColor + ';font-size:14px;font-weight:800;min-width:24px;text-align:center;padding-top:1px">' + (idx + 1) + '</div>';
      html += '<div style="flex:1">';
      html += '<div style="color:#eee;font-size:14px;font-weight:700;line-height:1.3">' + story.title + '</div>';
      html += '<div style="display:flex;gap:8px;align-items:center;margin-top:4px">';
      html += '<span style="color:' + borderColor + ';font-size:9px;font-weight:700;text-transform:uppercase;letter-spacing:0.5px;background:' + borderColor + '22;padding:2px 6px;border-radius:4px">' + catLabel + '</span>';
      html += '<span style="color:#555;font-size:10px">' + (story.source || '') + '</span>';
      if (timeAgo) html += '<span style="color:#444;font-size:10px">' + sentIcon + ' ' + timeAgo + '</span>';
      html += '</div></div></div>';

      // 3 bullet points
      html += '<div style="margin-left:34px;display:flex;flex-direction:column;gap:8px">';

      // Bullet 1: What it means (plain English)
      html += '<div style="display:flex;gap:8px;align-items:flex-start">';
      html += '<div style="color:#ffb400;font-size:10px;font-weight:700;min-width:70px;text-transform:uppercase;padding-top:1px">What it is</div>';
      html += '<div style="color:#bbb;font-size:12px;line-height:1.4">' + (story.plain_english || story.summary || 'Breaking story — details emerging.') + '</div>';
      html += '</div>';

      // Bullet 2: Market impact
      html += '<div style="display:flex;gap:8px;align-items:flex-start">';
      html += '<div style="color:#5b8def;font-size:10px;font-weight:700;min-width:70px;text-transform:uppercase;padding-top:1px">Impact</div>';
      html += '<div style="color:#999;font-size:11px;line-height:1.4">' + (story.market_impact || story.economic_impact || '') + '</div>';
      html += '</div>';

      // Bullet 3: Trade idea
      html += '<div style="display:flex;gap:8px;align-items:flex-start">';
      html += '<div style="color:#00dc5a;font-size:10px;font-weight:700;min-width:70px;text-transform:uppercase;padding-top:1px">Trade Idea</div>';
      html += '<div style="color:#999;font-size:11px;line-height:1.4">' + (story.trade_idea || '') + '</div>';
      html += '</div>';

      html += '</div>';

      // Link
      if (story.link) {
        html += '<div style="margin-left:34px;margin-top:8px">';
        html += '<a href="' + story.link + '" target="_blank" style="color:#555;font-size:10px;text-decoration:none;border-bottom:1px dotted #333">Read full story &rarr;</a>';
        html += '</div>';
      }

      html += '</div>';
    });

    feedEl.innerHTML = html;
  } catch(e) {
    console.error('News feed error', e);
    var el = document.getElementById('global-news-feed');
    if (el) el.innerHTML = '<div style="color:#ff5000;font-size:12px">Error loading news: ' + e.message + '</div>';
  }
}

// Legacy — kept for backward compat
async function loadTrends() {
  try {
    var data = await fetch(API + '/trends').then(function(r){ return r.json(); });
    // Version
    var vEl = document.getElementById('trend-version');
    if (vEl) vEl.textContent = data.summary ? data.summary.learning_version : 0;
    // Date
    var dEl = document.getElementById('trends-date');
    if (dEl) dEl.textContent = 'Overall: ' + (data.summary ? data.summary.overall_win_rate : 0) + '% win rate (' + (data.summary ? data.summary.total_wins : 0) + 'W / ' + (data.summary ? data.summary.total_losses : 0) + 'L) across ' + (data.summary ? data.summary.total_settled : 0) + ' settled trades';

    // Trends list
    var tEl = document.getElementById('trends-list');
    if (data.trends && data.trends.length > 0) {
      var h = '';
      data.trends.forEach(function(t, i) {
        h += '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px;display:flex;gap:12px;align-items:flex-start">';
        h += '<div style="font-size:24px;min-width:32px;text-align:center">' + t.icon + '</div>';
        h += '<div style="flex:1">';
        h += '<div style="color:' + t.color + ';font-size:13px;font-weight:700">' + (i+1) + '. ' + t.title + '</div>';
        h += '<div style="color:#888;font-size:11px;margin-top:4px">' + t.detail + '</div>';
        h += '</div></div>';
      });
      tEl.innerHTML = h;
    } else {
      tEl.innerHTML = '<div style="color:#555;font-size:11px;padding:20px;text-align:center">No trends yet — need more settled trades</div>';
    }

    // Enhancements
    var eEl = document.getElementById('trends-enhancements');
    if (data.enhancements && data.enhancements.length > 0) {
      var eh = '';
      data.enhancements.forEach(function(e) {
        eh += '<div style="background:#0a1a0a;border:1px solid #1a3a1a;border-radius:8px;padding:10px 14px;display:flex;align-items:center;gap:8px">';
        eh += '<span style="font-size:16px">' + e.icon + '</span>';
        eh += '<span style="color:' + e.color + ';font-size:11px;font-weight:600">' + e.text + '</span>';
        eh += '</div>';
      });
      eEl.innerHTML = eh;
    }

    // Learning parameters summary
    var pEl = document.getElementById('trends-params');
    var params = data.parameters || {};
    var pKeys = Object.keys(params);
    if (pKeys.length > 0) {
      var ph = '<table style="font-size:10px;width:100%"><tr><th style="text-align:left">Dimension</th><th>Buckets</th><th>Best</th><th>Worst</th></tr>';
      pKeys.forEach(function(dim) {
        var buckets = params[dim];
        var bKeys = Object.keys(buckets);
        var best = null, worst = null;
        bKeys.forEach(function(k) {
          var b = buckets[k];
          if (!best || b.win_rate > best.wr) best = {name: k, wr: b.win_rate, n: b.sample_size};
          if (!worst || b.win_rate < worst.wr) worst = {name: k, wr: b.win_rate, n: b.sample_size};
        });
        ph += '<tr>';
        ph += '<td style="color:#ccc;font-weight:600">' + dim.replace(/_/g, ' ') + '</td>';
        ph += '<td style="color:#888;text-align:center">' + bKeys.length + '</td>';
        ph += '<td style="color:#00dc5a;text-align:center">' + (best ? best.name + ' (' + (best.wr*100).toFixed(0) + '%)' : '--') + '</td>';
        ph += '<td style="color:#ff5000;text-align:center">' + (worst ? worst.name + ' (' + (worst.wr*100).toFixed(0) + '%)' : '--') + '</td>';
        ph += '</tr>';
      });
      ph += '</table>';
      pEl.innerHTML = ph;
    } else {
      pEl.innerHTML = '<div style="color:#555;font-size:10px;text-align:center;padding:8px">Learning engine has not run yet</div>';
    }
  } catch(e) {
    _setHTML('trends-list', '<div style="color:#ff5000;font-size:11px">Error: ' + e.message + '</div>');
  }
}

// --- Analytics Tab ---
async function loadAnalytics() {
  try {
    // Use both the /analytics endpoint and settled data
    var data = await fetch(API + '/analytics').then(r => r.json());
    if (data.error) { console.error('Analytics error:', data.error); return; }

    var ins = data.insights || {};
    var bySport = data.by_sport || {};
    var byPrice = data.by_price || {};
    var byTime = data.by_time || {};
    var catStats = data.category_stats || {};

    // Also merge settled data if available for broader coverage
    if (window._settledData && window._settledData.length > 0 && ins.total_trades === 0) {
      // Fallback: compute from settled data client-side
      var sd = window._settledData;
      var tw = 0, tl = 0, wp = 0, lp = 0;
      var sportMap = {};
      var priceMap = {'<70':{w:0,l:0,p:0,t:0},'70-74':{w:0,l:0,p:0,t:0},'75-79':{w:0,l:0,p:0,t:0},'80-84':{w:0,l:0,p:0,t:0},'85-89':{w:0,l:0,p:0,t:0},'90-100':{w:0,l:0,p:0,t:0}};
      sd.forEach(function(s) {
        var cat = s.category || 'other';
        if (!sportMap[cat]) sportMap[cat] = {wins:0,losses:0,pnl:0,total:0,win_rate:0};
        sportMap[cat].total++;
        if (s.won === true) { sportMap[cat].wins++; tw++; wp += s.pnl_usd; }
        else if (s.won === false) { sportMap[cat].losses++; tl++; lp += s.pnl_usd; }
        sportMap[cat].pnl += s.pnl_usd;
        // Price bucket
        var pc = s.entry_cents || 0;
        var bk = '<70';
        if (pc >= 90) bk = '90-100';
        else if (pc >= 85) bk = '85-89';
        else if (pc >= 80) bk = '80-84';
        else if (pc >= 75) bk = '75-79';
        else if (pc >= 70) bk = '70-74';
        priceMap[bk].t++;
        if (s.won === true) priceMap[bk].w++;
        else if (s.won === false) priceMap[bk].l++;
        priceMap[bk].p += s.pnl_usd;
      });
      Object.keys(sportMap).forEach(function(k) {
        var c = sportMap[k];
        c.win_rate = Math.round(c.wins / Math.max(1, c.wins + c.losses) * 100 * 10) / 10;
        c.pnl = Math.round(c.pnl * 100) / 100;
      });
      bySport = sportMap;
      Object.keys(priceMap).forEach(function(k) {
        var b = priceMap[k];
        byPrice[k] = {wins:b.w,losses:b.l,pnl:Math.round(b.p*100)/100,total:b.t,win_rate:Math.round(b.w/Math.max(1,b.w+b.l)*100*10)/10,avg_pnl:Math.round(b.p/Math.max(1,b.t)*100)/100};
      });
      ins.total_trades = sd.length;
      ins.total_wins = tw;
      ins.total_losses = tl;
      ins.overall_win_rate = Math.round(tw / Math.max(1, tw + tl) * 100 * 10) / 10;
      ins.avg_win_profit = tw > 0 ? Math.round(wp / tw * 100) / 100 : 0;
      ins.avg_loss_amount = tl > 0 ? Math.round(lp / tl * 100) / 100 : 0;
      var bestCat = Object.keys(sportMap).sort(function(a,b){ return sportMap[b].pnl - sportMap[a].pnl; })[0] || 'N/A';
      ins.best_sport = bestCat;
      var validPrices = Object.keys(byPrice).filter(function(k){ return k !== '<70' && byPrice[k].total > 0; });
      ins.best_price_range = validPrices.sort(function(a,b){ return byPrice[b].win_rate - byPrice[a].win_rate; })[0] || 'N/A';
    }

    // --- Render Key Insights ---
    var insEl = document.getElementById('analytics-insights');
    function insightBox(label, value, color) {
      return '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:10px 12px;text-align:center">' +
        '<div style="color:#666;font-size:9px;font-weight:500;text-transform:uppercase;letter-spacing:0.5px;margin-bottom:4px">' + label + '</div>' +
        '<div style="color:' + color + ';font-size:18px;font-weight:700">' + value + '</div></div>';
    }
    var wrColor = ins.overall_win_rate >= 55 ? '#00dc5a' : ins.overall_win_rate >= 45 ? '#ffb400' : '#ff5000';
    var ihtml = '';
    ihtml += insightBox('Overall Win Rate', ins.overall_win_rate + '%', wrColor);
    ihtml += insightBox('Total Trades', ins.total_trades || 0, '#00d4ff');
    ihtml += insightBox('Best Sport', (ins.best_sport || 'N/A').charAt(0).toUpperCase() + (ins.best_sport || 'N/A').slice(1), '#ffb400');
    ihtml += insightBox('Best Price Range', (ins.best_price_range || 'N/A') + String.fromCharCode(162), '#ffb400');
    ihtml += insightBox('Avg Win', '+$' + (ins.avg_win_profit || 0).toFixed(2), '#00dc5a');
    ihtml += insightBox('Avg Loss', '-$' + Math.abs(ins.avg_loss_amount || 0).toFixed(2), '#ff5000');
    insEl.innerHTML = ihtml;

    // --- Render Win Rate by Sport ---
    var sportEl = document.getElementById('analytics-sport');
    var sportKeys = Object.keys(bySport).filter(function(k){ return bySport[k].total > 0; }).sort(function(a,b){ return bySport[b].pnl - bySport[a].pnl; });
    if (sportKeys.length === 0) {
      sportEl.innerHTML = '<div style="color:#555;font-size:11px;padding:8px">No sport data yet. Place some trades and check back.</div>';
    } else {
      var shtml = '<table style="width:100%;border-collapse:collapse;font-size:11px">';
      shtml += '<tr style="color:#888;border-bottom:1px solid #222"><th style="padding:6px 8px;text-align:left">Sport</th><th style="padding:6px 8px;text-align:center">Trades</th><th style="padding:6px 8px;text-align:center">W/L</th><th style="padding:6px 8px;text-align:center">Win Rate</th><th style="padding:6px 8px;text-align:right">P&amp;L</th></tr>';
      sportKeys.forEach(function(k) {
        var s = bySport[k];
        var wrc = s.win_rate >= 55 ? '#00dc5a' : s.win_rate >= 45 ? '#ffb400' : '#ff5000';
        var pnlc = s.pnl >= 0 ? '#00dc5a' : '#ff5000';
        var rowBg = s.pnl >= 0 ? 'rgba(0,220,90,0.04)' : 'rgba(255,80,0,0.04)';
        shtml += '<tr style="border-bottom:1px solid #1a1a1a;background:' + rowBg + '">';
        shtml += '<td style="padding:8px;color:#ddd;font-weight:600;text-transform:capitalize">' + k + '</td>';
        shtml += '<td style="padding:8px;text-align:center;color:#ccc">' + s.total + '</td>';
        shtml += '<td style="padding:8px;text-align:center;color:#ccc">' + s.wins + '/' + s.losses + '</td>';
        shtml += '<td style="padding:8px;text-align:center;color:' + wrc + ';font-weight:700">' + s.win_rate.toFixed(1) + '%</td>';
        shtml += '<td style="padding:8px;text-align:right;color:' + pnlc + ';font-weight:700">' + (s.pnl >= 0 ? '+' : '') + '$' + Math.abs(s.pnl).toFixed(2) + '</td>';
        shtml += '</tr>';
      });
      shtml += '</table>';
      sportEl.innerHTML = shtml;
    }

    // --- Render Win Rate by Price Range ---
    var priceEl = document.getElementById('analytics-price');
    var priceOrder = ['<70','70-74','75-79','80-84','85-89','90-100'];
    var phtml = '<table style="width:100%;border-collapse:collapse;font-size:11px">';
    phtml += '<tr style="color:#888;border-bottom:1px solid #222"><th style="padding:6px 8px;text-align:left">Price Range</th><th style="padding:6px 8px;text-align:center">Trades</th><th style="padding:6px 8px;text-align:center">W/L</th><th style="padding:6px 8px;text-align:center">Win Rate</th><th style="padding:6px 8px;text-align:right">Avg P&amp;L</th></tr>';
    priceOrder.forEach(function(k) {
      var b = byPrice[k];
      if (!b || b.total === 0) return;
      var wrc = b.win_rate >= 55 ? '#00dc5a' : b.win_rate >= 45 ? '#ffb400' : '#ff5000';
      var avgPnl = b.avg_pnl || (b.pnl / Math.max(1, b.total));
      var pnlc = avgPnl >= 0 ? '#00dc5a' : '#ff5000';
      var rowBg = avgPnl >= 0 ? 'rgba(0,220,90,0.04)' : 'rgba(255,80,0,0.04)';
      phtml += '<tr style="border-bottom:1px solid #1a1a1a;background:' + rowBg + '">';
      phtml += '<td style="padding:8px;color:#ddd;font-weight:600">' + k + String.fromCharCode(162) + '</td>';
      phtml += '<td style="padding:8px;text-align:center;color:#ccc">' + b.total + '</td>';
      phtml += '<td style="padding:8px;text-align:center;color:#ccc">' + b.wins + '/' + b.losses + '</td>';
      phtml += '<td style="padding:8px;text-align:center;color:' + wrc + ';font-weight:700">' + b.win_rate.toFixed(1) + '%</td>';
      phtml += '<td style="padding:8px;text-align:right;color:' + pnlc + ';font-weight:700">' + (avgPnl >= 0 ? '+' : '') + '$' + Math.abs(avgPnl).toFixed(2) + '</td>';
      phtml += '</tr>';
    });
    phtml += '</table>';
    priceEl.innerHTML = phtml;

    // --- Render Time of Day Performance ---
    var timeEl = document.getElementById('analytics-time');
    var timeOrder = ['Morning (6am-12pm)','Afternoon (12pm-6pm)','Evening (6pm-12am)','Night (12am-6am)'];
    var thtml = '<table style="width:100%;border-collapse:collapse;font-size:11px">';
    thtml += '<tr style="color:#888;border-bottom:1px solid #222"><th style="padding:6px 8px;text-align:left">Time Period</th><th style="padding:6px 8px;text-align:center">Trades</th><th style="padding:6px 8px;text-align:center">W/L</th><th style="padding:6px 8px;text-align:center">Win Rate</th><th style="padding:6px 8px;text-align:right">P&amp;L</th></tr>';
    timeOrder.forEach(function(k) {
      var p = byTime[k];
      if (!p || p.total === 0) return;
      var wrc = p.win_rate >= 55 ? '#00dc5a' : p.win_rate >= 45 ? '#ffb400' : '#ff5000';
      var pnlc = p.pnl >= 0 ? '#00dc5a' : '#ff5000';
      var rowBg = p.pnl >= 0 ? 'rgba(0,220,90,0.04)' : 'rgba(255,80,0,0.04)';
      thtml += '<tr style="border-bottom:1px solid #1a1a1a;background:' + rowBg + '">';
      thtml += '<td style="padding:8px;color:#ddd;font-weight:600">' + k + '</td>';
      thtml += '<td style="padding:8px;text-align:center;color:#ccc">' + p.total + '</td>';
      thtml += '<td style="padding:8px;text-align:center;color:#ccc">' + p.wins + '/' + p.losses + '</td>';
      thtml += '<td style="padding:8px;text-align:center;color:' + wrc + ';font-weight:700">' + p.win_rate.toFixed(1) + '%</td>';
      thtml += '<td style="padding:8px;text-align:right;color:' + pnlc + ';font-weight:700">' + (p.pnl >= 0 ? '+' : '') + '$' + Math.abs(p.pnl).toFixed(2) + '</td>';
      thtml += '</tr>';
    });
    thtml += '</table>';
    timeEl.innerHTML = thtml;

  } catch(e) {
    console.error('Analytics load error', e);
    _setHTML('analytics-insights', '<div style="color:#ff5000;font-size:12px">Error loading analytics: ' + e.message + '</div>');
  }
}

// Load everything on page load
loadTicker();
loadSeventyFivers();
loadQuantPicks();
setInterval(loadSeventyFivers, 60000);
setInterval(loadQuantPicks, 60000);
loadStatus();
loadActivity();
loadBetsFeed();
loadAllBets();
loadPortfolio();
loadTopPicks();
loadTodayPicks();
loadPositions();
loadSettled();
loadMispriced();
loadTrades();
loadMoonshark();
// Auto-refresh: ticker every 60s, activity every 10s, portfolio every 30s
setInterval(() => { loadTicker(); }, 60000);
setInterval(() => { loadActivity(); loadBetsFeed(); checkForNotifications(); }, 10000);
setInterval(() => { loadStatus(); loadPortfolio(); loadTopPicks(); loadTodayPicks(); loadPositions(); loadSettled(); loadTrades(); checkNotifications(); if (document.getElementById('tab-performance') && document.getElementById('tab-performance').classList.contains('active')) loadPerformance(); }, 15000);

// --- Notification Bell ---
var _notifItems = [];
var _notifUnread = 0;
var _lastNotifCheck = 0;
var _notifPanelOpen = false;
var _NOTIF_TRIGGERS = ['HIT', 'WIN', 'LOSS', 'BLOWOUT EXIT', 'MOMENTUM', 'LEAD CHANGE', 'PRICE MOVE', 'ARB', 'CLOSEGAME'];

function toggleNotifPanel() {
  _notifPanelOpen = !_notifPanelOpen;
  var _np = _el('notif-panel'); if (_np) _np.style.display = _notifPanelOpen ? 'block' : 'none';
  if (_notifPanelOpen) renderNotifs();
}

// Close panel when clicking outside
document.addEventListener('click', function(e) {
  var wrapper = document.getElementById('notif-bell-wrapper');
  var panel = document.getElementById('notif-panel');
  if (_notifPanelOpen && wrapper && !wrapper.contains(e.target) && panel && !panel.contains(e.target)) {
    _notifPanelOpen = false;
    panel.style.display = 'none';
  }
});

function clearNotifs() {
  _notifUnread = 0;
  _notifItems.forEach(function(n) { n.read = true; });
  var badge = _el('notif-badge');
  if (badge) badge.style.display = 'none';
  var _bellIcon = _el('notif-bell-icon'); if (_bellIcon) _bellIcon.style.stroke = '#888';
  renderNotifs();
}

function renderNotifs() {
  var el = document.getElementById('notif-list');
  if (_notifItems.length === 0) {
    el.innerHTML = '<div style="padding:20px;text-align:center;color:#555;font-size:11px">No notifications yet</div>';
    return;
  }
  var html = '';
  _notifItems.slice().reverse().forEach(function(n) {
    var bg = n.read ? 'transparent' : '#1e2a1e';
    var timeStr = '--:--';
    try { timeStr = fmtTime(n.time); } catch(e) {}
    // Pick icon based on content
    var icon = '📋';
    if (n.msg.indexOf('HIT') >= 0) icon = '🎯';
    if (n.msg.indexOf('WIN') >= 0) icon = '🎉';
    if (n.msg.indexOf('LOSS') >= 0) icon = '❌';
    if (n.msg.indexOf('BLOWOUT') >= 0) icon = '💀';
    if (n.msg.indexOf('MOMENTUM') >= 0) icon = '🔥';
    if (n.msg.indexOf('LEAD') >= 0) icon = '🚀';
    if (n.msg.indexOf('ARB') >= 0) icon = '💰';
    if (n.msg.indexOf('PRICE') >= 0) icon = '📈';
    html += '<div style="padding:10px 16px;border-bottom:1px solid #222;background:' + bg + ';transition:background 0.2s">';
    html += '<div style="display:flex;gap:8px;align-items:flex-start">';
    html += '<span style="font-size:16px;flex-shrink:0">' + icon + '</span>';
    html += '<div style="flex:1;min-width:0">';
    html += '<div style="font-size:11px;color:#ddd;line-height:1.4;word-wrap:break-word">' + n.msg + '</div>';
    html += '<div style="font-size:9px;color:#555;margin-top:3px">' + timeStr + '</div>';
    html += '</div></div></div>';
  });
  el.innerHTML = html;
}

function checkNotifications() {
  fetch(API + '/bot-activity').then(function(r) { return r.json(); }).then(function(data) {
    var items = data.activity || [];
    // Find new important events
    items.forEach(function(a) {
      var isImportant = _NOTIF_TRIGGERS.some(function(t) { return a.msg && a.msg.toUpperCase().indexOf(t) >= 0; });
      if (!isImportant) return;
      // Dedupe by message
      var exists = _notifItems.some(function(n) { return n.msg === a.msg && n.time === a.time; });
      if (exists) return;
      _notifItems.push({ msg: a.msg, time: a.time, read: false });
      _notifUnread++;
    });
    // Keep last 50
    if (_notifItems.length > 50) _notifItems = _notifItems.slice(-50);
    // Update badge
    var badge = document.getElementById('notif-badge');
    var bell = document.getElementById('notif-bell-icon');
    if (_notifUnread > 0) {
      badge.textContent = _notifUnread > 99 ? '99+' : _notifUnread;
      badge.style.display = 'block';
      bell.style.stroke = '#ffb400';
    }
    if (_notifPanelOpen) renderNotifs();
  }).catch(function() {});
}

// Initial check
setTimeout(checkNotifications, 3000);
setInterval(checkNotifications, 15000);

// --- Closing Soon Panel ---
async function loadClosingSoon() {
  try {
    var data = await fetch(API + '/trades-today').then(function(r) { return r.json(); });
    var trades = data.trades || [];
    var el = document.getElementById('closing-soon-lines');
    var countEl = document.getElementById('closing-soon-count');

    // Filter to trades with close_time, sort by soonest
    var withClose = trades.filter(function(t) { return t.close_time; });
    withClose.sort(function(a, b) { return (a.close_time || '').localeCompare(b.close_time || ''); });

    // Also get open positions with close times — only show next 30 days
    var posData = await fetch(API + '/portfolio-summary').then(function(r) { return r.json(); });
    var _now = new Date();
    var _30d = new Date(_now.getTime() + 30 * 24 * 60 * 60 * 1000);
    var positions = (posData.open_positions || []).filter(function(p) {
      if (!p.close_time) return false;
      var ct = new Date(p.close_time);
      return ct <= _30d;  // only positions closing within 30 days
    });
    positions.sort(function(a, b) { return (a.close_time || '').localeCompare(b.close_time || ''); });

    var items = positions;
    countEl.textContent = items.length;

    if (items.length === 0) {
      el.innerHTML = '<div style="padding:16px;text-align:center;color:#555;font-size:11px">No positions closing today</div>';
      return;
    }

    var html = '';
    var now = new Date();
    items.forEach(function(p) {
      var title = (p.title || p.ticker || '').substring(0, 35);
      var closeTime = new Date(p.close_time);
      var diffMs = closeTime - now;
      var diffMin = Math.floor(diffMs / 60000);
      var timeLeft = '';
      var urgency = '#888';

      if (diffMin < 0) {
        timeLeft = 'Settling now';
        urgency = '#ffb400';
      } else if (diffMin < 60) {
        timeLeft = diffMin + 'm';
        urgency = '#ff3333';
      } else if (diffMin < 1440) {
        var h = Math.floor(diffMin / 60);
        var m = diffMin % 60;
        timeLeft = h + 'h ' + m + 'm';
        urgency = diffMin < 180 ? '#ff5000' : '#ffb400';
      } else {
        var d = Math.floor(diffMin / 1440);
        timeLeft = d + 'd';
        urgency = '#555';
      }

      var price = p.current_price || p.entry_price || 0;
      var side = (p.side || 'yes').toUpperCase();
      var pnl = p.unrealized_pnl_cents || 0;
      var pnlUsd = (pnl / 100).toFixed(2);
      var pnlColor = pnl >= 0 ? '#00dc5a' : '#ff3333';
      var pnlSign = pnl >= 0 ? '+' : '';

      html += '<div style="padding:6px 10px;border-bottom:1px solid #1a1a1a;display:flex;align-items:center;gap:8px">';
      html += '<div style="flex-shrink:0;min-width:55px;text-align:right">';
      html += '<span style="font-size:12px;font-weight:700;color:' + urgency + '">' + timeLeft + '</span>';
      html += '</div>';
      html += '<div style="flex:1;min-width:0">';
      html += '<div style="font-size:10px;color:#ddd;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">' + title + '</div>';
      html += '<div style="font-size:9px;color:#888">' + side + ' ' + price + 'c x' + (p.count || 0) + '</div>';
      html += '</div>';
      html += '<div style="flex-shrink:0;text-align:right">';
      html += '<span style="font-size:11px;font-weight:600;color:' + pnlColor + '">' + pnlSign + '$' + pnlUsd + '</span>';
      html += '</div>';
      html += '</div>';
    });
    el.innerHTML = html;
  } catch(e) {
    console.log('closingSoon error', e);
  }
}
setTimeout(loadClosingSoon, 4000);
setInterval(loadClosingSoon, 30000);

// --- News Feed ---
var _newsLoaded = false;
async function loadNews(forceRefresh) {
  var feed = document.getElementById('news-feed');
  var updEl = document.getElementById('news-updated');
  if (!forceRefresh && _newsLoaded) return;
  feed.innerHTML = '<div class="loading">Loading news...</div>';
  try {
    var url = API + (forceRefresh ? '/news/refresh' : '/news');
    var resp = await fetch(url);
    var data = await resp.json();
    if (data.error && (!data.stories || data.stories.length === 0)) {
      feed.innerHTML = '<div style="color:#888;font-size:12px;padding:20px;text-align:center">' + data.error + '</div>';
      return;
    }
    if (!data.stories || data.stories.length === 0) {
      feed.innerHTML = '<div style="color:#888;font-size:12px;padding:20px;text-align:center">No news stories available right now.</div>';
      return;
    }
    var html = '';
    data.stories.forEach(function(s) {
      var timeAgo = '';
      if (s.published) {
        try {
          var pub = new Date(s.published);
          var diff = Date.now() - pub.getTime();
          var mins = Math.floor(diff / 60000);
          var hrs = Math.floor(mins / 60);
          if (hrs >= 24) timeAgo = Math.floor(hrs / 24) + 'd ago';
          else if (hrs > 0) timeAgo = hrs + 'h ago';
          else if (mins > 0) timeAgo = mins + 'm ago';
          else timeAgo = 'just now';
        } catch(e) { timeAgo = ''; }
      }
      var srcColors = {
        'CNBC': '#ffb400',
        'Yahoo Finance': '#7b2ff7',
        'MarketWatch': '#00dc5a',
        'Google News': '#4285f4',
      };
      var srcColor = srcColors[s.source] || '#888';
      html += '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:12px">';
      html += '<a href="' + s.link + '" target="_blank" rel="noopener" style="color:#e0e0e0;text-decoration:none;font-size:13px;font-weight:600;line-height:1.4;display:block">' + s.title + '</a>';
      html += '<div style="display:flex;align-items:center;gap:8px;margin-top:6px">';
      html += '<span style="background:' + srcColor + '22;color:' + srcColor + ';font-size:10px;font-weight:700;padding:2px 6px;border-radius:4px">' + s.source + '</span>';
      if (timeAgo) html += '<span style="color:#666;font-size:10px">' + timeAgo + '</span>';
      html += '</div>';
      if (s.summary) {
        html += '<div style="color:#888;font-size:11px;margin-top:6px;line-height:1.4">' + s.summary + '</div>';
      }
      if (s.economic_impact) {
        html += '<div style="color:#ffb400;font-size:10px;margin-top:8px;line-height:1.4;padding:6px 8px;background:#1a1a0a;border-left:2px solid #ffb400;border-radius:0 4px 4px 0">';
        html += '<span style="font-weight:700">&#x1F4CA; Economic Impact:</span> ' + s.economic_impact + '</div>';
      }
      if (s.stock_picks && s.stock_picks.length > 0) {
        html += '<div style="display:flex;gap:6px;margin-top:6px;flex-wrap:wrap">';
        s.stock_picks.forEach(function(sp) {
          html += '<span style="font-size:9px;padding:3px 7px;background:#0a1a0a;border:1px solid #1a3a1a;border-radius:4px;color:#00dc5a" title="' + sp[1] + '">&#x1F4C8; <strong>' + sp[0] + '</strong> — ' + sp[1].split(' — ')[1] + '</span>';
        });
        html += '</div>';
      }
      html += '</div>';
    });
    feed.innerHTML = html;
    _newsLoaded = true;
    // Update timestamp
    if (data.cached_at) {
      var ago = Math.floor((Date.now() / 1000 - data.cached_at) / 60);
      updEl.textContent = ago <= 0 ? 'Updated just now' : 'Updated ' + ago + 'm ago';
    }
  } catch(e) {
    feed.innerHTML = '<div style="color:#ff5000;font-size:12px;padding:20px;text-align:center">Failed to load news. Try again later.</div>';
  }
}

var _newsIdeasLoaded = false;
async function loadNewsIdeas(forceRefresh) {
  var feed = document.getElementById('newsideas-feed');
  var updEl = document.getElementById('newsideas-updated');
  if (!forceRefresh && _newsIdeasLoaded) return;
  feed.innerHTML = '<div class="loading">Analyzing headlines...</div>';
  try {
    var url = API + (forceRefresh ? '/news-ideas/refresh' : '/news-ideas');
    var resp = await fetch(url);
    var data = await resp.json();
    if (data.error && (!data.ideas || data.ideas.length === 0)) {
      feed.innerHTML = '<div style="color:#888;font-size:12px;padding:20px;text-align:center">' + data.error + '</div>';
      return;
    }
    if (!data.ideas || data.ideas.length === 0) {
      feed.innerHTML = '<div style="color:#888;font-size:12px;padding:20px;text-align:center">No news ideas available right now.</div>';
      return;
    }
    var sentimentEmoji = { bullish: '🟢', bearish: '🔴', neutral: '⚪' };
    var sentimentLabel = { bullish: 'Bullish', bearish: 'Bearish', neutral: 'Neutral' };
    var html = '';
    data.ideas.forEach(function(idea) {
      var timeAgo = '';
      if (idea.published) {
        try {
          var pub = new Date(idea.published);
          var diff = Date.now() - pub.getTime();
          var mins = Math.floor(diff / 60000);
          var hrs = Math.floor(mins / 60);
          if (hrs >= 24) timeAgo = Math.floor(hrs / 24) + 'd ago';
          else if (hrs > 0) timeAgo = hrs + 'h ago';
          else if (mins > 0) timeAgo = mins + 'm ago';
          else timeAgo = 'just now';
        } catch(e) { timeAgo = ''; }
      }
      var catColor = idea.color || '#888';
      var catLabel = idea.category.replace('-', ' ').replace(/\\b\\w/g, function(l) { return l.toUpperCase(); });
      var sEmoji = sentimentEmoji[idea.sentiment] || '⚪';
      var sLabel = sentimentLabel[idea.sentiment] || 'Neutral';
      var sentBg = idea.sentiment === 'bullish' ? 'rgba(0,220,90,0.08)' : idea.sentiment === 'bearish' ? 'rgba(255,80,0,0.08)' : 'rgba(255,255,255,0.04)';
      var sentColor = idea.sentiment === 'bullish' ? '#00dc5a' : idea.sentiment === 'bearish' ? '#ff5000' : '#888';

      html += '<div style="background:#141414;border:1px solid #1f1f1f;border-radius:10px;padding:14px;border-left:3px solid ' + catColor + '">';
      // Top row: category badge + sentiment badge
      html += '<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">';
      html += '<span style="background:' + catColor + '18;color:' + catColor + ';font-size:10px;font-weight:700;padding:2px 8px;border-radius:4px;text-transform:uppercase;letter-spacing:0.5px">' + catLabel + '</span>';
      html += '<span style="background:' + sentBg + ';color:' + sentColor + ';font-size:10px;font-weight:600;padding:2px 8px;border-radius:4px">' + sEmoji + ' ' + sLabel + '</span>';
      html += '</div>';
      // Headline
      html += '<a href="' + idea.link + '" target="_blank" rel="noopener" style="color:#e0e0e0;text-decoration:none;font-size:13px;font-weight:600;line-height:1.4;display:block;margin-bottom:6px">' + idea.headline + '</a>';
      // Source + time
      html += '<div style="display:flex;align-items:center;gap:8px;margin-bottom:10px">';
      html += '<span style="color:#666;font-size:10px;font-weight:500">' + idea.source + '</span>';
      if (timeAgo) html += '<span style="color:#555;font-size:10px">&middot; ' + timeAgo + '</span>';
      html += '</div>';
      // Market take
      html += '<div style="color:#bbb;font-size:12px;line-height:1.5;margin-bottom:8px;padding:8px 10px;background:rgba(255,255,255,0.03);border-radius:6px">' + idea.market_take + '</div>';
      // Profit angle
      html += '<div style="color:#00dc5a;font-size:12px;font-weight:600;line-height:1.4;padding:6px 10px;background:rgba(0,220,90,0.06);border-radius:6px;border:1px solid rgba(0,220,90,0.12)">&#x1F4B0; ' + idea.profit_angle + '</div>';
      html += '</div>';
    });
    feed.innerHTML = html;
    _newsIdeasLoaded = true;
    if (data.cached_at) {
      var ago = Math.floor((Date.now() / 1000 - data.cached_at) / 60);
      updEl.textContent = ago <= 0 ? 'Updated just now' : 'Updated ' + ago + 'm ago';
    }
  } catch(e) {
    feed.innerHTML = '<div style="color:#ff5000;font-size:12px;padding:20px;text-align:center">Failed to load news ideas. Try again later.</div>';
  }
}
</script>
</body>
</html>
"""


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
