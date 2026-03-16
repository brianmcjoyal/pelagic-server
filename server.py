"""
Pelagic — Cross-Platform Prediction Market Trading Bot
"""

import os
import re
import uuid
import atexit
import base64
import datetime
import requests
import xml.etree.ElementTree as ET
from html import unescape as html_unescape
from urllib.parse import quote_plus
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError
from flask import Flask, jsonify, request
from flask_cors import CORS
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.backends import default_backend
from apscheduler.schedulers.background import BackgroundScheduler

app = Flask(__name__)
CORS(app)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
KALSHI_API_KEY_ID = os.environ.get("KALSHI_API_KEY_ID", "b5321140-8a40-47f5-a99e-edff618c887c")
KALSHI_BASE_URL   = "https://api.elections.kalshi.com"
KALSHI_API_PREFIX  = "/trade-api/v2"
PRIVATE_KEY_PEM = os.environ.get("KALSHI_PRIVATE_KEY", "")

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
# Bot configuration and state
# ---------------------------------------------------------------------------
BOT_CONFIG = {
    "enabled": False,
    "max_bet_usd": 10.0,
    "max_daily_usd": 50.0,
    "min_deviation": 0.15,
    "min_platforms": 2,
    "scan_interval_seconds": 15,
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
}

import json as _json

_STATE_FILE = "/tmp/tradeshark_state.json"

def _save_state():
    """Persist trade data to disk."""
    try:
        data = {
            "all_trades": BOT_STATE["all_trades"],
            "trades_today": BOT_STATE["trades_today"],
            "daily_spent_usd": BOT_STATE["daily_spent_usd"],
            "trade_date": BOT_STATE["trade_date"],
            "pick_history": BOT_STATE.get("pick_history", [])[-500:],  # keep last 500
        }
        with open(_STATE_FILE, "w") as f:
            _json.dump(data, f)
    except Exception as e:
        print(f"[STATE] Save error: {e}")

def _load_state():
    """Restore trade data from disk."""
    try:
        with open(_STATE_FILE, "r") as f:
            data = _json.load(f)
        BOT_STATE["all_trades"] = data.get("all_trades", [])
        BOT_STATE["trades_today"] = data.get("trades_today", [])
        BOT_STATE["daily_spent_usd"] = data.get("daily_spent_usd", 0.0)
        BOT_STATE["trade_date"] = data.get("trade_date", None)
        BOT_STATE["pick_history"] = data.get("pick_history", [])
        print(f"[STATE] Restored {len(BOT_STATE['all_trades'])} trades from disk")
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"[STATE] Load error: {e}")

_load_state()

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


def similarity(a, b, raw_a="", raw_b=""):
    cats_a = extract_categories(raw_a or a)
    cats_b = extract_categories(raw_b or b)
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
    seq = SequenceMatcher(None, a, b).ratio()
    kw = keyword_overlap(a, b)
    if kw < 0.3:
        return 0
    if seq < 0.25:
        return 0
    return (seq * 0.4 + kw * 0.6) * penalty

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


def find_opportunities(all_markets, min_similarity=0.55, max_cost=0.98):
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

    kalshi = []
    others = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        # Skip parlays
        if m["platform"] == "kalshi" and _is_parlay_title(m.get("question", "")):
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
            if sim >= 0.40:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                matches.append({"platform": om["platform"], "yes": om["yes"], "similarity": round(sim, 3)})

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
        })

    mispricings.sort(key=lambda x: x["deviation"], reverse=True)
    return mispricings

# ---------------------------------------------------------------------------
# Kalshi order placement (NEW)
# ---------------------------------------------------------------------------

def place_kalshi_order(ticker, side, price_cents, count=1):
    path = "/portfolio/orders"
    headers = signed_headers("POST", path)
    if not headers:
        return {"error": "No API key"}

    # Convert cents to dollar string (Kalshi API v2 migrated to _dollars fields March 12 2026)
    price_dollars = f"{price_cents / 100:.4f}"
    payload = {
        "ticker": ticker,
        "action": "buy",
        "side": side,
        "type": "limit",
        "count": count,
        "client_order_id": str(uuid.uuid4()),
        "time_in_force": "immediate_or_cancel",
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

# ---------------------------------------------------------------------------
# Bot scanner (runs every 10 minutes)
# ---------------------------------------------------------------------------

def run_bot_scan():
    now = datetime.datetime.utcnow()
    today = now.strftime("%Y-%m-%d")

    # Daily reset
    if BOT_STATE["trade_date"] != today:
        BOT_STATE["trade_date"] = today
        BOT_STATE["trades_today"] = []
        BOT_STATE["daily_spent_usd"] = 0.0

    BOT_STATE["last_scan"] = now.isoformat()

    try:
        all_markets = fetch_all_markets()
        BOT_STATE["last_scan_markets"] = len(all_markets)

        mispricings = find_consensus_mispricings(all_markets)
        BOT_STATE["last_scan_mispriced"] = len(mispricings)

        if not BOT_CONFIG["enabled"]:
            return

        for opp in mispricings:
            if BOT_STATE["daily_spent_usd"] >= BOT_CONFIG["max_daily_usd"]:
                break

            pc = opp["price_cents"]
            count = max(1, 500 // pc) if pc > 0 else 1  # target $5 per trade
            cost_usd = (pc * count) / 100.0
            if cost_usd > BOT_CONFIG["max_bet_usd"]:
                count = max(1, int(BOT_CONFIG["max_bet_usd"] * 100 / pc))
                cost_usd = (pc * count) / 100.0
            if BOT_STATE["daily_spent_usd"] + cost_usd > BOT_CONFIG["max_daily_usd"]:
                continue

            side = opp["signal"].replace("buy_", "")
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
            }

            BOT_STATE["trades_today"].append(trade_record)
            BOT_STATE["all_trades"].append(trade_record)
            if trade_record["success"]:
                BOT_STATE["daily_spent_usd"] += cost_usd
            print(f"[BOT] Trade: {side} {opp['kalshi_ticker']} @ {opp['price_cents']}c | success={trade_record['success']}")
            _save_state()

    except Exception as e:
        BOT_STATE["errors"].append({"time": now.isoformat(), "error": str(e)})
        BOT_STATE["errors"] = BOT_STATE["errors"][-50:]
        print(f"[BOT] Scan error: {e}")

# ---------------------------------------------------------------------------
# Scheduler
# ---------------------------------------------------------------------------

def _warm_picks_cache():
    """Pre-populate picks cache so the dashboard loads instantly."""
    try:
        with app.test_request_context():
            top_picks()
        print(f"[CACHE] Picks cache warmed: {_picks_cache['data']['total_scanned'] if _picks_cache.get('data') else 0} markets")
    except Exception as e:
        import traceback
        print(f"[CACHE] Warm error: {e}")
        traceback.print_exc()

# Use a simple background thread instead of APScheduler
# APScheduler's threadpool doesn't reliably work with gunicorn
import threading
import time as _time

def _background_loop():
    """Simple background loop that runs scans and warms cache."""
    _time.sleep(10)  # wait for server to fully start
    print("[BG] Background loop started")
    while True:
        try:
            # Run bot scan (updates BOT_STATE for status endpoint)
            run_bot_scan()
            # Warm the picks cache so /top-picks is fast
            _warm_picks_cache()
        except Exception as e:
            import traceback
            print(f"[BG] Error in background loop: {e}")
            traceback.print_exc()
        _time.sleep(30)  # scan every 30s

_bg_thread = None

def _ensure_bg_thread():
    global _bg_thread
    if _bg_thread is not None and _bg_thread.is_alive():
        return
    _bg_thread = threading.Thread(target=_background_loop, daemon=True)
    _bg_thread.start()
    print("[STARTUP] Background thread started")

# Try to start now, but also start on first request
_ensure_bg_thread()

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
    """Ensure background thread is running on first HTTP request."""
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
    k = load_private_key()
    return jsonify({"status": "ok", "private_key_loaded": k is not None, "bot_enabled": BOT_CONFIG["enabled"]})


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
    min_sim = float(request.args.get("min_similarity", 0.55))
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

            yes_count = pos.get("market_exposure", 0)
            no_count = pos.get("total_traded", 0)
            # Use the position fields from Kalshi
            enriched.append({
                "ticker": ticker,
                "title": title,
                "yes_contracts": pos.get("position", 0),
                "market_exposure": pos.get("market_exposure", 0),
                "resting_orders_count": pos.get("resting_orders_count", 0),
                "total_traded": pos.get("total_traded", 0),
                "realized_pnl": pos.get("realized_pnl", 0),
                "close_time": close_time,
                "result": result,
                "fees_paid": pos.get("fees_paid", 0),
            })
        return jsonify({"positions": enriched})
    except Exception as e:
        return jsonify({"positions": [], "error": str(e)})


@app.route("/settled")
def settled_positions():
    """Get settled positions with full scorecard data."""
    path = "/portfolio/positions"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"settled": [], "error": "No API key"})
    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 200, "settlement_status": "settled"},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        positions_list = resp.json().get("market_positions", [])
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

        for pos in positions_list:
            pnl_cents = pos.get("realized_pnl", 0)
            pnl = pnl_cents / 100
            total_pnl += pnl
            fees = pos.get("fees_paid", 0) / 100
            traded = pos.get("total_traded", 0)
            total_wagered += traded * 0.01  # rough estimate

            ticker = pos.get("ticker", "")

            # Enrich with market title
            title = ticker
            try:
                mkt_path = f"/markets/{ticker}"
                mkt_h = signed_headers("GET", mkt_path)
                mkt_r = requests.get(
                    KALSHI_BASE_URL + KALSHI_API_PREFIX + mkt_path,
                    headers=mkt_h, timeout=5,
                )
                if mkt_r.ok:
                    mkt = mkt_r.json().get("market", {})
                    title = mkt.get("title", ticker)
            except Exception:
                pass

            if pnl > 0:
                wins += 1
                won = True
                biggest_win = max(biggest_win, pnl)
                if current_streak_type == "win":
                    streak += 1
                else:
                    streak = 1
                    current_streak_type = "win"
            elif pnl < 0:
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

            # Check if this was a pick we recommended
            pick_type = "unknown"
            for ph in BOT_STATE.get("pick_history", []):
                if ph.get("ticker") == ticker:
                    pick_type = ph.get("type", "unknown")
                    break

            settled.append({
                "ticker": ticker,
                "title": title,
                "pnl_usd": round(pnl, 2),
                "won": won,
                "total_traded": traded,
                "fees_paid": round(fees, 2),
                "pick_type": pick_type,
            })

        total_bets = wins + losses + breakeven
        roi = round(total_pnl / max(0.01, total_wagered) * 100, 1) if total_wagered > 0 else 0

        return jsonify({
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
        })
    except Exception as e:
        return jsonify({"settled": [], "error": str(e)})


# ---------------------------------------------------------------------------
# Bot endpoints (NEW)
# ---------------------------------------------------------------------------

@app.route("/status")
def status():
    markets = BOT_STATE["last_scan_markets"]
    mispriced = BOT_STATE["last_scan_mispriced"]
    return jsonify({
        "bot_enabled": BOT_CONFIG["enabled"],
        "config": BOT_CONFIG,
        "last_scan": BOT_STATE["last_scan"],
        "last_scan_markets": markets,
        "last_scan_mispriced": mispriced,
        "trades_today": len(BOT_STATE["trades_today"]),
        "daily_spent_usd": BOT_STATE["daily_spent_usd"],
        "total_trades_all_time": len(BOT_STATE["all_trades"]),
        "recent_errors": BOT_STATE["errors"][-5:],
        "scheduler_running": scheduler.running,
    })


@app.route("/trades")
def trades():
    return jsonify({
        "total": len(BOT_STATE["all_trades"]),
        "today": len(BOT_STATE["trades_today"]),
        "daily_spent_usd": BOT_STATE["daily_spent_usd"],
        "trades": BOT_STATE["all_trades"],
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
    # Serve cached data if fresh (60s TTL)
    if _picks_cache["time"] and (now - _picks_cache["time"]).total_seconds() < 60 and _picks_cache["data"] is not None:
        return jsonify(_picks_cache["data"])
    # If cache expired or empty, do a full scan (may take 20-30s first time)
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
            if sim >= 0.40:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                matches.append({
                    "platform": om["platform"], "yes": om["yes"], "no": om["no"],
                    "similarity": round(sim, 3), "volume": om.get("volume", 0),
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
    opps = find_opportunities(all_markets, min_similarity=0.50, max_cost=1.0)
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
            if similarity(nq_k, normalize_question(opp["question_a"]), km["question"], opp["question_a"]) > 0.5:
                ticker = km["id"]; matched_km = km; break
            if similarity(nq_k, normalize_question(opp["question_b"]), km["question"], opp["question_b"]) > 0.5:
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
            if sim >= 0.40:
                if om["yes"] < 0.03 or om["yes"] > 0.97:
                    continue
                xplat_matches.append({
                    "platform": om["platform"], "yes": om["yes"],
                    "similarity": round(sim, 3),
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

    # ── Split into sports & non-sports, return exactly 10 each ──
    sports_picks = sorted([p for p in picks if p.get("is_sports")], key=lambda x: x["score"], reverse=True)[:10]
    nonsports_picks = sorted([p for p in picks if not p.get("is_sports")], key=lambda x: x["score"], reverse=True)[:10]

    # ── Top 5 hero picks: ranked by real win likelihood (honest probability) ──
    # Filter: must have volume, must settle within 90 days, must have real edge
    def _is_hero_worthy(p):
        # Must have SOME volume (people actually trading)
        if (p.get("volume") or 0) < 10:
            return False
        # Must have some edge — at least 5% deviation
        if p.get("deviation", 0) < 0.05:
            return False
        # Filter out terrible risk/reward — if you pay 90¢+ to win $1,
        # the profit is tiny but the loss is huge. Skip these.
        price = p.get("price_cents", 50)
        if price > 90:  # paying 90¢+ for $1 = max 10¢ profit
            return False
        # Also skip super cheap (<5¢) — usually longshots with no edge
        if price < 5:
            return False
        return True

    hero_candidates = [p for p in picks if _is_hero_worthy(p)]
    # Rank by: time_bonus (settle soon) * cross-platform * edge * volume
    def _hero_sort_key(p):
        is_xplat = 2.0 if p.get("type") in ("consensus", "arbitrage", "cross_validated") else 1.0
        plat_count = 1 + p.get("platform_count", 0) * 0.3
        deviation = p.get("deviation", 0)
        vol = min(2.0, 1.0 + (p.get("volume", 0) / 10000))
        tb = _time_bonus(p)
        return tb * is_xplat * plat_count * (1 + deviation) * vol
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
                "timestamp": datetime.datetime.utcnow().isoformat(),
            })
            existing_hist_tickers.add(tk)
    # Trim to last 500
    BOT_STATE["pick_history"] = BOT_STATE.get("pick_history", [])[-500:]
    _save_state()

    result = {"picks": all_ranked, "hero": [p["kalshi_ticker"] for p in hero_picks], "misc": [p["kalshi_ticker"] for p in misc_picks], "sports_count": len(sports_picks), "nonsports_count": len(nonsports_picks), "hero_count": len(hero_picks), "misc_count": len(misc_picks), "total_scanned": len(all_markets)}
    _picks_cache["data"] = result
    _picks_cache["time"] = datetime.datetime.utcnow()
    return jsonify(result)


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


@app.route("/config", methods=["POST"])
def config():
    data = request.get_json(force=True)
    allowed = {"enabled", "max_bet_usd", "max_daily_usd", "min_deviation", "min_platforms"}
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
        "timestamp": datetime.datetime.utcnow().isoformat(),
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
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: 'Courier New', 'SF Mono', 'Consolas', monospace; background: #000000; color: #ff8c00; overflow-x: hidden; }
.container { max-width: 1400px; margin: 0 auto; padding: 12px 16px; overflow-x: hidden; }
.header { display: flex; align-items: center; gap: 14px; margin-bottom: 4px; border-bottom: 2px solid #ff8c00; padding-bottom: 8px; }
.logo { width: 44px; height: 44px; }
h1 { font-size: 22px; color: #ff8c00; letter-spacing: 2px; text-transform: uppercase; }
h1 span { color: #00d4aa; }
.subtitle { color: #666; margin-bottom: 12px; font-size: 11px; letter-spacing: 1px; text-transform: uppercase; }
/* P/L Chart */
.chart-section { background: #0a0a0a; border: 1px solid #333; padding: 14px; margin-bottom: 10px; }
.chart-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; }
.chart-title { font-size: 11px; font-weight: 600; text-transform: uppercase; letter-spacing: 1.5px; color: #ff8c00; }
.chart-pl { font-size: 20px; font-weight: 700; font-family: 'Courier New', monospace; }
.chart-pl.positive { color: #00ff88; }
.chart-pl.negative { color: #ff4444; }
.chart-pl.zero { color: #555; }
.chart-canvas { width: 100%; height: 160px; position: relative; }
.chart-canvas canvas { width: 100%; height: 100%; }

/* Status bar */
.status-bar { display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 10px; }
.stat-card { background: #0a0a0a; border: 1px solid #333; padding: 10px 14px; flex: 1; min-width: 140px; }
.stat-label { font-size: 9px; color: #888; text-transform: uppercase; letter-spacing: 1.5px; }
.stat-value { font-size: 20px; font-weight: 700; margin-top: 2px; font-family: 'Courier New', monospace; }
.stat-value.green { color: #00ff88; }
.stat-value.red { color: #ff4444; }
.stat-value.blue { color: #4488ff; }
.stat-value.yellow { color: #ff8c00; }

/* Bot toggle */
.bot-toggle { display: flex; align-items: center; gap: 12px; margin-bottom: 10px; padding: 6px 0; border-bottom: 1px solid #222; }
.toggle-btn { padding: 6px 18px; border: 1px solid #ff8c00; border-radius: 2px; font-weight: 600; cursor: pointer; font-size: 11px; font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 1px; }
.toggle-btn.enable { background: transparent; color: #00ff88; border-color: #00ff88; }
.toggle-btn.disable { background: transparent; color: #ff4444; border-color: #ff4444; }
.toggle-btn:hover { opacity: 0.8; }
.bot-status { font-size: 12px; color: #888; }
.bot-status .dot { display: inline-block; width: 8px; height: 8px; border-radius: 50%; margin-right: 6px; }
.dot.on { background: #00ff88; box-shadow: 0 0 6px #00ff88; }
.dot.off { background: #555; }

/* Sections */
.section { margin-bottom: 16px; }
.section-title { font-size: 13px; font-weight: 600; margin-bottom: 8px; display: flex; align-items: center; gap: 8px; text-transform: uppercase; letter-spacing: 1.5px; color: #ff8c00; border-bottom: 1px solid #222; padding-bottom: 6px; }
.badge { background: #1a1a1a; border: 1px solid #333; padding: 1px 8px; border-radius: 2px; font-size: 11px; color: #ff8c00; }
.refresh-btn { background: transparent; border: 1px solid #444; color: #888; padding: 4px 10px; border-radius: 2px; cursor: pointer; font-size: 10px; margin-left: auto; font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 1px; }
.refresh-btn:hover { border-color: #ff8c00; color: #ff8c00; }

/* Table */
table { width: 100%; border-collapse: collapse; }
th { text-align: left; padding: 6px 10px; font-size: 9px; color: #ff8c00; text-transform: uppercase; letter-spacing: 1.5px; border-bottom: 1px solid #333; background: #0a0a0a; }
td { padding: 8px 10px; border-bottom: 1px solid #1a1a1a; font-size: 12px; color: #ccc; }
tr:hover { background: #111; }
.confidence { display: inline-block; padding: 2px 8px; border-radius: 2px; font-size: 10px; font-weight: 600; text-transform: uppercase; letter-spacing: 1px; }
.conf-high { background: rgba(0,255,136,0.1); color: #00ff88; border: 1px solid #00ff88; }
.conf-med { background: rgba(255,140,0,0.1); color: #ff8c00; border: 1px solid #ff8c00; }
.conf-low { background: rgba(255,68,68,0.1); color: #ff4444; border: 1px solid #ff4444; }
.trade-btn { background: transparent; color: #00ff88; border: 1px solid #00ff88; padding: 4px 12px; border-radius: 2px; cursor: pointer; font-size: 10px; font-weight: 600; font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 1px; }
.trade-btn:hover { background: #00ff88; color: #000; }
.trade-btn:disabled { border-color: #333; color: #555; cursor: not-allowed; background: transparent; }
.side-yes { color: #00ff88; font-weight: 600; }
.side-no { color: #ff4444; font-weight: 600; }
.result-win { color: #00ff88; }
.result-loss { color: #ff4444; }
.result-pending { color: #ff8c00; }
.empty { text-align: center; padding: 30px; color: #555; font-size: 12px; }
.loading { text-align: center; padding: 16px; color: #555; font-size: 12px; }
a { color: #4488ff; text-decoration: none; }
a:hover { text-decoration: underline; }
/* Bloomberg ticker bar */
.ticker-bar { background: #0a0a0a; border: 1px solid #222; padding: 6px 12px; margin-bottom: 10px; font-size: 11px; color: #888; overflow: hidden; white-space: nowrap; }
.ticker-bar span { margin-right: 24px; }
.ticker-bar .up { color: #00ff88; }
.ticker-bar .down { color: #ff4444; }
/* Top Picks - compact grid */
.top-picks { margin-bottom: 16px; }
.picks-grid { display: grid; grid-template-columns: repeat(5, 1fr); gap: 8px; }
@media (max-width: 900px) { .picks-grid { grid-template-columns: repeat(3, 1fr); } }
@media (max-width: 600px) { .picks-grid { grid-template-columns: repeat(2, 1fr); } }
.pick-card { background: #0a0a0a; border: 1px solid #333; padding: 10px; position: relative; display: flex; flex-direction: column; }
.pick-card:hover { border-color: #ff8c00; }
.pick-rank { position: absolute; top: 6px; right: 8px; font-size: 20px; font-weight: 800; color: #1a1a1a; font-family: 'Courier New', monospace; }
.pick-header { display: flex; align-items: center; gap: 6px; margin-bottom: 4px; flex-wrap: wrap; }
.pick-signal { font-size: 9px; font-weight: 700; padding: 2px 6px; border-radius: 2px; text-transform: uppercase; letter-spacing: 0.5px; }
.pick-signal.yes { background: rgba(0,255,136,0.12); color: #00ff88; border: 1px solid #00ff88; }
.pick-signal.no { background: rgba(255,68,68,0.12); color: #ff4444; border: 1px solid #ff4444; }
.pick-conf { font-size: 8px; padding: 1px 5px; border-radius: 2px; text-transform: uppercase; letter-spacing: 0.5px; font-weight: 600; }
.pick-conf.high { color: #00ff88; border: 1px solid #00ff88; }
.pick-conf.medium { color: #ff8c00; border: 1px solid #ff8c00; }
.pick-conf.low { color: #ff4444; border: 1px solid #ff4444; }
.pick-question { font-size: 10px; color: #ddd; margin-bottom: 4px; font-weight: 600; line-height: 1.3; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; }
.pick-question a { color: #ddd; }
.pick-question a:hover { color: #ff8c00; }
.pick-edge { font-size: 9px; color: #ff8c00; margin-bottom: 2px; font-weight: 600; overflow: hidden; white-space: nowrap; text-overflow: ellipsis; }
.pick-thesis { display: none; }
.pick-chart { width: 100%; height: 60px; margin: 4px 0; position: relative; flex-shrink: 0; }
.pick-chart canvas { width: 100%; height: 100%; }
.pick-footer { display: flex; align-items: center; gap: 6px; flex-wrap: wrap; margin-top: auto; }
.pick-meta { font-size: 8px; color: #666; text-transform: uppercase; letter-spacing: 0.5px; }
.pick-meta b { color: #ff8c00; }
.pick-profit { font-size: 10px; color: #00ff88; font-weight: 700; font-family: 'Courier New', monospace; }
.pick-execute { background: transparent; color: #00ff88; border: 1px solid #00ff88; padding: 4px 8px; border-radius: 2px; cursor: pointer; font-size: 9px; font-weight: 700; font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 0.5px; width: 100%; margin-top: 6px; }
.pick-execute:hover { background: #00ff88; color: #000; }
.pick-execute:disabled { border-color: #333; color: #555; cursor: not-allowed; background: transparent; }
/* Two-column layout */
.two-col { display: grid; grid-template-columns: 1fr 1fr; gap: 16px; margin-bottom: 16px; }
@media (max-width: 900px) { .two-col { grid-template-columns: 1fr; } }
/* Hero section */
.hero-section { margin-bottom: 16px; }
.hero-grid { display: grid; grid-template-columns: repeat(5, minmax(0, 1fr)); gap: 6px; width: 100%; }
@media (max-width: 1100px) { .hero-grid { grid-template-columns: repeat(3, minmax(0, 1fr)); } }
@media (max-width: 600px) { .hero-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
.hero-card { background: linear-gradient(135deg, #0d1a0d 0%, #0a0a0a 50%, #1a0d00 100%); border: 1px solid #00ff88; padding: 8px; position: relative; display: flex; flex-direction: column; min-width: 0; overflow: hidden; word-break: break-word; }
.hero-card:hover { border-color: #ff8c00; box-shadow: 0 0 15px rgba(255,140,0,0.15); }
.hero-rank { position: absolute; top: 2px; right: 6px; font-size: 20px; font-weight: 900; color: rgba(0,255,136,0.15); font-family: 'Courier New', monospace; }
.hero-prob { font-size: 20px; font-weight: 900; color: #00ff88; font-family: 'Courier New', monospace; line-height: 1; }
.hero-label { font-size: 7px; color: #888; text-transform: uppercase; letter-spacing: 1px; margin-top: 1px; }
.hero-question { font-size: 10px; color: #ddd; margin: 4px 0; font-weight: 600; line-height: 1.3; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; }
.hero-question a { color: #ddd; }
.hero-question a:hover { color: #ff8c00; }
.hero-edge-reason { font-size: 8px; color: #aaa; line-height: 1.3; margin: 2px 0 4px; overflow: hidden; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; font-style: italic; }
.hero-signal { font-size: 8px; font-weight: 700; padding: 1px 5px; border-radius: 2px; display: inline-block; }
.hero-signal.yes { background: rgba(0,255,136,0.12); color: #00ff88; border: 1px solid #00ff88; }
.hero-signal.no { background: rgba(255,68,68,0.12); color: #ff4444; border: 1px solid #ff4444; }
.hero-footer { display: flex; align-items: center; justify-content: space-between; gap: 4px; margin-top: auto; padding-top: 4px; }
.hero-execute { background: rgba(0,255,136,0.1); color: #00ff88; border: 1px solid #00ff88; padding: 3px 8px; border-radius: 2px; cursor: pointer; font-size: 9px; font-weight: 700; font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 0.5px; white-space: nowrap; }
.hero-execute:hover { background: #00ff88; color: #000; }
.hero-execute:disabled { border-color: #333; color: #555; cursor: not-allowed; background: transparent; }
/* Toast notifications */
.toast-container { position: fixed; top: 16px; right: 16px; z-index: 9999; display: flex; flex-direction: column; gap: 8px; pointer-events: none; }
.toast { pointer-events: auto; padding: 12px 18px; border-radius: 3px; font-size: 11px; font-family: 'Courier New', monospace; color: #fff; max-width: 380px; animation: toastIn 0.3s ease, toastOut 0.4s ease 4.6s; opacity: 0; word-break: break-word; }
.toast.success { background: #0d2818; border: 1px solid #00ff88; color: #00ff88; }
.toast.error { background: #2a0a0a; border: 1px solid #ff4444; color: #ff4444; }
.toast.info { background: #1a1a0a; border: 1px solid #ff8c00; color: #ff8c00; }
@keyframes toastIn { from { opacity: 0; transform: translateX(40px); } to { opacity: 1; transform: translateX(0); } }
@keyframes toastOut { from { opacity: 1; } to { opacity: 0; } }
</style>
</head>
<body>
<div class="container">
<div class="header">
  <svg class="logo" viewBox="0 0 64 64" xmlns="http://www.w3.org/2000/svg">
    <defs>
      <linearGradient id="metalBase" x1="0%" y1="0%" x2="100%" y2="100%">
        <stop offset="0%" style="stop-color:#e8e8e8"/>
        <stop offset="25%" style="stop-color:#a8a8a8"/>
        <stop offset="50%" style="stop-color:#d0d0d0"/>
        <stop offset="75%" style="stop-color:#888"/>
        <stop offset="100%" style="stop-color:#b0b0b0"/>
      </linearGradient>
      <linearGradient id="metalShine" x1="20%" y1="0%" x2="80%" y2="100%">
        <stop offset="0%" style="stop-color:#fff;stop-opacity:0.6"/>
        <stop offset="40%" style="stop-color:#fff;stop-opacity:0"/>
        <stop offset="60%" style="stop-color:#fff;stop-opacity:0.2"/>
        <stop offset="100%" style="stop-color:#fff;stop-opacity:0"/>
      </linearGradient>
      <linearGradient id="metalDark" x1="0%" y1="100%" x2="100%" y2="0%">
        <stop offset="0%" style="stop-color:#555"/>
        <stop offset="50%" style="stop-color:#999"/>
        <stop offset="100%" style="stop-color:#666"/>
      </linearGradient>
      <filter id="metalShadow"><feDropShadow dx="1" dy="1" stdDeviation="1" flood-color="#000" flood-opacity="0.4"/></filter>
    </defs>
    <path d="M8 38c0 0 4-18 20-22c2-6 8-12 14-14c-2 6-1 10 0 14c6 3 12 8 14 16c1 4 0 8-2 11l-6 3l2-6l-4 5l-8 2l3-4l-6 3c-4 1-10 1-14-1l4-3l-7 1c-4-1-7-3-9-6" fill="url(#metalBase)" filter="url(#metalShadow)"/>
    <path d="M8 38c0 0 4-18 20-22c2-6 8-12 14-14c-2 6-1 10 0 14c6 3 12 8 14 16c1 4 0 8-2 11l-6 3l2-6l-4 5l-8 2l3-4l-6 3c-4 1-10 1-14-1l4-3l-7 1c-4-1-7-3-9-6" fill="url(#metalShine)"/>
    <path d="M32 16c8-2 16 2 20 10" stroke="#666" stroke-width="1.5" fill="none" opacity="0.4"/>
    <path d="M20 28c6-1 14 0 22 4" stroke="#ccc" stroke-width="0.5" fill="none" opacity="0.5"/>
    <path d="M18 32c8-1 18 0 26 2" stroke="#fff" stroke-width="0.3" fill="none" opacity="0.3"/>
    <circle cx="44" cy="28" r="2.2" fill="#333"/>
    <circle cx="44.5" cy="27.3" r="0.8" fill="#fff" opacity="0.9"/>
    <path d="M8 38c3-1 6 2 10 1c-3 2-7 2-10-1z" fill="#777" opacity="0.3"/>
    <path d="M28 40l-4 10l6-8l5 12l4-11l6 8l-2-11" fill="url(#metalDark)" filter="url(#metalShadow)"/>
    <path d="M28 40l-4 10l6-8l5 12l4-11l6 8l-2-11" fill="url(#metalShine)" opacity="0.4"/>
    <path d="M52 32c2 0 6-1 8-3c-1 3-4 5-7 5" fill="url(#metalBase)" opacity="0.9"/>
  </svg>
  <div>
    <h1><span>Trade</span>Shark</h1>
    <p class="subtitle">Cross-platform prediction market trading &bull; Scanning 6 platforms + news every 15 seconds</p>
  </div>
</div>

<div style="margin-bottom:12px">
  <button id="auto-trade-btn" onclick="toggleAutoTrade()" style="
    padding: 12px 32px; font-family: 'JetBrains Mono', monospace; font-size: 1em; font-weight: 700;
    border: 2px solid #ff4444; background: rgba(255,68,68,0.15); color: #ff4444;
    cursor: pointer; text-transform: uppercase; letter-spacing: 2px; width: 100%;
  ">AUTO-TRADE: --</button>
</div>

<div class="status-bar" id="status-bar">
  <div class="stat-card"><div class="stat-label">Balance</div><div class="stat-value green" id="balance">--</div></div>
  <div class="stat-card"><div class="stat-label">Markets Scanned</div><div class="stat-value blue" id="markets-scanned">--</div></div>
  <div class="stat-card"><div class="stat-label">Mispriced Found</div><div class="stat-value yellow" id="mispriced-count">--</div></div>
  <div class="stat-card"><div class="stat-label">Trades Today</div><div class="stat-value" id="trades-today">--</div></div>
  <div class="stat-card"><div class="stat-label">Daily Spent</div><div class="stat-value red" id="daily-spent">--</div></div>
</div>

<div class="hero-section">
  <div class="section-title" style="font-size:15px;border-bottom:2px solid #00ff88;color:#00ff88">Top 5 Picks — Ranked by Cross-Platform Confidence <span class="badge" id="hero-badge" style="color:#00ff88;border-color:#00ff88">0</span><button class="refresh-btn" onclick="loadTopPicks()">Refresh</button></div>
  <div id="hero-picks" class="hero-grid"><div class="loading" style="grid-column:1/-1">Scanning 6 platforms + news...</div></div>
</div>

<div class="two-col">
  <div>
    <div class="top-picks">
      <div class="section-title">Sports <span class="badge" id="picks-badge-sports">0</span></div>
      <div id="top-picks-list-sports" class="picks-grid" style="grid-template-columns: repeat(2, 1fr)"><div class="loading" style="grid-column:1/-1">Analyzing markets...</div></div>
    </div>
    <div class="section">
      <div class="section-title">Sports Settling Today <span class="badge" id="today-badge-sports">0</span></div>
      <div id="today-table-sports"><div class="loading">Loading...</div></div>
    </div>
  </div>
  <div>
    <div class="top-picks">
      <div class="section-title">Non-Sports <span class="badge" id="picks-badge-nonsports">0</span></div>
      <div id="top-picks-list-nonsports" class="picks-grid" style="grid-template-columns: repeat(2, 1fr)"><div class="loading" style="grid-column:1/-1">Analyzing markets...</div></div>
    </div>
    <div class="section">
      <div class="section-title">Non-Sports Settling Today <span class="badge" id="today-badge-nonsports">0</span></div>
      <div id="today-table-nonsports"><div class="loading">Loading...</div></div>
    </div>
  </div>
</div>

<div class="section">
  <div class="section-title">Miscellaneous Opportunities <span class="badge" id="misc-badge">0</span></div>
  <div id="misc-picks" class="picks-grid"><div class="loading" style="grid-column:1/-1">Scanning...</div></div>
</div>

<div class="section">
  <div class="section-title">Open Positions <span class="badge" id="pos-badge">0</span><button class="refresh-btn" onclick="loadPositions()">Refresh</button></div>
  <div id="pos-table"><div class="loading">Loading positions...</div></div>
</div>

<div class="chart-section">
  <div class="chart-header">
    <span class="chart-title">P/L Performance</span>
    <span class="chart-pl zero" id="chart-pl">$0.00</span>
  </div>
  <div class="chart-canvas"><canvas id="pl-chart"></canvas></div>
</div>

<div class="section">
  <div class="section-title">Mispriced Opportunities <span class="badge" id="opp-badge">0</span><button class="refresh-btn" onclick="loadMispriced()">Refresh</button></div>
  <div id="opp-table"><div class="loading">Loading opportunities...</div></div>
</div>

<div class="section">
  <div class="section-title" style="color:#00ff88;border-bottom:1px solid #00ff88">📊 Scorecard — Path to $1M <button class="refresh-btn" onclick="loadSettled()">Refresh</button></div>
  <div id="settled-stats" style="display:flex;gap:10px;flex-wrap:wrap;margin-bottom:8px">
    <span style="color:#888">Loading...</span>
  </div>
  <div id="settled-table" style="margin-top:8px"></div>
</div>

<div class="section">
  <div class="section-title">Trade History <span class="badge" id="trade-badge">0</span><button class="refresh-btn" onclick="loadTrades()">Refresh</button></div>
  <div id="trade-table"><div class="loading">Loading trades...</div></div>
</div>
</div>

<div class="toast-container" id="toast-container"></div>

<script>
const API = window.location.origin;

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
  var pctColor = winPct >= 75 ? '#00ff88' : winPct >= 55 ? '#ff8c00' : '#ffcc00';
  h += '<div class="hero-prob" style="color:' + pctColor + '">' + winPct.toFixed(0) + '%</div>';
  h += '<div class="hero-label">Market Probability</div>';

  // Compact info line
  h += '<div style="display:flex;gap:5px;font-size:7px;color:#888;margin:2px 0;flex-wrap:wrap;align-items:center">';
  if (isConsensus) {
    h += '<span style="color:#00ff88;font-weight:700">' + platCount + ' PLATFORMS</span>';
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

async function loadStatus() {
  try {
    const [status, bal] = await Promise.all([
      fetch(API + '/status').then(r => r.json()),
      fetch(API + '/balance').then(r => r.json()),
    ]);
    window._currentBalance = bal.balance_usd || 0;
    document.getElementById('balance').textContent = '$' + (bal.balance_usd || 0).toFixed(2);
    document.getElementById('markets-scanned').textContent = status.last_scan_markets || 0;
    document.getElementById('mispriced-count').textContent = status.last_scan_mispriced || 0;
    document.getElementById('trades-today').textContent = status.trades_today || 0;
    document.getElementById('daily-spent').textContent = '$' + (status.daily_spent_usd || 0).toFixed(2);
    const atBtn = document.getElementById('auto-trade-btn');
    if (status.bot_enabled) {
      atBtn.textContent = 'AUTO-TRADE: ON';
      atBtn.style.border = '2px solid #00ff88';
      atBtn.style.background = 'rgba(0,255,136,0.15)';
      atBtn.style.color = '#00ff88';
    } else {
      atBtn.textContent = 'AUTO-TRADE: OFF';
      atBtn.style.border = '2px solid #ff4444';
      atBtn.style.background = 'rgba(255,68,68,0.15)';
      atBtn.style.color = '#ff4444';
    }
    window._botEnabled = status.bot_enabled;
  } catch(e) { console.error(e); }
}

async function toggleBot() {
  const enable = !window._botEnabled;
  await fetch(API + '/config', { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify({enabled: enable}) });
  loadStatus();
}

async function toggleAutoTrade() {
  const enable = !window._botEnabled;
  const atBtn = document.getElementById('auto-trade-btn');
  atBtn.textContent = enable ? 'ENABLING...' : 'DISABLING...';
  atBtn.style.opacity = '0.5';
  try {
    await fetch(API + '/config', { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify({enabled: enable}) });
    showToast(enable ? 'Auto-trading ENABLED' : 'Auto-trading DISABLED', enable ? 'success' : 'error');
  } catch(e) {
    showToast('Failed to toggle: ' + e.message, 'error');
  }
  atBtn.style.opacity = '1';
  loadStatus();
}

let _mispricedFirstLoad = true;
async function loadMispriced() {
  if (_mispricedFirstLoad) document.getElementById('opp-table').innerHTML = '<div class="loading">Scanning markets...</div>';
  try {
    const data = await fetch(API + '/mispriced').then(r => r.json());
    _mispricedFirstLoad = false;
    document.getElementById('opp-badge').textContent = data.mispriced_count;
    if (!data.mispricings || data.mispricings.length === 0) {
      document.getElementById('opp-table').innerHTML = '<div class="empty">No mispriced markets found right now. The bot scans every 10 minutes.</div>';
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
    document.getElementById('opp-table').innerHTML = html;
  } catch(e) {
    document.getElementById('opp-table').innerHTML = '<div class="empty">Error loading: ' + e.message + '</div>';
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
      grad.addColorStop(0, '#ff8c00');
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
  const typeColors = {consensus: '#00ff88', arbitrage: '#ff8c00', cross_validated: '#00d4ff', kalshi_only: '#666', news_researched: '#c084fc', high_probability: '#4a9eff'};
  const typeColor = typeColors[p.type] || '#888';
  let h = '<div class="pick-card">';
  h += '<div class="pick-rank">#' + (idx + 1) + '</div>';
  h += '<div class="pick-header">';
  h += '<span class="pick-signal ' + sigClass + '">' + sigLabel + '</span>';
  h += '<span class="pick-conf ' + confClass + '">' + p.confidence + '</span>';
  h += '<span class="pick-meta" style="color:' + typeColor + '">' + typeLabel + '</span>';
  var winPct = (p.win_probability || 0.5) * 100;
  var wpColor = winPct >= 75 ? '#00ff88' : winPct >= 55 ? '#ff8c00' : '#ffcc00';
  h += '<span class="pick-meta" style="color:' + wpColor + ';font-weight:700;font-size:1.2em">' + winPct.toFixed(0) + '%</span>';
  var pickSettle = formatSettleTime(p.close_time);
  h += '<span class="pick-meta" style="color:#ff8c00;font-weight:600">⏱ ' + pickSettle + '</span>';
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
    var sentColor = p.news_sentiment === 'bullish' ? '#00ff88' : p.news_sentiment === 'bearish' ? '#ff4444' : '#888';
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

async function loadTopPicks() {
  if (_picksFirstLoad) {
    document.getElementById('hero-picks').innerHTML = '<div class="loading" style="grid-column:1/-1">Scanning 6 platforms + news...</div>';
    document.getElementById('top-picks-list-sports').innerHTML = '<div class="loading" style="grid-column:1/-1">Loading...</div>';
    document.getElementById('top-picks-list-nonsports').innerHTML = '<div class="loading" style="grid-column:1/-1">Loading...</div>';
  }
  try {
    const data = await fetch(API + '/top-picks').then(r => r.json());
    _picksFirstLoad = false;
    const picks = data.picks || [];
    const heroTickers = new Set(data.hero || []);
    const miscTickers = new Set(data.misc || []);
    // Tag each pick with global index for trade execution
    picks.forEach((p, i) => { p._globalIdx = i; });
    _picksData = picks;

    // Hero: Top 5 best bets
    const heroPicks = picks.filter(p => heroTickers.has(p.kalshi_ticker)).slice(0, 5);
    document.getElementById('hero-badge').textContent = heroPicks.length;
    if (heroPicks.length === 0) {
      document.getElementById('hero-picks').innerHTML = '<div class="empty" style="grid-column:1/-1">Scanning for best bets...</div>';
    } else {
      let html = '';
      heroPicks.forEach((p, idx) => { html += renderHeroCard(p, idx); });
      document.getElementById('hero-picks').innerHTML = html;
    }

    // Sports
    const sports = picks.filter(p => isSports(p) && !miscTickers.has(p.kalshi_ticker)).slice(0, 10);
    document.getElementById('picks-badge-sports').textContent = sports.length;
    if (sports.length === 0) {
      document.getElementById('top-picks-list-sports').innerHTML = '<div class="empty" style="grid-column:1/-1">No sports picks right now.</div>';
    } else {
      let html = '';
      sports.forEach((p, idx) => { html += renderPickCard(p, idx, 'sports'); });
      document.getElementById('top-picks-list-sports').innerHTML = html;
      sports.forEach((p, idx) => { drawPickChart('sports-chart-' + idx, p.prices || {}, p.signal); });
    }

    // Non-sports
    const nonSports = picks.filter(p => !isSports(p) && !miscTickers.has(p.kalshi_ticker)).slice(0, 10);
    document.getElementById('picks-badge-nonsports').textContent = nonSports.length;
    if (nonSports.length === 0) {
      document.getElementById('top-picks-list-nonsports').innerHTML = '<div class="empty" style="grid-column:1/-1">No non-sports picks right now.</div>';
    } else {
      let html = '';
      nonSports.forEach((p, idx) => { html += renderPickCard(p, idx, 'nonsports'); });
      document.getElementById('top-picks-list-nonsports').innerHTML = html;
      nonSports.forEach((p, idx) => { drawPickChart('nonsports-chart-' + idx, p.prices || {}, p.signal); });
    }

    // Miscellaneous
    const misc = picks.filter(p => miscTickers.has(p.kalshi_ticker)).slice(0, 10);
    document.getElementById('misc-badge').textContent = misc.length;
    if (misc.length === 0) {
      document.getElementById('misc-picks').innerHTML = '<div class="empty" style="grid-column:1/-1">No miscellaneous picks.</div>';
    } else {
      let html = '';
      misc.forEach((p, idx) => { html += renderPickCard(p, idx, 'misc'); });
      document.getElementById('misc-picks').innerHTML = html;
      misc.forEach((p, idx) => { drawPickChart('misc-chart-' + idx, p.prices || {}, p.signal); });
    }
  } catch(e) {
    document.getElementById('hero-picks').innerHTML = '<div class="empty" style="grid-column:1/-1">Error: ' + e.message + '</div>';
    document.getElementById('top-picks-list-sports').innerHTML = '<div class="empty" style="grid-column:1/-1">Error: ' + e.message + '</div>';
    document.getElementById('top-picks-list-nonsports').innerHTML = '<div class="empty" style="grid-column:1/-1">Error: ' + e.message + '</div>';
  }
}

async function executePickTrade(btn, idx) {
  const m = _picksData[idx];
  btn.disabled = true;
  btn.textContent = 'PLACING...';
  btn.style.borderColor = '#ff8c00';
  btn.style.color = '#ff8c00';
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
      btn.style.borderColor = '#00ff88';
      btn.style.color = '#00ff88';
      btn.style.background = 'rgba(0,255,136,0.15)';
      showToast('Order filled: ' + m.kalshi_ticker + ' ' + m.signal.replace('buy_','').toUpperCase() + ' @ ' + (m.price_cents/100).toFixed(2), 'success');
    } else {
      btn.textContent = 'FAILED';
      btn.style.borderColor = '#ff4444';
      btn.style.color = '#ff4444';
      const errMsg = data.result && data.result.response_body ? data.result.response_body : (data.result && data.result.error ? data.result.error : 'Unknown error');
      showToast('Trade failed: ' + errMsg, 'error');
      var retrySide = m.signal === 'buy_yes' ? 'YES' : 'NO';
      setTimeout(() => { btn.disabled = false; btn.textContent = 'Retry ' + retrySide; btn.style.borderColor = '#ff8c00'; btn.style.color = '#ff8c00'; }, 3000);
    }
    loadStatus();
    loadTrades();
  } catch(e) {
    btn.textContent = 'ERROR';
    btn.style.borderColor = '#ff4444';
    btn.style.color = '#ff4444';
    showToast('Network error: ' + e.message, 'error');
  }
}

async function loadTrades() {
  try {
    const data = await fetch(API + '/trades').then(r => r.json());
    document.getElementById('trade-badge').textContent = data.total;
    drawPLChart(data.trades || []);
    if (!data.trades || data.trades.length === 0) {
      document.getElementById('trade-table').innerHTML = '<div class="empty">No trades yet. Enable the bot or click Trade on an opportunity.</div>';
      return;
    }
    let html = '<table><tr><th>Time</th><th>Market</th><th>Side</th><th>Qty</th><th>Cost</th><th>Deviation</th><th>Result</th><th>Source</th></tr>';
    data.trades.slice().reverse().forEach(t => {
      const time = new Date(t.timestamp + 'Z').toLocaleString();
      const sideClass = t.side === 'yes' ? 'side-yes' : 'side-no';
      const resultClass = t.success ? 'result-win' : 'result-loss';
      const resultLabel = t.success ? 'Filled' : 'Failed';
      const source = t.manual ? 'Manual' : 'Auto';
      const qty = t.count || 1;
      html += '<tr>';
      html += '<td>' + time + '</td>';
      html += '<td>' + (t.question || t.ticker).substring(0, 50) + '</td>';
      html += '<td class="' + sideClass + '">' + qty + 'x ' + t.side.toUpperCase() + '</td>';
      html += '<td>' + qty + '</td>';
      html += '<td>$' + (t.cost_usd || t.price_cents/100).toFixed(2) + '</td>';
      html += '<td>' + ((t.deviation || 0) * 100).toFixed(1) + '%</td>';
      html += '<td class="' + resultClass + '">' + resultLabel + '</td>';
      html += '<td>' + source + '</td>';
      html += '</tr>';
    });
    html += '</table>';
    document.getElementById('trade-table').innerHTML = html;
  } catch(e) {
    document.getElementById('trade-table').innerHTML = '<div class="empty">Error loading trades</div>';
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
  if (cumPL > 0) { plEl.className = 'chart-pl positive'; plEl.textContent = '+$' + cumPL.toFixed(2); }
  else if (cumPL < 0) { plEl.className = 'chart-pl negative'; plEl.textContent = '-$' + Math.abs(cumPL).toFixed(2); }
  else { plEl.className = 'chart-pl zero'; plEl.textContent = '$0.00'; }

  const maxX = points.length - 1 || 1;
  const ys = points.map(p => p.y);
  let minY = Math.min(...ys, 0);
  let maxY = Math.max(...ys, 0);
  if (minY === maxY) { minY -= 1; maxY += 1; }
  const pad = 10;

  function px(i) { return pad + (i / maxX) * (w - pad * 2); }
  function py(v) { return h - pad - ((v - minY) / (maxY - minY)) * (h - pad * 2); }

  // Grid lines
  ctx.strokeStyle = '#1a1a1a';
  ctx.lineWidth = 1;
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
  if (cumPL >= 0) { grad.addColorStop(0, 'rgba(0,255,136,0.15)'); grad.addColorStop(1, 'rgba(0,255,136,0)'); }
  else { grad.addColorStop(0, 'rgba(255,68,68,0)'); grad.addColorStop(1, 'rgba(255,68,68,0.15)'); }
  ctx.fillStyle = grad;
  ctx.fill();

  // P/L line
  ctx.beginPath();
  points.forEach((p, i) => { if (i === 0) ctx.moveTo(px(i), py(p.y)); else ctx.lineTo(px(i), py(p.y)); });
  ctx.strokeStyle = cumPL >= 0 ? '#00ff88' : '#ff4444';
  ctx.lineWidth = 2;
  ctx.stroke();

  // Current dot
  const last = points[points.length - 1];
  ctx.beginPath();
  ctx.arc(px(points.length - 1), py(last.y), 4, 0, Math.PI * 2);
  ctx.fillStyle = cumPL >= 0 ? '#00ff88' : '#ff4444';
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
    html += '<td style="color:#ff8c00;font-weight:700">' + p.time_left + '</td>';
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
    document.getElementById('today-table-sports').innerHTML = '<div class="empty">Error: ' + e.message + '</div>';
    document.getElementById('today-table-nonsports').innerHTML = '<div class="empty">Error: ' + e.message + '</div>';
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
    const data = await fetch(API + '/positions').then(r => r.json());
    const positions = data.positions || [];
    document.getElementById('pos-badge').textContent = positions.length;
    if (positions.length === 0) {
      document.getElementById('pos-table').innerHTML = '<div class="empty">No open positions. Place a trade to get started.</div>';
      return;
    }
    let html = '<table><tr><th>Market</th><th>Contracts</th><th>Exposure</th><th>Time Left</th><th>Status</th></tr>';
    positions.forEach(p => {
      let timeLeft = '--';
      let statusClass = 'result-pending';
      let statusLabel = 'Active';
      if (p.result) {
        statusLabel = p.result === 'yes' ? 'WON' : 'LOST';
        statusClass = p.result === 'yes' ? 'result-win' : 'result-loss';
        timeLeft = 'Settled';
      } else if (p.close_time) {
        const close = new Date(p.close_time);
        const now = new Date();
        const diff = close - now;
        if (diff <= 0) {
          timeLeft = 'Settling...';
        } else {
          const mins = Math.floor(diff / 60000);
          const hrs = Math.floor(mins / 60);
          const days = Math.floor(hrs / 24);
          if (days > 0) timeLeft = days + 'd ' + (hrs % 24) + 'h';
          else if (hrs > 0) timeLeft = hrs + 'h ' + (mins % 60) + 'm';
          else timeLeft = mins + 'm';
        }
      }
      const exposure = (p.market_exposure / 100).toFixed(2);
      html += '<tr>';
      html += '<td>' + (p.title || p.ticker).substring(0, 60) + '</td>';
      html += '<td>' + p.yes_contracts + '</td>';
      html += '<td>$' + exposure + '</td>';
      html += '<td style="color:#ff8c00;font-weight:600">' + timeLeft + '</td>';
      html += '<td class="' + statusClass + '">' + statusLabel + '</td>';
      html += '</tr>';
    });
    html += '</table>';
    document.getElementById('pos-table').innerHTML = html;
  } catch(e) {
    document.getElementById('pos-table').innerHTML = '<div class="empty">Error: ' + e.message + '</div>';
  }
}

async function loadSettled() {
  try {
    const data = await fetch(API + '/settled').then(r => r.json());
    window._settledData = data.settled || [];
    const el = document.getElementById('settled-stats');
    const w = data.wins || 0, l = data.losses || 0, wr = data.win_rate || 0;
    const pnl = data.total_pnl_usd || 0;
    const roi = data.roi_pct || 0;
    const bigW = data.biggest_win_usd || 0;
    const bigL = data.biggest_loss_usd || 0;
    const streak = data.streak || 0;
    const streakType = data.streak_type || 'none';
    const totalBets = data.total_bets || 0;
    const balance = window._currentBalance || 73.61;
    const pnlColor = pnl >= 0 ? '#00ff88' : '#ff4444';
    const wrColor = wr >= 60 ? '#00ff88' : wr >= 40 ? '#ff8c00' : '#ff4444';
    const roiColor = roi >= 0 ? '#00ff88' : '#ff4444';
    const streakColor = streakType === 'win' ? '#00ff88' : streakType === 'loss' ? '#ff4444' : '#888';
    const streakLabel = streakType === 'win' ? streak + 'W' : streakType === 'loss' ? streak + 'L' : '-';

    // Progress bar to $1M
    const progress = Math.min(100, (balance / 1000000) * 100);
    const progressLabel = progress < 0.01 ? '<0.01%' : progress.toFixed(3) + '%';

    function statBox(label, value, color) {
      return '<div style="background:#0a0a0a;border:1px solid #333;padding:8px 14px;min-width:80px;text-align:center;flex:1">' +
        '<div style="color:#888;font-size:0.6em;text-transform:uppercase;letter-spacing:0.5px">' + label + '</div>' +
        '<div style="color:' + color + ';font-size:1.2em;font-weight:700">' + value + '</div></div>';
    }

    var html = '';
    html += statBox('Wins', w, '#00ff88');
    html += statBox('Losses', l, '#ff4444');
    html += statBox('Win Rate', wr.toFixed(0) + '%', wrColor);
    html += statBox('P&L', (pnl >= 0 ? '+$' : '-$') + Math.abs(pnl).toFixed(2), pnlColor);
    html += statBox('ROI', roi.toFixed(1) + '%', roiColor);
    html += statBox('Streak', streakLabel, streakColor);
    html += statBox('Best Win', '+$' + bigW.toFixed(2), '#00ff88');
    html += statBox('Worst Loss', '-$' + Math.abs(bigL).toFixed(2), '#ff4444');
    html += statBox('Total Bets', totalBets, '#ff8c00');
    el.innerHTML = html;

    // Progress bar
    var prog = '<div style="margin-top:8px;background:#111;border:1px solid #333;padding:6px 10px">';
    prog += '<div style="display:flex;justify-content:space-between;font-size:9px;color:#888;margin-bottom:4px">';
    prog += '<span>$' + balance.toFixed(2) + ' balance</span>';
    prog += '<span style="color:#00ff88">$1,000,000 goal</span>';
    prog += '</div>';
    prog += '<div style="background:#1a1a1a;height:12px;border:1px solid #333;position:relative">';
    prog += '<div style="background:linear-gradient(90deg,#00ff88,#ff8c00);height:100%;width:' + Math.max(0.5, progress) + '%;transition:width 0.5s"></div>';
    prog += '<div style="position:absolute;top:0;left:50%;transform:translateX(-50%);font-size:7px;color:#fff;line-height:12px;font-weight:700">' + progressLabel + '</div>';
    prog += '</div></div>';
    el.innerHTML += prog;

    // Settled positions table
    var tableEl = document.getElementById('settled-table');
    var settled = data.settled || [];
    if (settled.length === 0) {
      tableEl.innerHTML = '<div style="color:#555;font-size:10px;padding:8px">No settled positions yet. Place some bets and we will track every result here.</div>';
    } else {
      var tbl = '<table style="width:100%;border-collapse:collapse;font-size:9px">';
      tbl += '<tr style="color:#888;border-bottom:1px solid #333;text-align:left">';
      tbl += '<th style="padding:4px">Market</th><th style="padding:4px">Type</th><th style="padding:4px">P&L</th><th style="padding:4px">Result</th>';
      tbl += '</tr>';
      settled.forEach(function(s) {
        var rc = s.won === true ? '#00ff88' : s.won === false ? '#ff4444' : '#888';
        var rl = s.won === true ? '✅ WIN' : s.won === false ? '❌ LOSS' : '➖ EVEN';
        var tc = {consensus:'#00ff88', arbitrage:'#ff8c00', cross_validated:'#00d4ff', kalshi_only:'#666'}[s.pick_type] || '#555';
        var tl = {consensus:'CONSENSUS', arbitrage:'ARB', cross_validated:'VERIFIED', kalshi_only:'KALSHI'}[s.pick_type] || s.pick_type.toUpperCase();
        tbl += '<tr style="border-bottom:1px solid #1a1a1a">';
        tbl += '<td style="padding:4px;color:#ddd;max-width:300px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + s.title + '</td>';
        tbl += '<td style="padding:4px;color:' + tc + '">' + tl + '</td>';
        tbl += '<td style="padding:4px;color:' + rc + ';font-weight:700">' + (s.pnl_usd >= 0 ? '+' : '') + '$' + s.pnl_usd.toFixed(2) + '</td>';
        tbl += '<td style="padding:4px;color:' + rc + '">' + rl + '</td>';
        tbl += '</tr>';
      });
      tbl += '</table>';
      tableEl.innerHTML = tbl;
    }
  } catch(e) {
    document.getElementById('settled-stats').innerHTML = '<span style="color:#ff4444">Error: ' + e.message + '</span>';
  }
}

// Load everything on page load
loadStatus();
loadTopPicks();
loadTodayPicks();
loadPositions();
loadSettled();
loadMispriced();
loadTrades();
// Auto-refresh every 30 seconds
setInterval(() => { loadStatus(); loadTopPicks(); loadTodayPicks(); loadPositions(); loadSettled(); loadTrades(); }, 30000);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
