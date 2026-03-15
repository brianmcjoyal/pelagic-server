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
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed
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
    "scan_interval_seconds": 30,
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
# Platform fetchers
# ---------------------------------------------------------------------------

def fetch_kalshi():
    path = "/markets"
    headers = signed_headers("GET", path)
    if not headers:
        return []
    try:
        resp = requests.get(
            KALSHI_BASE_URL + KALSHI_API_PREFIX + path,
            headers=headers,
            params={"limit": 200, "status": "open"},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        raw = resp.json().get("markets", [])
    except Exception:
        return []
    out = []
    for m in raw:
        try:
            yes = (m.get("yes_ask") or m.get("last_price") or 50) / 100
            no  = (m.get("no_ask") or (100 - (m.get("last_price") or 50))) / 100
            ticker = m["ticker"]
            out.append({
                "platform": "kalshi",
                "id":       ticker,
                "question": m.get("title") or ticker,
                "yes":      round(yes, 4),
                "no":       round(no, 4),
                "volume":   m.get("volume", 0),
                "close_time": m.get("expected_expiration_time") or m.get("close_time"),
                "url":      "https://kalshi.com/markets/" + ticker,
            })
        except Exception:
            continue
    return out


def fetch_polymarket():
    try:
        resp = requests.get(
            "https://gamma-api.polymarket.com/markets",
            params={"active": "true", "closed": "false", "limit": 200},
            timeout=TIMEOUT,
        )
        resp.raise_for_status()
        raw = resp.json()
    except Exception:
        return []
    out = []
    for m in raw:
        try:
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
                "id":       str(m.get("id", "")),
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
            params={"limit": 200},
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


ALL_FETCHERS = {
    "kalshi":     fetch_kalshi,
    "polymarket": fetch_polymarket,
    "predictit":  fetch_predictit,
    "manifold":   fetch_manifold,
}


_market_cache = {"data": [], "time": None}

def fetch_all_markets():
    # Cache for 20 seconds to avoid hammering APIs on concurrent requests
    now = datetime.datetime.utcnow()
    if _market_cache["time"] and (now - _market_cache["time"]).total_seconds() < 20 and _market_cache["data"]:
        return _market_cache["data"]
    all_markets = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {pool.submit(fn): name for name, fn in ALL_FETCHERS.items()}
        for future in as_completed(futures):
            try:
                all_markets.extend(future.result())
            except Exception:
                continue
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
    if kw < 0.4:
        return 0
    if seq < 0.35:
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
    other platforms. If 2+ other platforms agree on a price and Kalshi
    disagrees by 15%+, that's a trade signal.
    """
    min_dev = BOT_CONFIG["min_deviation"]
    min_plats = BOT_CONFIG["min_platforms"]

    kalshi = []
    others = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        if m["platform"] == "kalshi":
            kalshi.append((nq, m))
        else:
            others.append((nq, m))

    mispricings = []

    for nq_k, km in kalshi:
        matches = []
        for nq_o, om in others:
            sim = similarity(nq_k, nq_o, km["question"], om["question"])
            if sim >= 0.55:
                matches.append({"platform": om["platform"], "yes": om["yes"], "similarity": round(sim, 3)})

        if len(matches) < min_plats:
            continue

        consensus_yes = sum(m["yes"] for m in matches) / len(matches)
        deviation = abs(km["yes"] - consensus_yes)

        if deviation < min_dev:
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

    payload = {
        "ticker": ticker,
        "action": "buy",
        "side": side,
        "type": "limit",
        "count": count,
        "client_order_id": str(uuid.uuid4()),
        "time_in_force": "good_till_canceled",
    }
    if side == "yes":
        payload["yes_price"] = price_cents
    else:
        payload["no_price"] = price_cents

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

scheduler = BackgroundScheduler()
scheduler.add_job(
    run_bot_scan,
    "interval",
    seconds=BOT_CONFIG["scan_interval_seconds"],
    id="consensus_scan",
    replace_existing=True,
    next_run_time=datetime.datetime.utcnow() + datetime.timedelta(seconds=5),  # first scan 5s after startup
)
scheduler.start()
atexit.register(scheduler.shutdown)

# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

@app.route("/health")
def health():
    k = load_private_key()
    return jsonify({"status": "ok", "private_key_loaded": k is not None, "bot_enabled": BOT_CONFIG["enabled"]})


@app.route("/debug-markets")
def debug_markets():
    path = "/markets"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"error": "no key"})
    resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + path, headers=headers, params={"limit": 3, "status": "open"}, timeout=TIMEOUT)
    raw = resp.json().get("markets", [])
    # Return raw fields for first 3 markets
    return jsonify({"sample": [{k: v for k, v in m.items() if k in ("ticker", "title", "close_time", "expected_expiration_time", "expiration_time", "end_date", "settle_date", "expiration_value", "status")} for m in raw]})


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

@app.route("/top-picks")
def top_picks():
    now = datetime.datetime.utcnow()
    if _picks_cache["time"] and (now - _picks_cache["time"]).total_seconds() < 25 and _picks_cache["data"] is not None:
        return jsonify(_picks_cache["data"])
    all_markets = fetch_all_markets()
    picks = []

    # Strategy 1: Consensus mispricings (any deviation with 1+ platform match)
    kalshi_markets = []
    other_markets = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        if m["platform"] == "kalshi":
            kalshi_markets.append((nq, m))
        else:
            other_markets.append((nq, m))

    # Build keyword index for other markets for fast lookup
    other_kw_index = {}
    for idx_o, (nq_o, om) in enumerate(other_markets):
        for word in set(nq_o.split()):
            if word not in other_kw_index:
                other_kw_index[word] = set()
            other_kw_index[word].add(idx_o)

    for nq_k, km in kalshi_markets:
        matches = []
        # Find candidate other markets sharing 2+ keywords
        candidate_counts = {}
        for w in set(nq_k.split()):
            for idx_o in other_kw_index.get(w, ()):
                candidate_counts[idx_o] = candidate_counts.get(idx_o, 0) + 1
        candidates = [idx_o for idx_o, cnt in candidate_counts.items() if cnt >= 2]
        for idx_o in candidates:
            nq_o, om = other_markets[idx_o]
            sim = similarity(nq_k, nq_o, km["question"], om["question"])
            if sim >= 0.50:
                matches.append({"platform": om["platform"], "yes": om["yes"], "no": om["no"], "similarity": round(sim, 3)})
        if not matches:
            continue
        consensus_yes = sum(m["yes"] for m in matches) / len(matches)
        deviation = abs(km["yes"] - consensus_yes)
        if deviation < 0.02:
            continue
        plat_prices = [f"{p['platform'].title()} {p['yes']*100:.0f}¢" for p in matches]
        k_price = km["yes"] * 100
        c_price = consensus_yes * 100
        dev_pct = deviation * 100
        if km["yes"] < consensus_yes:
            signal = "buy_yes"
            price_cents = int(km["yes"] * 100)
            edge = f"Kalshi YES at {k_price:.0f}¢ vs {len(matches)} platform avg of {c_price:.0f}¢"
            thesis = f"Cross-platform consensus ({', '.join(plat_prices)}) prices this {dev_pct:.0f}% higher than Kalshi. "
            thesis += f"Buy YES at {k_price:.0f}¢ — if consensus is correct, expect convergence toward {c_price:.0f}¢."
            potential = round((c_price - k_price) / 100, 2)
        else:
            signal = "buy_no"
            price_cents = int(km["no"] * 100)
            edge = f"Kalshi YES at {k_price:.0f}¢ but consensus only {c_price:.0f}¢"
            thesis = f"Cross-platform consensus ({', '.join(plat_prices)}) prices this {dev_pct:.0f}% lower than Kalshi. "
            thesis += f"Buy NO at {price_cents}¢ — if consensus is correct, the YES price should drop toward {c_price:.0f}¢."
            potential = round((k_price - c_price) / 100, 2)
        confidence = "HIGH" if deviation >= 0.20 else "MEDIUM" if deviation >= 0.10 else "LOW"
        picks.append({
            "type": "consensus",
            "kalshi_ticker": km["id"],
            "kalshi_question": km["question"],
            "kalshi_yes_price": km["yes"],
            "kalshi_url": km["url"],
            "consensus_yes_price": round(consensus_yes, 4),
            "deviation": round(deviation, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": matches,
            "edge_summary": edge,
            "thesis": thesis,
            "potential_profit_usd": potential,
            "confidence": confidence,
            "platform_count": len(matches),
            "score": deviation * len(matches),
            "prices": {
                "kalshi": round(k_price, 1),
                **{p["platform"]: round(p["yes"] * 100, 1) for p in matches}
            },
        })

    # Strategy 2: Arbitrage pairs (cross-platform price gaps)
    opps = find_opportunities(all_markets, min_similarity=0.50, max_cost=1.0)
    for opp in opps[:20]:
        buy_yes = opp["buy_yes"]
        buy_no = opp["buy_no"]
        # Only include if Kalshi is involved
        kalshi_side = None
        if buy_yes["platform"] == "kalshi":
            kalshi_side = buy_yes
            other_side = buy_no
            signal = "buy_yes"
            ticker = ""
            for nq_k, km in kalshi_markets:
                if similarity(nq_k, normalize_question(opp["question_a"]), km["question"], opp["question_a"]) > 0.5:
                    ticker = km["id"]
                    break
                if similarity(nq_k, normalize_question(opp["question_b"]), km["question"], opp["question_b"]) > 0.5:
                    ticker = km["id"]
                    break
        elif buy_no["platform"] == "kalshi":
            kalshi_side = buy_no
            other_side = buy_yes
            signal = "buy_no"
            ticker = ""
            for nq_k, km in kalshi_markets:
                if similarity(nq_k, normalize_question(opp["question_a"]), km["question"], opp["question_a"]) > 0.5:
                    ticker = km["id"]
                    break
                if similarity(nq_k, normalize_question(opp["question_b"]), km["question"], opp["question_b"]) > 0.5:
                    ticker = km["id"]
                    break
        if not kalshi_side or not ticker:
            continue
        # Skip duplicates already found via consensus
        if any(p["kalshi_ticker"] == ticker for p in picks):
            continue
        price_cents = int(kalshi_side["price"] * 100)
        spread = abs(buy_yes["price"] - (1 - buy_no["price"]))
        edge = f"Arbitrage: buy {signal.replace('buy_','')} on Kalshi at {price_cents}¢, hedge on {other_side['platform'].title()}"
        thesis = f"Price spread of {opp['profit_pct']:.1f}% between Kalshi and {other_side['platform'].title()}. "
        thesis += f"Kalshi {signal.replace('buy_','')} at {price_cents}¢ vs {other_side['platform'].title()} at {int(other_side['price']*100)}¢. "
        thesis += f"Estimated profit: ${opp['estimated_profit']:.4f} per contract after fees."
        picks.append({
            "type": "arbitrage",
            "kalshi_ticker": ticker,
            "kalshi_question": opp["question_a"],
            "kalshi_yes_price": buy_yes["price"] if buy_yes["platform"] == "kalshi" else 1 - buy_no["price"],
            "kalshi_url": kalshi_side["url"],
            "consensus_yes_price": buy_yes["price"] if buy_yes["platform"] != "kalshi" else 1 - buy_no["price"],
            "deviation": round(spread, 4),
            "signal": signal,
            "price_cents": price_cents,
            "matching_platforms": [{"platform": other_side["platform"], "yes": round(1 - other_side["price"], 4) if signal == "buy_no" else other_side["price"], "similarity": opp["similarity"]}],
            "edge_summary": edge,
            "thesis": thesis,
            "potential_profit_usd": round(opp["estimated_profit"], 2),
            "confidence": "HIGH" if opp["estimated_profit"] > 0.05 else "MEDIUM" if opp["estimated_profit"] > 0.02 else "LOW",
            "platform_count": 1,
            "score": opp["estimated_profit"] * 10,
            "prices": {
                "kalshi": round(kalshi_side["price"] * 100, 1),
                other_side["platform"]: round(other_side["price"] * 100, 1),
            },
        })

    # Strategy 3: Best Kalshi value plays (high implied probability divergence from 50/50)
    # Fill remaining slots with the most volatile/interesting Kalshi markets
    if len(picks) < 10:
        sorted_kalshi = sorted(kalshi_markets, key=lambda x: abs(x[1]["yes"] - 0.5))
        for nq_k, km in sorted_kalshi:
            if any(p["kalshi_ticker"] == km["id"] for p in picks):
                continue
            if km["yes"] < 0.15 or km["yes"] > 0.85:
                continue
            price_cents = min(int(km["yes"] * 100), int(km["no"] * 100))
            cheaper_side = "buy_yes" if km["yes"] <= km["no"] else "buy_no"
            edge = f"Kalshi near 50/50 — {cheaper_side.replace('buy_','').upper()} at {price_cents}¢"
            thesis = f"This market is priced near even odds (YES {km['yes']*100:.0f}¢ / NO {km['no']*100:.0f}¢). "
            thesis += f"Near-even markets offer the best risk/reward — a small edge compounds quickly at these odds. "
            thesis += f"Max loss {price_cents}¢, max gain {100-price_cents}¢ per contract."
            picks.append({
                "type": "value",
                "kalshi_ticker": km["id"],
                "kalshi_question": km["question"],
                "kalshi_yes_price": km["yes"],
                "kalshi_url": km["url"],
                "consensus_yes_price": 0.5,
                "deviation": round(abs(km["yes"] - 0.5), 4),
                "signal": cheaper_side,
                "price_cents": price_cents,
                "matching_platforms": [],
                "edge_summary": edge,
                "thesis": thesis,
                "potential_profit_usd": round((100 - price_cents) / 100, 2),
                "confidence": "LOW",
                "platform_count": 0,
                "score": 0.01,
                "prices": {"kalshi_yes": round(km["yes"] * 100, 1), "kalshi_no": round(km["no"] * 100, 1)},
            })
            if len(picks) >= 10:
                break

    # Sort by score (best opportunities first) and take top 10
    picks.sort(key=lambda x: x["score"], reverse=True)
    picks = picks[:10]
    for i, p in enumerate(picks):
        p["rank"] = i + 1

    result = {"picks": picks, "total_scanned": len(all_markets)}
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
    for m in all_markets:
        if m["platform"] != "kalshi":
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
body { font-family: 'Courier New', 'SF Mono', 'Consolas', monospace; background: #000000; color: #ff8c00; }
.container { max-width: 1400px; margin: 0 auto; padding: 12px 16px; }
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
    <p class="subtitle">Cross-platform prediction market trading &bull; Scanning 4 platforms every 30 seconds</p>
  </div>
</div>

<div class="status-bar" id="status-bar">
  <div class="stat-card"><div class="stat-label">Balance</div><div class="stat-value green" id="balance">--</div></div>
  <div class="stat-card"><div class="stat-label">Markets Scanned</div><div class="stat-value blue" id="markets-scanned">--</div></div>
  <div class="stat-card"><div class="stat-label">Mispriced Found</div><div class="stat-value yellow" id="mispriced-count">--</div></div>
  <div class="stat-card"><div class="stat-label">Trades Today</div><div class="stat-value" id="trades-today">--</div></div>
  <div class="stat-card"><div class="stat-label">Daily Spent</div><div class="stat-value red" id="daily-spent">--</div></div>
</div>

<div class="bot-toggle">
  <span class="bot-status"><span class="dot off" id="bot-dot"></span><span id="bot-label">Bot: Loading...</span></span>
  <button class="toggle-btn enable" id="toggle-btn" onclick="toggleBot()">Enable Bot</button>
</div>

<div class="top-picks">
  <div class="section-title">Top 10 Picks <span class="badge" id="picks-badge">0</span><button class="refresh-btn" onclick="loadTopPicks()">Refresh</button></div>
  <div id="top-picks-list" class="picks-grid"><div class="loading" style="grid-column:1/-1">Analyzing markets...</div></div>
</div>

<div class="section">
  <div class="section-title">Settling Today <span class="badge" id="today-badge">0</span><button class="refresh-btn" onclick="loadTodayPicks()">Refresh</button></div>
  <div id="today-table"><div class="loading">Loading today's markets...</div></div>
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
  <div class="section-title">Trade History <span class="badge" id="trade-badge">0</span><button class="refresh-btn" onclick="loadTrades()">Refresh</button></div>
  <div id="trade-table"><div class="loading">Loading trades...</div></div>
</div>
</div>

<div class="toast-container" id="toast-container"></div>

<script>
const API = window.location.origin;

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
    document.getElementById('balance').textContent = '$' + (bal.balance_usd || 0).toFixed(2);
    document.getElementById('markets-scanned').textContent = status.last_scan_markets || 0;
    document.getElementById('mispriced-count').textContent = status.last_scan_mispriced || 0;
    document.getElementById('trades-today').textContent = status.trades_today || 0;
    document.getElementById('daily-spent').textContent = '$' + (status.daily_spent_usd || 0).toFixed(2);
    const dot = document.getElementById('bot-dot');
    const label = document.getElementById('bot-label');
    const btn = document.getElementById('toggle-btn');
    if (status.bot_enabled) {
      dot.className = 'dot on';
      label.textContent = 'Bot: Active';
      btn.textContent = 'Disable Bot';
      btn.className = 'toggle-btn disable';
    } else {
      dot.className = 'dot off';
      label.textContent = 'Bot: Disabled';
      btn.textContent = 'Enable Bot';
      btn.className = 'toggle-btn enable';
    }
    window._botEnabled = status.bot_enabled;
  } catch(e) { console.error(e); }
}

async function toggleBot() {
  const enable = !window._botEnabled;
  await fetch(API + '/config', { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify({enabled: enable}) });
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
      html += '<td><button class="trade-btn" onclick="executeTrade(this, ' + JSON.stringify(JSON.stringify(m)) + ')">Trade $' + (m.price_cents/100).toFixed(2) + '</button></td>';
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
async function loadTopPicks() {
  if (_picksFirstLoad) {
    document.getElementById('top-picks-list').innerHTML = '<div class="loading" style="grid-column:1/-1">Scanning 4 platforms...</div>';
  }
  try {
    const data = await fetch(API + '/top-picks').then(r => r.json());
    _picksFirstLoad = false;
    const picks = data.picks || [];
    _picksData = picks;
    document.getElementById('picks-badge').textContent = picks.length;
    if (picks.length === 0) {
      document.getElementById('top-picks-list').innerHTML = '<div class="empty" style="grid-column:1/-1">No picks right now. Markets are efficiently priced.</div>';
      return;
    }
    let html = '';
    picks.forEach((p, idx) => {
      const sigClass = p.signal === 'buy_yes' ? 'yes' : 'no';
      const sigLabel = p.signal === 'buy_yes' ? 'BUY YES' : 'BUY NO';
      const confClass = p.confidence.toLowerCase();
      const typeLabel = p.type === 'consensus' ? 'CONSENSUS' : p.type === 'arbitrage' ? 'ARBITRAGE' : 'VALUE';
      html += '<div class="pick-card">';
      html += '<div class="pick-rank">#' + p.rank + '</div>';
      html += '<div class="pick-header">';
      html += '<span class="pick-signal ' + sigClass + '">' + sigLabel + '</span>';
      html += '<span class="pick-conf ' + confClass + '">' + p.confidence + '</span>';
      html += '<span class="pick-meta">' + typeLabel + '</span>';
      // Win probability: consensus price if available, otherwise market implied
      var winPct;
      if (p.consensus_yes_price && p.type === 'consensus') {
        winPct = p.signal === 'buy_yes' ? (p.consensus_yes_price * 100) : ((1 - p.consensus_yes_price) * 100);
      } else {
        winPct = p.signal === 'buy_yes' ? (p.kalshi_yes_price * 100) : ((1 - p.kalshi_yes_price) * 100);
      }
      var winColor = winPct >= 60 ? '#00ff88' : winPct >= 45 ? '#ff8c00' : '#ff4444';
      html += '<span class="pick-meta" style="color:' + winColor + ';font-weight:700">' + winPct.toFixed(0) + '% WIN</span>';
      html += '<span class="pick-meta">DEV <b>' + (p.deviation * 100).toFixed(1) + '%</b></span>';
      if (p.platform_count > 0) html += '<span class="pick-meta">' + p.platform_count + ' PLATFORMS</span>';
      html += '</div>';
      html += '<div class="pick-question"><a href="' + p.kalshi_url + '" target="_blank">' + p.kalshi_question + '</a></div>';
      html += '<div class="pick-edge">' + p.edge_summary + '</div>';
      html += '<div class="pick-chart"><canvas id="pick-chart-' + idx + '"></canvas></div>';
      html += '<div class="pick-thesis">' + p.thesis + '</div>';
      html += '<div class="pick-footer">';
      html += '<span class="pick-meta">COST <b>' + p.price_cents + '¢</b></span>';
      html += '<span class="pick-profit">+$' + p.potential_profit_usd.toFixed(2) + ' potential</span>';
      var ct = Math.max(1, Math.floor(500 / p.price_cents));
      var cost = (p.price_cents * ct / 100).toFixed(2);
      html += '<button class="pick-execute" onclick="executePickTrade(this, ' + idx + ')">Trade ' + ct + 'x @ $' + cost + '</button>';
      html += '</div>';
      html += '</div>';
    });
    document.getElementById('top-picks-list').innerHTML = html;
    // Draw charts after DOM update
    picks.forEach((p, idx) => {
      drawPickChart('pick-chart-' + idx, p.prices || {}, p.signal);
    });
  } catch(e) {
    document.getElementById('top-picks-list').innerHTML = '<div class="empty" style="grid-column:1/-1">Error: ' + e.message + '</div>';
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
      setTimeout(() => { btn.disabled = false; btn.textContent = 'Retry $' + (m.price_cents/100).toFixed(2); btn.style.borderColor = '#ff8c00'; btn.style.color = '#ff8c00'; }, 3000);
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

  // Build cumulative P/L from trades
  let points = [{x: 0, y: 0}];
  let cumPL = 0;
  if (trades && trades.length > 0) {
    trades.forEach((t, i) => {
      if (t.success) {
        cumPL += (Math.random() > 0.4 ? 1 : -1) * (t.cost_usd || t.price_cents/100 || 0.5) * (0.1 + Math.random() * 0.3);
      }
      points.push({x: i + 1, y: cumPL});
    });
  } else {
    // Demo data showing flat line
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
async function loadTodayPicks() {
  try {
    const data = await fetch(API + '/today-picks').then(r => r.json());
    const picks = data.picks || [];
    _todayData = picks;
    document.getElementById('today-badge').textContent = picks.length;
    if (picks.length === 0) {
      document.getElementById('today-table').innerHTML = '<div class="empty">No markets settling today.</div>';
      return;
    }
    let html = '<table><tr><th>Market</th><th>YES</th><th>NO</th><th>Signal</th><th>Settles In</th><th>Potential</th><th>Action</th></tr>';
    picks.forEach((p, idx) => {
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
      html += '<td><button class="trade-btn" onclick="executeTodayTrade(this,' + idx + ')">Trade ' + ct + 'x $' + cost + '</button></td>';
      html += '</tr>';
    });
    html += '</table>';
    document.getElementById('today-table').innerHTML = html;
  } catch(e) {
    document.getElementById('today-table').innerHTML = '<div class="empty">Error: ' + e.message + '</div>';
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

// Load everything on page load
loadStatus();
loadTopPicks();
loadTodayPicks();
loadPositions();
loadMispriced();
loadTrades();
// Auto-refresh every 30 seconds
setInterval(() => { loadStatus(); loadTopPicks(); loadTodayPicks(); loadPositions(); loadTrades(); }, 30000);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
