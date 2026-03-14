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

TIMEOUT = 15

# ---------------------------------------------------------------------------
# Bot configuration and state
# ---------------------------------------------------------------------------
BOT_CONFIG = {
    "enabled": False,
    "max_bet_usd": 5.0,
    "max_daily_usd": 20.0,
    "min_deviation": 0.15,
    "min_platforms": 2,
    "scan_interval_minutes": 10,
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


def fetch_all_markets():
    all_markets = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {pool.submit(fn): name for name, fn in ALL_FETCHERS.items()}
        for future in as_completed(futures):
            try:
                all_markets.extend(future.result())
            except Exception:
                continue
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

def find_opportunities(all_markets, min_similarity=0.55, max_cost=0.98):
    entries = []
    for m in all_markets:
        nq = normalize_question(m["question"])
        if len(nq.split()) < 3:
            continue
        entries.append((nq, m))

    opportunities = []
    seen = set()

    for i, (nq_a, a) in enumerate(entries):
        for j, (nq_b, b) in enumerate(entries):
            if j <= i:
                continue
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
        "time_in_force": "fill_or_kill",
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

    if not BOT_CONFIG["enabled"]:
        return

    try:
        all_markets = fetch_all_markets()
        BOT_STATE["last_scan_markets"] = len(all_markets)

        mispricings = find_consensus_mispricings(all_markets)
        BOT_STATE["last_scan_mispriced"] = len(mispricings)

        for opp in mispricings:
            if BOT_STATE["daily_spent_usd"] >= BOT_CONFIG["max_daily_usd"]:
                break

            cost_usd = opp["price_cents"] / 100.0
            if cost_usd > BOT_CONFIG["max_bet_usd"]:
                continue
            if BOT_STATE["daily_spent_usd"] + cost_usd > BOT_CONFIG["max_daily_usd"]:
                continue

            side = opp["signal"].replace("buy_", "")
            result = place_kalshi_order(opp["kalshi_ticker"], side, opp["price_cents"], count=1)

            trade_record = {
                "timestamp": now.isoformat(),
                "ticker": opp["kalshi_ticker"],
                "question": opp["kalshi_question"],
                "side": side,
                "price_cents": opp["price_cents"],
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
    minutes=BOT_CONFIG["scan_interval_minutes"],
    id="consensus_scan",
    replace_existing=True,
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


# ---------------------------------------------------------------------------
# Bot endpoints (NEW)
# ---------------------------------------------------------------------------

@app.route("/status")
def status():
    return jsonify({
        "bot_enabled": BOT_CONFIG["enabled"],
        "config": BOT_CONFIG,
        "last_scan": BOT_STATE["last_scan"],
        "last_scan_markets": BOT_STATE["last_scan_markets"],
        "last_scan_mispriced": BOT_STATE["last_scan_mispriced"],
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
    result = place_kalshi_order(ticker, side, int(price_cents), count=1)
    trade_record = {
        "timestamp": datetime.datetime.utcnow().isoformat(),
        "ticker": ticker,
        "question": data.get("question", ""),
        "side": side,
        "price_cents": int(price_cents),
        "cost_usd": int(price_cents) / 100.0,
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
<title>Pelagic Trading Bot</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #0a0e17; color: #e0e6ed; }
.container { max-width: 1200px; margin: 0 auto; padding: 20px; }
h1 { font-size: 28px; margin-bottom: 5px; color: #fff; }
h1 span { color: #00d4aa; }
.subtitle { color: #6b7280; margin-bottom: 20px; font-size: 14px; }

/* Status bar */
.status-bar { display: flex; gap: 15px; flex-wrap: wrap; margin-bottom: 25px; }
.stat-card { background: #151b28; border: 1px solid #1e293b; border-radius: 10px; padding: 15px 20px; flex: 1; min-width: 150px; }
.stat-label { font-size: 11px; color: #6b7280; text-transform: uppercase; letter-spacing: 1px; }
.stat-value { font-size: 24px; font-weight: 700; margin-top: 4px; }
.stat-value.green { color: #00d4aa; }
.stat-value.red { color: #ef4444; }
.stat-value.blue { color: #3b82f6; }
.stat-value.yellow { color: #f59e0b; }

/* Bot toggle */
.bot-toggle { display: flex; align-items: center; gap: 12px; margin-bottom: 25px; }
.toggle-btn { padding: 10px 24px; border: none; border-radius: 8px; font-weight: 600; cursor: pointer; font-size: 14px; }
.toggle-btn.enable { background: #00d4aa; color: #000; }
.toggle-btn.disable { background: #ef4444; color: #fff; }
.toggle-btn:hover { opacity: 0.85; }
.bot-status { font-size: 14px; }
.bot-status .dot { display: inline-block; width: 10px; height: 10px; border-radius: 50%; margin-right: 6px; }
.dot.on { background: #00d4aa; box-shadow: 0 0 8px #00d4aa; }
.dot.off { background: #6b7280; }

/* Sections */
.section { margin-bottom: 30px; }
.section-title { font-size: 18px; font-weight: 600; margin-bottom: 12px; display: flex; align-items: center; gap: 8px; }
.badge { background: #1e293b; padding: 2px 10px; border-radius: 12px; font-size: 12px; color: #6b7280; }
.refresh-btn { background: #1e293b; border: 1px solid #334155; color: #e0e6ed; padding: 6px 14px; border-radius: 6px; cursor: pointer; font-size: 12px; margin-left: auto; }
.refresh-btn:hover { background: #334155; }

/* Table */
table { width: 100%; border-collapse: collapse; }
th { text-align: left; padding: 10px 12px; font-size: 11px; color: #6b7280; text-transform: uppercase; letter-spacing: 1px; border-bottom: 1px solid #1e293b; }
td { padding: 12px; border-bottom: 1px solid #1e293b; font-size: 13px; }
tr:hover { background: #151b28; }
.confidence { display: inline-block; padding: 3px 10px; border-radius: 12px; font-size: 12px; font-weight: 600; }
.conf-high { background: rgba(0,212,170,0.15); color: #00d4aa; }
.conf-med { background: rgba(245,158,11,0.15); color: #f59e0b; }
.conf-low { background: rgba(239,68,68,0.15); color: #ef4444; }
.trade-btn { background: #3b82f6; color: #fff; border: none; padding: 6px 16px; border-radius: 6px; cursor: pointer; font-size: 12px; font-weight: 600; }
.trade-btn:hover { background: #2563eb; }
.trade-btn:disabled { background: #334155; color: #6b7280; cursor: not-allowed; }
.side-yes { color: #00d4aa; font-weight: 600; }
.side-no { color: #ef4444; font-weight: 600; }
.result-win { color: #00d4aa; }
.result-loss { color: #ef4444; }
.result-pending { color: #f59e0b; }
.empty { text-align: center; padding: 40px; color: #6b7280; }
.loading { text-align: center; padding: 20px; color: #6b7280; }
a { color: #3b82f6; text-decoration: none; }
a:hover { text-decoration: underline; }
</style>
</head>
<body>
<div class="container">
<h1><span>Pelagic</span> Trading Bot</h1>
<p class="subtitle">Cross-platform prediction market trading &bull; Scanning 4 platforms every 10 minutes</p>

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

<div class="section">
  <div class="section-title">Mispriced Opportunities <span class="badge" id="opp-badge">0</span><button class="refresh-btn" onclick="loadMispriced()">Refresh</button></div>
  <div id="opp-table"><div class="loading">Loading opportunities...</div></div>
</div>

<div class="section">
  <div class="section-title">Trade History <span class="badge" id="trade-badge">0</span><button class="refresh-btn" onclick="loadTrades()">Refresh</button></div>
  <div id="trade-table"><div class="loading">Loading trades...</div></div>
</div>
</div>

<script>
const API = window.location.origin;

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

async function loadMispriced() {
  document.getElementById('opp-table').innerHTML = '<div class="loading">Scanning markets...</div>';
  try {
    const data = await fetch(API + '/mispriced').then(r => r.json());
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
    } else {
      btn.textContent = 'Failed';
      btn.style.background = '#ef4444';
    }
    loadStatus();
    loadTrades();
  } catch(e) {
    btn.textContent = 'Error';
    btn.style.background = '#ef4444';
  }
}

async function loadTrades() {
  try {
    const data = await fetch(API + '/trades').then(r => r.json());
    document.getElementById('trade-badge').textContent = data.total;
    if (!data.trades || data.trades.length === 0) {
      document.getElementById('trade-table').innerHTML = '<div class="empty">No trades yet. Enable the bot or click Trade on an opportunity.</div>';
      return;
    }
    let html = '<table><tr><th>Time</th><th>Market</th><th>Side</th><th>Price</th><th>Deviation</th><th>Result</th><th>Source</th></tr>';
    data.trades.slice().reverse().forEach(t => {
      const time = new Date(t.timestamp + 'Z').toLocaleString();
      const sideClass = t.side === 'yes' ? 'side-yes' : 'side-no';
      const resultClass = t.success ? 'result-win' : 'result-loss';
      const resultLabel = t.success ? 'Filled' : 'Failed';
      const source = t.manual ? 'Manual' : 'Auto';
      html += '<tr>';
      html += '<td>' + time + '</td>';
      html += '<td>' + (t.question || t.ticker).substring(0, 50) + '</td>';
      html += '<td class="' + sideClass + '">' + t.side.toUpperCase() + '</td>';
      html += '<td>' + t.price_cents + '¢</td>';
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

// Load everything on page load
loadStatus();
loadMispriced();
loadTrades();
// Auto-refresh every 60 seconds
setInterval(() => { loadStatus(); loadTrades(); }, 60000);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
