"""
Pelagic — Kalshi API Proxy Server
"""

import os
import base64
import datetime
import requests
from flask import Flask, jsonify
from flask_cors import CORS
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.backends import default_backend

app = Flask(__name__)
CORS(app)

KALSHI_API_KEY_ID = os.environ.get("KALSHI_API_KEY_ID", "b5321140-8a40-47f5-a99e-edff618c887c")
KALSHI_BASE_URL   = "https://trading-api.kalshi.com"
KALSHI_API_PREFIX  = "/trade-api/v2"

PRIVATE_KEY_PEM = os.environ.get("KALSHI_PRIVATE_KEY", "")


def load_private_key():
    pem = PRIVATE_KEY_PEM.strip()
    if not pem:
        print("KALSHI_PRIVATE_KEY environment variable is not set")
        return None
    try:
        key = serialization.load_pem_private_key(pem.encode(), password=None, backend=default_backend())
        return key
    except Exception as e:
        print(f"Key load error: {e}")
        return None


def sign_pss_text(private_key, text):
    message = text.encode("utf-8")
    signature = private_key.sign(
        message,
        padding.PSS(
            mgf=padding.MGF1(hashes.SHA256()),
            salt_length=padding.PSS.DIGEST_LENGTH
        ),
        hashes.SHA256()
    )
    return base64.b64encode(signature).decode("utf-8")


def signed_headers(method, path):
    """Sign with the full API path (e.g. /trade-api/v2/markets)."""
    key = load_private_key()
    if not key:
        return {}
    full_path = KALSHI_API_PREFIX + path
    ts = str(int(datetime.datetime.now().timestamp() * 1000))
    msg_string = ts + method.upper() + full_path.split("?")[0]
    sig = sign_pss_text(key, msg_string)
    return {
        "KALSHI-ACCESS-KEY":       KALSHI_API_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": ts,
        "KALSHI-ACCESS-SIGNATURE": sig,
        "Content-Type":            "application/json",
    }


@app.route("/health")
def health():
    k = load_private_key()
    return jsonify({"status": "ok", "private_key_loaded": k is not None})


@app.route("/markets")
def markets():
    path = "/markets"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"error": "Failed to load private key", "markets": []})
    try:
        resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + path, headers=headers, params={"limit": 200, "status": "open"}, timeout=10)
        resp.raise_for_status()
        raw = resp.json().get("markets", [])
    except Exception as e:
        return jsonify({"error": str(e), "markets": []})
    normalized = []
    for m in raw:
        try:
            yes = (m.get("yes_ask") or m.get("last_price") or 50) / 100
            no  = (m.get("no_ask")  or (100 - (m.get("last_price") or 50))) / 100
            normalized.append({
                "platform": "kalshi",
                "id":       m["ticker"],
                "question": m.get("title") or m["ticker"],
                "yes":      round(yes, 4),
                "no":       round(no,  4),
                "volume":   m.get("volume", 0),
                "url":      f"https://kalshi.com/markets/{m['ticker']}",
            })
        except Exception:
            continue
    return jsonify({"markets": normalized})


@app.route("/balance")
def balance():
    path = "/portfolio/balance"
    headers = signed_headers("GET", path)
    try:
        resp = requests.get(KALSHI_BASE_URL + KALSHI_API_PREFIX + path, headers=headers, timeout=10)
        resp.raise_for_status()
        return jsonify({"balance_usd": resp.json().get("balance", 0) / 100})
    except Exception as e:
        return jsonify({"error": str(e)})


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
