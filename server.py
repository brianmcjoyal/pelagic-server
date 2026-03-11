"""
Pelagic — Kalshi API Proxy Server
Handles RSA request signing so your browser can fetch Kalshi data securely.
Deploy this to Railway, then point your HTML file at its URL.
"""

import os
import time
import base64
import requests
from flask import Flask, jsonify
from flask_cors import CORS
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.backends import default_backend

app = Flask(__name__)
CORS(app)  # Allow your browser to call this server from anywhere

# ── CONFIG (set these as Railway environment variables) ────────────────────
KALSHI_API_KEY_ID    = os.environ.get("KALSHI_API_KEY_ID", "")
KALSHI_PRIVATE_KEY   = os.environ.get("KALSHI_PRIVATE_KEY", "")  # Full PEM string
KALSHI_BASE          = "https://trading-api.kalshi.com/trade-api/v2"


# ── SIGNING ────────────────────────────────────────────────────────────────
def load_private_key():
    """Load RSA private key from environment variable (PEM string)."""
    if not KALSHI_PRIVATE_KEY:
        return None
    try:
        pem = KALSHI_PRIVATE_KEY.replace("\\n", "\n").encode()
        return serialization.load_pem_private_key(pem, password=None, backend=default_backend())
    except Exception as e:
        print(f"Key load error: {e}")
        return None


def signed_headers(method: str, path: str) -> dict:
    """Generate Kalshi RSA auth headers."""
    key = load_private_key()
    if not key:
        return {}
    ts = str(int(time.time() * 1000))
    message = f"{ts}{method.upper()}{path}".encode()
    sig = key.sign(message, padding.PKCS1v15(), hashes.SHA256())
    return {
        "KALSHI-ACCESS-KEY":       KALSHI_API_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": ts,
        "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode(),
        "Content-Type":            "application/json",
    }


# ── ROUTES ─────────────────────────────────────────────────────────────────
@app.route("/health")
def health():
    return jsonify({"status": "ok", "kalshi_key_set": bool(KALSHI_API_KEY_ID)})


@app.route("/markets")
def markets():
    """
    Fetch open Kalshi markets and return them in a normalized format
    that matches Polymarket / Manifold so the frontend can treat all
    three platforms identically.
    """
    path = "/markets"
    params = {"limit": 200, "status": "open"}
    headers = signed_headers("GET", path)

    try:
        resp = requests.get(
            KALSHI_BASE + path,
            headers=headers,
            params=params,
            timeout=10
        )
        resp.raise_for_status()
        raw = resp.json().get("markets", [])
    except Exception as e:
        return jsonify({"error": str(e), "markets": []}), 200

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
    """Return Kalshi account balance in USD."""
    path = "/portfolio/balance"
    headers = signed_headers("GET", path)
    try:
        resp = requests.get(KALSHI_BASE + path, headers=headers, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        return jsonify({"balance_usd": data.get("balance", 0) / 100})
    except Exception as e:
        return jsonify({"error": str(e)}), 200


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
