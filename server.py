"""
Pelagic — Kalshi API Proxy Server
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
CORS(app)

KALSHI_API_KEY_ID  = os.environ.get("KALSHI_API_KEY_ID", "b5321140-8a40-47f5-a99e-edff618c887c")
KALSHI_BASE        = "https://trading-api.kalshi.com/trade-api/v2"

PRIVATE_KEY_PEM = """-----BEGIN RSA PRIVATE KEY-----
MIIEpAIBAAKCAQEA4oW7ktFaur26QL9GG4/2fddvEJXlSyAlQmthV/F9jX9jK/0D
7urdNrEhCu0tV17ftpL4/Wi+gFUg40roALGo3s1X6bqYUkGcC7LlEaBS14tUXdyI
b8tF6RvfRnD90ixZ8+JC/9gHqEO8lWFbwBnz0MEa2XcNXSBXWgWkqq744bwatUiV
MZUmVm1j7CW+GLu6OIusmsBXs/UF+FSIP7pCz4Z8Ml3KMHFhY47gMX8XGm9ICSQ7
zw1pE/ehMAPyh83BIXuiEQSUlt0C69GI0g+qpOy/juiw4J5U4QSJMS2KPT8tssCC
31IBbU+hP+W0Bp7PIR1amLf48TF07vgc8KzsOwIDAQABAoIBAAyxQeV/Y4vraU4d
crgOEpBki7a+n2e4E4eHEZ/4k1P2gAkNFv5Uiljm4napROixE36BjEkusXFYQXp/
crHmHe82AgMvqqz9ziHZG49MRtya+LHsii7V/x5kz0U0KZS5WgmHTsDlJlVCl4Sm
quNJGiBnmGiKsQluXg19G77HcspNZjj0PGrs6eOG99cSqD2JYXjIA9ExRKjjIVPi
240TMDtGvB01wXiZ3rPMig4nYgrduMBMshqQ2KFlZPD3dYqD+2pu0VIMMaZm/WSc
86o+xqiMHKG05+i5PAFhBWat3HheMdsgj2jmet70d35cp2j/zHuUQ8QhmS9NXiS5
l6YNEBkCgYEA7tXewKaN9HHWHIXWoUCJFlJJDnMsNUcgp3nKwo32iBRBbPEd7cx5
5Ez8AtuQ6SQzTuKRtNUhTikzFRuEU995ZVzmvLoVqsumKgJBQMGLQBSf43cXhI1b
eO+z2b89tY9Uw3c3ZIOA/0JowBI8+OzpjDZcVHYNG6O7d67vSNN/9XcCgYEA8s1T
U5c3BZBbP9kGEgFiqaUA+aKHRIEkFkycJ/70yWimpugfxlsb9TLe5yWbn9jpOrru
vaTLgU9kr87qd0pwIR6Q8wXcGgEbwLWcz4ZuyCCVo4IBAP0qDMT5pdDHi6mtML7t
dZ5XX5WAQlT1JLYm2gz4qV5B7DpzP9IS8OGFQF0CgYBp74kvMHE0pK2Q1zidK6/i
q7rl4uYP962fO2FZLHjWYQ2oEcbxrEnAnvkFF3jOQJVVfx+b8xEjxxh2W081mKES
+cMKoQttR4k7huaEn5RxZvSIg1F2JPEW0lOW2MG5X4r8bEuwlLfKAR3PXAeZbhQl
chNAD2C/Cr/jVT+jsNRH/wKBgQC0o5nY2OmwlAOvbtEbWDiFKiOdlhO5HbMxe/G5
t+96YQeLqarqMiKMvDomEk7ED+cFMMoqAY7+N4kbW4AJHDJsEYeZpsRn/Gcfan6t
zsBg2A08Rp5kk/VS5sEtYjTzbVtSptmX5iPvExUHRJnVpEcndvsRVvUIwTu5QZuh
5sbyaQKBgQDBhrP6PXifTMrFVtI2H4MRXlCyy8l+Cj3pCtsIR5v4KNna6broXeXt
/kEJ2GMvWq4/LMHyEPI4yx9xcGpAGVySzjCexfC/pZHda3WMjH1RaTLtFsWx9rvY
aJAsTvQqOe5yY1rOZzlIjxak2ucwFpYulsTNzxHcuuyfIdqma/egcw==
-----END RSA PRIVATE KEY-----"""

def load_private_key():
    try:
        key = serialization.load_pem_private_key(PRIVATE_KEY_PEM.strip().encode(), password=None, backend=default_backend())
        return key
    except Exception as e:
        print(f"Key load error: {e}")
        return None

def signed_headers(method: str, path: str) -> dict:
    key = load_private_key()
    if not key:
        return {}
    ts = str(int(time.time() * 1000))
    message = f"{ts}{method.upper()}{path}".encode('utf-8')
    sig = key.sign(
        message,
        padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=hashes.SHA256.digest_size),
        hashes.SHA256()
    )
    return {
        "KALSHI-ACCESS-KEY":       KALSHI_API_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": ts,
        "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode(),
        "Content-Type":            "application/json",
    }

@app.route("/health")
def health():
    key = load_private_key()
    return jsonify({"status": "ok", "private_key_loaded": key is not None})

@app.route("/markets")
def markets():
    path = "/markets"
    headers = signed_headers("GET", path)
    if not headers:
        return jsonify({"error": "Failed to load private key", "markets": []})
    try:
        resp = requests.get(KALSHI_BASE + path, headers=headers, params={"limit": 200, "status": "open"}, timeout=10)
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
        resp = requests.get(KALSHI_BASE + path, headers=headers, timeout=10)
        resp.raise_for_status()
        return jsonify({"balance_usd": resp.json().get("balance", 0) / 100})
    except Exception as e:
        return jsonify({"error": str(e)})

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
