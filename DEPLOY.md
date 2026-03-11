# Deploying Pelagic Server to Railway
### Takes about 5 minutes. Free tier, no credit card needed.

---

## Step 1 — Get your Kalshi credentials

1. Go to https://kalshi.com/account/api
2. Click **Create API Key**
3. Download the **private key** `.pem` file
4. Copy your **Key ID** (looks like: `abc123-def4-...`)

---

## Step 2 — Create a Railway account

1. Go to https://railway.app
2. Sign up with GitHub (easiest) or email
3. Click **New Project → Deploy from GitHub repo**

   OR if you don't want to use GitHub:
   Click **New Project → Empty Project**

---

## Step 3 — Upload the server files

### Option A: GitHub (recommended)
1. Create a new repo on github.com called `pelagic-server`
2. Upload all 4 files from this folder:
   - `server.py`
   - `requirements.txt`
   - `Procfile`
   - `railway.toml`
3. In Railway, connect to that repo — it auto-deploys

### Option B: Railway CLI
```bash
npm install -g @railway/cli
railway login
railway init
railway up
```

---

## Step 4 — Add your environment variables

In your Railway project dashboard:
1. Click your service → **Variables** tab
2. Add these two variables:

| Variable | Value |
|---|---|
| `KALSHI_API_KEY_ID` | Your Key ID from Step 1 |
| `KALSHI_PRIVATE_KEY` | The full contents of your .pem file |

**For the private key:** Open the .pem file in a text editor,
select ALL the text including the `-----BEGIN...` lines,
and paste it as the variable value.

Railway will keep this secret and encrypted.

---

## Step 5 — Get your server URL

1. In Railway, click **Settings → Networking → Generate Domain**
2. You'll get a URL like: `https://pelagic-server-production.up.railway.app`
3. Test it by visiting: `https://YOUR-URL/health`
   You should see: `{"status": "ok", "kalshi_key_set": true}`

---

## Step 6 — Connect your HTML file

Open `prediction-market-finder.html` in a text editor.

Find this line near the top of the `<script>` section:
```
const KALSHI_PROXY = "";
```

Replace it with your Railway URL:
```
const KALSHI_PROXY = "https://pelagic-server-production.up.railway.app";
```

Save the file, open it in your browser, and hit **Scan**.
Kalshi markets will now appear alongside Polymarket and Manifold.

---

## Troubleshooting

**"kalshi_key_set: false" on /health**
→ The environment variable wasn't saved. Re-add it in Railway Variables.

**Markets list is empty**
→ Check Railway logs (click your service → Logs tab) for error messages.

**CORS error in browser console**
→ The server already has CORS enabled. Make sure you're using the https:// URL.

**Private key format error**
→ Make sure the full PEM is pasted including `-----BEGIN RSA PRIVATE KEY-----`
  and `-----END RSA PRIVATE KEY-----` lines.
