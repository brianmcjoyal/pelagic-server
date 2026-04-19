#!/usr/bin/env python3
"""Pre-push JS syntax check for the dashboard.

Renders the Flask dashboard HTML via test_client, extracts every inline
<script> block, and validates each via `node --check`. Catches the kind
of failure that bricks the dashboard but leaves the server healthy
(e.g. an unescaped apostrophe inside a JS string literal).

Exit 0  → all inline JS parses cleanly
Exit 1  → at least one inline script has a syntax error (push aborted)
Exit 2  → setup problem (couldn't import the app or node not installed)

Usage:
    python3 scripts/check_js.py            # called by .git/hooks/pre-push
    python3 scripts/check_js.py --verbose  # show extracted block sizes
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

VERBOSE = "--verbose" in sys.argv or "-v" in sys.argv


def fail(code, msg):
    print(f"check_js: {msg}", file=sys.stderr)
    sys.exit(code)


def main():
    if shutil.which("node") is None:
        fail(2, "node not found on PATH — install with `brew install node` and retry")

    # Stub env vars so the app imports cleanly without real Kalshi creds.
    # The dashboard route doesn't make Kalshi calls during HTML render.
    os.environ.setdefault("KALSHI_PRIVATE_KEY", "stub")
    os.environ.setdefault("KALSHI_API_KEY_ID", "stub")
    os.environ.setdefault("ADMIN_TOKEN", "stub")

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sys.path.insert(0, repo_root)

    try:
        from server import app  # noqa: E402
    except Exception as e:
        fail(2, f"could not import server.py: {type(e).__name__}: {e}")

    with app.test_client() as c:
        rv = c.get("/")
        if rv.status_code != 200:
            fail(1, f"dashboard returned HTTP {rv.status_code}")
        html = rv.get_data(as_text=True)

    # Extract every inline <script> block (skip those with src=).
    pattern = re.compile(r"<script(?![^>]*\bsrc=)[^>]*>(.*?)</script>", re.DOTALL)
    inline = [m.group(1) for m in pattern.finditer(html) if m.group(1).strip()]

    if not inline:
        print("check_js: no inline scripts found — nothing to validate")
        return

    failures = 0
    for i, src in enumerate(inline):
        if VERBOSE:
            print(f"check_js: validating block {i + 1}/{len(inline)} ({len(src)} chars)")
        with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
            f.write(src)
            tmp = f.name
        try:
            res = subprocess.run(
                ["node", "--check", tmp],
                capture_output=True,
                text=True,
                timeout=20,
            )
        finally:
            os.unlink(tmp)
        if res.returncode != 0:
            failures += 1
            print(
                f"check_js: SYNTAX ERROR in inline script #{i + 1}:\n"
                f"{res.stderr.strip()}",
                file=sys.stderr,
            )

    if failures:
        fail(1, f"{failures} inline script block(s) failed validation — push aborted")
    print(f"check_js: {len(inline)} inline script block(s) OK")


if __name__ == "__main__":
    main()
