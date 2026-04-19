#!/usr/bin/env bash
# One-time setup: point git at the tracked .githooks directory so the
# pre-push JS validator runs on every push. Safe to re-run.
set -e
cd "$(git rev-parse --show-toplevel)"
chmod +x .githooks/pre-push scripts/check_js.py
git config core.hooksPath .githooks
echo "Hooks installed. Test with: python3 scripts/check_js.py"
