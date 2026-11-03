#!/usr/bin/env bash
set -euo pipefail

# Remote Control を常に有効にする（他の設定は残す）
settings="$CLAUDE_CONFIG_DIR/settings.json"
[ -f "$settings" ] || echo '{}' >"$settings"
tmp="$(mktemp)"
jq '.remoteControlAtStartup = true' "$settings" >"$tmp"
cat "$tmp" >"$settings"
rm "$tmp"

./check.sh
