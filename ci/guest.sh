#!/usr/bin/env bash
set -euo pipefail
mkdir -p /tmp/objects
export LEAN_PATH="/tmp/objects:$LEAN_PATH"
mapfile -d '' sources < <(find /proof -type f -name '*.lean' -print0)
pending=("${sources[@]}")
while ((${#pending[@]})); do
  failed=()
  for src in "${pending[@]}"; do
    rel=${src#/proof/}; out="/tmp/objects/${rel%.lean}.olean"
    mkdir -p "$(dirname "$out")"
    if ! lean -R /proof -o "$out" "$src" >/dev/null 2>&1; then failed+=("$src"); fi
  done
  (( ${#failed[@]} < ${#pending[@]} )) || exit 1
  pending=("${failed[@]}")
done
exec lean --run /tools/ExportEntry.lean Main
