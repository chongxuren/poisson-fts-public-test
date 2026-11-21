#!/usr/bin/env bash
set -euo pipefail
mkdir -p build
tool="$RUNNER_TEMP/fts-lean"
mkdir -p "$tool"
release=lean-4.32.0-linux
curl -fsSL --retry 3 "https://github.com/leanprover/lean4/releases/download/v4.32.0/$release.tar.zst" -o "$tool/release.tar.zst"
echo "fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516  $tool/release.tar.zst" | sha256sum -c -
tar --zstd -xf "$tool/release.tar.zst" -C "$tool"
rm "$tool/release.tar.zst"
export PATH="$tool/$release/bin:$PATH" MATHLIB_NO_CACHE_ON_UPDATE=1
echo "$tool/$release/bin" >> "$GITHUB_PATH"
xargs lake exe cache get < formal/starter-cache-roots.txt
lake build PoissonDAG.V2.Lower99
# Mathlib cache files can be owner-only. Both containers use an unprivileged UID.
find .lake -type d -path "*/build/lib/lean" -prune -exec chmod -R a+rX {} +
mkdir -p build/lib/Export
export LEAN_PATH="$PWD/build/lib"
lean -o build/lib/Export.olean judge/vendor/Export.lean
lean -o build/lib/Export/Parse.olean judge/vendor/Export/Parse.lean
lean -o build/lib/ExportEntry.olean judge/ExportEntry.lean
lean -o build/lib/Replay.olean judge/Replay.lean
image=ubuntu@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a
docker pull "$image"
echo "JUDGE_IMAGE=$image" >> "$GITHUB_ENV"
