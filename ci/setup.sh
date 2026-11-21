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
targets=(PoissonDAG.V2.Lower99)
roots=(formal/starter-cache-roots.txt)
if [[ ${FTS_BUILD_GRSCC:-false} == true ]]; then
  targets+=(PoissonDAG.Constructions.GRSCC.Circuit)
  roots+=(formal/grscc-cache-roots.txt)
fi
if [[ ${FTS_BUILD_FORS:-false} == true ]]; then
  targets+=(PoissonDAG.Constructions.FORS.Components)
  roots+=(formal/fors-cache-roots.txt)
fi
if [[ ${FTS_BUILD_PORS:-false} == true ]]; then
  targets+=(PoissonDAG.Constructions.PORS.{LiteralAssembly,SingleRefinedSupport,BucketRefinedSupport,ChainRefinedSupport,ChainRefinedCoefficients})
  roots+=(formal/pors-cache-roots.txt)
fi
cat "${roots[@]}" | xargs lake exe cache get
lake build "${targets[@]}"
python3 - <<'PROBE'
import re
from pathlib import Path
p = Path('formal/PoissonDAG/Constructions/GRSCC/AuthCore.lean')
s = p.read_text().replace('namespace PoissonDAG.GRSCC', 'set_option Elab.async false\nnamespace PoissonDAG.GRSCC')
# Insert markers before docs and scoped options, keeping each attached to its declaration.
starts = list(re.finditer(r'(?m)^(?:private )?(?:theorem|def) ([A-Za-z_.]+)', s))
for m in reversed(starts):
    begin = s.rfind('\n\n', 0, m.start()) + 2
    if begin < s.index('namespace PoissonDAG.GRSCC') + len('namespace PoissonDAG.GRSCC'):
        begin = m.start()
    s = s[:begin] + 'run_cmd do\n  let h ← IO.FS.Handle.mk "build/profile-progress" .append\n  h.putStrLn "' + m[1] + '"\n  h.flush\n' + s[begin:]
Path('build/AuthProfile.lean').write_text(s)
PROBE
libs=$(lake env printenv LEAN_PATH)
probe_status=0
docker run --rm --network=none --memory=5g --memory-swap=5g \
  -e LEAN_NUM_THREADS=1 -e LEAN_PATH="$libs" -v "$PWD:$PWD" -v "$tool:$tool:ro" -w "$PWD" \
  ubuntu@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a \
  /usr/bin/timeout --signal=KILL 65s "$tool/$release/bin/lean" -j1 build/AuthProfile.lean || probe_status=$?
cat build/profile-progress
exit "$probe_status"
