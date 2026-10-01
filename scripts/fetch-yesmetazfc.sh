#!/usr/bin/env bash
# Fetch the pinned YesMetaZFC / BMS-Well-Ordering-Lean snapshot into third_party/YesMetaZFC
# and apply the single recorded local change (see third_party-provenance.json):
#   YesMetaZFC/SetTheory/Notation/Surface.lean: `(by native_decide)` -> `(by decide_cbv)`
# The upstream snapshot ships no license file, so it is fetched rather than redistributed here.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dest="$root/third_party/YesMetaZFC"
repo="https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean"
commit="bae7e3d741f24a56d80da9b99c1345562cd10c2d"
file="YesMetaZFC/SetTheory/Notation/Surface.lean"
before="10f6df2712aae0a6aa71d9bfcaf92806ee81d3f515d06051f922162b3f499761"
after="80225f10e73914c1fbb914ce50dc3984bd9b0b7eddda8225839dcae60ab166ad"

sha() { sha256sum "$1" | cut -d' ' -f1; }

if [ -e "$dest" ]; then
  if [ "$(sha "$dest/$file")" = "$after" ]; then
    echo "third_party/YesMetaZFC already present and patched."
    exit 0
  fi
  echo "error: $dest exists but $file is not the patched version; remove it and rerun." >&2
  exit 1
fi

mkdir -p "$root/third_party"
git clone --quiet "$repo" "$dest"
git -C "$dest" -c advice.detachedHead=false checkout --quiet "$commit"
[ "$(sha "$dest/$file")" = "$before" ] || { echo "error: unexpected upstream $file" >&2; exit 1; }
sed -i 's/(by native_decide) : SetTheory.Definitional.Project.Sentence))/(by decide_cbv) : SetTheory.Definitional.Project.Sentence))/' "$dest/$file"
[ "$(sha "$dest/$file")" = "$after" ] || { echo "error: patch did not produce the recorded file" >&2; exit 1; }
echo "Fetched $repo@$commit into third_party/YesMetaZFC and applied the recorded change."
