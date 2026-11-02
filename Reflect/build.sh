#!/bin/bash
# Compile Reflect modules (and test files) against the main tree's build, without
# writing to the main tree. Usage: Reflect/build.sh Reflect/Core.lean [more ...]
# A file under Reflect/ is compiled to .rbuild/<module>.olean; other files are only checked.
set -e
WT=/home/byhoson/workspace/conPanna-reflection
MAIN=/home/byhoson/workspace/conPanna
cd "$MAIN"
LP=$(lake env printenv LEAN_PATH)
for f in "$@"; do
  rel=${f#$WT/}
  if [[ $rel == Reflect/*.lean ]]; then
    mod=${rel%.lean}
    mkdir -p "$WT/.rbuild/$(dirname "$mod")"
    LEAN_PATH="$WT/.rbuild:$LP" systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
      lean -j 2 -R "$WT" -o "$WT/.rbuild/$mod.olean" -i "$WT/.rbuild/$mod.ilean" "$WT/$rel"
  else
    LEAN_PATH="$WT/.rbuild:$LP" systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
      lean -j 2 "$WT/$rel"
  fi
done
