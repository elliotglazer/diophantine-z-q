#!/bin/bash
# usage: scratch/r1univ-rigid/check.sh FILE.lean  (from repo root). Uses ~/dzq-check2's build (same commit df98652a).
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
P=$HOME/dzq-wt/r1univ-rigid/.lake/packages
LP=$HOME/dzq-check2/.lake/build/lib/lean:$HOME/dzq-check2/lean/.lake/build/lib/lean
for d in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient Cli; do LP=$LP:$P/$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
uptime; free -g | sed -n 2p
/usr/bin/time -f "%e s %M KB" lean "$@"
