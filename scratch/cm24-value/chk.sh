#!/bin/bash
# Compile checks for cm24-value (run from the worktree root). One Lean process at a time.
# 1. Self-contained file (verbatim qm-glue copy + proof), import Mathlib only:
#      python3 scratch/cm24-value/mk.py   (in scratch/cm24-value; assembles CM24Value.lean)
#      lake env lean scratch/cm24-value/CM24Value.lean
# 2. Against the build's own statement (import ZInQKernel.OneProof.H.TailZ3). Needs built oleans of the
#    TailZ3 closure; ~/dzq-check2 has them for identical sources (checked by /tmp/cm24_cmp.py-style
#    comparison of all 527 closure files on 2026-11-14):
#      LP="$HOME/dzq-check2/.lake/build/lib/lean:$HOME/dzq-check2/lean/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
#      LEAN_PATH="$LP" lean scratch/cm24-value/CM24Kernel.lean
#    (after `lake build ZInQKernel.OneProof.H.TailZ3`, plain `lake env lean` works too).
set -e
cd "$(git rev-parse --show-toplevel)"
(cd scratch/cm24-value && python3 mk.py && python3 mk_kernel.py)
lake env lean scratch/cm24-value/CM24Value.lean
if [ -d "$HOME/dzq-check2/.lake/build/lib/lean" ]; then
  LP="$HOME/dzq-check2/.lake/build/lib/lean:$HOME/dzq-check2/lean/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
  LEAN_PATH="$LP" lean scratch/cm24-value/CM24Kernel.lean
fi
