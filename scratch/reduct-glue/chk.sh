#!/bin/bash
# Re-check the deliverable in a built worktree (kernel modules built with `lake build`).
# ReductGlue.lean = Base.lean (verbatim reduct-split Reduction.lean) + Body.lean, assembled by mk.sh.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
scratch/reduct-glue/mk.sh
/usr/bin/time -f "%e s %M KB" lake env lean scratch/reduct-glue/ReductGlue.lean 2>&1 | grep "depends on axioms\|error\| s .*KB"
