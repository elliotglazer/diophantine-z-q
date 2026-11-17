#!/bin/bash
# Check the deliverable in a built worktree (kernel modules imported by RBBase built with `lake build`).
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
scratch/reduct-b/mk.sh
/usr/bin/time -f "%e s %M KB" lake env lean scratch/reduct-b/ReductB.lean 2>&1 | grep "depends on axioms\|error\| s .*KB"
