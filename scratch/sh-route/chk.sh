#!/bin/bash
# Re-check the deliverable in a built worktree (kernel modules built with `lake build`), one Lean process.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
scratch/sh-route/mk.sh
/usr/bin/time -f "%e s %M KB" lake env lean scratch/sh-route/ShRoute.lean 2>&1 | grep "depends on axioms\|error\| s .*KB\|sorry"
