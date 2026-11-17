#!/bin/bash
# usage: scratch/c-to-printed/run.sh FILE.lean  -- compiles against ~/ctp-lib (copy of ~/dzq-check2 build at e38375b3)
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
P=$HOME/dzq-wt/c-to-printed/.lake/packages
LP=$HOME/ctp-lib:$HOME/ctp-lib-zinq
for d in $P/*/; do LP="$LP:$d.lake/build/lib/lean"; done
export LEAN_PATH="$LP"
cd "$(dirname "$0")/../.."
exec lean "$@"
