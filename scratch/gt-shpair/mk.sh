#!/bin/bash
# usage: scratch/gt-shpair/mk.sh Name [o]   (run from the worktree root; compiles scratch/gt-shpair/Name.lean,
# with o: also writes scratch/gt-shpair/build/Name.olean so later scratch files can import Name)
cd ~/dzq-wt/gt-shpair
D=scratch/gt-shpair
LP=$(lake env printenv LEAN_PATH):$PWD/$D/build
if [ "$2" = "o" ]; then
  LEAN_PATH=$LP lean --root=$D -o $D/build/$1.olean -i $D/build/$1.ilean $D/$1.lean
else
  LEAN_PATH=$LP lean $D/$1.lean
fi
