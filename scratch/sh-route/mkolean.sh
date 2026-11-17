#!/bin/bash
# compile a development part to an olean in scratch/sh-route/olean (one Lean process)
# usage: mkolean.sh Name "import lines"   (Name.lean in scratch/sh-route, its own import lines stripped)
cd "$(dirname "$0")/../.."
D=$PWD/scratch/sh-route/olean
{ echo "$2" | tr ';' '\n'; grep -v '^import' scratch/sh-route/$1.lean; } > $D/$1.lean
start=$(date +%s)
LEAN_PATH=$D:$(cat /tmp/shroute_lp.txt) ~/.elan/bin/lean -o $D/$1.olean -i $D/$1.ilean $D/$1.lean 2>&1 | grep -E "error" | head
echo "exit ${PIPESTATUS[0]} in $(( $(date +%s)-start ))s"
