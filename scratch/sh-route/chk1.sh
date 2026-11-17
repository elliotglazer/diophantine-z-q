#!/bin/bash
# check one development file in scratch/sh-route/olean against the olean prefix (one Lean process)
cd "$(dirname "$0")/../.."
D=$PWD/scratch/sh-route/olean
L=$(uptime | sed 's/.*load average: \([0-9]*\).*/\1/'); M=$(free -g | awk '/Mem/{print $7}')
if [ "$L" -gt 150 ] || [ "$M" -lt 20 ]; then echo "BLOCKED load=$L avail=$M"; exit 1; fi
start=$(date +%s)
LEAN_PATH=$D:$(cat /tmp/shroute_lp.txt) timeout 1500 ~/.elan/bin/lean "$PWD/scratch/sh-route/$1" 2>&1 | grep -v "^warning\|linter\|^$\|Note:\|difference between\|goal is a prop\|But this is not\|Try this\|letI̵\|haveI̵\|Hint:\|\[apply\]\|binding can be removed" 
echo "exit ${PIPESTATUS[0]} in $(( $(date +%s)-start ))s"
