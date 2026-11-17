#!/bin/bash
# usage: scratch/shimura-cft/run.sh <file.lean>   (one Lean process; checks load first)
cd ~/dzq-wt/shimura-cft
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
/usr/bin/time -f "%e s, %M KB" lake env lean "$1" 2>&1
