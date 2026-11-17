#!/bin/bash
# compile a test file against the private olean of RBBase (in /tmp/rblib)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
lake env bash -c "LEAN_PATH=\$LEAN_PATH:/tmp/rblib /usr/bin/time -f '%e s %M KB' lean $1" 2>&1 | grep -v "linter\|^Note\|set_option\|^$" 
