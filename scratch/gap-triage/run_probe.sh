#!/bin/bash
# Compile a probe against the main checkout's build (~/dzq at e38375b3, `lake build ZInQKernel.OneProof.Main` exit 0),
# read-only: plain `lean` with LEAN_PATH from `lake env` there. Usage: run_probe.sh File.lean
export PATH=$HOME/.elan/bin:$PATH
export LEAN_PATH="$(cat "$(dirname "$0")/.leanpath")"
cd "$(dirname "$0")" && lean "$1"
