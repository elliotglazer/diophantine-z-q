#!/bin/bash
# Assemble ShRoute.lean = Base.lean + Body.lean (verbatim copies of reduct-glue's) + Top + CA1 + CA2 + CA3 + Final
cd "$(dirname "$0")"
{ grep '^import' Base.lean; grep '^import' Body.lean | grep -v ReductSplitBase; grep -v '^import' Base.lean; echo;
  grep -v '^import' Body.lean; echo;
  for f in Top CA1 CA2 CA3 Final; do grep -v '^import' $f.lean; echo; done; } > ShRoute.lean
