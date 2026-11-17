#!/bin/bash
# Assemble ReductB.lean = RBBase.lean (reduct-glue's ReductGlue.lean minus its #print lines: Base = kernel TailZ7,
# Body = kernel TailZ14) + Body.lean (namespace ReductB) minus its `import RBBase` line.
cd "$(dirname "$0")"
{ cat RBBase.lean; echo; grep -v '^import RBBase' Body.lean; } > ReductB.lean
