# route-a-fold results log

- 11-14 16:00 start. origin/wip/r1univ-rigid already merged in base (e38375b3). frozenTarget fields among the 18 L
  (used-fields.txt on wip/prune-scan): r1r2 (R1R2fpRep), shimuraFamily (ShimuraFamily), gonzalezRotgerCountX6
  (OpenResearchLeaves10); deligneComponentsY3Printed (OpenAddedLeaves9). No textbook field.
- TailZ16 (R1UnivRigid core verbatim, 32.6 KB) and TailZ17 (4 printed LAb, 4 iff, OpenResearchLeaves11 29 fields, OpenAddedLeaves10 14 fields, conversions, sixContactMin_of_open13; 15.7 KB) COMPILED (8.2 s, 4.9 s).
- Main switched to sixContactMin_of_open13; lake build +ZInQKernel.OneProof.Main OK, axioms [propext, Classical.choice, Quot.sound]. DumpCompact: before 11811, after 11940, only-after 129 (61 TailZ16, 68 TailZ17), changed 1 (ZInQ.OneProof.frozenTarget, the statement switch). VERIFIED.
- CheckRAF.lean: field types of the 4 changed + 1 added field, types of conversions/top, axioms of 9 new theorems and frozenTarget all standard. VERIFIED (check_result.txt).
- Counts (from leaf-fold10 counts10.md, minus pruned r3 comp, serreTateThm2 pub, t10 c): before 59 = pub 44, c 8, comp 6, pg 1 (strict 44/15, lenient 52/7); after 60 = pub 45, c 8, comp 6, pg 1 (strict 45/15, lenient 53/7). The four LAb keep their kinds.
- Report docs/research/route-a-fold.md and .fleet/route-a-fold.md written.
