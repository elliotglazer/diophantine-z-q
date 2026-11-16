# Independent inventory and source-import review

This review concerns the exact Version 2 manuscript
`quartic_12504.tex`, SHA256
`a8b3f7e2d86ef33082d22874a823bfbdf2f3ad120664ace8c4c1b1e82399c8bd`,
the historical-review bridge, the current dependency inventory, its
validator, and the scope of imported arithmetic evidence. It supplements
`REVIEW.md`, which covers the source compiler and exact quartic certificate.

The current manuscript's arithmetic and finite-computation boundaries are
correctly stated. The new source is not justified merely by changing a
digest, nor by claiming equal output with the older finite logarithm.
The new local lemmas and revised-source theorem provide the missing
mathematical connection. The final theorem then uses exact projection
equivalence and the full polynomial expansion. No combined-source, H19,
37-contact, scalar32, or shortened-high-precision result enters this release.

Verdict: PASS for the final versions pinned below. All findings were
repaired and reviewed. The final validator also passed on the staged public
checkout. No manuscript, frozen compiler, or frozen candidate was edited by
this reviewer.

## Historical applications

The historical manuscript has SHA256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`.
Its coverage record identifies 82 application records with 443 anchored
contexts and 147 citation paragraphs. The final bridge contains all 443
application anchors and all 147 citation paragraphs, with no unmapped
entries. Each current range is exactly the old line sequence and retains
its old excerpt hash. The bridge names both whole-manuscript hashes.

Relocation changes the historical manuscript path and inventory links; it
does not assign the old review verdicts to the new reciprocal-source text.
The original applications, source identities, hypotheses, source versions,
and qualifications retain their historical scope. The historical coverage
record itself disclaims semantic exhaustiveness and proof of application
correctness. Exact text transport does not remove either limitation.

The accepted H5 material is newer than that historical manuscript. Its
separate source-application ledgers and acceptance records remain necessary.
The new reciprocal and compressed-chart material has separate review records
and a current source theorem. Therefore the historical bridge is not used
as a substitute for either of these later reviews.

## Current mathematical connection

The manuscript's `lem:quartic-reciprocal-log` states the formal identity and
the full tail estimate at every selected split prime for precisions16 and64.
It uses the curve parameter `z=-x/y`, the reciprocal coordinate `f=1/x`, and
the exact new coefficient recurrence. Its proof includes the denominators
in the infinite tail; it does not infer a precision from circuit degree.

`lem:quartic-reciprocal-nonzero` proves global nonvanishing over
`Q(sqrt(2))`, including zero f and the negative-valuation case. The proof
uses the exact new G polynomial and is sufficient for the compressed-chart
inverse obligations. It does not borrow the obsolete old-logarithm lemma.

`thm:quartic-source-arithmetic` retains height exponent24, 41 contacts,
anchor24 and scalar48. It treats arbitrary rational solutions before
introducing ordinary primes in completeness. The two beta comparisons use
order16; the common denominator and the three Lucas comparisons use64.
The first contradiction uses the high-precision Lucas defect; the second
uses the changed beta numerator bound. The common root is chosen last in
completeness, with the old orientation and exclusion conditions retained.

`lem:quartic-compressed-primary` gives both rational solution maps for the
actual chart and ratio equations. The G equations imply nonzero p and
Lambda. The retained chart equations then imply nonzero v, allowing the
reverse definition `w=u*p/v`. The manuscript explicitly retains all
difference-point parameters, common auxiliary parameters, root parameters,
and subtraction guards. The source's exact G15 and G3 circuits are given
separately as finite identities, with their outputs inserted into the
actual ratio equations.

The final proof of `thm:quartic` uses the revised-source arithmetic theorem,
the compressed-chart equivalence, the initial product lift, every algebraic
transformation, the input-fixing variable map, and the rational sum-of-squares
argument. The last step identifies the exact delivered coefficient file,
not an unspecified polynomial with the same zero set. The text explicitly
says the finite checks do not replace the height, elliptic-group,
prime-pattern, norm, or pole arguments.

## Dependency and import scope

The current inventory retains twelve applicable algebraic lemmas and adds
eight current local proof obligations. The obsolete finite z-logarithm,
logarithm inverse-removal and field-ratio-fusion claims are retired from the
active proof. The four shears have their own elementary invertible-change
statement. Source circuit evaluation is identified as finite algebra,
whereas reciprocal approximation and the revised integer projection are
arithmetic claims.

Eleven inherited families cover the five-contact height theorem,
generator/index-height results, formal group, anchor, prime pattern,
pole/parity, norm tests, common auxiliary point, root approximation,
scalar height, and Lucas growth. The recorded source versions preserve the
Yuan translation qualification, Pan author-proof/published-formulation
distinction, and corrected-author/erratum conventions for the prime pattern.
The inventory does not upgrade those inputs to unconditional machine proofs.

The import plan is evidence-only. It copies plaintext statements, ledgers,
finite checks, review records, and exact original module data. Publisher
PDFs, scans, and downloaded HTML are excluded. Source URLs, version details,
locators and hashes remain provenance information; they do not promise
local copies of those primary sources. The finite reproduction package has
its own complete runtime-file manifest and is reviewed separately.

The release inventory must not claim that an old padded H5 constant is the
current constant merely because an old ledger is included. Its family
qualification correctly gives priority to the current assembled H5 proof
and acceptance record. The manuscript's other arithmetic text was preserved
from the accepted current baseline; the exact historical excerpts provide
an additional, narrower check.

## Findings sent to the inventory author

1. The first dependency graph omitted edges from the revised-source
   declaration to its proof lemmas and from the quartic theorem to its
   algebraic lemmas. Its detailed nodes therefore were unreachable from
   the root. The author added the declaration edges.
2. The first validator checked reachability without checking that each
   declared dependency edge existed. Reachability alone could accept a
   graph with altered logical edges. Exact edge-set validation was requested.
3. The first citation loop did not compare its list to the historical
   citation inventory and could accept a dropped list. Exact ID/count,
   old-range, current-range and hash checks were requested.
4. The inherited norm-inverse paragraph locator and the field-conventions
   locator were stale after the new section was assembled. They must point
   to the current paragraph and source subsection, with all local lemmas
   bound to actual current text.
5. Two historical whole-directory manifests named omitted publisher PDFs
   despite the evidence import's exclusion policy. These redundant manifests
   should be omitted or explicitly retained only as historical provenance,
   rather than represented as current local file closure.

These findings concern inventory completeness and honest file scope. They
do not identify a new defect in the exact candidate or its arithmetic proof.

## Final repair review and byte pins

The final validator requires the exact declared edge set, with no duplicate
edges, and then checks that every node is reachable from the quartic root.
The current graph connects the revised-source theorem to its integer
projection proof and all of that proof's local and inherited dependencies.
The quartic root also reaches all algebraic reductions and the finite
certificate boundary.

The validator requires complete application and citation ID sets and
compares the historical provenance fields and both old and current text.
Its final `span` helper requires exactly two integer bounds satisfying
`1 <= lo <= hi <= line_count`. This closes the intermediate empty-list
bypass, where `current_paragraph_lines=[]` could previously skip a citation
comparison. Current citations are now compared unconditionally. Missing,
changed or malformed excerpts cause failure. The program uses explicit
exceptions rather than assertions for these checks.

The two stale local-lemma locators now identify the current field-convention
subsection and `Norm inverses.` paragraph. I matched the retained algebraic
statements and new local lemmas to the actual current TeX. The evidence
import excludes the redundant `manifest.json` files naming omitted primary
sources and now selects 78 evidence files. The final validator binds each
imported evidence file, the release review records, six original modules,
and the source-audit checker hash. It preserves the distinction between an
evidence collection and a complete computational dependency package.

| File | SHA256 |
|---|---|
| `inventory/validate.py` | `0f4df4c7f451899a8874a16b4b9a025f6ae52d95897a0a50b8f71ca11b32e72c` |
| `inventory/build_inventory.py` | `afa8c6f07ee2cf1948ef5ce257684caf025cc5bd073d0a1b7648f824eba881ad` |
| `inventory/prepare_baseline_bridge.py` | `7dfd54cf7920aa9e9ffecd7a0a0b8fe2b1067fe52c459e261779cdd4cc52ae1d` |
| `inventory/install_inventory.py` | `7000e5208b2669429f71a4d0f31faae0f6f8198d313b6225f8bf7573e8fac02e` |
| `inventory/inventory-spec.json` | `996b6afde455612f08a917d35e61d05b654d71e48fd5e42e08d9cf033c54dde2` |
| `inventory/dependency-families.json` | `d0740e9d9127dbd6b44df111476bedc6a87a9730a68570da5179d140b905b368` |
| `inventory/README.md` | `f1592dc065a48100ebe7a7f14ad6b5bd5f39fe681abbeddf16e679bb311e05d3` |
| Installed `theorem-applications.json` | `5dd944e44a052bdd25038fc368615fcc48f0388506c5b1ef6bd3f5825568ea63` |
| Installed `dependency-closure.json` | `39d20608feced138a8bd074fd959011ef97cf4fb32bf1d0ed302a54d95c90d63` |
| Installed `evidence-import-manifest.json` | `0cc83d906491ee3bbe33285690747c4b2ca074d6093860ddf2e3868f6101df05` |
| Installed `baseline-bridge.json` | `2673145a23f413038b59af01b4c14fe252a64f3995c984b5f2d6e33b90604da6` |

Paths beginning `inventory/` are relative to
`work/quartic-12504-release/`. Installed files are under the staged public
checkout's `docs/quartic-12504/` directory.

I ran the final pinned validator against the staged checkout, writing only
`compiler-review/INVENTORY_VALIDATION.json`. It passed with 443 historical
application anchors, no unmapped citation paragraphs, 20 local lemmas,
11 inherited families, and 92 bound evidence files. This was a subsecond
metadata/text/hash check, not a new arithmetic proof or certificate replay.
The historical inventory's own validator and the finite reproduction
runner remain separate checks, as the README states.

No outstanding inventory or source-import blocker remains for this exact
manuscript and these pinned files.
