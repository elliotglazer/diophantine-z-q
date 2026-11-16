# Independent review of the exact 12,504-variable release

The frozen source auditor, generated named-source checker, adapter, and exact
candidate pass this static implementation review. I found no blocking
algebraic defect in their treatment of the source equations or rational
existential projection. A read-only byte and metadata audit also passed.
This conclusion applies to the hashes below and in `BINDINGS.json`.

This review does not itself rerun the full certificate or prove the inherited
arithmetic theorem. The downloaded wave13 receipts record successful source
auditing, 38 semantic source mutations, five resource-abort regressions, and
full certificate replay. The release runner must repeat those checks in its
clean package. New release-runner and certificate-test code is being reviewed
separately below; its completion is not inferred from the frozen receipts.

The combined-source, H19, root37, precision40, and scalar32 drafts are outside
this release. The reviewed source uses high precision64, beta precision16,
24 anchor squarings, scalar orders `[1,1,1,1,48,48]`, and 41 contact comparisons.

## Exact scope and pins

Paths in the binding manifest are relative to the workspace root
`C:/Users/glaze/Documents/Codex/2026-11-02/lo`.

| Object | SHA256 |
|---|---|
| Frozen source auditor | `495ca32737687fca335704c6bdbabacf8f20a7698839aa680639e8e1b60a948f` |
| Frozen source mutation harness | `f6e402489872a7418edd17c7c78a582334df88e954987abe14af13a95b022656` |
| Generated named-source checker | `d2079177a4960740c5b7d42fbd0756dfc4ce8953cc947cee91c8786ba26fa8ba` |
| Adapter generator | `72e0aafbb95166143cebc0005c8e93ac4047407c43a70340ec6ebb2b0602cf70` |
| Source-entry JSON | `c0fc67ef6ead31dd018ca92643dc4988fcf28f9755dd9be7e017651bf4b14abc` |
| Source residual gzip | `ce9eeac7c4730aced8cfb70a1ab3b1b6a7fb2110c597afad1f56ddc92aeea73f` |
| Plain source residual stream | `b5e836d7764363fcbfdafbacefe80a5f53e0979eba73af990827942b0fa9351d` |
| Independent construction map | `edad166ce99d33fe50271e2afdc1628bbec0361d812762212240cadd30f93cfe` |
| Frozen certificate gzip | `9f7979c1e786bebad624b9ea4631b7eccd879f4bebb5b9ab69250b945973b268` |
| Expanded polynomial | `7f5aa3117af82a0b323f0a4e74a18599204f5540408106d3ce99612b5ed830ca` |
| Expanded polynomial gzip | `aafb76c3ac0791ad2ed0bb73ee2526dd2c9056f9bdc617e09ed017d0fa14c5ba` |
| This review's binding evidence | `ab0242c77c4f72895a267fdf2382991357400a8e801ab0df37309c3e543e5a8a` |

The candidate has 12,503 existential rational witnesses and one free input,
11,939 quadratic residuals, and 135,721 monomials after squaring and collecting.
The reported maximum absolute coefficient is
`685783949153203534233601`, strictly below `2^80`. Every final weight is one.
The declared polynomial degree is exactly four.

## Source auditing and typing

The source checker pins all six original module files before using any
original-module data. The height batch and parity module must equal those
original dictionaries. The root must also equal the original dictionary,
apart from the explicitly chosen precision and anchor metadata. For this
64/16 source the anchor is unchanged. These comparisons include all rows,
allocated coordinates, calls, labels, constants, root charts, doubling steps,
height tests, and contact arguments; they are not comparisons of summaries.

`Module` accepts only integer nonzero coefficients, sorted nonrepeating
monomials, bounded integer coordinate indices, sequential allocations, and
sequential row logs. Every residual must occur in the construction log.
Arithmetic coordinates have a checked nonzero constant linear leading
coefficient and no self-occurrence in the remaining right side. Their right
sides use only coordinates already allocated and defined. Exact Fraction
substitution eliminates these definitions. Ordinary core variables remain
indeterminates, so an arithmetic label cannot silently turn a source
constraint into an assumed identity. Core labels and multiplicities, every
nonarithmetic row, every call argument, and the complete local-variable
partition are checked after expansion.

The comparison checker independently reconstructs all five primary chart
systems, five subtraction systems, five distinct-abscissa norm guards, the
reciprocal-logarithm interfaces, and all 41 rational tests in order. The sole
outgoing batch call has exactly 42 arguments. Its first argument is the
contact parameter, followed by the root error and the ordered real/imaginary
tests. The G polynomial coefficients are derived by binomial convolution,
independently of the producer recurrence. At 64 and16 they have 16 and4 terms.

The batch checker reconstructs the order-dependent pairing plan, all leaf
equations, all upper norm equations, its power definitions, and its sole
parity argument. It requires consumption of every row. No changed height
order, reordered test, missing constant leaf, or extra batch call is allowed.

Flattening starts with the checked 25 shared coordinates and follows each
module call in source order. Locals receive new disjoint intervals; free
coordinates are mapped through the call arguments. Negative indices map only
to the allowed shared coordinates. Cyclic module calls are rejected. Every
flattened row is compared to the actual stream, with no missing or trailing
rows. If both raw and gzip streams exist, their full bytes must agree after
decompression. Visit counts must be exactly root1, anchor1, height1,
comparison41, batch41, parity42. The independent visit list is serialized
canonically and hashed as the construction map.

The source auditor has bounded allocation, polynomial degree, term count,
coefficient size, aggregate expansion, stream size, and elapsed time.
Resource errors have a separate exception type; the source mutation harness
must propagate them instead of counting them as semantic rejections. Its
recorded 38-case receipt covers extra and missing rows/calls, arithmetic
capture and forward references, missing chart/log/guard interfaces, changed
order/constant signs, both flattened coordinate mappings, and gzip mismatch.

## Compressed chart interface and arithmetic boundary

For each primary point, the source retains field coordinates `u,v,f,x,p` and
the exact equations

```
f=u^2, v^2+d*f=1, p^2=x-D*f, x*f=1,
d=3-sqrt(2), D=d^2=11-6sqrt(2).
```

It substitutes `y=x*p` into every primary-point consumer. It retains each
difference point's own `z`, `x`, `y`, and reciprocal coordinate, and retains
the common auxiliary parameter and its inverse in the unchanged root. The
subtraction signs and all five nonzero abscissa-difference guards match the
original source. No difference parameter was confused with the deleted
primary parameter.

The remaining interfaces are `Lambda*p_H=G_H`, `A_i=C_i*p_i`, and
`A_i*Lambda=G_i`. They encode `Lambda=-L_H` and `C_i=L_i/L_H` with
`L_i=z_i*G_i` and `z_i=-1/p_i`. Their signs agree. The four chart equations
alone would permit unwanted zero-parameter cases; the global G nonvanishing
lemma is therefore essential. It implies all the displayed `p_i` and
`Lambda` are nonzero. From `x*f=1`, both `u` and `f` are nonzero; from
`f*p^2=v^2*(1+d*f)`, `v` is nonzero. The deleted old coordinates are recovered
by `z=-1/p`, `y=x*p`, `h=u*p`, and `w=u*p/v`. Conversely an original point
defines `p=y*f`; the reciprocal and curve identities give these four chart
equations and the ratio equations. All outside primary consumers are
independently reconstructed by the source auditor.

The global G nonvanishing, formal-logarithm error estimate at every selected
prime, mixed 64/16 proxy argument, and revised beta contradiction are
mathematical dependencies. They are not consequences of certificate replay.
The frozen `RECIPROCAL_PROOF.md`, `INDEPENDENT_RECIPROCAL_REVIEW.md`, and
`BETA16_INDEPENDENT_REVIEW.md` identify them and are pinned in the binding
manifest. The original rank/generator, height, prime-pattern, pole, scalar,
common-orientation, and completeness results remain dependencies too. A
release claiming an integer definition must carry their source acceptance
and the mixed-order statement through to the manuscript. This review found
no implementation drift to a different precision, height, or contact theorem.

## Adapter and named-source binding

The adapter pins its original checker and rule inputs, verifies every
reported source-file hash and construction-map hash, and emits a named source
registry entry. It preserves the original registry entry. Locator changes to
the producers do not establish soundness; the independent checker rechecks
every emitted transformation. The generated checker embeds the chart,
parity, and batch rule texts. This review's AST inspection confirmed exact
equality between those embedded texts and the separately pinned rule files.

The adapter consumes an audit receipt; it does not itself run the source
auditor. Therefore a fresh release must run the pinned auditor against the
packaged source and originals and compare the result to the frozen receipt,
ignoring only elapsed time. This is a dependency of source acceptance, not a
defect in subsequent algebraic replay. The source registry pins both raw and
gzip source hashes, full source header, source size, map, audit, and inspected
source files. The initial certificate must select the entry and match its
canonical hash. The byte audit verified each of those relationships.

## Complete existential projection

The initial lift validates every reused source product equation with nonzero
rational scale, keeps those anchor equations, allocates each fresh product
coordinate consecutively, permits only earlier inputs, and checks its actual
defining row. It then expands every lifted source row and compares it to the
original, reducing only by the retained source-product identities. The
resulting rows must all be quadratic. These operations have polynomial
witness extensions and exact reverse substitutions.

The exact certificate uses the following nine rule kinds. Other supported
checker branches are not premises of this candidate.

| Rule | Count | Reverse-map or equivalence obligation |
|---|---:|---|
| Norm inverse | 205 | Replace `q*(A^2-2B^2)=1` by the two coordinates of `(A+B*sqrt(2))*(s+t*sqrt(2))=1`. Forward `s=q*A,t=-q*B`; reverse `q=s^2-2t^2`. Norm multiplicativity is checked explicitly, old dependent definitions are acyclic, and all deleted coordinates are private. |
| Redundant inverse | 41 | Retained `E=theta^2-2` and `R*H=E^2` imply `R!=0` over Q; restore the private inverse as `1/R`. Its sole occurrence is checked. |
| Gpoint chart | 6 | Check all 14 source field-coordinate rows and the fixed d. Drop private `w,h`, set `p=y*f`, and restore `h=u*p,w=u*p/v`. Retained inverse/parameter equations imply `p,u,v!=0`. |
| Field ordinate | 2 | Check all six rows for `x*f=1,p=y*f,y*z=-x`; substitute both components of `y=x*p` through the full incidence set and retain `p*z=-1`. Reject any resulting degree above two. |
| Parity conic | 42 | Reconstruct all four original rows after expanding private gates. Forward rational parametrization has denominator `1+b*t^2!=0`. Reverse treats `b=0`, `u+b!=0`, and the exceptional `u=-b` branch separately, changing only private witnesses. |
| Batch absorption | 1 | Retained `R*(F-1)=E^2` with `E!=0` permits division by R. Introduce `R*O=P` and `Q=B^2`, replacing `P*N-E^2*B^2-R*T^2` by `O*N-(F-1)*Q-T^2`. All deleted definitions have their full incidence inside changed rows. |
| Linear row operation | 366 | Replace one equation by `a*r_i+b*r_j` with nonzero integer a while retaining `r_j`; invert the row operation over Q. |
| Elimination | 800 | The defining row is checked to be a nonzero scalar multiple of `v-replacement`, with v absent from replacement. Substitute through every other occurrence. Input coordinate zero cannot be deleted. |
| Shear | 4 | Substitute `v -> v+c*w` through every occurrence, with `v!=w` and `v!=0`; inverse uses `-c`. |

Every expected patch is independently derived. Duplicate or omitted patch
indices are rejected, patch equality is exact up to a nonzero rational
scalar, and every resulting row is quadratic with valid allocated indices.
Incidence is updated after each patch. The final allocation count, row hash,
and saved uncompressed row contents must equal replay. The variable map is
a bijection onto exactly the remaining active coordinates and starts with
input zero. Its full compact residual list must equal the delivered list.

Final weights are checked positive integers. Over Q, a positive weighted sum
of squares is zero exactly when every residual is zero. The verifier uses
all ordered products to independently expand that sum, checks both polynomial
encodings, rejects repeated/unsorted monomials, and compares the entire
coefficient dictionary. It then checks exact degree four, occurrence of all
reported variables, the strict `2^80` bound, and the final claimed statistics.
Thus the conclusion is equality of rational input projections, including
all exceptional cases accounted for above, not only agreement on sampled
witnesses.

## Release code findings and validation status

1. The frozen source auditor relies on assertions without its own `__debug__`
   guard. The generated named checker already rejects Python optimization.
   I asked the release runner to reject optimization itself and invoke
   children with `-E -B`, while removing `PYTHONOPTIMIZE`. Its first reviewed
   version implements that requirement. No frozen file needs alteration.
2. The first new certificate-mutation suite assumed the frozen certificate
   had no weights event. A read-only scan established that it has exactly
   one. The oversized-quartic case would abort before exercising the bound.
   I reported this to the test author and root; a repair must update the
   existing weights instead of inserting a second event.
3. Exact gzip reproduction is environment-sensitive. The frozen source has
   gzip OS byte3; local CPython3.14 uses byte255, and the compressed body also
   differs for this source. Therefore a claim of portable byte-for-byte
   rebuilding needs either the original compression environment or explicit
   transport handling after exact decompressed-byte equality. Frozen replay
   itself does not depend on reproducing gzip compression. I reported this
   to the runner author and root.

The local `check_bindings.py` execution completed successfully in under one
second and wrote `BINDINGS.json`. It checked all source and candidate byte
pins, the embedded rule text, the source registry, source-entry hash, audit
and map bindings, exact certificate operation counts, protected input
coordinates in elimination/shear records, final statistics, and gzip/plain
polynomial equality. It did not perform symbolic certificate replay, execute
the source producer, launch any external job, or modify any frozen input.

## Final release-wrapper addendum

The following new files also pass static review after the repairs above.
Execution of the clean release package remains the final computational gate.

| File | Reviewed SHA256 |
|---|---|
| `reproducibility/run.py` | `db924e8a24b8b3a6eb04f8d7f0dc4e3dc721618b436073e87fa7b3a9d31c535f` |
| `reproducibility/prepare_package.py` | `235c232f97d96008b75172dc8efab053fefed66b7c58b70993b8b5265eb00a77` |
| `reproducibility/copy-plan.json` | `7e2de0f98b11b6ffa0fb21a8fa8f1f2172db386b72f904313261544b573de4e8` |
| `final-checks/test_named_certificate.py` | `0d8cca89f045bc38089eddcf8b22aeedb1db08779bbf6fcfcd9d16dbe0a4856e` |

The runner rejects disabled assertions, invokes children with `-E -B`, and
removes `PYTHONOPTIMIZE`. It compares freshly reconstructed source audit
reports to the frozen report, omitting only the elapsed-time field. It checks
the exact map hash, requires 38 source mutations and five resource
regressions, replays a copy of the exact certificate, then requires all 30
new certificate mutations. It regenerates the source, compares every audited
source file, audits it again, and performs the complete fresh pipeline with
the named checker after every stage. Every final artifact is compared byte
for byte except the certificate transport. For that file, all parsed records
must agree after deleting only `final.report.seconds`. Thus nondeterministic
timing cannot hide a changed operation, polynomial row, or source entry.

The runner now explicitly tests the local gzip compressor against the frozen
source transport before creating the output directory. A mismatch stops with
a specific Linux CPython3.12/compatible-zlib requirement and identifies
portable frozen replay as a separate operation. The summary reports Python,
platform, and compile/runtime zlib versions. This handles the demonstrated
portability issue without weakening any equality or hash test.

The copy plan contains the 65 explicit files needed by the current runner,
including the original modules, their small arithmetic checkers and hashed
text dependencies, the reciprocal checker import, source compiler, source
auditor and its local import, and the producer imports used by this exact
pipeline. The unused merge-kernel and separate embedded-rule source files
are not runtime dependencies of the selected scripts. The package preparer
checks each source's size and hash before creating a fresh output directory,
checks resolved containment, and checks hashes again after copying. No
frozen source is rewritten. The generated manifest covers the copied files.

The repaired certificate suite scales the existing positive weights and
the compact weight list in its oversized-quartic case. It also scales every
expanded coefficient by the same amount. Consequently the full polynomial
equality check can succeed before the intended strict coefficient bound
rejects. Each malformed case must raise AssertionError at its named checker
source statement; other exceptions, wrong checkpoints, process failures,
and timeouts fail the suite. The baseline must first match the exact source,
checker, certificate, polynomial, and numerical claim. Children use `-E -B`.
The new suite was not run locally during this review.

No outstanding static blocker remains in these reviewed versions.
