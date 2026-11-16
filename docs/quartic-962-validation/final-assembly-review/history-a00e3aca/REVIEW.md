# Independent final assembly review

## Authorized attribution update

The current accepted candidate is
`a00e3aca8bb55987bce8548ab9e5ce4392c89d1d76459a7c7ac33fca303a287b`.
The earlier review and receipt below are preserved verbatim in
`history-b43f096/`. I independently inspected the eight explicit prose,
theorem-title and bibliography replacements and the citation-key rename
from `Brox2026` to `agentic-improvements`. They implement the requested
collective attribution without changing a mathematical statement or proof.
The author field remains blank. The source URLs are unchanged, including
their pinned revisions and line anchors; neutral visible link labels hide
no change of source.

The read-only checker `check_editorial.py` executes the current assembly
with and without exactly that editorial block. Without it the result has
the previously accepted `b43f096...dce7` hash; with it the result has the
current hash above. It also reproduces the candidate and all four exports
exactly. Thus there are no additional manuscript changes concealed in the
update. `gaussian-analytic` and `sun-completed` retain their previous hashes;
`source962` changes only its attribution prose and citation key. The new
`degree-lower-bound` export contains the same reviewed mathematical proof,
with the authorized collective attribution and shorter theorem title.

The current receipt binds all four exports and retains a pointer and hash
for the preceding receipt. The original source-status qualification and
the separation between assembly review and complete analytic review still
apply. No manuscript, release, or remote publication was changed by this
review.

## Original assembly review at b43f096

Reviewer: `/root/astra_sub1000_quotients`.
Date: 2026-11-06.

Verdict: accepted for assembly fidelity at candidate SHA256
`b43f096ba3a4b1a979778ae1593ce3ad89048a2d28016e5ee9f35b124238dce7`.
No manuscript or release file was changed during this review. This receipt
covers preservation, transformations and component interfaces. The separate
complete analytic review remains responsible for the analytic chain as a
whole; this receipt does not duplicate that proof audit.

## Reproduction and preserved source

I read both assembly scripts, then replayed them with filesystem writes
intercepted in memory. Both generated TeX strings equal the respective
on-disk manuscripts exactly. The input hashes recorded by the final
assembly report also match the current files. The read-only replay and
all exact comparisons are reproducible with `check_assembly.py`; its
results are in `assembly-check.json`.

The assembly script also exports `gaussian-analytic.tex`, `source962.tex`
and `sun-completed.tex`. The final read-only replay checks all three exports
against their on-disk contents. They are exact assembled spans, with only
surrounding whitespace stripped and a final newline appended. Their hashes
are recorded by name in `receipt.json` for inventory provenance.

The immutable V5 source has SHA256
`16033e0471df605093b28210a9f81718c2486b147016ec8afc75d166dff0b90f`.
The following blocks compare exactly with it:

- The original construction and its arithmetic foundations, after the
  introductory announcements and with the new lower-bound section removed.
- The complete existing 4,973-variable construction.
- The arithmetic interfaces for the smaller quartic.
- The entire shared-point source from its point-domain subsection through
  the source-projection proof.
- The subsequent old arithmetic appendices before the simultaneous-prime
  appendix.

The version, abstract and introductory edits change the advertised third
polynomial and add the degree-lower-bound announcement. The old 1,272-variable
polynomial theorem and its compiler exposition are replaced, rather than
retained as a fourth advertised construction. The line-level change ranges
are recorded in the machine report.

## Analytic insertion and notation

The norm-transfer, Type I/II, affine interpolation, factorization, bridge
and SW fragments each occur exactly once, with no mathematical edits
beyond the declared notation and citation substitutions. In particular,
the affine interpolation exponent, its explicit hypotheses, the product
equidistribution hypothesis and the factorization parameter-choice order
are retained.

`GTMobius2012` becomes `moebius`, whose existing bibliography item is Green
and Tao, *The Möbius function is strongly orthogonal to nilsequences*,
Annals 175 (2012). `v6gtlinear` becomes `greentao`, whose existing item is
*Linear equations in primes*, Annals 171 (2010), 1753–1850. These are the
same cited works, not substitutions of different theorems. The new
`GTOrbits2012` item identifies the inspected Annals 175 (2012), 465–540
paper. The assembled references resolve without duplicate labels.

The substitution of `lambda_{b,W}` for `Lambda_{b,W}` occurs only in the
affine fragment. The progression section explicitly defines this weight
as `(phi(W)/W) Lambda'(Wn+b)`, which is precisely the normalized ordinary
prime weight intended by the affine fragment. This substitution does not
replace an unnormalized von Mangoldt function or change the centering
constant.

The progression fragment loses its working-source comments and receives
the accepted Mitsui SW lemma immediately before its displayed SW
consequence. That lemma proves the previously assumed estimate uniformly
for fixed Gaussian character, q up to any fixed logarithmic power and
1 <= Y <= X. Exponential square-root-log decay implies every requested
logarithmic saving. At Y=0 both the sum and main term vanish; for 0<Y<1
the sum is empty and the bounded main term is absorbed. The ordinary
rational SW estimate is supplied by the same inserted lemma. Thus deleting
the two conditional invocations of the displayed Gaussian SW input does
not delete an unproved hypothesis.

The polynomial-count proposition is now scoped to the fixed ray class
field of Q(i) for H Z[i], with 16 dividing H, and to conjugation-invariant
subsets of its Gaussian ray group. The later ray-class application uses
exactly these fields and sets. It no longer asserts the result for arbitrary
finite Galois extensions. The FT citation remains a method attribution;
the former imported-theorem invocation and its repair remark are removed.
The Gowers estimate and boundary treatment now point to the inserted
bridge. Acceptance of that bridge's full analytic proof is a separate
review obligation, not a consequence of textual assembly.

## The 962-variable component

The construction fragment appears byte-for-text unchanged. Its original
halfpoints, Boolean corrections and pole witnesses remain the semantic
source. The implementation coordinates are expressly related to them by
the displayed maps, rather than silently reinterpreting the old symbols.
I compared those maps with the frozen package's `PROOF.md` and the retained
source: point-chart inversion, logarithm quotient domains, nonzero detector
scales, retained delta and trace guards, scalar norm relations, correction
chain and pole rescaling all agree. In particular F5 nonvanishing is
derived on candidate solutions from the positive scale and retained delta
inverse; it is not merely inherited from old solutions.

All frozen manifest file hashes verify. The archived baseline builder is
byte-identical to the V5 builder. The manifest is
`36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787`,
and its polynomial table is
`6b798de7d00ac3c7d725ca0a69d39f1eac1ddb02fee2756cb6323770b952af32`.
The compiled map fixes input coordinate zero and has precisely compact
coordinates 0 through 961. Counts match the accepted exact-check evidence:
994 raw coordinates, 951 raw residuals, 32 eliminations, 962 final
coordinates, 919 residuals, 55,409 monomials and degree four. The manuscript's
height, primitive-content and distinguished-coefficient statements match
the frozen checker evidence. This audit checks the connection to that
evidence and does not rerun its full polynomial convolution.

## Degree lower bound and review boundary

The lower-bound section occurs exactly once and matches the reviewed
fragment and its receipt hashes. Its conclusion concerns a single
polynomial and total degree in all variables over Q. The introductory
claim of quartic degree optimality is exactly that conclusion. It does not
claim a lower bound on witness count or rule out systems of quadratics.
The attribution to Brox remains explicit.

The existing lower-bound review records that Kollár's theorem was checked
in its author version with published metadata, while the full published
text was not compared. Assembly does not strengthen that source-status
claim. The separate Müller published-source check and the proof's cone,
geometric-reducibility and integral-specialization cases are preserved.

Signed: `/root/astra_sub1000_quotients`, independent assembly review.
