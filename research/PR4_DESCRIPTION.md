# Proposed PR #4 title

Propose a 933-variable quartic with explicit integer coefficients, building on Version 6

# Proposed PR #4 description

## Summary

Rebuilt against Version 6 at `f87226569fa7ceeae0c783c3e4d1241ac727733a`. This PR now proposes a **933-variable quartic with fully explicit integer coefficients**. It supersedes the earlier 1,267-variable presentation and incorporates the former stacked 1,180-variable refinement.

| Construction | Variables, including input | Quadratic residuals | Monomials | Coefficients |
| --- | ---: | ---: | ---: | --- |
| Upstream Version 6 | 962 | 919 | 55,409 | Fixed symbolic integer S = 3^(2^27) |
| This proposal | **933** | **890** | **51,907** | **Ordinary integer strings; maximum 3,247 bits** |

The polynomial has degree four and primitive content one. The published Version 6 source and artifacts remain unchanged.

## Mathematical and computational changes

Start from Version 6's optimized point chart, shared polynomial circuits, scaled pole witnesses and finite-correction chain. These optimizations are credited to the upstream authors. The additional changes are:

- Apply the exponent-19 height bound to use comparison precisions 12/40, while retaining scalar order 32.
- Replace fourfold comparison targets with doubled targets. The proof gives the soundness argument at split and inert primes and the compatible common-index congruences using the finite doubling subgroups.
- Remove the redundant detector delta inverse, with an explicit proof that the remaining norm equation forces every required denominator to be nonzero.
- Compute the precision weights through the quadratic quotient equations e² q12 = q1 e²⁴ and e² q40 = q1 e⁸⁰. The shared power circuit saves one coordinate in each of the nine detectors.
- Use a degree-nine block evaluation for G9 and direct quadratic evaluation for G2.
- Specialize to the smaller anchor 3^(2^26), justified by the height inequalities, and encode it with seventeen uniquely determined constant-chain coordinates.

The combined result saves 247 variables relative to our earlier 1,180-variable proposal. The intermediate experiment lowering only the beta precision increased the count and is recorded but not selected.

## Files and review path

Begin with [research/v6-comparison/README.md](https://github.com/scduko/diophantine-z-q-explorations/blob/combined-comparison/research/v6-comparison/README.md). It gives the derivation, exact dependency boundary, count progression and reproduction commands.

The new package includes pinned inputs, the generator, complete compressed ordinary-coefficient artifacts, elimination certificates, coordinate maps, hashes, an independent symbolic logarithm check, and a dedicated artifact replay. Earlier 1,267- and 1,180-variable artifacts and their proofs are preserved as historical references; they are not the current proposed endpoint.

## Verification

- All five experimental stages passed the unchanged upstream independent algebraic checker.
- The selected 933-variable package passed a fresh hash, constant-chain, exact arithmetic budget, certificate, coordinate-map and complete sum-of-squares replay.
- All ten emitted G2/G9 logarithm circuits were independently expanded over Q[f0,f1] and checked as exact polynomial identities.
- The historical 1,267-variable package still replays successfully after the rebase.
- The published Git tree was matched to the locally checked tree.

Replay the selected artifact:

```sh
python3 -B research/v6-comparison/check_artifacts.py
```

Regenerate it in a new directory:

```sh
python3 -B research/v6-comparison/explore.py --only 4 --out /tmp/v6-replay
```

Ordinary polynomial SHA-256: `5dade132700c872ea5fbfb60913e1dd82b2f6d39cb86a0db37d3b1de71303c7a`.

## Arithmetic dependencies and review status

Independent human mathematical review remains pending. Algebraic replay does not certify the quotient-domain lemmas, height theorem, doubled-target arithmetic argument or inherited number-theoretic results.

The current dependency is Version 6's simultaneous-prime construction and its in-manuscript Gaussian ray-field estimate. Frei–Tinková is methodological provenance, not an assumed theorem in Version 6. Remaining source-version qualifications and incomplete Lean status are retained.

The new composition, quotient-weight circuit, exposition and scripts were developed with AI assistance under the repository owner's direction. Upstream construction, optimization and compiler/checker attribution is preserved. No minimality claim is made.
