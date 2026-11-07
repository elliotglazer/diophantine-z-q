# Research checkpoint — mixed weights, 7 November 2026

## Starting state and upstream

Read CONTRIBUTING.md, the previous continuation note, actual emitted
detector source, existing proof notes and verification scripts. No AGENTS.md
was found in the checkout. Upstream main was freshly checked at
`5856286a57fba19574a40704571ee70e79738281`, unchanged from the integrated
Version 8. Fork head was `0003db3df076d10330b4e612b59b4739d71709e9`.
No new upstream changes required integration. One unrelated untracked
compiler temporary file was present and was left untouched.

## New result

A hand-derived mixed rational circuit saves one gate in each detector:
powers 2,4,8,16, then 30 via the quotient 32-2, then 60;
q12 uses 30-8 and q40 uses the already computed q12 plus 60-4.
The result is 924 variables with doubled targets, or 900 with the
separately proposed direct targets. This is not an exhaustive circuit
search and no lower bound on the new circuit is claimed.

Both variants passed fresh compilation, elimination certificates and full
ordinary-polynomial replay. Both passed separate constant-chain, numerical
budget, ten-logarithm and nine-detector weight checks. The weight checker
reads actual emitted gates and records all 27 quotient denominators as
powers of e (2,4,8 per detector). The README proves e nonzero from the
retained inverse and norm equations without assuming gate evaluation order.

The 924 transformation is exact on the existing source domain and needs
no new number-theoretic input. The 900 candidate additionally inherits
the direct-target arithmetic proof obligations. Neither is a claim of
independent human review of the entire Diophantine proposal. Frozen 933
artifacts remain unchanged. Reproduction scripts, result hashes, input
pins and verification reports are saved; complete outputs are generated
on demand rather than replacing or duplicating the archived package.

## Proof architecture and metadata

The new README gives an elementary explanation of the circuit change,
a two-way projection proof and the precise boundary with the deep
arithmetic inputs. Use it alongside the earlier intuitive proof and
parameterized comparison lemma. This pass makes no claim to replace
the elliptic group, height or prime-pattern theorems by elementary proofs.

research/PR4_DESCRIPTION.md now contains proposed metadata for the 924
refinement and 900 candidate, with review qualifications. Its previous
933 draft is preserved here as PR4_DESCRIPTION_933_ARCHIVE.md. Upstream
metadata editing was previously forbidden by a 403; no browser login,
metadata write, merge or unsolicited comment was attempted in this pass.

## Avoid repeated dead ends

- The previous restricted nine-gate lower bound did not cover intermediate
  quotients or reuse of q12. Do not misstate this improvement as a
  contradiction of that bound.
- The historical logarithm verifier contains a handwritten old power chain.
  Its logarithm expansion remains usable, but that chain does not verify
  the new weights. verify_run.py deliberately takes only its logarithm
  results and uses verify_weights.py for actual emitted weight gates.
- Dropping the w0 inverse is not authorized by this proof. If w0=0,
  the norm equation gives w1=0 but need not force N nonzero. The retained
  inverse is essential to the domain argument used here.
- Lower precisions remain blocked by the comparison thresholds from the
  preceding pass; circuit savings alone do not change those thresholds.

## Next best direction

Seek shared quadratic equations across the q1/e/delta circuit and the
norm/B circuit, rather than optimizing the e-power chain in isolation.
Allow intermediate quotients only after deriving their nonvanishing from
unchanged global equations. An exact search over mixed monomial circuits
could test whether seven weight gates are possible; this pass has neither
run nor certified such an exhaustive search. The structural lower-degree
growth-relation direction remains open, with auxiliary height control
and divisible completeness as the key obligations.

All new proof prose and code have AI authorship/self-review. Exact
algebraic replay is distinct from an independent human mathematical review.
This checkpoint describes work performed in this pass, not continuous
execution between passes.
