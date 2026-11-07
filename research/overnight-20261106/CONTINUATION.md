# Research checkpoint — 6 November 2026, evening

## Current state

Upstream checked at `5856286a57fba19574a40704571ee70e79738281` (Version 8). Prior integrated upstream was `f87226569fa7ceeae0c783c3e4d1241ac727733a` (Version 6). The seven intervening commits add the Version 7 Gaussian repairs, source relocation, handoff validation and the Version 8 abstract revision. They do not alter the 962-variable circuit or its polynomial. Upstream was merged locally without conflicts and is included in this checkpoint commit.

The archived Version 6 manuscript survives byte-for-byte as `docs/quartic-962/evidence/gaussian-four-audit-20261106/baseline.tex`; the old Version 4 manuscript moved byte-for-byte to `manuscripts/archive/quartic_4973.tex`. Both hashes were checked. The two affected INPUTS.json files now use those paths with unchanged hashes and explicit relocation maps. This repairs generation after the upstream move without silently repinning the arithmetic proof to a newer text.

The repaired Gaussian appendix makes the fixed cutoff, fixed-modulus uniformity, majorant rescalings, dense-model normalization and parameter order explicit. These repairs matter to the common-index completeness argument. This pass inspected the audit summary and the preserved interfaces; it did not independently reprove every analytic estimate.

## New candidate

The direct-target experiment reaches **909 variables, 866 residuals, 51,279 monomials, 3,247 coefficient bits**, degree four and primitive content one. Full algebraic replay, all ten exact logarithm identities, constant-chain projection and arithmetic budget checks passed. See DIRECT_TARGETS.md and VERIFICATION.json. The ordinary polynomial hash is recorded in RESULTS.json. The complete outputs can be regenerated with unit_target.py; they are not substituted for the frozen 933-variable artifacts.

The new proof observation is that the current targets Qi already belong to 2E(K). The finite doubling-image argument therefore permits shift one, not merely shift two. This removes the four remaining variable-target doublings. Both soundness and the common-index completeness argument are written out, but they have only AI self-review so far.

## Intuitive proof

INTUITIVE_PROOF.md develops the construction from hidden integer labels, the two local observations, the height-transfer inequality and two growth contradictions. It identifies the deep inputs explicitly and maps the explanatory steps to named lemmas. It is an explanatory architecture, not a newly discovered elementary proof.

## Avoid repeating these approaches

- Lowering only beta precision to 12 increased the ordinary-coordinate count to 951 in the earlier V6 experiments. The shared power circuit must be optimized jointly.
- Shift zero makes both observations identical and loses the equation that recovers ni. It does not extend the shift-one improvement.
- A pure degree-based height argument with exponent 19 and Lucas discrepancy degree four needs precision strictly above 38. Moving from 40 to 36 does not close the present contradiction. This is a limitation of this argument, not an impossibility result for all constructions.
- Moving the first explicit constant farther up the squaring chain trades fewer variables for larger coefficients; report it as a tradeoff, not a structural reduction.
- The source relocation is already handled in input manifests. Do not restore obsolete root manuscripts or replace historical source hashes with current-manuscript hashes.

## Next pass

1. Freshly examine the direct-target proof: source index conventions, all consumers of removed targets, local continuity at h0, and CRT compatibility. If satisfactory, package a standalone replayable 909-variable artifact while preserving 933.
2. Extract a parameterized comparison lemma with height exponent alpha, discrepancy degree d, precision k and anchor threshold. The inequality k>alpha*d/2 explains the first contradiction; retain the scalar and Lucas conditions needed for the second.
3. Investigate reducing the number of scale detectors or sharing their evaluation circuits. Such a change needs a new height-transfer proof, not just deleted gates.
4. Check upstream main afresh and preserve any concurrent changes to combined-comparison. No upstream merge or unsolicited PR comment is authorized by this research checkpoint.

All new reasoning and scripts in this directory were developed with AI assistance. No independent human mathematical review is claimed.
