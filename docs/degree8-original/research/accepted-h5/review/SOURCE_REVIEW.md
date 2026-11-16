# Original polynomial: source and contract review

This is a source-only review while the root schedules the finite rebuild. It does not accept the defining-Z claim or replace the height and anchor reviews.

## Portable code

The new `degree8-original/build.py` invokes the original builder with all identifying options explicitly fixed: chart 10, parity 7, unit scaling, base-point gates, logarithm block 2. It does not substitute the optimized 125,328-term construction. The archive builder's defaults also fix precision 64 and 24 anchor squarings. The wrapper independently instantiates the source modules before accepting their flattened rows.

`polynomial.py` recursively allocates private locals, checks call arities, prohibits recursive module calls, translates shared negative indices, requires primitive nonzero integer rows, and checks the full variable support. Its sum-of-squares expansion uses ordered term pairs and checks the precise coefficient maximum as well as degree and monomial count. This is a complete numerical expansion check once executed, not a probabilistic fingerprint.

`check.py` validates its manifest before replay, compares every residual and expanded coefficient, and can regenerate the full construction. Its archived-audit wrapper copies the four original audits and the original builder into a temporary layout, passes the data directory explicitly, and reads the actual report filenames. This contains the import-time `audit_semantics.py` writes used by the comparison and chart audits. The `-O` rejection preserves assertions in the normal entrypoints. No historical working directory is needed by the inspected runtime path.

The archived audits check different parts of the circuit. `audit_main.py` checks allocation, flattening and full expansion. `audit_semantics.py` checks the beta/Lucas expression, 41 contacts, nine coordinate scalars, norm-tree leaves and internal nodes, finite scalar correction and anchor input indices. `audit_comparison.py` checks all 41 test slots and exact logarithm expressions. `audit_charts.py` checks point charts, subtraction guards, and the fixed [4] base point. None proves the global arithmetic realization or the five-contact height estimate. Their passing labels must not be read that way.

## Arithmetic contracts inspected

The original seven-witness parity block is precisely the four equations in `make_parity`, without extra guards. I independently derived its negative-odd-valuation obstruction, including zero conic variables, and reviewed the new parity proof's completeness reduction. Its weak approximation, mutual square-class argument, matrix rank construction, and final curve rescaling are correct under the identified baseline inputs.

The exact reused baseline scope was checked in the frozen manuscript: `hyp:RC`, lines 1005–1016, is for positive squarefree l congruent to 11 modulo 12; local descent appears at 1033–1070; `lem:corank` at 1072–1084; `lem:forward-rank` at 1086–1109; and the realization at 1111–1120. The new matrix construction produces n and n theta in that domain. It does not need an unrestricted or simultaneous converse as a new hypothesis. This conclusion does not independently certify the baseline RC proof.

The original common-J argument does not require a cross-prime gcd theorem. It rescales local h_q individually while replacing J by a common multiple of local j_q. The compatibility condition is local, h_q congruent to 4 modulo q raised to v_q(j_q). The full local-witness and prime-pattern proof must still establish the hypotheses actually used.

The archive's five-contact H and 24-squaring anchor are not covered by the accepted 20,371-witness adaptation. Its source theorem explicitly assumes the earlier arithmetic inputs. The previously cited quartic article is absent from the original `source-inputs/`, despite the archive README's broader description. The height reviewer has located it elsewhere in the supplied records; its applications and explicit constants require their own review and pins.

## Pending acceptance

The root's coordinated finite run must verify the imported exact 129,497-term data and all archived audits. The completed height, anchor and 41-prime-pattern arguments, and the final new manuscript section, remain to be reviewed. Until those steps are complete, the original object is an explicitly checked candidate polynomial with a conditional arithmetic characterization, not an accepted second proof of the ordinary integer definition.

## Follow-up review after the coordinated run

The root's `packaging/check-report.json` now records the complete rebuild and all four archived audits passing. I read that report against the inspected wrapper code. It gives 15,671 witnesses, 15,107 residuals, degree eight, 129,497 monomials and maximum absolute coefficient 685783949153203534233601. It reports 327,323 ordered term pairs, complete residual and expansion equality, all 41 test slots, all logarithm identities, 11 stored point charts and five stored subtraction blocks. These stored-block counts are not counts of all recursively instantiated copies.

The field `anchor_original_coordinate_conversion: false` is expected descriptive metadata. The audit detects whether the optional label `anchor original f/C` is present. The original normalized-coordinate builder emits `anchor f/C`, so it selects direct normalized f coordinates and the audit verifies those. It is not a failed assertion. The new anchor proof separately shows that the original-coordinate and normalized-coordinate conditions are equivalent through the integral matrix [[17,24],[12,17]], whose determinant is one.

I also read the complete original41 proof. Its small-prime admissibility, distinct-slope argument, fixed-cutoff asymptotic, uniform fiber sieve and common-J construction check out. The anchor proof gives the exact subgroup of permitted nonzero indices, rather than merely existence of some large indices. The new author section preserves the exact original norm tree, scalar correction, [4] shifts, shared chain and witness count. Its theorem explicitly retains H5 as a hypothesis. No arithmetic correction was identified in these components. H5 and its exact constant, plus final integrated source review, remain open acceptance conditions.

I independently checked the published [Koenigsmann article](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n1-p02-p.pdf), Definition 4 on printed page 75 and Proposition 6 on page 76. Its trace-sum set is exactly S+S, without a finite offset, and its specialization to the quaternion algebra (2,3) gives the asserted intersection of the two local integer rings. This confirms the anchor's external application, rather than relying only on the archive's naming of that predicate.
