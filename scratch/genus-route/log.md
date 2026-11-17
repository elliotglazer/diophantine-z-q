# genus-route results log

## Consumers of t34 (VERIFIED by reading ZInQKernel/OneProof/H/TailD.lean:236, :250, LPrefix.lean:12078)
- TailD:236 `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1` → uses only `∃ g, J.dim = g ∧ g ≤ N²`.
- TailD:250 `javanpeykarJ1 hR18 hBelyi t.t34 ...`; javanpeykarJ1 (LPrefix:12078) uses hT34 only via
  `LeafModCurves.dim_J1_le hT34 N hN J hJ`. So both need exactly DimJ1Le (curve-split's def), nothing more.

## ConstField.lean — COMPILED (lake env lean), axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `GenusRoute.constantFieldIsQ_of_curve (X : Over SpecQ) (hC : IsCurve X) [IsIntegral X.left] (F)
  [Field F] [Algebra Qj F] (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F`.
- Pieces: `exists_global_section` (sheaf gluing over affine opens, irreducible ⇒ overlaps nonempty),
  `exists_global_of_isIntegral` (normal ⇒ Γ(U) integrally closed, Frac = K(X)), `hom_specQ_ext`,
  `not_subsingleton_of_roots` (two roots ⇒ two primes of ℚ̄ ⊗ ℚ[T]/(q)), `algebraic_mem_range`
  (GeometricallyConnected + surjective base change + Artinian ⇒ discrete ⇒ deg minpoly = 1).
- Copied from scratch/curve-split/CurveBij.lean: closure_mem_irreducibleComponents, isDomain_of_dim_one,
  stalk_closed_normal, topDim_le_one, isNormal_of_integral, isIntegrallyClosed_of_normal.

## GenusRoute.lean — COMPILED (16 s), no errors, all 5 #print axioms standard. VERIFIED.
- `GenusRoute.dimJ1Le_of_rh_curve : DimJacobianEqGenus → RiemannHurwitzQj → DimJ1Le`.
- `GenusRoute.genus_le_of_model : RiemannHurwitzQj → ∀ N > 0, IsX1Model N X → ∃ P, 2 g(K_N) + 1 ≤ N²`.
- X0Transitive and GenusX1Field no longer used. Leaf: RiemannHurwitzQj (Stichtenoth 3.4.13 + 3.5.1,
  numbers UNVERIFIED). DimJacobianEqGenus: proved by dimjac-glue (other branch, not checked here).

## Fold.lean — COMPILED (25 s, after `lake build ZInQKernel.Hypotheses.JHeight` for the upstream lean/ package),
## no errors; axioms standard for t34Le_of_rh, javanpeykarJ1_of_le. VERIFIED.
- Contents: GenusRoute.lean verbatim + `import ZInQKernel.OneProof.H.TailM` + namespace HDec.HSyn:
  `DimJ1Le5` (DimJ1Le on OneProof copies), `dimJ1Le5_of_kernel`, `t34Le_of_rh : DimJacobianEqGenus →
  RiemannHurwitzQj → DimJ1Le5`, `dimJ1Le5_of_t34`, `dim_J1_le_of5` (drop-in for TailD:236),
  `G0Split.javanpeykarJ1_of_le (hR18) (hB) (h : DimJ1Le5) : JavanpeykarJ1` (drop-in for TailD:250);
  `example … : javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34 := rfl` compiles.
## Verbatim checks (python substring test): VERIFIED True for the 6 copied CurveBij theorems and the whole
## GenusBound namespace body (CurveSplit→GenusRoute); javanpeykarJ1_of_le differs from javanpeykarJ1 only in the
## renamed `h'` and the line `obtain … := h N J hN hJ`.

## GenusElem.lean — COMPILED, no errors, all #print axioms standard. VERIFIED.
- New leaf `GenusRoute.LocalDerivation`: F finite over ℚ(j), ConstantFieldIsQ F, P a place, π a local
  parameter (π ≠ 0, π ∈ 𝔪_P, 𝔪_P = π·𝒪_P) ⇒ ∃ δ : Derivation ℚ F F, δ π = 1 ∧ δ 𝒪_P ⊆ 𝒪_P.
  Source: Stichtenoth §4.1 (δ_t for a prime element t preserves 𝒪_P; Prop. 4.1.8, UNVERIFIED number);
  equivalently Ω_{𝒪_P/ℚ} free on dπ (Hartshorne II.8, UNVERIFIED numbers).
- `genusLeDegree_of_localDerivation : LocalDerivation → GenusLeDegree` (g(F) ≤ [F:ℚ(j)] for F with
  constant field ℚ and Belyi t). Proof pieces (all compiled): mem_span_D_sF (Ω_{F/ℚ} = F·dj via
  range_mapBaseChange + FormallyUnramified), deriv_unit_pow, decomp_nonunit, localParam_of,
  exists_uniformizer_all (twist for ∞), lift_mem_of_regularAt, local_conditions (h·dj holomorphic ⇒ h ∈ V),
  Vspace, mem_rat_of_all_places (Stacks 090P in Mathlib), exists_place_inf (FI at ∞), mem_OF_of_places
  (mem_integers_of_valuation_le_one), finrank_Vspace_le (V ↪ OF/j·OF ≅ ℚ^d by a ℚ[j]-basis of OF).
- `dimJ1Le_of_localDerivation : DimJacobianEqGenus → LocalDerivation → DimJ1Le`.
- No Riemann–Hurwitz, no identification of fieldGenus with another genus, no X0Transitive, no GenusX1Field.
## Fold.lean regenerated on GenusElem — COMPILED; adds `HDec.HSyn.t34Le_of_localDerivation`. VERIFIED.

## LocalDer.lean — COMPILED, axioms standard. VERIFIED.
- `GenusRoute.localDerivation : LocalDerivation` PROVED (the leaf is now a theorem).
  Pieces: isScalarTower_Q_Qj, essFiniteType_QF, sF_transcendental, nontrivial_kaehler
  (FormallyUnramified.iff_isSeparable), D_sF_ne_zero, exists_deriv_s (Projective.exists_dual_eq_one),
  exists_pow_mul_mem, frac_rep (𝒪_P = OF_𝔭 via valuationSubringAtPrime), inv_mem_of_not_mem_center,
  deriv_bound (ℚ[j]-basis of OF), residue_structure (OF/𝔭 finite over ℚ by
  finite_of_finite_type_of_isJacobsonRing; Field.exists_primitive_element; separable ⇒ g'(θ) unit),
  localDer_fin (iteration hQ, δ_s π ≠ 0, δ = δ_s/δ_s π), localDerivation (twist j ↦ 1/j at ∞).
- `dimJ1Le_of_dimJacobianEqGenus : DimJacobianEqGenus → DimJ1Le`, `genusLeDegree : GenusLeDegree`.
## Closed.lean — COMPILED (30 s), axioms standard. VERIFIED.
- dimjac-glue's DimJacGlue.lean (origin/wip/dimjac-glue 24435c82) verbatim (python substring test True)
  + LocalDer.lean verbatim (True) ⇒ `GenusRoute.dimJ1Le : DimJ1Le` with NO hypothesis.
## Fold.lean regenerated on Closed.lean — COMPILED (30 s). `HDec.HSyn.t34Le : DimJ1Le5` (no hypothesis),
## drop-ins dim_J1_le_of5, G0Split.javanpeykarJ1_of_le; Closed verbatim in Fold (True). VERIFIED.
## Fold.lean + refolded consumer — COMPILED (29 s), axioms standard. VERIFIED.
- `HDec.HSyn.glueOutputs_of_leaves3_t34Le`: TailD.lean:204-257 copied with only the name and the two
  lines (:236, :250) changed to `dim_J1_le_of5 t34Le …` / `javanpeykarJ1_of_le hR18 hBelyi t34Le …`;
  no `t.t34` left (python assert). Same type as `glueOutputs_of_leaves3`.
