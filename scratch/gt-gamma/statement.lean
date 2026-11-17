-- Verbatim from ZInQKernel/OneProof/H/TailZ2.lean (namespace HDec.LeafQCheck.HM.QMSplit), lines 46-95.
-- Reference copy only (not compiled separately): the proof uses the chain's own constants.

/-- `Γ` acts on `ℍ` as a cocompact Fuchsian group (see `Valence.lean`). -/
structure IsCocompactFuchsian (Γ : Set (GL (Fin 2) ℝ)) : Prop where
  one_mem : 1 ∈ Γ
  mul_mem : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ
  inv_mem : ∀ a ∈ Γ, a⁻¹ ∈ Γ
  det_pos : ∀ a ∈ Γ, 0 < (a : Matrix (Fin 2) (Fin 2) ℝ).det
  properlyDiscontinuous : ∀ K : Set UpperHalfPlane, IsCompact K →
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, f = (fun z => γ • z) ∧ (f '' K ∩ K).Nonempty}.Finite
  cocompact : ∃ C : Set UpperHalfPlane, IsCompact C ∧ ∀ z, ∃ γ ∈ Γ, γ • z ∈ C

/-- A fundamental domain of `Γ` on `ℍ` (see `Valence.lean`). -/
def IsFundDomain (Γ : Set (GL (Fin 2) ℝ)) (s : Set UpperHalfPlane) : Prop :=
  MeasurableSet s ∧ (∀ z, ∃ γ ∈ Γ, γ • z ∈ s) ∧
    ∀ γ ∈ Γ, (fun z : UpperHalfPlane => γ • z) ≠ id →
      MeasureTheory.volume (s ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' s) = 0

/-- Every zero of `F` in `ℍ` is `Γ`-equivalent to a point of `T`. -/
def Covers (Γ : Set (GL (Fin 2) ℝ)) (T : Finset UpperHalfPlane) (F : ℂ → ℂ) : Prop :=
  ∀ z : UpperHalfPlane, F (z : ℂ) = 0 → ∃ t ∈ T, ∃ γ ∈ Γ, γ • t = z

/-- **LEAF (the valence formula for a cocompact Fuchsian group, equality form).** For `Γ` a cocompact
Fuchsian group with fundamental domain `s` and `F` a nonzero holomorphic automorphic form of weight
`k = 2m` (unitary multiplier): the zeros of `F` lie in finitely many `Γ`-orbits, and for a set `T` of
representatives (pairwise inequivalent, covering the zeros) `Σ_{P ∈ T} ord_P(F)/e_P = k·vol(s)/(4π)`; the
same sum over any finite set of pairwise inequivalent points is `≤ k·vol(s)/(4π)`.

Published form: Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16
and Thm. 2.20 (`Σ_{P ∈ Γ\ℍ} ν_P(F)/e_P = k·vol(Γ\ℍ)/(4π)` for `Γ` of the first kind without cusps; the zeros
are finitely many orbits since `Γ\ℍ` is compact); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4
(unitary multipliers); numbers UNVERIFIED. The third clause drops nonnegative terms. -/
def ValenceFormulaCocompactEq : Prop :=
  ∀ (Γ : Set (GL (Fin 2) ℝ)), IsCocompactFuchsian Γ → ∀ s, IsFundDomain Γ s →
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    (∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) ∧
        Covers Γ T F) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      Covers Γ T F →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) =
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi)) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) ≤
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi))

/-- **GLUE (`Γ*` is a cocompact Fuchsian group with covolume `π/6`)**, as in `Valence.lean` (row H-87). -/
def GammaStarCocompactArea : Prop :=
  IsCocompactFuchsian PkgI1.GammaStar ∧
    ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)

-- Verbatim from the same file, lines 1007-1020 (the open leaf `shimizuCovolumeO1`, also proved).
/-- `Γ¹ = ι(𝒪¹)`: the images of the norm-one units of `𝒪` (`det ι(x) = nrd(x)`). -/
def Gamma1 : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : PkgI1.B, PkgI1.InO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧
    (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1}

/-- **LEAF (Shimura; Shimizu's volume formula).** `Γ¹ = ι(𝒪¹)`, for the maximal order `𝒪` of the indefinite
division algebra `B` of discriminant `6`, is a cocompact Fuchsian group, with a fundamental domain of
hyperbolic area `(π/3) ∏_{p | 6} (p − 1) = 2π/3`. Shimura, *Introduction to the arithmetic theory of
automorphic functions*, 1971, Prop. 9.2 (cocompactness); H. Shimizu, *On zeta functions of quaternion
algebras*, Ann. of Math. 81 (1965) (volume); Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800,
IV §1; Voight, *Quaternion algebras*, Thm 39.1.13; locators UNVERIFIED. -/
def ShimizuCovolumeO1 : Prop :=
  IsCocompactFuchsian Gamma1 ∧
    ∃ s, IsFundDomain Gamma1 s ∧ MeasureTheory.volume s = ENNReal.ofReal (2 * Real.pi / 3)
