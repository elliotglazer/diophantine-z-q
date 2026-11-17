-- Verbatim copy of ZInQKernel/OneProof/H/TailZ2.lean lines 36-90 (namespace HDec.LeafQCheck.HM.QMSplit),
-- the statement ValenceFormulaCocompactEq and the definitions it uses. U is
-- HSyn.G0Split.FibreQM.PeriodMap.U (ZInQKernel/OneProof/H/TailJ.lean L45): def U : Set ℂ := {z : ℂ | 0 < z.im}.
-- Not compiled standalone (reference copy).

/-- `G20 = ∏θ²∘Ω/dF¹⁰`. -/
abbrev G20 : ℂ → ℂ := HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20

/-! ## Genuine definitions (as in `Valence.lean`) -/

/-- `e_P` for a general `Γ`: the number of distinct Möbius maps of elements of `Γ` fixing `P`. -/
noncomputable def ellOrderOf (Γ : Set (GL (Fin 2) ℝ)) (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • P = P ∧ f = fun z => γ • z}

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
