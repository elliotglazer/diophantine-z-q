
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura

/-! ## §6. Row T-5 (the kernel's `Shimura.ShimuraReciprocityModFn`) from the leaves and glue -/

/-- `HeegnerForm 0 D` is empty (tyz-split, verbatim). -/
theorem heegnerForm_level_pos {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have := Q.N_dvd
    simp only [Nat.cast_zero, zero_dvd_iff] at this
    exact absurd this (ne_of_gt Q.A_pos)
  · exact h

/-- tyz-split's `shimuraReciprocityModFn_of_split` (verbatim proof, over the copies of §3). -/
theorem shimuraReciprocityModFn_of_split (hCM : CMModuli) (hX : X0RatStructure) :
    ShimuraReciprocityModFn := by
  intro N g hg m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  have hN := heegnerForm_level_pos Q
  obtain ⟨x, hx, hx'⟩ := hCM N hN m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  exact hX N hN g hg Q.tauH Q'.tauH ρ x hx hx'

/-- **Row T-5 from two printed leaves** (`ShimuraMainCM`: Shimura 1971 Thm. 5.4; `X0ModuliGalois`:
the canonical model of `X₀(N)`), one textbook fact (`DiscNeZero`) and five glue Props
(`AutExtends`, `FixedAlgebraic`: field theory; `ArtinLift`: class field theory; `LatHatInter`,
`IdeleLatticeHeegner`: adelic lattice computations). -/
theorem shimuraReciprocityModFn_of_leaves (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hD : DiscNeZero) (hA : AutExtends) (hF : FixedAlgebraic) (hAL : ArtinLift)
    (hI : LatHatInter) (hH : IdeleLatticeHeegner) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split (cmModuli_of hCM hA hF hAL hI hH) (x0RatStructure_of hX hA hF hD)

end T5Glue
