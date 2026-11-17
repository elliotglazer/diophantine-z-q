
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Shimura

/-! ## §7. The field-theory glue and `DiscNeZero`, proved; final forms -/

/-- **`AutExtends`, proved** (`exists_ringEquiv_extend`, Steinitz via Mathlib's transcendence
bases and `IsAlgClosure.equivOfEquiv`). -/
theorem autExtends : AutExtends := fun ρ => exists_ringEquiv_extend ιC ρ.toRingEquiv

/-- **`FixedAlgebraic`, proved** (`mem_range_of_fixed`). -/
theorem fixedAlgebraic : FixedAlgebraic := fun z hz => mem_range_of_fixed ιC z hz

/-- **`DiscNeZero`, proved** (`disc_ppD_ne_zero`: `Δ = (64π¹²/27)·1728·Δ_{Mathlib}(τ)`). -/
theorem discNeZero : DiscNeZero := fun τ => disc_ppD_ne_zero τ

/-- **`X0RatStructure` from the canonical-model leaf alone.** -/
theorem x0RatStructure_of_leaf (hL : X0ModuliGalois) : X0RatStructure :=
  x0RatStructure_of hL autExtends fixedAlgebraic discNeZero

/-- **`CMModuli` from the printed main theorem of CM and two glue Props**: `ArtinLift`
(surjectivity of the global Artin map onto `Gal(K^ab/K)`) and `IdeleLatticeScale` (the ring-class
lattice computation). -/
theorem cmModuli_of_leaf (hL : ShimuraMainCM) (hAL : ArtinLift) (hS : IdeleLatticeScale) :
    CMModuli :=
  cmModuli_of hL autExtends fixedAlgebraic hAL latHatInter
    (ideleLatticeHeegner_of hS strongApprox latHatInter)

/-- **Row T-5 (the kernel's `Shimura.ShimuraReciprocityModFn`) from two printed leaves and two glue
Props** (`ArtinLift`, `IdeleLatticeScale`). -/
theorem shimuraReciprocityModFn_of_t5Leaves (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hAL : ArtinLift) (hS : IdeleLatticeScale) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split (cmModuli_of_leaf hCM hAL hS) (x0RatStructure_of_leaf hX)

/-- **`CMModuli`, final form**: the printed main theorem of CM, the surjectivity of Tau Ceti's
absolute Artin map for `ℚ(√−m)`, and the ring-class lattice computation. -/
theorem cmModuli_of_final (hL : ShimuraMainCM) (hA : AbsArtinSurjectiveQNeg)
    (hS : IdeleLatticeScale) : CMModuli :=
  cmModuli_of_leaf hL (artinLift_of_abs hA) hS

/-- Row T-5 from two printed leaves and the two glue Props `AbsArtinSurjectiveQNeg`,
`IdeleLatticeScale`. -/
theorem shimuraReciprocityModFn_of_final (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hA : AbsArtinSurjectiveQNeg) (hS : IdeleLatticeScale) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split (cmModuli_of_final hCM hA hS) (x0RatStructure_of_leaf hX)

/-- **`CMModuli`, final form**: the printed main theorem of CM and the ring-class lattice
computation (`AbsArtinSurjectiveQNeg` is proved: `absArtinSurjectiveQNeg`). -/
theorem cmModuli_of_t5 (hL : ShimuraMainCM) (hS : IdeleLatticeScale) : CMModuli :=
  cmModuli_of_final hL absArtinSurjectiveQNeg hS

/-- **Row T-5 (the kernel's `Shimura.ShimuraReciprocityModFn`): final form.** Two printed leaves
(`ShimuraMainCM`: Shimura 1971 Thm. 5.4; `X0ModuliGalois`: the canonical model of `X₀(N)`) and one
glue Prop (`IdeleLatticeScale`: the ring-class lattice computation). -/
theorem shimuraReciprocityModFn_of_t5 (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hS : IdeleLatticeScale) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split (cmModuli_of_t5 hCM hS) (x0RatStructure_of_leaf hX)

end T5Glue

namespace T5Glue

open ZInQ.Contrib.TYZGenus.Shimura

/-- **Row T-5 with `IdeleLatticeScale` split**: two printed leaves and two small glue Props
(`RingClassLattice`: TC's ring-class quotient is the lattice class `[K ∩ s_f Ô_O]`;
`InvertibleColon`: `J ∩ O` is invertible). -/
theorem shimuraReciprocityModFn_of_t5' (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hA : RingClassLattice) (hB : InvertibleColon) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_t5 hCM hX (ideleLatticeScale_of hA hB)

/-- **`CMModuli` from the printed main theorem of CM and `RingClassLattice`.** -/
theorem cmModuli_of_t5' (hL : ShimuraMainCM) (hA : RingClassLattice) : CMModuli :=
  cmModuli_of_t5 hL (ideleLatticeScale_of hA invertibleColon)

/-- **Row T-5 (the kernel's `Shimura.ShimuraReciprocityModFn`): final form.** Two printed leaves
(`ShimuraMainCM`: Shimura 1971 Thm. 5.4; `X0ModuliGalois`: the canonical model of `X₀(N)`) and one
glue Prop (`RingClassLattice`: Tau Ceti's ring-class quotient of an idele `s` is the class of the
`O`-lattice `K ∩ s_f Ô_O`). -/
theorem shimuraReciprocityModFn_of_t5'' (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hA : RingClassLattice) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_t5' hCM hX hA invertibleColon

end T5Glue
