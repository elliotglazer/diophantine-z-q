module

import Mathlib.Topology.Algebra.Group.SubmonoidClosure

/-!
# A common return index in two compact groups

These anonymous applications use only the pinned Mathlib dependency. They are
optional examples, outside the accepted helper snapshot and the `ZInQ` root.
The source and the conditional connection to `CondZQ.HypCC` are in `lean/README.md`.

Apply recurrence to the pair first: both coordinates then use the same index.
The conclusion is arbitrarily late returns, not convergence of every iterate.
Neither infinite order nor commutativity is required.
-/

open Filter Set
open scoped Topology

section Additive

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [CompactSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [CompactSpace B] [IsTopologicalAddGroup B]

example (x : A) (y : B) (U : Set A) (V : Set B)
    (hU : U ∈ 𝓝 (0 : A)) (hV : V ∈ 𝓝 (0 : B)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ a • x ∈ U ∧ a • y ∈ V := by
  have h : ∃ᶠ a : ℕ in atTop, a • (x, y) ∈ U ×ˢ V :=
    mapClusterPt_iff_frequently.mp (mapClusterPt_zero_atTop_nsmul (x, y))
      (U ×ˢ V) (prod_mem_nhds hU hV)
  obtain ⟨a, ha, hUV⟩ := frequently_atTop.mp h (N + 1)
  exact ⟨a, lt_of_lt_of_le (Nat.lt_succ_self N) ha,
    lt_of_lt_of_le (Nat.zero_lt_succ N) ha, hUV.1, hUV.2⟩

end Additive

section Multiplicative

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [CompactSpace H] [IsTopologicalGroup H]

example (x : G) (y : H) (U : Set G) (V : Set H)
    (hU : U ∈ 𝓝 (1 : G)) (hV : V ∈ 𝓝 (1 : H)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ x ^ a ∈ U ∧ y ^ a ∈ V := by
  have h : ∃ᶠ a : ℕ in atTop, (x, y) ^ a ∈ U ×ˢ V :=
    mapClusterPt_iff_frequently.mp (mapClusterPt_one_atTop_pow (x, y))
      (U ×ˢ V) (prod_mem_nhds hU hV)
  obtain ⟨a, ha, hUV⟩ := frequently_atTop.mp h (N + 1)
  exact ⟨a, lt_of_lt_of_le (Nat.lt_succ_self N) ha,
    lt_of_lt_of_le (Nat.zero_lt_succ N) ha, hUV.1, hUV.2⟩

end Multiplicative

-- Inspect the axiom closures of the supplying results used above.
#print axioms mapClusterPt_zero_atTop_nsmul
#print axioms mapClusterPt_one_atTop_pow
#print axioms mapClusterPt_iff_frequently
#print axioms prod_mem_nhds
#print axioms Filter.frequently_atTop
#print axioms lt_of_lt_of_le
#print axioms Nat.lt_succ_self
#print axioms Nat.zero_lt_succ
