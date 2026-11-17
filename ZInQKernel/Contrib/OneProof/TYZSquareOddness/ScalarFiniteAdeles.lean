import Mathlib

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Algebraic scalar finite-adèle primitives on the actual rational carrier

The carrier is Mathlib's `FiniteAdeleRing (RingOfIntegers ℚ) ℚ`. This file ports only the
algebraic integral-component, denominator and finite-CRT approximation cuts of public
Tau Ceti `5a01f5fe3621126cccf9ba22e700493cbc7b7156`:
* `RingTheory/DedekindDomain/FiniteAdeleRing/Basic.lean`, 112–128, 206–212, 229–308;
* `RingTheory/DedekindDomain/AdicValuation/Approximation.lean`, 45–58;
* the single-place argument of `AdicValuation/Completion.lean`, 313–324 and 387–417.

Copyright (c) 2026 The Tau Ceti contributors. Source released under Apache 2.0; full source,
license and change notices are retained separately. This new application uses Mathlib's
valuation-ball openness, density in a single completion and integer approximation directly;
it imports no Tau Ceti topology/Henselian/extension world. No abstract approximation or
lattice-result input is assumed. All prime indices are the actual height-one primes.
-/

noncomputable section
set_option autoImplicit false

open IsDedekindDomain NumberField
open IsDedekindDomain.HeightOneSpectrum WithZero

namespace TYZSquareOddness

/-- A definitional convenience for the actual Mathlib finite adèles of ℚ, not a new carrier. -/
abbrev AQ : Type := FiniteAdeleRing (RingOfIntegers ℚ) ℚ

namespace ScalarFiniteAdeles

/-- Actual integral finite adèles, with their literal componentwise carrier. -/
def integralAdeles : Subalgebra (RingOfIntegers ℚ) AQ where
  carrier := {a | ∀ v : HeightOneSpectrum (RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' {a b} ha hb v := by
    change a v * b v ∈ _
    exact mul_mem (ha v) (hb v)
  add_mem' {a b} ha hb v := by
    change a v + b v ∈ _
    exact add_mem (ha v) (hb v)
  algebraMap_mem' r v := by
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers ℚ) ℚ, FiniteAdeleRing.algebraMap_apply]
    exact v.coe_mem_adicCompletionIntegers r

@[simp] theorem mem_integralAdeles {a : AQ} :
    a ∈ integralAdeles ↔ ∀ v : HeightOneSpectrum (RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- The actual completion algebra map, not a potentially different rational-cast notation. -/
theorem valued_algebraMap (v : HeightOneSpectrum (RingOfIntegers ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self_apply]
  exact valuedAdicCompletion_eq_valuation' v q

theorem valued_integer_algebraMap (v : HeightOneSpectrum (RingOfIntegers ℚ))
    (r : RingOfIntegers ℚ) :
    Valued.v (algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (RingOfIntegers ℚ) ℚ, valued_algebraMap,
    valuation_of_algebraMap]

/-- The rational diagonal meets actual integral components exactly in the original integer ring. -/
theorem algebraMap_mem_integralAdeles_iff (q : ℚ) :
    algebraMap ℚ AQ q ∈ integralAdeles ↔ q ∈ (algebraMap (RingOfIntegers ℚ) ℚ).range := by
  simp only [mem_integralAdeles, FiniteAdeleRing.algebraMap_apply, mem_adicCompletionIntegers,
    valuedAdicCompletion_eq_valuation']
  refine ⟨mem_integers_of_valuation_le_one ℚ q, ?_⟩
  rintro ⟨r, rfl⟩ v
  exact v.valuation_le_one r

/-- Fully literal diagonal criterion with an actual integer witness. -/
theorem diagonal_integral_iff (q : ℚ) :
    algebraMap ℚ AQ q ∈ integralAdeles ↔ ∃ m : ℤ, q = (m : ℚ) := by
  rw [algebraMap_mem_integralAdeles_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
    exact hr.symm.trans (Rat.ringOfIntegersEquiv_apply_coe r).symm
  · rintro ⟨m, rfl⟩
    exact ⟨(m : RingOfIntegers ℚ), by simp⟩

/-- A finite adèle has one actual nonzero integer-ring denominator. -/
theorem mul_nonZeroDivisor_mem_integralAdeles (a : AQ) :
    ∃ b ∈ nonZeroDivisors (RingOfIntegers ℚ),
      a * algebraMap (RingOfIntegers ℚ) AQ b ∈ integralAdeles := by
  classical
  have hT : {v : HeightOneSpectrum (RingOfIntegers ℚ) | a v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb0 hb using fun v : HeightOneSpectrum (RingOfIntegers ℚ) =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hT.toFinset, b v, prod_mem fun v _ => hb0 v,
    mem_integralAdeles.mpr fun v => ?_⟩
  change a v * algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) _ ∈ _
  by_cases hv : v ∈ hT.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, map_mul, ← mul_assoc]
    exact mul_mem (hb v) (v.coe_mem_adicCompletionIntegers _)
  · exact mul_mem (by simpa using hv) (v.coe_mem_adicCompletionIntegers _)

/-- One nonzero ordinary integer clears every component of the given finite adèle. -/
theorem common_integer_denominator (a : AQ) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : AQ) * a ∈ integralAdeles := by
  obtain ⟨b, hb, hab⟩ := mul_nonZeroDivisor_mem_integralAdeles a
  let m : ℤ := Rat.ringOfIntegersEquiv b
  have hbEq : b = (m : RingOfIntegers ℚ) := by
    apply Rat.ringOfIntegersEquiv.injective
    simp [m]
  have hm : m ≠ 0 := by
    intro hm0
    apply nonZeroDivisors.ne_zero hb
    rw [hbEq, hm0]
    simp
  refine ⟨m, hm, ?_⟩
  rw [hbEq, map_intCast] at hab
  simpa only [mul_comm] using hab

/-- Actual single-place approximation by the original ring of integers, to an integral power bound.
The open valuation ball and Mathlib's integer approximation replace unused Henselian scaffolding. -/
theorem single_place_approximation (v : HeightOneSpectrum (RingOfIntegers ℚ))
    (x : v.adicCompletionIntegers ℚ) (n : ℕ) :
    ∃ r : RingOfIntegers ℚ,
      Valued.v ((x : v.adicCompletion ℚ) - algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) r) ≤
        exp (-(n : ℤ)) := by
  let δ : ℤᵐ⁰ := exp (-(n : ℤ))
  have hδ0 : δ ≠ 0 := exp_ne_zero
  have hδ1 : δ ≤ 1 := exp_le_one_iff.mpr (by omega)
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective ℚ δ
  have hr0 : Valued.v.restrict z ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hz]
    exact hδ0
  have hopen : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ δ} := by
    have heq : {y : v.adicCompletion ℚ | Valued.v y ≤ δ} =
        {y : v.adicCompletion ℚ | Valued.v.restrict y ≤ Valued.v.restrict z} := by
      ext y
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.restrict_le_iff, hz]
    rw [heq]
    exact Valued.isOpen_closedBall _ hr0
  let U : Set (v.adicCompletion ℚ) := {y | Valued.v (y - (x : v.adicCompletion ℚ)) ≤ δ}
  have hUopen : IsOpen U := hopen.preimage (continuous_sub_right (x : v.adicCompletion ℚ))
  have hxU : (x : v.adicCompletion ℚ) ∈ U := by
    change Valued.v ((x : v.adicCompletion ℚ) - x) ≤ δ
    simp
  obtain ⟨q, hq⟩ := (v.denseRange_algebraMap (K := ℚ)).exists_mem_open hUopen ⟨x, hxU⟩
  have hqx : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - (x : v.adicCompletion ℚ)) ≤ δ := hq
  have hqIntegral : v.valuation ℚ q ≤ 1 := by
    have h : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
      calc
        Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) =
            Valued.v ((algebraMap ℚ (v.adicCompletion ℚ) q - x) + x) := by simp
        _ ≤ 1 := Valuation.map_add_le _ (hqx.trans hδ1) x.2
    rwa [valued_algebraMap] at h
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hqIntegral (Units.mk0 δ hδ0)
  change v.valuation ℚ (algebraMap (RingOfIntegers ℚ) ℚ r - q) < δ at hr
  have hqr : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q -
      algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) r) ≤ δ := by
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers ℚ) ℚ, ← map_sub,
      valued_algebraMap, Valuation.map_sub_swap]
    exact hr.le
  refine ⟨r, ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap ℚ (v.adicCompletion ℚ) q)]
  exact Valuation.map_add_le _ (by rw [Valuation.map_sub_swap]; exact hqx) hqr

/-- Finite CRT approximation of the actual local integral elements, not of an invented coefficient model. -/
theorem finite_crt_approximation (s : Finset (HeightOneSpectrum (RingOfIntegers ℚ)))
    (x : ∀ v : HeightOneSpectrum (RingOfIntegers ℚ), v.adicCompletionIntegers ℚ)
    (n : HeightOneSpectrum (RingOfIntegers ℚ) → ℕ) :
    ∃ r : RingOfIntegers ℚ, ∀ v ∈ s,
      Valued.v ((x v : v.adicCompletion ℚ) - algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) r) ≤
        exp (-(n v : ℤ)) := by
  choose a ha using fun v : HeightOneSpectrum (RingOfIntegers ℚ) =>
    single_place_approximation v (x v) (n v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun v => v.asIdeal) n
    (fun v _ => v.prime) (fun _ _ _ _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v)
  refine ⟨r, fun v hv => ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) (a v))]
  refine Valuation.map_add_le _ (ha v) ?_
  rw [← map_sub, valued_integer_algebraMap, Valuation.map_sub_swap,
    intValuation_le_pow_iff_mem]
  exact hr v hv

/-- Every actual finite adèle differs from an actual rational diagonal by integral components at ALL primes. -/
theorem exists_sub_diagonal_integral (a : AQ) :
    ∃ q : ℚ, ∀ v : HeightOneSpectrum (RingOfIntegers ℚ),
      a v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  classical
  obtain ⟨d, hd0, hda⟩ := mul_nonZeroDivisor_mem_integralAdeles a
  replace hda (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
      a v * algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) d ∈ v.adicCompletionIntegers ℚ :=
    mem_integralAdeles.mp hda v
  replace hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd0
  have hD : {v : HeightOneSpectrum (RingOfIntegers ℚ) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let N : HeightOneSpectrum (RingOfIntegers ℚ) → ℕ := fun v => multiplicity v.asIdeal (Ideal.span {d})
  have hvd (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
      Valued.v (algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) d) = exp (-(N v : ℤ)) := by
    rw [valued_integer_algebraMap, v.intValuation_eq_exp_neg_multiplicity hd0]
  obtain ⟨r, hr⟩ := finite_crt_approximation hD.toFinset
    (fun v => ⟨a v * algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) d, hda v⟩) N
  let q : ℚ := algebraMap (RingOfIntegers ℚ) ℚ r / algebraMap (RingOfIntegers ℚ) ℚ d
  have key (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - a v) * exp (-(N v : ℤ)) =
        Valued.v (a v * algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) d -
          algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) r) := by
    have hd : algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ) d ≠ 0 := fun h =>
      exp_ne_zero (by rw [← hvd v, h, map_zero])
    rw [← hvd v, ← map_mul]
    dsimp [q]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      sub_mul, div_mul_cancel₀ _ hd, Valuation.map_sub_swap]
  refine ⟨q, fun v => ?_⟩
  have hbound : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - a v) ≤ 1 := by
    by_cases hv : v ∈ hD.toFinset
    · have h := hr v hv
      rw [← key v] at h
      exact le_of_mul_le_mul_right (a := exp (-(N v : ℤ)))
        (by simpa only [one_mul] using h) exp_pos
    · have hN : N v = 0 := multiplicity_eq_zero_of_not_dvd fun h => hv (hD.mem_toFinset.mpr h)
      have hkey := key v
      rw [hN, Nat.cast_zero, neg_zero, exp_zero, mul_one] at hkey
      rw [hkey]
      exact Valuation.map_sub_le _ (hda v) (v.coe_mem_adicCompletionIntegers r)
  rw [mem_adicCompletionIntegers, Valuation.map_sub_swap]
  exact hbound

end ScalarFiniteAdeles
end TYZSquareOddness
