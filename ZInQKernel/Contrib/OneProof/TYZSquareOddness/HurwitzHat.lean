import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HamiltonAdeleTensor

/-!
# Literal integral-coefficient Hurwitz finite-adèle subgroup

This port uses the actual Mathlib finite-adèle coefficient ring and its componentwise
integral subalgebra. The additive subgroup below has precisely the original five-coefficient
carrier, with real shift `-e/2` and imaginary shifts `+e/2`. No H29 predicate/model or desired
unit factorization premise is introduced. Both inverse memberships later refer to actual Units.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness

private abbrev Zhat := ScalarFiniteAdeles.integralAdeles

lemma intCast_mem_Zhat (n : ℤ) : (n : AQ) ∈ Zhat := by
  simpa using Zhat.algebraMap_mem (n : NumberField.RingOfIntegers ℚ)

/-- The actual literal Hurwitz-hat carrier as a real additive subgroup. -/
def hurwitzHatAddSubgroup : AddSubgroup ℍ[AQ] where
  carrier := {x | ∃ a b c d e : AQ,
    a ∈ Zhat ∧ b ∈ Zhat ∧ c ∈ Zhat ∧ d ∈ Zhat ∧ e ∈ Zhat ∧
      x = ⟨a - e * algebraMap ℚ AQ (1 / 2), b + e * algebraMap ℚ AQ (1 / 2),
        c + e * algebraMap ℚ AQ (1 / 2), d + e * algebraMap ℚ AQ (1 / 2)⟩}
  zero_mem' := by
    refine ⟨0, 0, 0, 0, 0, Zhat.zero_mem, Zhat.zero_mem, Zhat.zero_mem,
      Zhat.zero_mem, Zhat.zero_mem, ?_⟩
    apply Quaternion.ext <;> simp
  add_mem' := by
    rintro x y ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩
      ⟨a', b', c', d', e', ha', hb', hc', hd', he', rfl⟩
    refine ⟨a + a', b + b', c + c', d + d', e + e', Zhat.add_mem ha ha',
      Zhat.add_mem hb hb', Zhat.add_mem hc hc', Zhat.add_mem hd hd', Zhat.add_mem he he', ?_⟩
    apply Quaternion.ext <;> dsimp <;> ring
  neg_mem' := by
    rintro x ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩
    refine ⟨-a, -b, -c, -d, -e, Zhat.neg_mem ha, Zhat.neg_mem hb,
      Zhat.neg_mem hc, Zhat.neg_mem hd, Zhat.neg_mem he, ?_⟩
    apply Quaternion.ext <;> dsimp <;> ring

@[simp] lemma mem_hurwitzHatAddSubgroup (x : ℍ[AQ]) :
    x ∈ hurwitzHatAddSubgroup ↔ ∃ a b c d e : AQ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        a v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        b v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        c v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        d v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        e v ∈ v.adicCompletionIntegers ℚ) ∧
      x = ⟨a - e * algebraMap ℚ AQ (1 / 2), b + e * algebraMap ℚ AQ (1 / 2),
        c + e * algebraMap ℚ AQ (1 / 2), d + e * algebraMap ℚ AQ (1 / 2)⟩ := Iff.rfl

lemma hurwitzHat_zero : (0 : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := hurwitzHatAddSubgroup.zero_mem
lemma hurwitzHat_one : (1 : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
  refine ⟨1, 0, 0, 0, 0, Zhat.one_mem, Zhat.zero_mem, Zhat.zero_mem, Zhat.zero_mem, Zhat.zero_mem, ?_⟩
  apply Quaternion.ext <;> simp
lemma hurwitzHat_add {x y : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) (hy : y ∈ hurwitzHatAddSubgroup) :
    x + y ∈ hurwitzHatAddSubgroup := hurwitzHatAddSubgroup.add_mem hx hy
lemma hurwitzHat_neg {x : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) :
    -x ∈ hurwitzHatAddSubgroup := hurwitzHatAddSubgroup.neg_mem hx
lemma hurwitzHat_sub {x y : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) (hy : y ∈ hurwitzHatAddSubgroup) :
    x - y ∈ hurwitzHatAddSubgroup := hurwitzHatAddSubgroup.sub_mem hx hy
lemma hurwitzHat_zsmul (z : ℤ) {x : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) :
    z • x ∈ hurwitzHatAddSubgroup := hurwitzHatAddSubgroup.zsmul_mem hx z

lemma hurwitzHat_integral_smul {a : AQ} (ha : a ∈ Zhat) {x : ℍ[AQ]}
    (hx : x ∈ hurwitzHatAddSubgroup) : a • x ∈ hurwitzHatAddSubgroup := by
  obtain ⟨b, c, d, e, f, hb, hc, hd, he, hf, rfl⟩ := hx
  refine ⟨a * b, a * c, a * d, a * e, a * f, Zhat.mul_mem ha hb, Zhat.mul_mem ha hc,
    Zhat.mul_mem ha hd, Zhat.mul_mem ha he, Zhat.mul_mem ha hf, ?_⟩
  apply Quaternion.ext <;> dsimp <;> ring

end TYZSquareOddness
