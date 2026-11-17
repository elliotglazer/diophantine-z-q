import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.Contrib.OneProof.JonesPall
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

/-!
# TYZ's arithmetic admissible quaternion embeddings over the original quadratic fields

This is a minimal arithmetic source port, not an H29 or H10 assembly. The source construction is
`Deicyde/diophantine-z-q@c1e4ed1b8765f016c8fd5808e79bb0124b364952`,
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:617–780` (Hurwitz coordinates at 256–257).
The original carrier `ZInQ.RouteK.Rank5b.QNeg n` and its genuine field/number-field instances are
imported from the original upstream `RedeiStatement` module. No new number-field model or
shadow H29 proposition is defined.

The representation suppliers are the canonical Jones–Pall and common Atlas sources of upstream
PR134 at `fd991dc09912ba1616586edca7f5317eb11050f9`; that source dependency is unmerged at the
publication base. It is recorded explicitly, never treated as an accepted main dependency or
copied into a second provider. The final literal theorem includes n = 1 and every actual
ring-of-integers element, not just a chosen generator.

Changes from the fork: own namespace and upstream imports; genuine membership/representation
statements written literally rather than copying missing H29 Prop aliases; the actual quadratic
algebra generator is `QuadraticAlgebra.omega`. Trace/norm, denominator, parity and lift proof
bodies follow the source construction. Source epochs and attribution are recorded separately.
-/

noncomputable section
set_option autoImplicit false

namespace ZInQ.Contrib.TYZTauArithmetic

open NumberField ZInQ.RouteK.Rank5b

/-- The full composite representation needed for the embedding, with no supplied premise. -/
theorem representation_of_squarefree :
    ∀ n : ℕ, Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
      ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ (n % 8 = 1 → 4 ∣ c) := by
  intro n hsq hcl
  rcases hcl with h1 | h3
  · obtain ⟨a, b, c, h⟩ := ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof n hsq h1
    exact ⟨a, b, 4 * c, by rw [h]; ring, fun _ => ⟨c, rfl⟩⟩
  · have hnot : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
      rintro ⟨a, b, hab⟩
      rcases a with _ | a
      · rw [pow_zero, one_mul] at hab
        omega
      · have h2 : 2 ∣ n := ⟨2 * 4 ^ a * (8 * b + 7), by rw [hab, pow_succ]; ring⟩
        omega
    obtain ⟨a, b, c, h⟩ :=
      ZInQ.Contrib.OneProof.LegendreThreeSquares.Atlas.Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven n hnot
    refine ⟨(a : ℤ), (b : ℤ), (c : ℤ), ?_, fun h1 => by omega⟩
    exact_mod_cast h.symm

/-- The pure Hamilton quaternion `ai + bj + ck`. -/
def pure (a b c : ℤ) : Quaternion ℚ := ⟨0, a, b, c⟩

theorem pure_mul_self {n : ℕ} {a b c : ℤ}
    (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    pure a b c * pure a b c = (-(n : ℚ)) • (1 : Quaternion ℚ) + (0 : ℚ) • pure a b c := by
  have hq : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by exact_mod_cast h
  apply Quaternion.ext <;> simp [pure, hq] <;> ring

/-- Genuine ℚ-algebra map defined by the quadratic algebra's universal property. -/
def tauOf (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    QNeg n →ₐ[ℚ] Quaternion ℚ :=
  QuadraticAlgebra.lift ⟨pure a b c, pure_mul_self h⟩

theorem tauOf_apply (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2)
    (x : QNeg n) : tauOf n h x = ⟨x.re, x.im * a, x.im * b, x.im * c⟩ := by
  rw [tauOf, QuadraticAlgebra.lift_apply_apply]
  apply Quaternion.ext <;> simp [pure, Algebra.smul_def]

/-- Actual integral elements have integral trace and norm, proved without a generator model. -/
theorem trace_norm_int {n : ℕ} [NeZero n] (x : RingOfIntegers (QNeg n)) :
    (∃ m : ℤ, (m : ℚ) = 2 * (x : QNeg n).re) ∧
      ∃ N : ℤ, (N : ℚ) = (x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2 := by
  have hx : IsIntegral ℤ (x : QNeg n) := x.2
  have hs : IsIntegral ℤ (star (x : QNeg n)) := hx.map ((starRingEnd (QNeg n)).toIntAlgHom)
  have h1 : (x : QNeg n) + star (x : QNeg n) = algebraMap ℚ (QNeg n) (2 * (x : QNeg n).re) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have h2 : (x : QNeg n) * star (x : QNeg n) =
      algebraMap ℚ (QNeg n) ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have i1 : IsIntegral ℤ (2 * (x : QNeg n).re) := by
    have := hx.add hs
    rw [h1] at this
    exact isIntegral_algebraMap_iff.mp this
  have i2 : IsIntegral ℤ ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    have := hx.mul hs
    rw [h2] at this
    exact isIntegral_algebraMap_iff.mp this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp i1
  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp i2
  exact ⟨⟨m, by simpa using hm⟩, ⟨N, by simpa using hN⟩⟩

/-- `n w² ∈ ℤ` with squarefree natural n forces the rational w to be integral. -/
theorem int_of_squarefree_mul_sq {n : ℕ} (hn : Squarefree n) {w : ℚ} {k : ℤ}
    (h : (n : ℚ) * w ^ 2 = k) : ∃ z : ℤ, (z : ℚ) = w := by
  have hden : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_nz
  have hw : w = w.num / w.den := (Rat.num_div_den w).symm
  have key : (n : ℤ) * w.num ^ 2 = k * (w.den : ℤ) ^ 2 := by
    have : (n : ℚ) * (w.num : ℚ) ^ 2 = k * (w.den : ℚ) ^ 2 := by
      rw [hw] at h
      field_simp at h
      linarith
    exact_mod_cast this
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact w.reduced
  have hd : (w.den : ℤ) ^ 2 ∣ (n : ℤ) * w.num ^ 2 := ⟨k, by rw [key]; ring⟩
  have hd2 : (w.den : ℤ) ^ 2 ∣ (n : ℤ) := hcop.dvd_of_dvd_mul_right hd
  have hd3 : w.den * w.den ∣ n := by
    have : ((w.den * w.den : ℕ) : ℤ) ∣ (n : ℤ) := by push_cast; rwa [← sq]
    exact_mod_cast this
  have h1 : w.den = 1 := Nat.isUnit_iff.mp (hn _ hd3)
  exact ⟨w.num, by rw [hw, h1]; simp⟩

theorem parity_one {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 1) * V ^ 2) :
    (∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  all_goals (exfalso; ring_nf at h; omega)

theorem parity_three {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 3) * V ^ 2) :
    ((∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t) ∨ ((∃ s, m = 2 * s + 1) ∧ ∃ t, V = 2 * t + 1) := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact Or.inl ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  · exfalso; ring_nf at h; omega
  · exfalso; ring_nf at h; omega
  · exact Or.inr ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩

theorem odd_of_three {a b c k : ℤ} (h : 8 * k + 3 = a ^ 2 + b ^ 2 + c ^ 2) :
    (∃ a', a = 2 * a' + 1) ∧ (∃ b', b = 2 * b' + 1) ∧ ∃ c', c = 2 * c' + 1 := by
  rcases Int.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> rcases Int.even_or_odd' b with ⟨b', rfl | rfl⟩ <;>
    rcases Int.even_or_odd' c with ⟨c', rfl | rfl⟩
  all_goals first
    | exact ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    | (exfalso; ring_nf at h; omega)

/-- Every actual ring-of-integers element lands in the genuine five-integer Hurwitz lattice. -/
theorem tauOf_ringOfIntegers {n : ℕ} [NeZero n] (hsq : Squarefree n)
    (hcl : n % 8 = 1 ∨ n % 8 = 3) {a b c : ℤ}
    (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    ∀ x : RingOfIntegers (QNeg n), ∃ A B C D E : ℤ,
      tauOf n h (x : QNeg n) =
        ⟨(A : ℚ) - (E : ℚ) / 2, (B : ℚ) + (E : ℚ) / 2,
          (C : ℚ) + (E : ℚ) / 2, (D : ℚ) + (E : ℚ) / 2⟩ := by
  intro x
  obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := trace_norm_int x
  set u := (x : QNeg n).re with hu
  set v := (x : QNeg n).im with hv
  have hV : (n : ℚ) * (2 * v) ^ 2 = ((4 * N - m ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [hN, hm]; ring
  obtain ⟨V, hVv⟩ := int_of_squarefree_mul_sq hsq hV
  have hEq : 4 * N = m ^ 2 + (n : ℤ) * V ^ 2 := by
    have : ((4 * N : ℤ) : ℚ) = ((m ^ 2 + (n : ℤ) * V ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [hN, hm, hVv]; ring
    exact_mod_cast this
  have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + ((n % 8 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod n 8).symm
  rw [tauOf_apply]
  have hev : (∃ s, m = 2 * s) ∧ (∃ t, V = 2 * t) →
      ∃ A B C D E : ℤ, (⟨u, v * a, v * b, v * c⟩ : Quaternion ℚ) =
        ⟨(A : ℚ) - (E : ℚ) / 2, (B : ℚ) + (E : ℚ) / 2,
          (C : ℚ) + (E : ℚ) / 2, (D : ℚ) + (E : ℚ) / 2⟩ := by
    rintro ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
    have hus : u = s := by push_cast at hm; linarith
    have hvt : v = t := by push_cast at hVv; linarith
    refine ⟨s, t * a, t * b, t * c, 0, ?_⟩
    apply Quaternion.ext <;> simp [hus, hvt]
  rcases hcl with h1 | h3
  · rw [h1] at hk
    push_cast at hk
    rw [hk] at hEq
    exact hev (parity_one hEq)
  · rw [h3] at hk
    push_cast at hk
    rw [hk] at hEq
    rcases parity_three hEq with he | ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
    · exact hev he
    · rw [hk] at h
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := odd_of_three h
      have hus : u = s + 1 / 2 := by push_cast at hm; linarith
      have hvt : v = t + 1 / 2 := by push_cast at hVv; linarith
      refine ⟨s + 1, 2 * t * a' + t + a', 2 * t * b' + t + b', 2 * t * c' + t + c', 1, ?_⟩
      have e1 : (x : QNeg n).re = s + 1 / 2 := hu ▸ hus
      have e2 : (x : QNeg n).im = t + 1 / 2 := hv ▸ hvt
      rw [e1, e2]
      apply Quaternion.ext <;> simp <;> ring

/-- Full literal upstream arithmetic τ statement; no missing H29 Prop is aliased or assumed. -/
theorem tyzTauExists :
    ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
      ∃ τ : ZInQ.RouteK.Rank5b.QNeg n →ₐ[ℚ] Quaternion ℚ,
        (∀ x : NumberField.RingOfIntegers (ZInQ.RouteK.Rank5b.QNeg n), ∃ a b c d e : ℤ,
          τ (x : ZInQ.RouteK.Rank5b.QNeg n) =
            ⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
              (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩) ∧
        (n % 8 = 1 → ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ 4 ∣ c ∧
          τ (QuadraticAlgebra.omega : ZInQ.RouteK.Rank5b.QNeg n) =
            ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩) := by
  intro n _ hsq hcl
  obtain ⟨a, b, c, habc, h4⟩ := representation_of_squarefree n hsq hcl
  refine ⟨tauOf n habc, tauOf_ringOfIntegers hsq hcl habc, fun hn => ⟨a, b, c, habc, h4 hn, ?_⟩⟩
  rw [tauOf_apply]
  apply Quaternion.ext <;> simp [QuadraticAlgebra.omega]

end ZInQ.Contrib.TYZTauArithmetic
