import ZInQKernel.OneProof.H.TailA

/-! # theta-glue: `IgusaAlg k` proved by `ring` (copies of the definitions from ThetaGlue.lean) -/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue

/-- `ψ₆` as a function of the squares `t_m = θ_m²`. -/
def psi6T (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / 4) * ((t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2)


/-- `χ₁₂` as a function of the squares `t_m = θ_m²`. -/
def chi12T (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2)

/-- `ψ₄` as a function of the squares `t_m = θ_m²`. -/
def psi4T (t : PkgI1.Char2 → ℂ) : ℂ := (∑ m ∈ PkgI1.evenChars, t m ^ 4) / 4

/-- `χ₁₀` as a function of the squares `t_m = θ_m²`. -/
def chi10T (t : PkgI1.Char2 → ℂ) : ℂ := -(∏ m ∈ PkgI1.evenChars, t m) / 2 ^ 14


/-- The polynomials `P_k` with `e_k(θ_m⁸) = P_k(ψ₄, ψ₆, χ₁₀, χ₁₂)` (py/pk.py, exact). -/
def igusaP : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 3, a, b, _, d => (1081344 : ℂ) * d + (-8 / 27 : ℂ) * b ^ 2 + (116 / 27 : ℂ) * a ^ 3
  | 4, a, b, c, d => (-262144 / 3 : ℂ) * b * c + (1507328 : ℂ) * a * d + (-16 / 27 : ℂ) * a * b ^ 2 + (43 / 27 : ℂ) * a ^ 4
  | 5, a, b, c, d => (33017561088 : ℂ) * c ^ 2 + (131072 / 3 : ℂ) * a * b * c + (819200 : ℂ) * a ^ 2 * d + (-8 / 27 : ℂ) * a ^ 2 * b ^ 2 + (8 / 27 : ℂ) * a ^ 5
  | 6, a, b, c, d => (34628173824 : ℂ) * d ^ 2 + (-655360 / 9 : ℂ) * b ^ 2 * d + (16 / 729 : ℂ) * b ^ 4 + (50465865728 / 3 : ℂ) * a * c ^ 2 + (131072 / 3 : ℂ) * a ^ 2 * b * c + (1835008 / 9 : ℂ) * a ^ 3 * d + (-32 / 729 : ℂ) * a ^ 3 * b ^ 2 + (16 / 729 : ℂ) * a ^ 6
  | 7, a, b, c, d => (40802189312 / 3 : ℂ) * b * c * d + (-524288 / 81 : ℂ) * b ^ 3 * c + (23622320128 : ℂ) * a * d ^ 2 + (-524288 / 27 : ℂ) * a * b ^ 2 * d + (22011707392 / 9 : ℂ) * a ^ 2 * c ^ 2 + (524288 / 81 : ℂ) * a ^ 3 * b * c + (524288 / 27 : ℂ) * a ^ 4 * d
  | 8, a, b, c, d => (-290271069732864 : ℂ) * c ^ 2 * d + (10737418240 / 27 : ℂ) * b ^ 2 * c ^ 2 + (8589934592 / 3 : ℂ) * a * b * c * d + (4294967296 : ℂ) * a ^ 2 * d ^ 2 + (2147483648 / 27 : ℂ) * a ^ 3 * c ^ 2
  | 9, a, b, c, d => (281474976710656 : ℂ) * d ^ 3 + (-246290604621824 / 27 : ℂ) * b * c ^ 3 + (-175921860444160 / 3 : ℂ) * a * c ^ 2 * d
  | _, _, _, _, _ => 0



/-- The square `θ_m² = Σ_c (−1)^{(c+a)·b} U_c U_{c+a}` as a polynomial in the four second-order theta
constants `U_c = θ[c;0](2Ω)` (`thetaConst_sq_eq`). -/
def Sq (m : PkgI1.Char2) (u : (Fin 2 → Fin 2) → ℂ) : ℂ :=
  ∑ c : Fin 2 → Fin 2, (-1 : ℂ) ^ ((((c + m.1) 0 : Fin 2) : ℕ) * (m.2 0 : ℕ) +
    (((c + m.1) 1 : Fin 2) : ℕ) * (m.2 1 : ℕ)) * (u c * u (c + m.1))


/-- **GLUE (closed polynomial identity, weight `4k`; VERIFIED by exact expansion, py/verify_pk.py).**
For all `u : {0,1}² → ℂ`, with `t_m = Sq m u`: `e_k(t_m⁴) = P_k(ψ₄(t), ψ₆(t), χ₁₀(t), χ₁₂(t))`. -/
def IgusaAlg (k : ℕ) : Prop :=
  ∀ u : (Fin 2 → Fin 2) → ℂ,
    (PkgI1.evenChars.val.map (fun m => Sq m u ^ 4)).esymm k =
      igusaP k (psi4T (fun m => Sq m u)) (psi6T (fun m => Sq m u)) (chi10T (fun m => Sq m u))
        (chi12T (fun m => Sq m u))


/-! ## Explicit forms -/

def esymmL : List ℂ → ℕ → ℂ
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: l, k + 1 => esymmL l (k + 1) + a * esymmL l k

theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem esymm_coe (l : List ℂ) (k : ℕ) : (l : Multiset ℂ).esymm k = esymmL l k := by
  induction l generalizing k with
  | nil => cases k <;> simp [esymmL, Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a l ih =>
    cases k with
    | zero => simp [esymmL, Multiset.esymm]
    | succ k => rw [← Multiset.cons_coe, esymm_cons_succ, ih, ih, esymmL]

theorem evenChars_val : PkgI1.evenChars.val = (([(![0, 0], ![0, 0]), (![0, 0], ![0, 1]),
    (![0, 0], ![1, 0]), (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]),
    (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])] : List PkgI1.Char2) : Multiset PkgI1.Char2) := by decide


theorem univ_fin2_fin2 : (Finset.univ : Finset (Fin 2 → Fin 2)) =
    {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide

theorem Sq0 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![0, 0]) u = u ![0, 0] ^ 2 + u ![0, 1] ^ 2 + u ![1, 0] ^ 2 + u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq1 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![0, 1]) u = u ![0, 0] ^ 2 - u ![0, 1] ^ 2 + u ![1, 0] ^ 2 - u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq2 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![1, 0]) u = u ![0, 0] ^ 2 + u ![0, 1] ^ 2 - u ![1, 0] ^ 2 - u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq3 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![1, 1]) u = u ![0, 0] ^ 2 - u ![0, 1] ^ 2 - u ![1, 0] ^ 2 + u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq4 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 1], ![0, 0]) u = 2 * u ![0, 0] * u ![0, 1] + 2 * u ![1, 0] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq5 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 1], ![1, 0]) u = 2 * u ![0, 0] * u ![0, 1] - 2 * u ![1, 0] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq6 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 0], ![0, 0]) u = 2 * u ![0, 0] * u ![1, 0] + 2 * u ![0, 1] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq7 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 0], ![0, 1]) u = 2 * u ![0, 0] * u ![1, 0] - 2 * u ![0, 1] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq8 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 1], ![0, 0]) u = 2 * u ![0, 0] * u ![1, 1] + 2 * u ![0, 1] * u ![1, 0] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq9 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 1], ![1, 1]) u = 2 * u ![0, 0] * u ![1, 1] - 2 * u ![0, 1] * u ![1, 0] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem evenChars_eq : PkgI1.evenChars = {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]), (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by decide

theorem sum_evenChars (f : PkgI1.Char2 → ℂ) :
    ∑ m ∈ PkgI1.evenChars, f m = f (![0, 0], ![0, 0]) + f (![0, 0], ![0, 1]) + f (![0, 0], ![1, 0]) + f (![0, 0], ![1, 1]) + f (![0, 1], ![0, 0]) + f (![0, 1], ![1, 0]) + f (![1, 0], ![0, 0]) + f (![1, 0], ![0, 1]) + f (![1, 1], ![0, 0]) + f (![1, 1], ![1, 1]) := by
  rw [evenChars_eq]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, not_false_eq_true]
  ring

theorem prod_evenChars (f : PkgI1.Char2 → ℂ) :
    ∏ m ∈ PkgI1.evenChars, f m = f (![0, 0], ![0, 0]) * f (![0, 0], ![0, 1]) * f (![0, 0], ![1, 0]) * f (![0, 0], ![1, 1]) * f (![0, 1], ![0, 0]) * f (![0, 1], ![1, 0]) * f (![1, 0], ![0, 0]) * f (![1, 0], ![0, 1]) * f (![1, 1], ![0, 0]) * f (![1, 1], ![1, 1]) := by
  rw [evenChars_eq]
  simp (config := {decide := true}) only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, not_false_eq_true]
  ring

set_option maxHeartbeats 0 in
theorem igusaAlg3 : IgusaAlg 3 := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [psi4T, chi10T, psi6T, chi12T, igusaP, sum_evenChars, prod_evenChars, List.map, esymmL]
  simp only [Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  generalize u ![0, 0] = x0
  generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2
  generalize u ![1, 1] = x3
  ring

end HDec.HSyn.G0Split.ThetaPt.ThetaGlue

#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaGlue.igusaAlg3
