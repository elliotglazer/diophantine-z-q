module

public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

public section

namespace V15RetainedContact

open Polynomial

def P5 (r : ℚ) : ℚ :=
  r^5 - (35893742479489 / 3813373161796 : ℚ)*r^4 +
    (122376041313918 / 3813373161796 : ℚ)*r^3 -
    (192222345736537 / 3813373161796 : ℚ)*r^2 +
    (141822723674536 / 3813373161796 : ℚ)*r -
    (39896049934224 / 3813373161796 : ℚ)

def obstruction : ℤ[X] :=
  C (-35893742479489)*X^8 + C 122376041313918*X^6 -
    C 192222345736537*X^4 + C 141822723674536*X^2 - C 39896049934224

theorem obstruction_no_rational_root (s : ℚ) : aeval s obstruction ≠ 0 := by
  intro hs
  have hdeg : obstruction.natDegree = 8 := by unfold obstruction; compute_degree
  have hlc : obstruction.leadingCoeff = (-35893742479489 : ℤ) := by
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [obstruction]
  let n : ℤ := IsFractionRing.num ℤ s
  let d : ℤ := IsFractionRing.den ℤ s
  have hd : (d : ZMod 5) ≠ 0 := by
    obtain ⟨k, hk⟩ := den_dvd_of_is_root hs
    rw [hlc] at hk
    intro hzero
    have hm := congrArg (Int.castRingHom (ZMod 5)) hk
    change (-35893742479489 : ZMod 5) = (d : ZMod 5) * (k : ZMod 5) at hm
    norm_num [hzero] at hm
  have hn := num_isRoot_scaleRoots_of_aeval_eq_zero hs
  change (obstruction.scaleRoots d).eval n = 0 at hn
  rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, hdeg] at hn
  norm_num [Finset.sum_range_succ, Polynomial.coeff_scaleRoots, hdeg, obstruction] at hn
  have hm := congrArg (Int.castRingHom (ZMod 5)) hn
  push_cast at hm
  generalize hn5 : (n : ZMod 5) = a at hm
  generalize hd5 : (d : ZMod 5) = b at hm hd
  fin_cases a <;> fin_cases b <;> norm_num at hm hd

/-- Unrestricted rational contact obstruction; no sign or inverse guard. -/
theorem contact_nonzero (t q : ℚ)
    (h : (1+q)*P5 ((t-1)^2) = ((t-1)^2)^5) : q ≠ 0 := by
  intro hq
  subst q
  apply obstruction_no_rational_root (t-1)
  norm_num [obstruction]
  norm_num [P5] at h
  linear_combination (3813373161796 : ℚ)*h

/-- The five literal source contact factors, with all rational t and q retained. -/
theorem contact_product_nonzero (t q : ℚ)
    (h : (1+q) * (((t-1)^2-1) * ((t-1)^2-9/4) * ((t-1)^2-4) *
      ((t-1)^2-(2398/2399)^2) * ((t-1)^2-(439/407)^2)) = ((t-1)^2)^5) :
    q ≠ 0 := by
  apply contact_nonzero t q
  convert h using 1 <;> norm_num [P5] <;> ring

def Retained (A input inputSq a b c v q f g T R w : ℚ) : Prop :=
  input^2-inputSq=0 ∧
  a^2-2*a*T-b*T+T^2=0 ∧
  b^2-c*T=0 ∧
  -141822723674536*b*T+35893742479489*b*w+192222345736537*c*T-
    3813373161796*c*w+3813373161796*v+39896049934224*T^2-
    122376041313918*T*w=0 ∧
  c*w-v-v*q=0 ∧
  6255001+255102*inputSq+2601*inputSq^2-4*f=0 ∧
  14315517724+291790992*inputSq+15531948*inputSq*f+767410608*f-512*f^2+g=0 ∧
  T-R^2=0 ∧
  22201*g*R+R-A*g=0 ∧
  b*c-T*w=0

theorem retained_nonzero (A input inputSq a b c v q f g T R w : ℚ)
    (hA : A ≠ 0) (h : Retained A input inputSq a b c v q f g T R w) :
    R ≠ 0 ∧ T ≠ 0 ∧ q ≠ 0 := by
  rcases h with ⟨h9,h43,h44,h45,h46,h56,h57,h68,h71,h73⟩
  have hsq : 0 ≤ inputSq := by nlinarith only [h9, sq_nonneg input]
  have hf : f = (6255001+255102*inputSq+2601*inputSq^2)/4 := by linarith only [h56]
  rw [hf] at h57
  have hg : g = 51948354689656+28892074377045*inputSq+
      1634130961866*inputSq^2+32365650141*inputSq^3+216486432*inputSq^4 := by
    linear_combination h57
  have hgpos : 0 < g := by rw [hg]; positivity
  have hR : R ≠ 0 := by
    intro hz
    have hzero : A*g=0 := by rw [hz] at h71; nlinarith only [h71]
    exact mul_ne_zero hA (ne_of_gt hgpos) hzero
  have hT : T ≠ 0 := by
    have hpos : 0 < R^2 := sq_pos_of_ne_zero hR
    intro hz
    nlinarith only [h68, hpos, hz]
  refine ⟨hR,hT,?_⟩
  let t := a/T
  let r := b/T
  have hrt : r=(t-1)^2 := by
    dsimp [r,t]
    field_simp [hT]
    linear_combination -h43
  have hbc : c/T=r^2 := by
    dsimp [r]
    field_simp [hT]
    linear_combination -h44
  have hwr : w/T=r^3 := by
    dsimp [r]
    field_simp [hT]
    linear_combination -T*h73-b*h44
  have hb : b=r*T := by dsimp [r]; field_simp [hT]
  have hc : c=r^2*T := (div_eq_iff hT).mp hbc
  have hw : w=r^3*T := (div_eq_iff hT).mp hwr
  have hv : v=P5 r*T^2 := by
    rw [hb,hc,hw] at h45
    unfold P5
    linear_combination (1/3813373161796 : ℚ)*h45
  have hcontact : (1+q)*P5 r=r^5 := by
    rw [hc,hw,hv] at h46
    have heq : ((1+q)*P5 r-r^5)*T^2=0 := by linear_combination -h46
    have := (mul_eq_zero.mp heq).resolve_right (pow_ne_zero 2 hT)
    linarith only [this]
  rw [hrt] at hcontact
  exact contact_nonzero t q hcontact

/-- Literal raw224 rows 9,43--46,56--57,68,71,73. -/
def Raw224Ten (A : ℚ) (x : ℕ → ℚ) : Prop :=
  Retained A (x 1) (x 55) (x 98) (x 99) (x 100) (x 101) (x 102)
    (x 113) (x 114) (x 125) (x 126) (x 128)

theorem raw224_q_nonzero (A : ℚ) (x : ℕ → ℚ) (hA : A ≠ 0) (h : Raw224Ten A x) :
    x 102 ≠ 0 := (retained_nonzero _ _ _ _ _ _ _ _ _ _ _ _ _ hA h).2.2

theorem raw224_family_q_nonzero (N : ℤ) (x : ℕ → ℚ)
    (h : Raw224Ten ((149 : ℚ)^(2*N+1)) x) : x 102 ≠ 0 :=
  raw224_q_nonzero _ x (zpow_ne_zero _ (by norm_num)) h

end V15RetainedContact
