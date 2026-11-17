/-! ## Verified polynomial arithmetic in four variables (proof by reflection)

A polynomial is a list of terms `(c, (a, b, c', d))` standing for `c·x₀ᵃx₁ᵇx₂^{c'}x₃ᵈ`. The operations
`padd`, `pmul`, `ppow`, `pscale`, `esymmP` are evaluated by the kernel (`decide +kernel`); their
semantics (`ev_padd`, `ev_pmul`, …) are proved once, for all inputs. Sorted inputs give sorted,
duplicate-free outputs, so two normal forms are equal as lists iff the polynomials are equal (only
the direction "lists equal ⇒ values equal" is used, and it holds for all inputs). -/

abbrev Mono := ℕ × ℕ × ℕ × ℕ
abbrev Poly := List (ℤ × Mono)

/-- Decoding of packed literals (`a·256³ + b·256² + c·256 + d`); used only to write data compactly. -/
def unpackP (l : List (ℤ × ℕ)) : Poly :=
  l.map fun t => (t.1, (t.2 / 16777216, t.2 / 65536 % 256, t.2 / 256 % 256, t.2 % 256))

def evM (m : Mono) (x0 x1 x2 x3 : ℂ) : ℂ := x0 ^ m.1 * x1 ^ m.2.1 * x2 ^ m.2.2.1 * x3 ^ m.2.2.2

def ev (p : Poly) (x0 x1 x2 x3 : ℂ) : ℂ := (p.map fun t => (t.1 : ℂ) * evM t.2 x0 x1 x2 x3).sum

def madd (m n : Mono) : Mono := (m.1 + n.1, m.2.1 + n.2.1, m.2.2.1 + n.2.2.1, m.2.2.2 + n.2.2.2)

theorem evM_madd (m n : Mono) (x0 x1 x2 x3 : ℂ) :
    evM (madd m n) x0 x1 x2 x3 = evM m x0 x1 x2 x3 * evM n x0 x1 x2 x3 := by
  simp only [evM, madd, pow_add]; ring

def mbeq (m n : Mono) : Bool :=
  Nat.beq m.1 n.1 && Nat.beq m.2.1 n.2.1 && Nat.beq m.2.2.1 n.2.2.1 && Nat.beq m.2.2.2 n.2.2.2

theorem mbeq_eq {m n : Mono} (h : mbeq m n = true) : m = n := by
  obtain ⟨a, b, c, d⟩ := m
  obtain ⟨a', b', c', d'⟩ := n
  simp only [mbeq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4; rfl

def mlt (m n : Mono) : Bool :=
  Nat.blt m.1 n.1 || (Nat.beq m.1 n.1 && (Nat.blt m.2.1 n.2.1 || (Nat.beq m.2.1 n.2.1 &&
    (Nat.blt m.2.2.1 n.2.2.1 || (Nat.beq m.2.2.1 n.2.2.1 && Nat.blt m.2.2.2 n.2.2.2)))))

def merge : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, a :: p, [] => a :: p
  | n + 1, a :: p, b :: q =>
    if mbeq a.2 b.2 then
      (if a.1 + b.1 = 0 then merge n p q else (a.1 + b.1, a.2) :: merge n p q)
    else if mlt a.2 b.2 then a :: merge n p (b :: q)
    else b :: merge n (a :: p) q

theorem ev_nil (x0 x1 x2 x3 : ℂ) : ev [] x0 x1 x2 x3 = 0 := rfl

theorem ev_cons (t : ℤ × Mono) (p : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (t :: p) x0 x1 x2 x3 = (t.1 : ℂ) * evM t.2 x0 x1 x2 x3 + ev p x0 x1 x2 x3 := by
  simp [ev]

theorem ev_append (p q : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (p ++ q) x0 x1 x2 x3 = ev p x0 x1 x2 x3 + ev q x0 x1 x2 x3 := by
  simp [ev]

theorem ev_merge (x0 x1 x2 x3 : ℂ) : ∀ (n : ℕ) (p q : Poly),
    ev (merge n p q) x0 x1 x2 x3 = ev p x0 x1 x2 x3 + ev q x0 x1 x2 x3
  | 0, p, q => ev_append p q _ _ _ _
  | _ + 1, [], q => by simp [merge, ev_nil]
  | _ + 1, a :: p, [] => by simp [merge, ev_nil]
  | n + 1, a :: p, b :: q => by
    unfold merge
    by_cases h1 : mbeq a.2 b.2 = true
    · have hm := mbeq_eq h1
      rw [if_pos h1]
      by_cases h0 : a.1 + b.1 = 0
      · rw [if_pos h0, ev_merge x0 x1 x2 x3 n p q, ev_cons, ev_cons, hm]
        have h0' : (a.1 : ℂ) + (b.1 : ℂ) = 0 := by exact_mod_cast h0
        linear_combination (-evM b.2 x0 x1 x2 x3) * h0'
      · rw [if_neg h0, ev_cons, ev_merge x0 x1 x2 x3 n p q, ev_cons, ev_cons, hm]
        push_cast; ring
    · rw [if_neg h1]
      by_cases h3 : mlt a.2 b.2 = true
      · rw [if_pos h3, ev_cons, ev_merge x0 x1 x2 x3 n p (b :: q)]; simp only [ev_cons]; ring
      · rw [if_neg h3, ev_cons, ev_merge x0 x1 x2 x3 n (a :: p) q]; simp only [ev_cons]; ring

/-- Fuel large enough for every merge in this file (each step consumes one term). -/
def fuel : ℕ := 1000000

def padd (p q : Poly) : Poly := merge fuel p q

theorem ev_padd (p q : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (padd p q) x0 x1 x2 x3 = ev p x0 x1 x2 x3 + ev q x0 x1 x2 x3 := ev_merge _ _ _ _ _ _ _

def pmulT (t : ℤ × Mono) (q : Poly) : Poly := q.map fun s => (t.1 * s.1, madd t.2 s.2)

theorem ev_pmulT (t : ℤ × Mono) (q : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (pmulT t q) x0 x1 x2 x3 = (t.1 : ℂ) * evM t.2 x0 x1 x2 x3 * ev q x0 x1 x2 x3 := by
  induction q with
  | nil => simp [pmulT, ev_nil]
  | cons s q ih =>
    simp only [pmulT, List.map_cons] at ih ⊢
    rw [ev_cons, ih, ev_cons, evM_madd]; push_cast; ring

def pmulAux (q : Poly) : Poly → Poly → Poly
  | acc, [] => acc
  | acc, t :: p => pmulAux q (padd acc (pmulT t q)) p

theorem ev_pmulAux (q : Poly) (x0 x1 x2 x3 : ℂ) : ∀ (acc p : Poly),
    ev (pmulAux q acc p) x0 x1 x2 x3 = ev acc x0 x1 x2 x3 + ev p x0 x1 x2 x3 * ev q x0 x1 x2 x3
  | acc, [] => by simp [pmulAux, ev_nil]
  | acc, t :: p => by
    rw [pmulAux, ev_pmulAux q x0 x1 x2 x3 _ p, ev_padd, ev_pmulT, ev_cons]; ring

def pmul (p q : Poly) : Poly := pmulAux q [] p

theorem ev_pmul (p q : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (pmul p q) x0 x1 x2 x3 = ev p x0 x1 x2 x3 * ev q x0 x1 x2 x3 := by
  rw [pmul, ev_pmulAux, ev_nil, zero_add]

def pone : Poly := [(1, (0, 0, 0, 0))]

theorem ev_pone (x0 x1 x2 x3 : ℂ) : ev pone x0 x1 x2 x3 = 1 := by simp [pone, ev, evM]

def ppow (p : Poly) : ℕ → Poly
  | 0 => pone
  | n + 1 => pmul (ppow p n) p

theorem ev_ppow (p : Poly) (x0 x1 x2 x3 : ℂ) : ∀ n,
    ev (ppow p n) x0 x1 x2 x3 = ev p x0 x1 x2 x3 ^ n
  | 0 => by simp [ppow, ev_pone]
  | n + 1 => by rw [ppow, ev_pmul, ev_ppow p x0 x1 x2 x3 n, pow_succ]

def pscale (c : ℤ) (p : Poly) : Poly := p.map fun t => (c * t.1, t.2)

theorem ev_pscale (c : ℤ) (p : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (pscale c p) x0 x1 x2 x3 = (c : ℂ) * ev p x0 x1 x2 x3 := by
  induction p with
  | nil => simp [pscale, ev_nil]
  | cons t p ih =>
    simp only [pscale, List.map_cons] at ih ⊢
    rw [ev_cons, ih, ev_cons]; push_cast; ring

def psub (p q : Poly) : Poly := padd p (pscale (-1) q)

theorem ev_psub (p q : Poly) (x0 x1 x2 x3 : ℂ) :
    ev (psub p q) x0 x1 x2 x3 = ev p x0 x1 x2 x3 - ev q x0 x1 x2 x3 := by
  rw [psub, ev_padd, ev_pscale]; push_cast; ring

def pneg (p : Poly) : Poly := pscale (-1) p

theorem ev_pneg (p : Poly) (x0 x1 x2 x3 : ℂ) : ev (pneg p) x0 x1 x2 x3 = -ev p x0 x1 x2 x3 := by
  rw [pneg, ev_pscale]; push_cast; ring

/-- `e_j` of a list of polynomials, as a vector `[e_0, …, e_K]`, one pass over the list. -/
def esymmStep (a : Poly) (v : List Poly) : List Poly :=
  List.zipWith (fun vj vjm => padd vj (pmul a vjm)) v ([] :: v)

def esymmVec (K : ℕ) : List Poly → List Poly
  | [] => pone :: List.replicate K []
  | a :: l => esymmStep a (esymmVec K l)
