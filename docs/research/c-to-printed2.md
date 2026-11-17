# c-to-printed2: `eigenformHTNew`, `r17` and `t09SymmIsogenyExists` against their printed theorems

Task c-to-printed2, 2026-11-14. Base e38375b3 (wip/w62, `frozenTarget` with 59 fields). Nothing under `ZInQKernel/` or
`blueprint/` was edited. The Lean is in `scratch/c-to-printed2/`, and the results log is `log.md` there. This is model
work with no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number, locator or printed wording recalled without a source.
There is no network on this host, so every printed statement quoted below is from memory and UNVERIFIED unless
`docs/research/locators.md` read it.

## 1. Main result

There are three fields, all GLUE (c) in leaf-fold10 §2. None is false, vacuous or inert as stated. No statement was
changed.

| field | result | leaf left | glue left |
|---|---|---|---|
| `eigenformHTNew` (`ZInQ.Contrib.HodgeSplit.EigenformHTNew`) | **a theorem from one realization leaf plus two existing bundle LEAF fields.** modular-split's open glue `HTDual` is now proved, and so is the semisimplicity of the contragredient. The field is **equivalent** to its realization leaf over the bundle, in both normalizations. | `KatoRealizationCohSS` (Kato's normalization, semisimple witness), or `KatoRealization` (Tate normalization) | none |
| `r17` (`LadicCond.CarayolR17'`) | **a theorem from one realization leaf** (modular-split's proof, re-checked against the top of the H assembly). New: the field is **equivalent** to the leaf over the bundle. | `CarayolRealization` | none |
| `t09SymmIsogenyExists` (`HDec.WeilPairing.T09_SymmIsogenyExists`) | **unchanged.** The printed statements are about `Pic⁰_{A/K}`, `φ_L` and Mumford's `e_n`, and none of these can be defined over Mathlib and the vendored Picard library today (§5). The field is already the smallest faithful substitute: an existential over genuine objects, witnessed by `(Pic⁰, e_n, φ_L)`. | — (the field itself) | — |

**What "equivalent over the bundle" means.** Write `DS` for the bundle LEAF fields `dsThm965`, `dsThm966`
(Deligne–Serre / Deligne in Diamond–Shurman's form), and `Tate` for the bundle LEAF fields `tateTwistInvariants`,
`axSenTate` (Tate 1967 §3.3, Thms 1–2). Then:

- `DS → (CarayolRealization ↔ CarayolR17')`;
- `DS → (KatoRealization ↔ EigenformHTNew)`;
- `DS → Tate → (KatoRealizationCohSS ↔ EigenformHTNew)`.

So the existential substitute for the undefinable object (Carayol's `σ_λ(π_f)`, Kato's `V_{F_λ}(f)`) loses nothing
relative to the field. Modulo those bundle leaves, each field says exactly as much as the existential leaf. The leaf
is in turn a consequence of the printed theorem at the author's realization, and strictly weaker than it.

**Strict kind.** For `eigenformHTNew` and `r17` the kind is unchanged: GLUE (c) under the strict reading, LEAF under the
lenient one. Each realization leaf is still a consequence, because the printed object is quantified existentially
(§2). What changed is that no project glue is left between leaf and field, and the leaf is as weak as the field allows
(equivalent to it modulo the bundle leaves above). A fold could replace the two fields by `KatoRealizationCohSS` (or `KatoRealization`) and
`CarayolRealization` (§6). Counts are SPECULATIVE until a fold applies this.

**VERIFIED** (`scratch/c-to-printed2/CToPrinted2_out.txt`):
- `lake env lean scratch/c-to-printed2/CToPrinted2.lean` (imports `ZInQKernel.OneProof.H.TailZ15`) gives 0 errors.
- 10 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`.
- `HTDual.lean` (imports `OneProof.H.TailT`) also compiles on its own, with standard axioms (`HTDual_out.txt`).
- The independent model review found no mathematical error. Its wording corrections are applied here and in two
  docstrings.

## 2. The printed theorems, the missing definitions, the substitutes

### 2.1 `eigenformHTNew`: Kato

**Field** (verbatim in `CToPrinted2.lean` §0, `rfl`-checked):

> For every `ℓ`, `ιC`, `ιL`, newform `f ∈ S_k(Γ₁(N))` with `k ≥ 2`, and **every** semisimple `ρ : G_ℚ → GL₂(ℚ̄_ℓ)`
> attached to `f` (Tate normalization), `ρ|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `{0, 1 − k}` (the cyclotomic
> character has weight `−1`).

**Printed theorem** (UNVERIFIED wording; locators read by `locators.md` row R13: Kato, Astérisque 295 (2004), §8.3
pp. 181–182 and §§9.2–9.4, (9.2.2), pp. 187–188):
- for a newform `f` of weight `k ≥ 2`, Kato defines a 2-dimensional `F_λ`-representation `V_{F_λ}(f)` of `G_ℚ`, a
  Hecke quotient of the étale cohomology of `Y₁(N)_ℚ̄` with coefficients `Sym^{k−2}` of the relative Tate module of
  the universal elliptic curve;
- this `V_{F_λ}(f)` is de Rham at `ℓ` (in fact potentially semistable, at every level);
- the Hodge filtration on `D_dR` has jumps `0` and `k − 1`.

**Definitions Mathlib lacks** for the print:
1. étale cohomology with coefficients (or the Kuga–Sato variety);
2. the modular curve `Y₁(N)` over `ℚ` with its universal elliptic curve;
3. the Hecke action on that cohomology, hence `V_{F_λ}(f)`.

Mathlib's `B_dR` (and the kernel's `IsDeRhamStd`) exist. But the Hodge–Tate conclusion is stated over the kernel's
genuine `htMult` (Tate's `H⁰(G, ℂ_ℓ(i) ⊗ V^∨)`), so the conclusion side needs nothing new.

**Smallest faithful substitute.** Replace the object `V_{F_λ}(f)` by "there is a `ρ`" carrying the properties that
determine `V_{F_λ}(f)` up to isomorphism, and keep Kato's conclusion. The leaf is `KatoRealizationCohSS`:

> For every `ℓ`, `ιC`, `ιL` and newform `f` of weight `k ≥ 2`, there is a semisimple continuous `ρ`, unramified at
> `p ∤ Nℓ`, whose **geometric** Frobenius traces are `a_p(f)`, and whose `ρ|_{G_{ℚ_ℓ}}` has Hodge–Tate weights
> `{0, k − 1}`.

The Frobenius and semisimplicity clauses determine `ρ` up to conjugacy: by Chebotarev with Brauer–Nesbitt
(`attachedConj_proof`, proved in the kernel), two such `ρ` are conjugate. So the existential pins down Kato's object.

**No stronger than the print.** The witness is `V_{F_λ}(f) ⊗_{F_λ, ιL ιC⁻¹} ℚ̄_ℓ`. Its clauses are:
- the Frobenius clause, which is the Eichler–Shimura–Deligne normalization of `H¹_ét` (Kato §8.3; UNVERIFIED);
- semisimplicity, from Ribet's irreducibility (Ribet 1977 for `k = 2`, Ribet 1985 in general; UNVERIFIED locators),
  which is stronger than semisimplicity;
- the weights, which are Kato's.

A second caveat is unchecked: Kato's Hecke quotient might have geometric Frobenius trace `ā_p` (complex
conjugate) rather than `a_p`. In that case the witness is `V_{F_λ}(f^*)` for the conjugate newform `f^*`, and the
leaf is still a consequence of the print.

The convention caveat is modular-split's (UNVERIFIED). In the kernel's convention, `ℚ_ℓ(1)` has weight `−1`, so `H¹`
of an elliptic curve has weights `{0, 1}`; this matches `{0, k − 1}` at `k = 2`. If Kato's `V_{F_λ}(f)` is in the
arithmetic normalization instead, its leaf is `KatoRealization` (Tate normalization, weights `{0, 1 − k}`). Both
leaves are given, and both are equivalent to the field over the bundle (§1). So the reduction does not depend on
which normalization Kato prints.

The stronger leaf `KatoRealizationCoh` (modular-split, irreducible witness) implies `KatoRealizationCohSS`
(`katoRealizationCohSS_of_coh`).

### 2.2 `r17`: Carayol

**Field** (verbatim, `rfl`-checked):

> For every `ℓ`, `ιC`, `ιL`, newform `f ∈ S₂(Γ₁(N))`, **every** semisimple attached `ρ`, and every prime `p ≠ ℓ`,
> `condExp(ρ|_{G_{ℚ_p}}) = v_p(N)`. Here `condExp` is the kernel's Serre–Tate conductor exponent.

**Printed theorem** (`locators.md` row R17 read it: Carayol, Ann. Sci. ÉNS (4) 19 (1986), Théorème (A), pp. 409–411,
and §0.8). Wording UNVERIFIED:
- for a cuspidal automorphic `π` of `GL₂` over a totally real `F`, here `F = ℚ` in weight 2, and a place `λ ∤ p` of
  the coefficient field, the restriction of `σ_λ(π)` to a decomposition group at `p` corresponds to `π_p` under the
  local Langlands correspondence;
- the audit read the coverage: every finite `p` and every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`.

The conductor clause also needs:
- the conductor of `π_p` is preserved by local Langlands;
- `a(π_{f,p}) = v_p(N)` for a newform (Casselman 1973; UNVERIFIED locator);
- the Weil–Deligne conductor equals the Serre–Tate conductor of the ℓ-adic representation (Grothendieck monodromy;
  `condExp` docstring).

**Definitions Mathlib lacks:**
1. cuspidal automorphic representations of `GL₂(𝔸_ℚ)` and `f ↦ π_f`;
2. smooth irreducible representations of `GL₂(ℚ_p)`, their conductor, and the local Langlands correspondence;
3. Weil–Deligne representations attached to ℓ-adic representations of `G_{ℚ_p}`;
4. `σ_λ(π)`, built from the étale cohomology of Shimura curves.

**Smallest faithful substitute** (modular-split's leaf `CarayolRealization`, unchanged):

> There is a semisimple continuous `ρ` attached to `f` with `condExp(ρ|_{G_{ℚ_p}}) = v_p(N)` for all `p ≠ ℓ`.

This keeps the numerical content of (A) and Casselman, stated over the kernel's genuine `condExp`.

**No stronger than the print.** The witness is `σ_λ(π_f) ⊗ ℚ̄_ℓ`, adjusted as needed:
- if Carayol uses geometric Frobenius, take its contragredient;
- if Carayol normalizes by an unramified twist (a power of the cyclotomic character, unramified at `p ≠ ℓ`), undo
  the twist.

The audit's row R17 says neither adjustment changes the conductor. The witness is irreducible by Ribet 1977, hence
semisimple.

New here: `carayolRealization_of_field`. Over `DS`, the field gives the leaf back, so the two are equivalent. The
converse direction takes the attached `ρ` that `DS` provides (hodge-split's `r14Det_of_printed`), applied with the
field.

## 3. `HTDual`, proved (`CToPrinted2.lean` §1–§5; also `HTDual.lean`)

```lean
theorem CToPrinted2.htDual_proof (hT : TateTwistInvariants) (hA : AxSenTate) : HTDual
```

`HTDual` and `dualGR` are modular-split's, copied verbatim. `HTDual` says: `ρ` Hodge–Tate with weights `S`,
`card S = n`, implies that `ρ^∨ = (σ ↦ ρ(σ⁻¹)ᵀ)` is Hodge–Tate with weights `−S`.

The proof uses hodge-split's coordinates `Y_i(ρ) = {y ∈ ℂ_ℓⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_E}` (`Ysp`), where `E` is a
finite Galois extension containing the entries. It reuses hodge-split's `exists_basis_Ysp` (Tate–Sen independence:
bases of the `Y_j` together are `ℂ_ℓ`-independent) and `htMult_eq_finrank_Ysp` (`htMult(ρ, w) = dim_E Y_{−w}(ρ)`).
1. `pair_twist`: for `y ∈ Y_i(ρ)` and `z ∈ Y_j(ρ^∨)`, `χ(σ)^{i+j} σ(yᵀz) = yᵀz` on `G_E`. So `yᵀz = 0` if `i + j ≠ 0`
   (Tate), and `yᵀz ∈ E` if `i + j = 0` (Ax–Sen–Tate).
2. Hodge–Tate means `Σ_j dim_E Y_j(ρ) = n`, so there is a `ℂ_ℓ`-basis `b_k ∈ Y_{j_k}(ρ)`.
3. `cvec_mem`: the dual basis `c_m` (`b_k ⬝ c_m = δ_{km}`) lies in `Y_{−j_m}(ρ^∨)`. Apply `σ` to `b_k ⬝ c_m = δ_{km}`
   and test against the basis.
4. `finrank_Ysp_dual`: by step 1, every `z ∈ Y_i(ρ^∨)` is `Σ_m (b_m ⬝ z) c_m`, with coefficients in `E` that vanish
   unless `j_m = −i`. So `dim_E Y_i(ρ^∨) = #{m | j_m = −i}`. The same lemma with `(c, b)` gives
   `dim_E Y_i(ρ) = #{m | j_m = i}`.
5. Hence `htMult(ρ^∨, w) = htMult(ρ, −w) = (−S).count w`.

Also new: `dualGR_isSemisimple`, the contragredient of a semisimple representation is semisimple. Take `W^⊥` for the
dot product (via `Subspace.finrank_add_finrank_dualAnnihilator_eq`). A `ρ`-stable complement `U` of `W^⊥` then gives
the `ρ^∨`-stable complement `U^⊥` of `W`. This lets the Kato leaf ask for semisimplicity only.

## 4. Lean names (all in `scratch/c-to-printed2/CToPrinted2.lean`, namespace `CToPrinted2`)

| statement | name |
|---|---|
| `TateTwistInvariants → AxSenTate → HTDual` | `htDual_proof` |
| contragredient of semisimple is semisimple | `dualGR_isSemisimple` |
| `KatoRealizationCohSS → Tate → EigenformHTNew` | `eigenformHTNew_of_printedSS` |
| `KatoRealizationCoh → Tate → EigenformHTNew` | `eigenformHTNew_of_printed` |
| `KatoRealization → EigenformHTNew` | `eigenformHTNew_of_realization` (modular-split) |
| `DS → (KatoRealization ↔ EigenformHTNew)` | `katoRealization_iff_field` |
| `DS → Tate → (KatoRealizationCohSS ↔ EigenformHTNew)` | `katoRealizationCohSS_iff_field` |
| `CarayolRealization → CarayolR17'` | `R17.carayolR17'_of_realization` (modular-split) |
| `DS → (CarayolRealization ↔ CarayolR17')` | `R17.carayolRealization_iff_field` |
| both fields from the two leaves and `OpenAddedLeaves9` | `fields_of_printed` |
| the three fields verbatim, `rfl` against the bundle constants | `Verbatim.*` (§0) |

## 5. `t09SymmIsogenyExists`: why it stays

**Field:** `∀ K A, Nonempty (SymmIsogeny A)`. That is, there are:
- an abelian variety `Â` (`D.dual`);
- pairings `e_n : A[n] × Â[n] → μ_n` for `n` invertible in `K` that are perfect, `G_K`-equivariant, compatible in
  `n`, and under which every endomorphism has a dual;
- an isogeny `λ : A → Â` with `e_n(x, λx) = 1`.

The objects are genuine: `AbVar` (proper smooth geometrically integral group scheme, `HDecomp/Objects.lean`), `K̄`-points,
torsion, `μ_n`, the Galois action and `IsIsogenyMor` (finite and surjective). The only invented structure, `WeilDual`,
occurs existentially. So the field is a true consequence and not a vacuous one.

**Printed statements** (Mumford, *Abelian varieties*; UNVERIFIED numbers):
- §6 Application 1: `A` is projective, so there is an ample `L`, and `φ_L` is an isogeny;
- §8 Thm 1 and §13: `Â = Pic⁰` exists;
- §20: `ē_n` is perfect, compatible and functorial (`e_n(x, f^∨y) = e_n(fx, y)`);
- §23: `e^L_n(x, x) = 1`.

Over a non-closed `K`, Milne 1986 §§8–16 applies (Galois equivariance from `K`-rationality). Every axiom of
`WeilDual` and `SymmIsogeny` is one of these printed properties of `(Pic⁰, ē_n, φ_L)`, so the field is no stronger
than the print.

**What exists now** (VERIFIED by reading `ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Picard/`):
- `Scheme.Pic` (isomorphism classes of invertible sheaves, `Basic.lean`) and `Scheme.Pic.map`;
- `picardFunctor f`, the relative Picard functor as an fppf sheaf for **any** `f : X ⟶ S` (`Sheaf.lean`);
- representability only for smooth proper geometrically integral **curves** over a separably closed field
  (`exists_representableBy_picardFunctor`, `exists_picardDegreeZeroScheme`).

Mathlib 4.35 has no ample line bundles (`grep Ample` in `Mathlib/AlgebraicGeometry` finds nothing; VERIFIED).

**Missing definitions, in the order a published-form chain needs them:**
1. Grothendieck's representability of `Pic_{A/K}` for `A` projective (FGA; Kleiman, *The Picard scheme*, Thm
   9.4.8; UNVERIFIED numbers). This is statable today over `picardFunctor`: **VERIFIED**, since
   `scratch/c-to-printed2/T09Roadmap.lean` (`PicRepresentableAbVar`, unused) compiles.
2. The identity component of a group scheme locally of finite type over `K`, and the theorem that `Pic⁰_{A/K}` is an
   abelian variety (Mumford §13; UNVERIFIED).
3. The translation `t_x` on `A_{K̄}`, and `φ_L(x) = t_x^*L ⊗ L⁻¹` through `Pic.map`; the theorem of the square.
4. Ample invertible sheaves (absent from Mathlib), for "`φ_L` is an isogeny".
5. Mumford's `e_n`. It needs isomorphisms of line bundles, not just classes: `[n]^*L ≅ 𝒪`, and translation acts on
   the trivialization by a scalar in `μ_n`. Alternatively, Cartier duality `Â[n] ≅ A[n]^D`.

With 1–5 in place, T09 becomes "Mumford §§20, 23 at `(Pic⁰, ē_n, φ_L)`" in published form. Until then the field is
itself the smallest faithful substitute. **Shortcuts ruled out:**
- `D.dual = A` over `K` needs an isomorphism `A ≅ Â` with the right pairings, i.e. essentially a principal
  polarization (av-split §4.1). Over `K̄` the `WeilDual` docstring notes that even `Â = A` carries a structure. That
  does not help over a number field, where Galois equivariance is the content;
- a `∀ D : WeilDual A` form would be unsafe (`WeilDual` docstring: over `K̄` even `Â = A` carries one).

## 6. Effect on the single proof (SPECULATIVE until a fold applies it)

- **`eigenformHTNew`.**
  - A fold can replace the field in `OpenResearchLeaves10` by `katoCohSS : CToPrinted2.KatoRealizationCohSS` and
    fill it with `eigenformHTNew_of_printedSS r.katoCohSS l.tateTwistInvariants l.axSenTate`.
  - Alternatively, use `kato : KatoRealization` with `eigenformHTNew_of_realization`, which needs no other field.
  - Either way the kind stays strict (c) → (c). The leaf is the weakest one, since it is equivalent to the old field.
- **`r17`.** A fold can replace the field by `carayol : CToPrinted2.R17.CarayolRealization` and fill it with
  `R17.carayolR17'_of_realization r.carayol`. The kind stays (c) → (c).
- **`t09SymmIsogenyExists`.** Unchanged.
- **Module.** `CToPrinted2.lean` imports `TailZ15` and holds the leaves and proofs.
  - Its §1–§7 need only `TailT` and `LadicCond`. `HTDual.lean` is §1–§5 on `TailT` alone.
  - A fold module should import `TailZ15` (for `fields_of_printed`) or be placed before the bundle that uses it.
- **Build notes.**
  - Under the `TailZ15` import, `IsGalois.mk` in `htDual_proof` hit the instance-synthesis limit (instance drift).
    It needs `set_option synthInstance.maxHeartbeats 400000 in`, which is in the file.
  - This worktree lacked the upstream helper build `lean/.lake`, so it was copied from `~/dzq-wt/leaf-fold10` (the
    sources are identical by `diff -rq`).

## 7. Files

- `scratch/c-to-printed2/CToPrinted2.lean`: everything (§0 verbatim fields, §1–§5 `HTDual`, §6 Kato, §7 Carayol, §9
  integration). Output: `CToPrinted2_out.txt`.
- `scratch/c-to-printed2/HTDual.lean`: §1–§5 alone, on `TailT`. Output: `HTDual_out.txt`.
- `scratch/c-to-printed2/T09Roadmap.lean`: statability check of Grothendieck's Picard representability (unused).
  Output: `T09Roadmap_out.txt` (empty, meaning no errors or warnings).
- `scratch/c-to-printed2/log.md`: results log.
- Sources copied verbatim: modular-split's `EigenHT.lean` and `R17.lean` (leaves, `dualGR`, `HTDual`, the conjugation
  lemmas) and the three field definitions.
