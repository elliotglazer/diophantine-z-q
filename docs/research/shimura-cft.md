# shimura-cft: Shimura's Main Theorem I with its reciprocity law; `shimuraFamily` and `shimuraFamilyAb` from it

Task shimura-cft (2026-11-14/15). Base e38375b3. Files: `scratch/shimura-cft/ShimuraCFT.lean` (one file, no
`sorry`, no `axiom`), results log `scratch/shimura-cft/log.md`. There was no network, so every locator and every
"printed" wording below is UNVERIFIED unless it is marked otherwise.

## 1. Main result

**Shimura's Main Theorem I for the level-3 group of `B = (2, −3 | ℚ)`, reciprocity law included, is now one Lean
Prop over genuine definitions.** These are Mathlib's schemes, finite adeles, ideles and quaternion algebras, plus Tau
Ceti's global Artin map `ideleClassArtinMap` and adelic base change `finiteAdeleBaseChangeAlgEquiv`, both vendored in
`ZInQKernel/Contrib/TauCeti/`. The Prop is in Deligne's adelic form, on the moduli scheme `Y₃` over `ℚ`. Both fields
follow from it with no glue (all compiled; every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`):

| field | theorem | inputs |
|---|---|---|
| `shimuraFamilyAb` (route-a-fold's `QMSplit.Moduli.ShimuraFamilyAb`) | `ShimuraCFT.shimuraFamilyAb_of_mainThmI` | LEAF `ShimuraMainThmIDeligneY3Ab` |
| `shimuraFamily` (the kernel's `QMSplit.Moduli.ShimuraFamily`) | `ShimuraCFT.shimuraFamily_of_mainThmIAb` | LEAF `ShimuraMainThmIDeligneY3Ab` + LEAF `MumfordRigidityCore` (r1univ-rigid) |
| `shimuraFamily` | `ShimuraCFT.shimuraFamily_of_mainThmI` | `ShimuraMainThmIDeligneY3` (the same leaf with `R1fpProps`) |

`mainThmI_iff_ab : MumfordRigidityCore → (ShimuraMainThmIDeligneY3 ↔ ShimuraMainThmIDeligneY3Ab)`.

The new leaf also implies c-to-printed's leaf: `mainThmIY3_of_mainThmI : ShimuraMainThmIDeligneY3 →
CToPrinted.Shimura.ShimuraMainThmIY3`. Its fibre clause at `g = 1` is c-to-printed's `Γ(3)`-orbit clause, because
`K₃ ∩ B^×_+ = Γ(3)` (`dcRel_one_iff`, proved).

**The canonical-model clause can be stated, and is stated.** No definition is missing. Deligne showed that Shimura's
system of models `(V_S, φ_S)` over the fields `k_S` is the same thing as one canonical model `M_K` of
`G(ℚ)\(X × G(𝔸_f))/K` over the reflex field, here `ℚ`. For `K = K₃` that model is the moduli scheme `Y₃`, and its
complex points are `B^×_+\(ℍ × (B⊗𝔸_f)^×)/K₃`. Shimura's `V_S` over `k_S = ℚ(ζ₃)` and Deligne's comparison
`Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ` come out of clauses 1 and 4 below with Deligne's comparison. Clause 1 gives
`π₀ = ℚ^×_{>0}\𝔸_f^×/nrd K₃ = (ℤ/3)^×`, and clause 4 gives the Galois action on `π₀` through `nrd q̂(s)`. The leaf is
Deligne's form over `ℚ`, so no model over `ℚ(ζ₃)` has to be named.

Shimura's own per-`S` form is also statable: a scheme `V` over `Spec ℚ(ζ₃)` with `φ : ℍ → V(ℂ)`. Linking that form to
`Y₃` would need the comparison as a separate theorem (Deligne 1971 §4), so it was not chosen. §5 has the details.

## 2. The leaf

`ShimuraCFT.ShimuraMainThmIDeligneY3Ab : Prop :=
  ∃ Y Φ, R1fpPropsAb Y Φ ∧ ShimuraDeligneBody Y Φ`

`ShimuraDeligneBody Y Φ` asks for a map `Ψ : ℍ → (B ⊗ 𝔸_f)^× → Y(ℂ)` with the four clauses below.

1. **Uniformization.** `Ψ` is onto, and `Ψ(τ, g) = Ψ(τ', g')` iff `(τ', g') = (γτ, γ g k)` for some `γ ∈ B` with
   `nrd γ > 0` and some `k ∈ K₃` (`DCRel`). So `Ψ` induces `B^×_+\(ℍ × G(𝔸_f))/K₃ ≃ Y(ℂ)`.
2. **Complex structure.** `τ ↦ Ψ(τ, g)` is holomorphic for every `g`. This is `ShimuraSplit.IsHolFamily`: preimages
   of Zariski opens are open, and regular functions pull back to analytic functions.
3. **Moduli interpretation at `g = 1`.** `IsShimuraHolFamily Y Φ (Ψ · 1)`, shimura-split's clause, verbatim. The
   object at `Ψ(τ, 1)` is `ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `ι`.
4. **Shimura's reciprocity law at CM points.** There are `ε : ℤˣ` and `δ : Bool` such that the following holds for
   every imaginary quadratic `K` (`NumberField`, `IsTotallyComplex`, `finrank ℚ K = 2`), every `κ : K →+* ℂ`, every
   `q : K →ₐ[ℚ] B` and every `z ∈ ℍ` with `IsCMPoint q (κ or conj ∘ κ, by δ) z`. For every idele `s` of `K` and every
   `σ ∈ Aut(ℂ)` with `ArtinCondC κ σ s` (that is, `σ = [s, K]` on `K^ab`), and every `g`:
   `σ(Ψ(z, g)) = Ψ(z, q̂(s_f)^ε · g)`.

**Definitions** (Part B of the file; the first five are new over Mathlib, Tau Ceti and the kernel):
- `AQ = FiniteAdeleRing (𝓞 ℚ) ℚ` and `BAQ = (2, −3 | AQ)`.
- `ZhatQ`, `OhatQ` and `K3Q = {k ∈ 𝒪̂^× : k ≡ 1 mod 3𝒪̂}`. These are the kernel's `ShimuraGlue.Zhat`, `Ohat` and
  `K3` (TailZ12), with `𝓞 ℚ` in place of `ℤ`. That change makes Tau Ceti's base change applicable.
- `bEmb : B →ₐ[ℚ] B ⊗ 𝔸_f`.
- `qHat q : 𝔸_{K,f} →+* B ⊗ 𝔸_f`. This is `a ⊗ k ↦ a·q(k)`, read through Tau Ceti's `𝔸_{ℚ,f} ⊗_ℚ K ≅ 𝔸_{K,f}`.
  `qHat_algebraMap` checks that it extends `q`.
- `qHatU q : 𝕀_K →* (B⊗𝔸_f)^×`, which is `s ↦ q̂(s_f)`.
- `ArtinCondC κ σ s`. It holds when, for every finite abelian `L/K` and every `K`-embedding `j : L → ℂ`,
  `σ ∘ j = j ∘ ideleClassArtinMap K L [s]`. Tau Ceti's map sends uniformizers to arithmetic Frobenius (t5-glue
  checked this normalization).
- `galPt σ y = Spec σ ≫ y`.
- `IsCMPoint q κ z`. It holds when `ι(q(a))·(z, 1)ᵀ = κ(a)·(z, 1)ᵀ` for all `a ∈ K`, with `ι = BPAnalytic.QM.iota`.
- `DCRel`. Here `γ` acts on `ℍ` through `ι(γ) ∈ GL₂(ℝ)` and Mathlib's action, as in c-to-printed's `InGamma3`
  clause.

**Sources** (UNVERIFIED):
- Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of Math. 85 (1967), Main
  Theorem I, and §§2-3 for the moduli construction when `F = ℚ`.
- Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§3-4: the adelic reformulation, the characterization
  `σ[h, g] = [h, r(s)g]` at special points, and the moduli interpretation for quaternion algebras over `ℚ`.
- Milne, *Introduction to Shimura varieties* (2005), §§12-14.

## 3. Faithfulness: why the leaf is not stronger than the print

- **Conventions are existential.** The signs `ε` and `δ` absorb the conventions:
  - Deligne's 1971 versus 1979 normalization of the reciprocity map;
  - `h_z` versus `h_{z̄}` in identifying `ℍ` with `X⁺`, which swaps the reflex embedding `κ ↔ κ̄`;
  - `Spec σ ≫ y` versus its inverse.

  Each convention changes the law only by `s ↦ s⁻¹` (absorbed by `ε`) or `s ↦ s̄` (absorbed by `δ`). For the second,
  `(q, z)` is κ̄-normalized iff `(q ∘ c, z)` is κ-normalized, and `q̂(c s) = (q ∘ c)^(s)`. Since one choice of
  `(ε, δ)` is the true convention, the clause is a consequence of the print.
- **`ℍ` with `B^×_+` instead of `ℍ^±` with `B^×`.** This is the standard equivalent form: `B` is indefinite, so an
  element of negative norm swaps the two half planes.
- **Weakened.**
  - The biholomorphism `Sh_{K₃}(ℂ) ≅ Y₃(ℂ)^an` becomes a bijection plus holomorphy in `τ`.
  - The moduli interpretation is kept at `g = 1` only.
  - The field-of-moduli clause (`k_S(φ_S(z))` is the class field of `K^× q^{-1}(S)`) is dropped. It follows from
    clauses 1 and 4.
- **Inherited caveats.**
  - The polarization caveat (Lemma QP) for `R1fpProps`/`R1fpPropsAb`, as for every leaf on these witnesses.
  - The reading "the fine moduli scheme `Y₃` *is* `Sh_{K₃}(B^×, ℍ^±)` over `ℚ`" (Deligne §4). This is the same reading
    as the kernel leaf `DeligneComponentsY3Printed`.
- **Not vacuous.**
  - The reciprocity hypotheses can be met for either value of `δ`: `K = ℚ(√−3)`, `q(√−3) = j`, `z = i√3`
    (`recip_hyp_nonempty`).
  - Every `σ ∈ Aut(ℂ/κ(K))` satisfies `ArtinCondC κ σ s` for some idele `s` (`exists_artinCondC`). This uses t5-glue's
    proof that Tau Ceti's absolute Artin map is surjective when `K` has no real places. So clause 4 fixes
    `σ(Ψ(z, g))` for all such `σ`.

  Both are in Part C/D of the file; their status is in §4.
- **The leaf is at least as strong as the earlier one.** `mainThmIY3_of_mainThmI`: the orbit clause of c-to-printed's
  `ShimuraMainThmIY3` is the `g = g' = 1` case of clause 1, via `K₃ ∩ B^×_+ = Γ(3)` (`dcRel_one_iff`, proved).

## 4. What compiles

`scratch/shimura-cft/ShimuraCFT.lean` (`lake env lean`, about 13 s, 8.6 GB):
- Part A: verbatim copies of `R1UnivLeaves.lean` lines 10-564 (the `R1UnivRigid` core), c-to-printed's
  `Shimura.lean`, and `ShimuraFamilyAb`.
- Part B: the definitions, the leaf, and `shimuraFamilyAb_of_mainThmI`, `shimuraFamily_of_mainThmI`,
  `mainThmI_iff_ab`, `shimuraFamily_of_mainThmIAb`.
- Part B6: `qHat_algebraMap`, `rat_mem_zhat_iff`, `dcRel_one_iff`, `mainThmIY3_of_mainThmI`.

- Part C: copies from t5-glue (`mem_range_of_isAlgebraic`, `AbsArtinSurjective`, the section `AbsArtin` with
  `absArtinSurjective_of_noReal`, `not_isReal_QNeg`) and new `exists_tau`, `exists_iota`,
  `exists_artinCondC_of_abs`, `exists_artinCondC`.
- Part D: `q3`, `z3`, `isCMPoint_q3`, `IsTotallyComplex (QNeg 3)`, `recip_hyp_nonempty`.

Whole file: 0 errors, about 20.5 s and 8.8 GB, 17 `#print axioms` lines, all `[propext, Classical.choice,
Quot.sound]`, including the leaf definition itself (VERIFIED). The file imports TailZ12, the three Contrib modules
of R1UnivLeaves, Tau Ceti `Global.Reciprocity` and `Adeles.FiniteBaseChange`, and `TYZGenus.ShimuraModFn`.

Independent model review (read-only, one pass): no PROBLEM. It checked DCRel, the reciprocity conventions,
`ArtinCondC`, `qHat`, `IsCMPoint` and `K3Q`, and it constructed a `Ψ` meeting all four clauses. One wording RISK
("the comparison is clause 1") is fixed: §1 and the docstring now say "clauses 1 and 4 with Deligne's comparison".
One minor RISK: Tau Ceti's global normalization was checked only locally, and `ε` absorbs it anyway. No human
review.

## 5. Shimura's per-`S` form, and what was not done

- Shimura's literal statement is per open compact `S`. It names `V_S` over `k_S` and the maps `J_{TS}(x)` between
  different levels, and it states the reciprocity law through those maps. With Mathlib it can be stated as a scheme
  `V` over `Spec ℚ(ζ₃)` (`CyclotomicField 3 ℚ`) with `φ : ℍ → V(ℂ)` along a fixed embedding. To derive the fields one
  would then also need the moduli link between `V_S` and the `ℚ`-scheme `Y₃` (Deligne §4, Shimura §§2-3): a theorem,
  not a missing definition. Deligne's form makes that link part of the leaf, so it was chosen.
- Not done: the per-`S` form as a separate Prop, and a proof that it follows from the Deligne form.

## 6. Classification

- `shimuraFamilyAb`: from one LEAF (`ShimuraMainThmIDeligneY3Ab`), no glue.
- `shimuraFamily`: from that leaf and the existing leaf `MumfordRigidityCore` (r1univ-rigid, already a route-a-fold
  field), no glue.
- The leaf is a consequence of the print (the conventions are existential, and §3 lists the weakenings). Its only
  readings are the inherited Lemma QP caveat and "`Y₃ = Sh_{K₃}`".

## 7. For integration

- To replace route-a-fold's field `shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb` by the new leaf, use
  `ShimuraCFT.shimuraFamilyAb_of_mainThmI`. The new leaf field is `ShimuraCFT.ShimuraMainThmIDeligneY3Ab`.
- The file's copies of `R1fpPropsAb`, `ShimuraFamilyAb`, `IsHolFamily`, `IsShimuraHolFamily` and the t5-glue
  sections are verbatim. On a base with TailZ16/TailZ17 (route-a-fold), drop the duplicates and keep Part B onward.
- Part B onward uses no kernel edit and no new axiom. Tau Ceti modules are imported only from the vendored
  `ZInQKernel/Contrib/TauCeti/`.
