# t09-pic: `t09SymmIsogenyExists` from four printed leaves over the genuine Picard functor

Task t09-pic (2026-11-14/15). The field is `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`, i.e.
`∀ K A, Nonempty (SymmIsogeny A)` (Mumford, *Abelian Varieties*, §§6, 8, 20, 23).

Files:
- `scratch/t09-pic/Pic.lean`: everything;
- `scratch/t09-pic/Ample.lean`: the ampleness proof alone, on vendored imports only;
- `scratch/t09-pic/FoldCheck.lean`: the fold check against leaf-fold12's bundle;
- the results log, `scratch/t09-pic/log.md`.

## 1. Main result

**The field is proved from four printed leaves, all stated over genuine definitions.** Those definitions are:
- the vendored relative Picard fppf sheaf `picardFunctor` and its tensor-product group law;
- `Scheme.Pic`;
- the twisting sheaf `𝒪(1)`;
- vendored zero loci of sections;
- Mathlib's connected components, open immersions and pull-back of module sheaves.

Mumford's Weil pairing `ē_n` is now itself a genuine definition (`weilScalar`). No leaf quantifies over an object
invented for the purpose.

```
theorem T09Pic.t09SymmIsogenyExists_of_four (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (h4 : WeilPairingMumford) : HDec.WeilPairing.T09_SymmIsogenyExists
```

**Compile status.**
- `scratch/t09-pic/Pic.lean` compiles with 0 errors. Every one of its 13 `#print axioms` lines is
  `[propext, Classical.choice, Quot.sound]`; see `Pic_out.txt`. VERIFIED.
- The fold check also compiles, with standard axioms:
  `HDec.HSyn.sixContactMin_of_open15_t09pic : OpenResearchLeaves12 → OpenTextbookLeaves10 → OpenAddedLeaves11T09Pic →
  OpenGlue7 → ZInQ.SixContactMin`. Here `OpenAddedLeaves11T09Pic` is leaf-fold12's `OpenAddedLeaves11` with
  `t09SymmIsogenyExists` replaced by the four leaves (16 fields). VERIFIED.

**Effect on the count.** One GLUE (c) field (c-to-printed2 kept it as "the smallest faithful substitute") is replaced
by four LEAF fields. No statement was changed, and the field is not false, vacuous or inert.

**c-to-printed2's list of missing pieces, all built:**

| missing piece (c-to-printed2 §5) | now |
|---|---|
| `Pic⁰` as an abelian variety | **Genuine definitions:**<br>- `identityComponent G`, the connected component of the unit point;<br>- `IsPicZero rep B ι`: an open immersion onto it that is a homomorphism for the Picard group law.<br>**Leaves:** L1 (representability) and L2 (`Pic⁰` is an abelian variety). |
| `φ_L : A → Pic⁰` | **Genuine:** `mumfordBundle` `Λ(L)` and `phiL` (Yoneda).<br>**Proved:** `φ_L(0) = 0`, and `φ_L = λ_L ≫ ι` with `λ_L : Hom A B`. |
| ample line bundles | **Genuine:** `IsAmple` (Stacks 01PS) and `IsVeryAmple`.<br>**Proved:**<br>- a very ample class exists on every abelian variety over every field;<br>- **very ample ⇒ ample** (`veryAmpleIsAmple`).<br>The second removed a leaf. |
| Mumford's `e_n` | **Genuine:**<br>- `weilScalar`, the scalar `t_x^*ψ ∘ ψ⁻¹` on `A_K̄`;<br>- `dualP`, Mumford's `f^∨`.<br>**Leaf:** L4 pins the pairing to `weilScalar`. |

## 2. Genuine definitions (`Pic.lean`)

| Lean | meaning |
|---|---|
| `mumfordBundle A L` | `Λ(L) = m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹ ∈ Pic(A ×_K A)` (Mumford §8) |
| `phiL rep L : A.X ⟶ P` | the classifying map of `Λ(L)` over the second factor (Yoneda through `rep`). On points, `x ↦ [t_x^*L ⊗ L⁻¹]`. |
| `identityComponent G` | the connected component of `η_G(Spec K)` |
| `IsPicZero rep B ι` | `ι` is an open immersion onto `identityComponent P` and a homomorphism. This pins `(B, ι)` up to unique isomorphism. |
| `IsVeryAmple A L` | `L = i^*𝒪(1)` for an immersion `i : A → ℙ(N; Spec K)` over `K`, with `N` finite |
| `IsAmple X L` | `X` is quasi-compact, and every point lies in an affine `X_s`, where `s : 𝒪 → L^{⊗n}`, `n ≥ 1`, and `X_s` is the complement of the zero locus (Stacks 01PS) |
| `famMap`, `picPresheafMap`, `dualSheafMap`, `dualP rep f` | pull-back of families along `f × id`, sheafified; `f^∨ : P → P` by Yoneda |
| `ptK`, `transl x`, `mulN A n` | `Spec K̄` as a `K`-scheme; `t_x : (a, s) ↦ (a + x(s), s)` on `A ×_K K̄`; `n_A = id^n` base-changed |
| `picClass rep ι y` | a class in `Pic(A_K̄)` mapping to the point `y ≫ ι` of `Pic_{A/K}(K̄)` (by choice) |
| `weilScalar rep ι n x y` | `t_x^*ψ ∘ ψ⁻¹ ∈ Γ(A_K̄, 𝒪)` for a trivialization `ψ : 𝒪 ≅ n_A^*M_y`, i.e. Mumford's `ē_n(x, y)` up to inverse (Mumford §20, via the descent description of §§12, 15) |
| `constK A : K̄ →+* Γ(A_K̄, 𝒪)` | the constants. They are all of `Γ` by the vendored `bijective_appTop_of_isProper_of_geometricallyIntegral`. |

## 3. Leaves (`Pic.lean` §3, §6)

All locators are UNVERIFIED (from memory, no network). Each leaf is the printed statement, or a consequence of it, at
the genuine objects. The quantifiers `∀ rep`, `∀ (B, ι)` and `∀ λ` are safe: representing objects and identity
components are unique up to unique isomorphism, and `ι` is a monomorphism.

| leaf | statement | printed source |
|---|---|---|
| L1 `PicRepresentableAbVar` | `picardFunctor A.X.hom` is representable (statement copied from c-to-printed2's `T09Roadmap.lean`) | Murre (1964) and Oort (1962) for proper `X` over a field; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with Thm 9.2.5 (section `0`) |
| L2 `PicZeroAbVar` | for every `rep` there are `B : AbVar K` and `ι` with `IsPicZero rep B ι` | Mumford §13; Kleiman Prop. 9.5.1 and 9.5.3; SGA 3 VI_A 2.4 / Stacks 0B7R (identity component geometrically connected); Milne 1986 §§9–10 |
| L3 `PhiAmpleIsogeny` | if `IsPicZero rep B ι`, `L` is ample and `λ ≫ ι = φ_L`, then `λ` is finite and surjective | Mumford §6 Application 1 (`K(L)` finite; pass to `L^m` effective) and §8 Thm 1; fpqc descent from `K̄` |
| L4 `WeilPairingMumford` | there is a pairing `e_n : A[n] × Pic⁰[n] → μ_n` with values `weilScalar` (through `constK`) for `n` invertible in `K`. It is perfect, `G_K`-equivariant and compatible (`e_{mn}(x, y) = e_n(mx, y)`), satisfies `e_n(x, f^∨y) = e_n(fx, y)` for the genuine `f^∨`, and has `e_n(x, λ_L x) = 1` for ample `L`. | Mumford §20 and §23; Milne 1986 Lemma 16.2(c) and §16. Kleiman Thm 9.2.5 and Mumford §8 (iv) make `weilScalar` the printed value. |

**Why L4 is a consequence of the print and not stronger.**
- Mumford's `ē_n` at `Â = Pic⁰` satisfies every clause, and each clause is one printed property.
- If Mumford's convention is the inverse of `weilScalar`, take `e := -ē`. Every clause is invariant under
  `e ↦ -e` (perfectness, equivariance, compatibility, adjunction and alternation are all additive), so the leaf holds
  under either sign.
- The choices in `weilScalar` (of the class `picClass`, and of `ψ`) do not affect the value: Mumford's `ē_n` is
  independent of them.
- The default branches of the `dite`s never fire on `A[n] × Pic⁰[n]`:
  - `transl_left_comp_mulN_left` proves `n_A ∘ t_x = n_A`;
  - L5 `PicPointsAlgClosed` (Kleiman 9.2.5) gives the class;
  - L6 `MulNTrivialPicZero` (Mumford §8 (iv)) gives `ψ`;
  - `weilScalar_spec` proves that under L6 the value is `t_x^*ψ ∘ ψ⁻¹`.
- L5 and L6 are statable now and stated, but not used by the main theorem.

**L4 split into one printed property per leaf.** `IsMumfordPairing rep ι e` says that the values of `e` are
`weilScalar` for `n` invertible; since `constK` is injective, this pins `e`. Each of the following is stated for every
`e` satisfying it:

| leaf | property | printed source |
|---|---|---|
| L4a `WeilPairingExists` | such an `e` exists (`ē_n` is bilinear and `μ_n`-valued) | Mumford §20 |
| L4b `WeilPairingPerfect` | perfect | Mumford §20 |
| L4c `WeilPairingGalois` | `G_K`-equivariant | Milne 1986 §16 |
| L4d `WeilPairingCompat` | `ē_{mn}(x, y) = ē_n(mx, y)` | Mumford §20 |
| L4e `WeilPairingDual` | `ē_n(x, f^∨y) = ē_n(fx, y)` | Mumford §20 (5); Milne Lemma 16.2(c) |
| L4f `WeilPairingAlternating` | `e^L_n(x, x) = 1` for ample `L` | Mumford §23 |

`weilPairingMumford_of_split` combines them, and `t09SymmIsogenyExists_of_split` proves the field from the nine leaves
L1, L2, L3, L4a–f. VERIFIED.

**Weaker variants, also compiled.** `WeilPairingPicZeroPrinted` is L4 without the `weilScalar` clause, and
`WeilPairingPicZero` is the same with an existential `f^∨` and very ample `L`. Each is implied by the one before it
(`weilPairingPicZeroPrinted_of_mumford`, `weilPairingPicZero_of_printed`). The corresponding main theorems are
`t09SymmIsogenyExists_of_printed` and `t09SymmIsogenyExists_of_leaves`.

## 4. Glue (proved)

- `exists_isVeryAmple`: every abelian variety over any field has a very ample class. It comes from the vendored
  `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`.
- `veryAmpleIsAmple` (formerly leaf L0, EGA II 4.5.10). The steps:
  - `compl_support_zeroLocus_coordSection` proves `X_{i^*X_k} = i⁻¹ D₊(X_k)`. It uses the vendored transition rule
    `X_k = (X_k/X_j)·X_j`, the vendored `basicOpen_coeff_eq` and the vendored `Proj.basicOpen_ratio`.
  - `i` is proper, so its image is closed, so `i⁻¹ D₊(X_k)` is affine
    (`Scheme.Hom.isAffineOpen_preimage_of_le_coborderRange`).
  - The `D₊(X_k)` cover.
- `exists_isAmple_of_isAlgClosed`: non-vacuity of `IsAmple` over `K̄`, from the vendored ample family.
- `comp_classify`, `mumfordBundle_restrict_zero`, `eta_comp_phiL`: `φ_L(0) = 0`. The steps are Yoneda naturality,
  `m ∘ (id, 0) = p₁`, and `Pic(Spec K) = 1`.
- `exists_hom_comp_eq_phiL`: `φ_L = λ_L ≫ ι` with `λ_L : Hom A B`. `A` is connected, so `φ_L` lands in the identity
  component; then lift through the open immersion, and rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`) makes
  the lift a homomorphism.
- `eta_comp_dualP` and `exists_dual_on_picZero`: `f^∨(0) = 0`, and `f^∨` restricts to `End(Pic⁰)`.
- `transl_comp_mulN` and `transl_left_comp_mulN_left`: `n_A ∘ t_x = n_A` on `A[n]`.
- `weilScalar_spec`, plus the assembly theorems.

## 5. Frontier and what remains

**Every object in Mumford's statements of §§6, 8, 13, 20, 23 is now a Lean definition.** That covers `Pic`, `Pic⁰`,
`Λ(L)`, `φ_L`, `f^∨`, ample, very ample, `t_x`, `n_A` and `ē_n`. The four remaining leaves are published theorems
about these objects:
- L1, Grothendieck–Murre–Oort representability;
- L2, `Pic⁰` is an abelian variety;
- L3, `φ_L` is an isogeny for ample `L`;
- L4, the properties of `ē_n`.

Further reductions would mean formalizing these textbook theorems themselves (FGA-level representability, the theorem
of the square, Mumford's §20 duality). That is the crowdsourcing target.

**Caveats.**
- All locators are UNVERIFIED: Mumford numbering, Kleiman 9.2.5/9.4.8/9.5.x, EGA II 4.5.10, Milne 16.2(c), SGA 3 VI_A
  2.4, Stacks 01PS/0B7R.
- The fold can use the four-leaf form (L4 bundled) or the nine-leaf form (L4a–f, one printed property per leaf). Both
  are compiled.

## 6. Fold recipe

The steps below are SPECULATIVE until a fold applies them.

1. Replace the field `t09SymmIsogenyExists` in `OpenAddedLeaves11` (and its successors) by four fields:
   `picRepresentableAbVar`, `picZeroAbVar`, `phiAmpleIsogeny` and `weilPairingMumford`.
2. Produce the field from them with `T09Pic.t09SymmIsogenyExists_of_four`.
   `scratch/t09-pic/FoldCheck.lean` does exactly this on top of `TailZ19`.
3. Imports to add, beyond the OneProof chain:
   - the vendored `Picard.RepresentableGroup`, `Picard.Field`, `Picard.Group`;
   - `Group.QuasiProjective`;
   - `ProjectiveSpace.{Twist, Invertible, CoordinateCover, Embedding, Relative}`;
   - `Modules.{ClearDenominators, GlobalSection, ZeroLocusFunctorial}`;
   - `Morphisms.ImmersionAffine`;
   - `ZInQKernel.Contrib.FrobChain.Rigidity`.

   No name clashes arose on top of `TailB` or `TailZ19`.
4. Pitfall: `ι` is a token after `TailB`, so do not use it as a binder name.

## 7. Review

One independent model review read `Pic.lean` and found no errors; see `log.md` for its cautions. Every caution was
applied to the docstrings:
- cite EGA II 4.5.10 first;
- Kleiman 9.2.5 needs the section `0`;
- cite the geometric connectedness of the identity component;
- Mumford App. 1 is for effective `D`;
- the adjunction holds for all homomorphisms (Milne 16.2(c)).
