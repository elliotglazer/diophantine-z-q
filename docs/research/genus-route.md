# genus-route: `t34`'s two uses closed, with no literature leaf

**Verdict (VERIFIED: compiled, `#print axioms` = `[propext, Classical.choice, Quot.sound]`).** The two
consumers of `t34` in the single proof (TailD.lean:236 and :250) need only `dim J₁(N) ≤ N²`, and that
bound is now a Lean theorem **with no hypothesis**:

```lean
theorem GenusRoute.dimJ1Le : DimJ1Le                    -- scratch/genus-route/Closed.lean
theorem HDec.HSyn.t34Le : DimJ1Le5                       -- scratch/genus-route/Fold.lean (OneProof copies)
theorem HDec.HSyn.dim_J1_le_of5 (h : DimJ1Le5) ...       -- drop-in for TailD.lean:236
theorem HDec.HSyn.G0Split.javanpeykarJ1_of_le (hR18 : R18_JavanpeykarConcrete)
    (hB : X1BelyiOnModel) (h : DimJ1Le5) : JavanpeykarJ1  -- drop-in for TailD.lean:250
```

where `DimJ1Le := ∀ N J, 0 < N → IsJ1 N J → ∃ g : ℕ, J.dim = g ∧ g ≤ N²`. So the fold can delete the bundle
field `genusX1Field` (and `GenusX1Field`, which has no Lean form, is never needed), and `X0Transitive` is not
used on this route. Ingredients:

1. `DimJacobianEqGenus` (`dim Jac X = fieldGenus K(X)`): dimjac-glue's theorem
   `ModularSplit.DimJac.dimJacobianEqGenus` (branch `wip/dimjac-glue`, commit 24435c82), copied verbatim into
   `Closed.lean` (python substring check: True) and compiled here.
2. **New:** `constantFieldIsQ_of_curve` (section 4): `ℚ` is algebraically closed in the function field of a
   smooth proper geometrically connected integral curve over `ℚ`; applied to the model of `X₁(N)` carried by
   `IsJ1`. This is what replaced `X0Transitive` (curve-split needed it only for this).
3. **New:** the elementary genus bound `g(K_N) ≤ [K_N : ℚ(j)]` (section 6, `genusLeDegree`): every
   holomorphic differential is `h · dj` with `h` in an explicit `ℚ`-space `V`, and `V` injects into
   `OF / j·OF ≅ ℚ^d` (`OF` the integral closure of `ℚ[j]`). No Riemann–Roch, no Riemann–Hurwitz, and no
   identification of `fieldGenus` with another genus. Its one local input, `LocalDerivation` (`d/dπ`
   preserves `𝒪_P` for a local parameter `π`; Stichtenoth §4.1), was first stated as a leaf and is now
   **proved** (section 7, `localDerivation`).
4. Kernel theorem `ZInQ.RLeaf.belyiX1`: `j/1728` is a Belyi function on `K_N` and `[K_N : ℚ(j)] ≤ N²`.

Alternative routes kept (compiled): `dimJ1Le_of_rh_curve : DimJacobianEqGenus → RiemannHurwitzQj → DimJ1Le`
(textbook leaf Riemann–Hurwitz, curve-split's reduction with `X0Transitive` removed) and
`dimJ1Le_of_localDerivation : DimJacobianEqGenus → LocalDerivation → DimJ1Le`.

Files (all compile with `lake env lean scratch/genus-route/<file>.lean`):

| file | lines | time | content |
|---|---|---|---|
| `ConstField.lean` | 410 | 70 s cold | the constant-field theorem alone |
| `GenusRoute.lean` | 1770 | 16 s | `ConstField` + curve-split's `GenusBound.lean` (verbatim, namespace `CurveSplit` → `GenusRoute`) + `dimJ1Le_of_rh_curve` |
| `GenusElem.lean` | 2370 | 20 s | `GenusRoute.lean` + the elementary genus bound from `LocalDerivation` |
| `LocalDer.lean` | 2780 | 25 s | `GenusElem.lean` + `localDerivation` (proof of the leaf) + `dimJ1Le_of_dimJacobianEqGenus` |
| `Closed.lean` | 3470 | 30 s | dimjac-glue's `DimJacGlue.lean` + `LocalDer.lean`, verbatim; `GenusRoute.dimJ1Le` |
| `Fold.lean` | 3570 | 30 s | `Closed.lean` verbatim + `import ZInQKernel.OneProof.H.TailM` + `t34Le`, `dim_J1_le_of5`, `javanpeykarJ1_of_le` (needs the upstream `lean/` package built once: `lake build ZInQKernel.Hypotheses.JHeight`) |

Imports are kernel modules only: `Contrib.CurvesG.{GenusSplit,CurveSplit}`, `Contrib.RLeaf.{BelyiX1,T40}`,
`Contrib.Dim.{SmoothStalk,Basic}`, `Contrib.SmoothFibre.Basic`, `Contrib.CloudW07JacobiansCurves.*` (for
dimjac-glue), `HDecomp.ModCurves.X1Belyi` (and `OneProof.H.TailM` for `Fold.lean`).

## 1. What the consumers need from `t34` (VERIFIED by reading)

`t34 : LeafModCurves.DimJ1Genus` (`dim J₁(N) = genus Γ₁(N)`) enters the proof only through
`t34_of_split5 t.dimJacobianEqGenus t.genusX1Field` (TailM.lean:365, bundle `TailZ9`) and is consumed at

* `TailD.lean:236`: `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1`, whose conclusion is
  `∃ g : ℕ, J.dim = g ∧ g ≤ N²`;
* `TailD.lean:250`: `javanpeykarJ1 hR18 hBelyi t.t34 …` (LPrefix.lean:12078), whose proof uses
  `hT34` only in `LeafModCurves.dim_J1_le hT34 N hN J hJ`.

So both need exactly `DimJ1Le := ∀ N J, 0 < N → IsJ1 N J → ∃ g : ℕ, J.dim = g ∧ g ≤ N²`
(curve-split's definition; `DimJ1Le5` is the same statement over the OneProof copies
`PkgI3.AbVar`/`LeafModCurves.IsJ1` of namespace `HDec`). Nothing else about the genus is used.

## 2. The fold

Delete the bundle fields `genusX1Field` and `dimJacobianEqGenus` (both unused after the change; the latter is
proved anyway) and the definition `t34 := t34_of_split5 …`, and at the consumers use the theorem `t34Le`:

| site | now | replacement |
|---|---|---|
| TailD.lean:236 | `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1` | `dim_J1_le_of5 t34Le N hN0 J hJ1` (same type; checked by an `example`) |
| TailD.lean:250 | `javanpeykarJ1 hR18 hBelyi t.t34 …` | `G0Split.javanpeykarJ1_of_le hR18 hBelyi t34Le …` |

Checked in context (compiled, `Fold.lean`): `HDec.HSyn.glueOutputs_of_leaves3_t34Le` is TailD's
`glueOutputs_of_leaves3` (TailD.lean:204-257, with that file's options) with only these two lines changed;
it has the same type and does not mention `t.t34`.

`javanpeykarJ1_of_le` is `javanpeykarJ1`'s proof with one line changed (diff in the log), and
`javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34` holds by `rfl`
(compiled). Since `DimJ1Le5` follows from `t34` (`dimJ1Le5_of_t34`), the change only weakens the hypotheses.

If a fold prefers a field to an inlined theorem, `t34Le_of_localDerivation` and `t34Le_of_rh` give the
same conclusion from the (now proved) leaf `LocalDerivation` or from `RiemannHurwitzQj`.

Note (VERIFIED by grep): in the current OneProof bundles `x0Transitive` also supplies T40
(`t40 := t40_of_x0Transitive4 t.x0Transitive`, TailK.lean:250, TailN.lean:236). This report removes only
its use in the genus route (curve-split's `dimJ1Le_of_rh`); its T40 use is outside this task.

## 3. Leaves and glue

| item | kind | status | source |
|---|---|---|---|
| `GenusRoute.dimJ1Le`, `HDec.HSyn.t34Le` | GLUE | **proved, no hypothesis** | — |
| `localDerivation` and its 11 lemmas | GLUE | proved (new, section 7) | — |
| `LocalDerivation` (as first stated) | was LEAF (textbook, local) | now a theorem | Stichtenoth §4.1: for a `P`-prime element `t`, the `t`-derivative `δ_t` maps `𝒪_P` into `𝒪_P` (Prop. 4.1.8, number UNVERIFIED); equivalently `Ω_{𝒪_P/ℚ}` is free on `dπ` (Hartshorne II.8, numbers UNVERIFIED) |
| `genusLeDegree_of_localDerivation` and its 14 lemmas | GLUE | proved (new) | — |
| `RiemannHurwitzQj` (alternative route) | LEAF (textbook, composite) | open | Stichtenoth, *Algebraic Function Fields and Codes*, Thm 3.4.13 (Hurwitz genus formula) with Thm 3.5.1 (Dedekind's different theorem, `d_P = e_P − 1` in char 0) and the identification of `fieldGenus` (holomorphic Kähler differentials) with the Riemann–Roch genus (Stichtenoth §4.3; Hartshorne II.8, IV.2.4); numbers UNVERIFIED |
| `DimJacobianEqGenus` | kernel LEAF, now proved | dimjac-glue's proof copied verbatim into `Closed.lean` and compiled here | Milne 1986 |
| `constantFieldIsQ_of_curve` | GLUE | proved (new) | — |
| `belyiGenusBound_of_rh`, `fundamentalIdentityQj` | GLUE | proved (curve-split, copied) | — |
| `ZInQ.RLeaf.belyiX1` | kernel theorem | proved | — |
| `dimJ1Le_of_rh_curve`, `t34Le_of_rh`, `javanpeykarJ1_of_le` | GLUE | proved (new) | — |

`RiemannHurwitzQj` (verbatim from curve-split's `GenusBound.lean`): for `F` finite over `ℚ(j) = RatFunc ℚ`
with `ℚ` algebraically closed in `F`, the function `P ↦ (e_P − 1)·deg P` on places of `F/ℚ` (proper
valuation subrings containing `ℚ`; `e_P` the index of `U_P·ℚ(j)ˣ` in `Fˣ`; `deg P = dim_ℚ κ(P)`) has
finite support and `2·g(F) − 2 = −2·[F : ℚ(j)] + Σ_P (e_P − 1) deg P`, `g = fieldGenus`. Checked again
for this report: the `Algebra ℚ F` and `Algebra Qj F` instances are not linked, which is harmless since a
field has at most one `ℚ`-algebra structure; `e_P` as a unit-group index equals the ramification index
(value group `ℤ`, image of `ℚ(j)ˣ` is `e_P ℤ`); for `F = ℚ(j)` both sides are `−2`. Not vacuous: it is
applied to `K_N`, which satisfies the hypotheses (`constantFieldIsQ_of_curve`, `fieldX1_finiteDimensional`).

## 4. The constant-field theorem (new glue, proved)

```lean
theorem GenusRoute.constantFieldIsQ_of_curve (X : Over LeafModCurves.SpecQ) (hC : LeafModCurves.IsCurve X)
    [IsIntegral X.left] (F : Type) [Field F] [Algebra LeafModCurves.Qj F]
    (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F
```

Proof (each step a compiled lemma):

1. `isNormal_of_integral` (copied from curve-split's `CurveBij.lean`): the stalks of an integral smooth
   curve over a field are integrally closed (DVRs at closed points, the function field at the generic point).
2. `exists_global_of_isIntegral`: `y ∈ K(X)` algebraic over `ℚ` is integral over each `Γ(X, U)`, `U` affine
   nonempty; `Γ(X, U)` is integrally closed with fraction field `K(X)`, so `y ∈ Γ(X, U)`.
   `exists_global_section`: these local sections glue to `s ∈ Γ(X, ⊤)` (Mathlib's
   `TopCat.Sheaf.existsUnique_gluing'`; overlaps are nonempty because `X` is irreducible, and
   `germToFunctionField` is injective).
3. `algebraic_mem_range`: with `q = minpoly ℚ y` and `A = ℚ[T]/(q)` (a field), `s` gives
   `φ = X.toSpecΓ ≫ Spec(A → Γ(X, ⊤)) : X → Spec A`, and `X → Spec ℚ` equals `φ ≫ (Spec A → Spec ℚ)`
   (`hom_specQ_ext`: maps to `Spec ℚ` are unique). Geometric connectedness at `ℚ̄`, Mathlib's
   `pullbackRightPullbackFstIso`, and surjectivity of `φ` (`Spec A` is a point) and of its base change
   make `Spec ℚ̄ ×_ℚ Spec A ≅ Spec (ℚ̄ ⊗_ℚ A)` connected (`pullbackSpecIso`). `ℚ̄ ⊗ A` is finite over `ℚ̄`,
   so Artinian, so its spectrum is discrete, hence a single point. If `deg q ≥ 2`, `q` has two distinct
   roots `α ≠ β` in `ℚ̄` (separable, `card_rootSet_eq_natDegree`), and the kernels of
   `a ⊗ b ↦ a·b(α)`, `a ⊗ b ↦ a·b(β)` are distinct primes (`not_subsingleton_of_roots`). So `deg q = 1`.
4. Transport along `e` (ring maps out of `ℚ` are unique).

## 5. What remains

* Nothing on this route: no literature leaf is needed for the two uses of `t34`.
* The fold itself (bundle edit in TailN/TailO/TailZ9/…, done after the announcement), and the deletion of
  `GenusX1Field` and of the `genusX1Field` fields.
* Not checked: whether `X0Transitive` can also be dropped from its T40 use (outside this task).

## 6. The elementary genus bound (new glue, proved): `g(F) ≤ [F : ℚ(j)]`

```lean
def GenusRoute.LocalDerivation : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → ∀ (P : Place F) (π : F), π ≠ 0 → π ∈ P.w.nonunits →
      (∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) →
        ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w

def GenusRoute.GenusLeDegree : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      fieldGenus F ≤ Module.finrank Qj F

theorem GenusRoute.genusLeDegree_of_localDerivation (hL : LocalDerivation) : GenusLeDegree
```

`Place F` (curve-split): a proper valuation subring of `F` containing `ℚ`. `LocalDerivation` is a
statement about one place and one local parameter, over Mathlib's `Derivation` and `ValuationSubring`;
it is true for every place of a function field over a field of characteristic `0` (the completion
`𝒪̂_P ≅ κ(P)[[π]]`, and `d/dπ` acts coefficientwise), and the constant-field hypothesis only weakens
it to Stichtenoth's standing assumption.

Proof of `genusLeDegree_of_localDerivation` (`s = j`, `t = j/1728`, `d = [F : ℚ(j)]`; each step a
compiled lemma of `GenusElem.lean`):

1. `mem_span_D_sF`: `Ω_{F/ℚ} = F · ds`. (`F/ℚ(j)` is finite separable, hence formally unramified, so
   `Ω_{F/ℚ(j)} = 0`; Mathlib's exact sequence `F ⊗ Ω_{ℚ(j)/ℚ} → Ω_{F/ℚ} → Ω_{F/ℚ(j)}` and the quotient
   rule in `ℚ(j)`.) So every `ω ∈ holoDiff F` is `h · ds`.
2. `local_conditions`: if `h · ds` is regular at every place, then `h s (s − 1728) ∈ 𝒪_P` at every
   place with `s ∈ 𝒪_P`, and `h (s − 1728) ∈ 𝔪_P` at every place with `s ∉ 𝒪_P`. For each place take a
   uniformizer `π` (`exists_uniformizer_all`: curve-split's `exists_uniformizer`, twisted by `j ↦ 1/j`
   at infinity) and `δ = d/dπ` from the leaf; `δ` extends to `Ω_{F/ℚ} → F` and maps the differentials
   regular at `P` into `𝒪_P` (`lift_mem_of_regularAt`), so `h δ(s) ∈ 𝒪_P`. Then: over `j = 0` and
   `j = 1728`, `z = u π^(m+1)` and `δ z = π^m c` with `c` a unit (`deriv_unit_pow`, characteristic 0);
   over `j = ∞`, the same for `z = 1/s`; elsewhere the Belyi property gives the local parameter
   `q(t)` and `δ t = 1/q'(t)` (curve-split's `polyIdeal`, `exists_monic_irreducible_mem`).
3. `Vspace`: the `ℚ`-space of such `h`. `finrank_Vspace_le`: `h ↦ h s (s − 1728)` lands in `OF`
   (`mem_OF_of_places`, Mathlib's `mem_integers_of_valuation_le_one` with curve-split's `placeOf`),
   and composing with the coordinates at `s = 0` in a `ℚ[s]`-basis of `OF` (free of rank `d`:
   `IsIntegralClosure.module_free`, `IsIntegralClosure.rank`) gives a `ℚ`-linear map `V → ℚ^d`. It is
   injective: if `h s (s − 1728) = s k` with `k ∈ OF`, then `k = h (s − 1728)` lies in every place and
   in `𝔪_P` over `∞`; elements in every place are rational (`mem_rat_of_all_places`: `ℚ` is integrally
   closed in `F` by `ConstantFieldIsQ`, and Mathlib's Stacks 090P), and a place over `∞` exists
   (`exists_place_inf`, curve-split's fundamental identity), so `k = 0` and `h = 0`.
4. `fieldGenus F = dim holoDiff ≤ dim V ≤ d`.

With `constantFieldIsQ_of_curve` and `ZInQ.RLeaf.belyiX1` (`d ≤ N²`): `dimJ1Le_of_localDerivation`.

## 7. `LocalDerivation` is a theorem (new glue, proved)

```lean
theorem GenusRoute.localDerivation : LocalDerivation
theorem GenusRoute.genusLeDegree : GenusLeDegree
theorem GenusRoute.dimJ1Le_of_dimJacobianEqGenus (h1 : DimJacobianEqGenus) : DimJ1Le
```

Proof (`LocalDer.lean`; `s = j`, `𝒪 = 𝒪_P`, `π` the given local parameter):

1. `exists_deriv_s`: a derivation `δ_s` of `F/ℚ` with `δ_s(s) = 1`. `Ω_{F/ℚ} = F·ds` (section 6, step 1) and
   `Ω_{F/ℚ} ≠ 0`: otherwise `F/ℚ` is formally unramified, hence separable algebraic (Mathlib
   `FormallyUnramified.iff_isSeparable`, `F` being essentially of finite type over `ℚ`), but `s` is
   transcendental. A functional with `ds ↦ 1` (`Projective.exists_dual_eq_one`).
2. Places containing `s` (`localDer_fin`):
   * `frac_rep`: `𝒪 = OF_𝔭` (`𝔭` the center of `P` in `OF`; Mathlib's `valuationSubringAtPrime` and
     curve-split's `w_eq_valuationSubring`), so every `x ∈ 𝒪` is `a/b` with `a, b ∈ OF`, `b ∉ 𝔭`.
   * `deriv_bound`: `∃ N, π^N δ_s(𝒪) ⊆ 𝒪` (a `ℚ[s]`-basis `b_i` of `OF`, a common bound for the `δ_s(b_i)`,
     the quotient rule).
   * `residue_structure`: `OF/𝔭` is a field and a finitely generated `ℚ`-algebra, hence finite over `ℚ`
     (Mathlib `finite_of_finite_type_of_isJacobsonRing`, Zariski's lemma); a primitive element `θ̄` with
     minimal polynomial `g` (separable, so `g'(θ)` is a unit of `𝒪`), and every `x ∈ 𝒪` is `p(θ) mod 𝔪`.
   * Writing `x = p(θ) + π y` and `g(θ) = π z`: `δ_s x = A·δ_s(π) + π (B·δ_s z + δ_s y)` with `A, B ∈ 𝒪`.
     By induction on `k`, `π^N (δ_s x − a δ_s π) ∈ π^k 𝒪` for some `a ∈ 𝒪`. For `x = s` and `k = N + 1` this
     forces `δ_s(π) ≠ 0` (else `π` would be a unit), and for large `k` it gives `δ_s(x) ∈ 𝒪·δ_s(π)`. So
     `δ = δ_s(π)⁻¹ δ_s` has `δ π = 1` and `δ 𝒪 ⊆ 𝒪`.
3. Places not containing `s`: the same for the twisted structure `j ↦ 1/j` (curve-split's `twistAlg`).

The constant-field hypothesis of `LocalDerivation` is not used in its proof.
