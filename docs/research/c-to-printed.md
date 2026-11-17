# c-to-printed: four "consequence of one theorem" fields from printed-form leaves

Task c-to-printed, 2026-11-14. Base e38375b3 (wip/w62). Two Lean files, neither with a `sorry` or an `axiom`:
- `scratch/c-to-printed/CToPrinted.lean` imports `ZInQKernel.OneProof.H.TailZ14` and contains parts N, F and S.
- `scratch/c-to-printed/Shimura.lean` imports `ZInQKernel.OneProof.H.TailU` and contains part H.

Every theorem named below depends only on `[propext, Classical.choice, Quot.sound]`; this is checked by the
`#print axioms` lines at the end of each file (VERIFIED). The results log is `scratch/c-to-printed/log.md`.
Nothing under `ZInQKernel/` or `blueprint/` was edited. This is model work: there was one independent model
review of the statements (§6) and no human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or wording recalled without a source. There is no network on this host,
so BLR, SGA 3, SGA 7, EGA IV, Stacks, Faltings 1983, Raynaud (Astérisque 127) and Shimura 1967 could not be
consulted. Every locator and every "printed" wording below is UNVERIFIED.

Each field is proved as the exact kernel constant, so no statement changed. Each file also carries a verbatim copy
of its field, checked by `example : copy = kernel constant := rfl`.

## 1. Main result

**Three of the four fields are now Lean theorems from published-form leaves alone, with no glue left.** The fourth,
`shimuraFamily`, is proved from the fullest form of Shimura's Main Theorem I that Mathlib can state. That form is a
consequence of the print rather than the print itself, because the reciprocity law needs global class field
theory, which Mathlib lacks.

| field (kernel constant) | Lean theorem (compiled) | leaves (all published form, UNVERIFIED wording) | glue left |
|---|---|---|---|
| `neronLocalizesDVR` (`ReductGlue.NeronLocalizesDVR`) | `CToPrinted.neronLocalizesDVR_of_printed` | `BLR_1_2_4`: BLR 1.2 Prop. 4, the full "iff", over any Dedekind domain and any smooth separated scheme of finite type | **none** |
| `faltingsLemma5BC` (`ZInQ.HeightSplit.FaltingsLemma5BC`) | `CToPrinted.faltingsLemma5BC_of_printed` | `FaltingsLemma5Printed` (Faltings 1983 Lemma 5: the identity with correction term `[K:ℚ]⁻¹ log #s*Ω¹_{G/S}`); `RaynaudKernelBound` (Raynaud, Ast. 127 VII 2.1.3) | **none** |
| `semistableNeronBaseChange` (`ZInQ.HeightSplit.SemistableNeronBaseChange`) | `CToPrinted.semistableNeronBaseChange_of_printed_full` | `BLR_1_2_4`; `SGA3_VIB_3_10` (`G⁰` is open); `SGA7_IX_3_3` (`N⁰ ⊗ R' ≅ N'⁰`); `EGAIV_8_10_5_openImm` (open immersions spread out); and the leaf `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV), already in the bundles | **none** |
| `shimuraFamily` (`HDec.QMSplit.Moduli.ShimuraFamily`) | `CToPrinted.Shimura.shimuraFamily_of_mainThmI` | `ShimuraMainThmIY3`: Shimura 1967 Main Thm I with the moduli interpretation, without the reciprocity law and without surjectivity onto `V_S(ℂ)` | none, but the leaf is a consequence of the print (§5) |

**Definitions added over Mathlib** (none of these exists in Mathlib 4.35):
- `IsNeronModelOver` (BLR 1.2 Def. 1);
- `idCompSet`, the identity component of a group scheme over a base, as a set;
- `kerScheme`, `kerUnit`, `kerOmegaLog`: the kernel of a homomorphism of group schemes, its unit section and
  `log #s*Ω¹`. The last is computed stalkwise, since Mathlib has no sheaf of relative differentials on schemes;
- `InGamma3`.

**Effect on the strict count** (SPECULATIVE until the integrator rules):

| field | before | after |
|---|---|---|
| `neronLocalizesDVR` | GLUE (c) | LEAF `BLR_1_2_4` |
| `faltingsLemma5BC` | GLUE (c) | 2 LEAVES: `FaltingsLemma5Printed`, `RaynaudKernelBound` |
| `semistableNeronBaseChange` | GLUE (c) | 3 new LEAVES (`SGA3_VIB_3_10`, `SGA7_IX_3_3`, `EGAIV_8_10_5_openImm`), plus `BLR_1_2_4` (shared) and `geomConnOfRationalPoint` (already in the bundles) |
| `shimuraFamily` | GLUE (c) | still GLUE (c), with leaf `ShimuraMainThmIY3` |

Side effect for reduct-glue: three of its leaves become theorems from these printed forms:
- `NeronLocalizesDVR` from `BLR_1_2_4`;
- `OpenImmersionOfLocal` from `EGAIV_8_10_5_openImm` (`openImmersionOfLocal_of_printed`);
- `IdentityComponentOL` from SGA 3 and Stacks 04KV (`identityComponentOL_of_printed_full`; the stronger
  `IdentityComponentOLRange` is also proved).

Its fourth leaf, reduct-split's `IdentityComponentBaseChangeDVR`, is replaced in the proof by
`IdentityComponentBaseChangeDVRRange`, which is proved from SGA 3, SGA 7 and Stacks 04KV.

No statement was found false or vacuous.

## 2. `neronLocalizesDVR` (part N)

**Definition** `IsNeronModelOver R K X` (BLR §1.2 Def. 1), for `R` a ring, `K` an `R`-algebra and
`X : Over (Spec R)`, requires:
- `X` is smooth, separated, locally of finite type and quasi-compact;
- for every smooth `R`-scheme `Y`, the map `Hom_R(Y, X) → Hom_K(Y_K, X_K)`, `f ↦ f_K`, is bijective.

The definition uses only Mathlib objects (`Over.pullback`, `Spec.map`). "X is a Néron model of X_K" for an
`R`-model `X` is this predicate, because composing with an identification `X ×_R K ≅ X_K` does not change
bijectivity.

**Leaf** `BLR_1_2_4` (BLR, *Néron models*, §1.2 Prop. 4; UNVERIFIED). The setting: `R` a Dedekind domain with
fraction field `K`, and `X` smooth, separated and quasi-compact over `R`. Then

`IsNeronModelOver R K X ↔ ∀ maximal 𝔭, ∀ R𝔭 with IsLocalization.AtPrime R𝔭 𝔭 and R → R𝔭 → K, IsNeronModelOver R𝔭 K (X ×_R R𝔭)`.

`IsLocalization.AtPrime` is Mathlib's characteristic predicate for `𝒪_{S,s}`. Every such ring is uniquely
isomorphic to `Localization.AtPrime 𝔭`, so quantifying over all of them says no more than the print.

**Glue, all proved:**
- `isLocalization_center`: a DVR `O` of a number field `L` is `IsLocalization.AtPrime O (center O)` along
  `toOL`. This uses reduct-glue's `mem_iff_exists`.
- `isNeronModelOver_of`: the kernel's `GroupModel.IsNeronModel` gives `IsNeronModelOver (𝓞 L) L 𝒩.G`.
- In `neronLocalizesDVR_of_printed`, the kernel's `toO 𝒩 O` is `𝒩.G ×_{𝓞_L} O` with the generic identification
  composed with an isomorphism.

**Reading risk** (flagged by reduct-glue §5): BLR may state 1.2/4 with strict henselizations `𝒪^{sh}_{S,s}`
instead of local rings, or with both. The localization form would then follow from the print through BLR 1.2/2
(Néron models and étale base change) with descent. That derivation is not in Lean.

## 3. `faltingsLemma5BC` (part F)

reduct-split had already reduced the field, with no glue, to the base-field form `HeightSplit.FaltingsLemma5`
(`ReductSplit.faltingsLemma5BC_final`). `FaltingsLemma5` is `|h(A) − h(B)| ≤ ½ log deg φ` for semistable Néron
models over `𝓞_K`. height-split §8 classified it as a consequence of two printed results. Both are now stated.

**Definitions** (Mathlib objects; `S = Spec 𝓞_K`, `X, Y : Over S` group objects, `f : X ⟶ Y` a homomorphism):
- `kerScheme f := pullback f.left η_Y.left`. This is `G = ker f = X ×_{f, Y, e} S`.
- `kerUnit f hf : S → G`, the unit section, `pullback.lift η_X (𝟙 S)`. The lift exists by `IsMonHom.one_hom`.
- `kerOmegaLog f hf := ∑ᶠ P : S, log #(ker(s^#_P : 𝒪_{G,s(P)} → 𝒪_{S,P})).Cotangent`. This is `log #s*Ω¹_{G/S}`,
  computed stalkwise. For a section, `s*Ω¹_{G/S}` is the conormal sheaf `s*(I/I²)` (EGA IV 17.2.5, UNVERIFIED), and
  its stalk at `P` is `I_P/I_P²`. A torsion coherent sheaf on a Dedekind scheme is the sum of its stalks. Mathlib
  4.35 has no sheaf of relative differentials on schemes, so the global `s*Ω¹` cannot be written directly. The
  stalkwise form is the closest genuine object.
- `ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩`: `(φ𝒩)_K ≫ 𝒩B.gen = 𝒩A.gen ≫ φ_K`.

**Leaves:**
- `FaltingsLemma5Printed` (Faltings, Invent. Math. 73 (1983), Lemma 5, p. 358; wording recalled, UNVERIFIED;
  locators.md could not read it). Setting: `A`, `B` over `K` with semistable Néron models `𝒩A`, `𝒩B`, and `φ𝒩`
  the homomorphism extending the isogeny `φ`. Statement: `h(B) = h(A) + ½ log deg φ − kerOmegaLog φ𝒩 / [K:ℚ]`.
  The identity does not depend on how the metric is normalized: a change shifts `h(A)` and `h(B)` by the same
  constant.
- `RaynaudKernelBound` (Raynaud, Astérisque 127 (1985), Exp. VII, Cor. 2.1.3 as cited by height-split §8 and
  Pazuki 2012 Rem. 2.3; UNVERIFIED): `kerOmegaLog φ𝒩 ≤ [K:ℚ] log deg φ`.

**Glue, all proved:**
- `exists_extension`: the Néron mapping property of `𝒩B` extends `φ`, and the extension is a homomorphism by
  reduct-glue's `isMonHom_of_ext`.
- `kerOmegaLog_nonneg`: the lower bound `0 ≤`.
- The arithmetic in `faltingsLemma5_of_printed`, then reduct-split's `faltingsLemma5BC_final`.

**Consistency check** (by hand, SPECULATIVE). Take `φ = [n]` on `A`, so `B = A`, `deg φ = n^{2g}` and
`G = 𝒩[n]`. Since `ω_{𝒩[n]} = ω_𝒩/n ≅ (𝒪_K/n)^g`, the identity gives `log # = g[K:ℚ] log n`, which is correct.
Raynaud's bound gives `g[K:ℚ] log n ≤ 2g[K:ℚ] log n`, which is consistent.

**Reading risk:** Faltings' Lemma 5 is unread. It may be printed only for good reduction, where `G` is finite
flat. In the semistable case `G` is only quasi-finite. The bound for that case is the one height-split attributes
to Raynaud.

## 4. `semistableNeronBaseChange` (part S)

**Final theorem** (compiled, standard axioms):

`semistableNeronBaseChange_of_printed_full (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10) (h7 : SGA7_IX_3_3)
(hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint) : ZInQ.HeightSplit.SemistableNeronBaseChange`.

### 4.1 The leaves

**Definition** `idCompSet G`, the identity component `G⁰` of a group scheme `G → S` as a set: `x` belongs to it if it
lies in the connected component of `e(f x)` in the fibre `f⁻¹{f x}`, with the subspace topology. Mathlib's
`Scheme.Hom.fiberHomeo` identifies that subspace with the scheme fibre.

| leaf (UNVERIFIED wording) | Lean statement |
|---|---|
| `SGA3_VIB_3_10` (SGA 3 VI_B 3.10; EGA IV 15.6.5) | `G` a smooth group scheme over any `S` ⇒ `IsOpen (idCompSet G)` |
| `SGA7_IX_3_3` (SGA 7 I, IX 3.3, second assertion) | Setting: `O ⊆ O'` DVRs with `K'/K` finite and `O' ∩ K = O`, `A` semistable at `O`, Néron models `𝒩`, `𝒩'`; `c : 𝒩 ×_O O' → 𝒩'` a homomorphism with isomorphic generic fibre; `U` the open `idCompSet (𝒩 ×_O O')`. Conclusion: `U → 𝒩'` is an open immersion with image `idCompSet 𝒩'` |
| `EGAIV_8_10_5_openImm` (EGA IV₃ 8.10.5, open-immersion item) | In the kernel's limit setting (as in its leaf `EGAIV_8_10_5_xii`): if the base change of a finitely presented `f_i : X_i → Y_i` to `lim D` is an open immersion, so is its base change to some `D_j` |
| `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV; **already a bundle leaf**) | a connected `k`-scheme of finite type with a rational point is geometrically connected |
| `BLR_1_2_4` | part N |

Each Lean form of SGA 7 IX 3.3 is a consequence of the print:
- It allows any homomorphism `c` whose generic fibre is an isomorphism. Such a map is the canonical one followed by
  a group automorphism of `𝒩'` (Néron), and that automorphism preserves `𝒩'⁰`.
- It writes `N⁰ ⊗ R'` as `(N ⊗ R')⁰`. These agree by `idComp_baseChange`, which is proved here.
- It takes `K'/K` finite, while the print allows any extension of DVRs (as recalled).

### 4.2 What is proved (all compiled)

1. **`neronLocalizesDVR_of_printed`** (part N) gives reduct-glue's `NeronLocalizesDVR`.
2. **`openImmersionLocalization`** gives reduct-glue's `OpenImmersionOfLocal` from EGA IV 8.10.5.
   - `Spec O = lim_{a ∉ 𝔭} Spec 𝓞_L[1/a]`, indexed by `𝔭.primeCompl` preordered by divisibility
     (`ringCoconeOIsColimit`, `specConeOIsLimit`).
   - EGA IV 8.10.5 gives `s_𝔭 ∉ 𝔭` (`exists_away_of_dvr`).
   - Finish with the open cover of `Y` by `Y ×_S D(s_𝔭)` and `IsZariskiLocalAtTarget.of_openCover`.
3. **`geomConnected_idComp`**: `G⁰ → S` is geometrically connected.
   - At each `y`, the fibre of `G⁰` is homeomorphic (`fiberHomeo`) to the connected component of `e(y)`, hence
     connected.
   - It has the rational point `e(y)`, so Stacks 04KV applies; conclude with
     `GeometricallyConnected.iff_geometricallyConnected_fiber`.
4. **`idComp_baseChange`**: `fst⁻¹(G⁰) = (G ×_S S')⁰` for a smooth quasi-compact `G` over a noetherian `S` and any
   `S' → S`.
   - `G⁰ ×_S Spec κ(s')` is connected and maps onto the points of `fst⁻¹(G⁰)` over `s'`.
   - Conversely, `fst` maps the component of `e'(s')` to a connected set containing `e(g s')`.
5. **`idCompSubgroup_of`**: `G⁰` is closed under `μ` and the inverse.
   - `G⁰ ×_S G⁰ → S` is geometrically connected (`GeometricallyConnected.comp`), so its fibres are connected.
   - `μ(e, e) = e`.
6. **`OpenSub.grpG0`, `OpenSub.isMonHom_incl`**: an open `W` closed under the group law carries a group structure
   for which `W → G` is a homomorphism (`GrpObj.ofRepresentableBy` on `T ↦ {f : T ⟶ G | f(T) ⊆ W}`). This is
   general and reusable.
7. **`identityComponentOLRange_of`**: every group model `𝒢` over `𝓞_L` has the group model `𝒢₀` on `𝒢⁰`, with
   image exactly `𝒢⁰`.
   - Smooth and separated, because `𝒢₀ → 𝒢` is an open immersion.
   - Quasi-compact, because `𝒢` is noetherian.
   - Its generic fibre equals `𝒢`'s, because `idCompGenericFibre` puts the generic fibre of `𝒢` inside `𝒢⁰`
     (`A_L` is connected).
8. **`identityComponentBaseChangeDVRRange_of`**: for an open subgroup `U` with image `𝒩⁰`, `U ×_O O' → 𝒩'` is an
   open immersion and a homomorphism.
   - The canonical `c` comes from `bcDVR`, the Néron property and `isMonHom_of_ext`.
   - `range(U ×_O O') = (𝒩 ×_O O')⁰` by `range_map` and `idComp_baseChange`.
   - Then apply SGA 7 IX 3.3.
9. **`semistableNeronBaseChange_of_printed_full`** reuses reduct-glue's `semistableNeronBaseChangeLocalGlobal_of`
   with two changes:
   - `𝒢₀` comes from (7), and the image of `𝒢₀ ×_{𝓞_L} O` is `(𝒩 ×_{𝓞_L} O)⁰` by (4);
   - the local step is (8) instead of reduct-split's connectedness form.

   So reduct-split's `IdentityComponentBaseChangeDVR` and the topological claim "an open subgroup with connected
   fibres is the identity component" (`OpenSubgroupIsIdComp`) are no longer needed.

The intermediate reductions stay in the file and compile. They give successively smaller sets of named glue:
- `semistableNeronBaseChange_of_printedBLR` (reduct-glue's four leaves with BLR printed);
- `_of_printed`, `_of_printed'`, `_of_printed''`;
- `_of_printed_final`, `_of_printed_final'`, `_of_printed_final''`;
- `_of_printed_best` (glue `OpenSubgroupIsIdComp` only).

## 5. `shimuraFamily` (part H)

shimura-split reduced the field to its `ShimuraHolFamily` (`shimuraFamily_of_hol`). That reduction is one
holomorphic `τ ↦ y_τ ∈ Y₃(ℂ)` with the moduli clause, and its composition step with every `π : Y → P¹` is proved.
`Shimura.lean` copies shimura-split's file verbatim, and it still compiles at e38375b3 (VERIFIED). It then adds
the fullest form of the print that can be stated today:

**Leaf** `ShimuraMainThmIY3`. Sources (UNVERIFIED): Shimura, Ann. of Math. 85 (1967), Main Thm I; the moduli
interpretation comes from Shimura 1967 §§2-3, Ann. of Math. 78 (1963), and Deligne, Bourbaki 389, §4. Statement: on
a fine witness `(Y, Φ)`, some `y_τ` satisfies:
- `IsShimuraHolFamily`: the moduli clause `ℂ²/Λ_τ`, and holomorphy;
- the fibres of `τ ↦ y_τ` are exactly the `Γ(3)`-orbits, for `Γ(3) = {x ∈ 𝒪 : x x̄ = 1, x ≡ 1 mod 3𝒪}`
  (`InGamma3`), acting through `BPAnalytic.QM.iota` and Mathlib's `GL(2,ℝ)` action on `ℍ`. This is the
  injectivity of `Γ_S\ℍ → V_S(ℂ)`.

The orbit clause was checked by hand (SPECULATIVE). `Λ_{γτ} = Λ_τ/(cτ+d)` for `γ ∈ 𝒪¹`. The level structure
`η_τ(a) = ι(a)v_τ/3` is preserved iff `γ ≡ 1 mod 3𝒪`. An `ι`-compatible isomorphism `ℂ²/Λ_τ → ℂ²/Λ_{τ'}` is a
scalar, and it forces `τ' = uτ` with `u ∈ 𝒪^×` of norm `1`. `det ι(x) = nrd x`.

`shimuraFamily_of_mainThmI : ShimuraMainThmIY3 → ShimuraFamily` compiles.

**What the literal print needs and Mathlib 4.35 lacks:**
1. **Global class field theory.** Shimura's reciprocity law at a CM point `z` (fixed by `q(K^×)`) reads
   `φ_S(z)^{[s,K]} = φ_{S'}(z)`. It uses the Artin map `[·, K] : 𝔸_K^× → Gal(K^ab/K)` of an imaginary quadratic
   `K`. Mathlib has `FiniteAdeleRing` but no global reciprocity map. The reciprocity law characterizes the
   canonical model, so without it Main Thm I is only "a model over `k_S` with a holomorphic uniformization".
2. **The canonical model `V_S` of one component over `k_S = ℚ(ζ₃)` as a separate object, and Deligne's comparison
   `Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ` (Bourbaki 389, §4).** shimura-glue §5.4 says the same. Without them the surjectivity
   of `Γ_S\ℍ → V_S(ℂ)` cannot be stated on the `ℚ`-model.

The holomorphy part is concrete over Mathlib (`IsHolFamily`: regular functions pull back to analytic functions).
No analytification is needed.

## 6. Statement review

- **No field statement changed.** Each field is proved as its kernel constant, and the verbatim copies are checked
  by `rfl` (VERIFIED).
- **Independent review.** One model reviewer read all 18 leaf and glue statements with no access to my
  conclusions. It found nothing false, vacuous or stronger than the print. In particular:
  - it re-derived the sign and factor of `FaltingsLemma5Printed` against the kernel's height normalization;
  - it checked `RaynaudKernelBound` locally (it is sharp for `μ_p`);
  - it checked the `Γ(3)` orbit clause of `ShimuraMainThmIY3` (`det ι = nrd`, `Γ(3)` has no `±` ambiguity).

  It had three cosmetic notes:
  - `LocallyOfFiniteType` is redundant in `IsNeronModelOver`; it is kept to match BLR's definition.
  - The docstring of `SGA3_VIB_3_10` was rewritten.
  - The docstring of `kerOmegaLog` now says that Faltings' `G = 𝒩_A⁰ ×_{𝒩_B⁰} S` is an open subscheme of the Lean
    `G` containing `s(S)`, so the value is the same.

  Its locator doubts match mine: BLR 1.2/4 may be printed with strict henselizations, and "3.10" and "2.1.3" may be
  numbered differently.
- **Not vacuous.**
  - The hypotheses of `BLR_1_2_4`, `SGA7_IX_3_3`, `FaltingsLemma5Printed` and `RaynaudKernelBound` are Néron
    models, which exist (BLR 1.4/3).
  - The open `U = idCompSet` in `SGA7_IX_3_3` exists by `SGA3_VIB_3_10`.
  - `ShimuraMainThmIY3` is an existential that holds for Shimura's `φ_S`.
- **Not stronger than the print, as recalled.**
  - BLR quantifies over isomorphic copies of `𝒪_{S,s}`.
  - SGA 3 is stated for smooth `G`.
  - SGA 7 allows any homomorphism with isomorphic generic fibre and only finite `K'/K`.
  - EGA uses the kernel's own limit setting.
  - Shimura drops reciprocity and surjectivity.
- **Definitions Mathlib lacks:**
  - a sheaf of relative differentials on schemes (replaced by stalkwise conormal modules);
  - the identity component of a group scheme over a base (`idCompSet`);
  - global class field theory and Shimura's canonical models (§5).

## 7. Checks

`scratch/c-to-printed/run.sh FILE` runs `lean` with `LEAN_PATH` on a copy of the e38375b3 build (`~/ctp-lib`), one
Lean process at a time. Results:
- `CToPrinted.lean`: about 11 s, no errors, 14 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`
  (VERIFIED).
- `Shimura.lean`: about 6 s, no errors, 3 `#print axioms` lines, all standard (VERIFIED).
- `grep` finds no `sorry` and no `axiom` in either file (VERIFIED).

For integration:
- the bundle `CToPrinted.CToPrintedLeaves` holds the six new leaves and `AVGlue.GeomConnOfRationalPoint`;
- `CToPrinted.fields_of_leaves` gives three of the four fields;
- `CToPrinted.reductGlue_leaves_of_printed` gives reduct-glue's leaves `NeronLocalizesDVR`, `IdentityComponentOL`
  and `OpenImmersionOfLocal`.

The field theorems are:
- `CToPrinted.neronLocalizesDVR_of_printed`;
- `CToPrinted.faltingsLemma5BC_of_printed`;
- `CToPrinted.semistableNeronBaseChange_of_printed_full`;
- `CToPrinted.Shimura.shimuraFamily_of_mainThmI`.

The new leaves are:
- `BLR_1_2_4`, `FaltingsLemma5Printed`, `RaynaudKernelBound`, `SGA3_VIB_3_10`, `SGA7_IX_3_3`,
  `EGAIV_8_10_5_openImm`, `Shimura.ShimuraMainThmIY3`;
- plus the existing bundle leaf `AVGlue.GeomConnOfRationalPoint`.
