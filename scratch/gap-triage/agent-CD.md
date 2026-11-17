# gap-triage agent CD: groups C and D (Néron models, semistable reduction, Faltings 1983, Faltings heights)

Read-only survey, 2026-11-14. Base e38375b3 (w62); the six printed leaves are read on origin/wip/w63 (b5ff0474) with
`git show`. Nothing was compiled. Line numbers are at e38375b3 unless marked "w63".

## 0. Cross-cutting findings

**F1. What the height fields feed.** Every height field reaches exactly one live consumer,
`HDec.HSyn.glueOutputs_of_leaves3` (TailD.lean:200), plus `G0RevIsog.reverseIsogeny_of_leaves3` (TailD.lean:118).
The chain (VERIFIED by grep and reading):
- the field;
- `researchLeaves9_of_open10` (TailZ15.lean:92), then `researchLeaves8_of_open9` (TailZ9.lean:95);
- `heightLeaves_of8` (TailZ4.lean:158): `ss2 bost javanpeykar faltings5 pazuki gaudronRemond`, with `n1` from
  `neronSchemeExtensionExists`;
- `ZInQ.HeightGlue.heightRows_of_t35` (TailZ.lean:1498), then `ZInQ.HeightSplit.heightRows_of` (TailY.lean:822). This
  gives R18 (`r18_of_leaves` :534), R19 (`r19_of_leaves` :794), R20 (`r20_of_leaves'` :619), R21 (`r21_of_leaves'`
  :497), R22 (`r22_of_upper` :764) and `StableHeightFinite` (`stableHeightFinite_of'` :424);
- `researchLeaves7_of_open8` (TailZ4.lean:179, `r18 … h5fin`), then the older generations down to
  `researchLeaves3_of_open2` (TailE.lean:6568) and `HSyn.ResearchLeaves3` (TailD.lean).

Inside `glueOutputs_of_leaves3` (the proofs live in LPrefix.lean):
- R18 goes through `javanpeykarJ1` (LPrefix:12068). It is applied to `J = J₁(N)` over ℚ only, with the Belyi function
  `j/1728` of degree `≤ N²` and `g ≤ N²`.
- R22 goes through `thetaPazuki` (LPrefix:12090). It is applied to the fibre QM abelian surface `A` over the number
  field `L` only (dimension 2).
- R19, R20 and R21 go through `transfer_core` (LPrefix:12153). They are applied over `L` to `J₁(N)_L` (dimension
  `g ≤ N²`), `P = A × Z` and `Z`, where `Z` is the Poincaré complement of `A` in `J₁(N)_L` (`dim Z ≤ g`).
- `StableHeightFinite` (`r.h5.1`) is applied to `A`, `J₁(N)_L`, `P` and `Z`.
- The CM branch of `GlueOutputs` is never used: the proof always takes `Or.inl`.

So the heights are used for:
- abelian varieties over number fields that vary with `u` (`[L:ℚ] ≤ Q_D·M_S(u)`), not one fixed field;
- several dimensions: 2 for `A`, up to `N²` for `J₁(N)`, `P` and `Z`;
- an **explicit** bound, never for finiteness.

The target `ZInQ.SixContactMin` (Hypotheses/HeightMin.lean:50) is the explicit inequality
`ratHeight u ≤ heightH6 heightD · M_S(u)^24`. `GlueOutputs` (HDecomp/Assembly.lean:550) carries the numerical outputs
(`NonCMOutput`, `PazukiOutput`). **No route avoids heights inside this architecture.** A finiteness statement
(Shafarevich or Faltings type) gives no constant, and `heightD` is a fixed explicit number in the target. Avoiding
Faltings heights would mean a different proof of `SixContactMin`, which is out of scope.

**F2. The Faltings 1983 theorems are used qualitatively, never for finiteness.** `r9a` (semisimplicity) and `r9b`
(Tate's conjecture) enter G8–G12, G13 and E1 (§r9a). No Faltings finiteness or Shafarevich statement is anywhere in
the chain.

**F3. R20 is used one-sidedly, so `raynaudKernelBound` is dead weight.** In `transfer_core` (LPrefix:12153):

```lean
  have hvar := r20 L J P ψ hψ x y hx hy        -- |h(J) − h(P)| ≤ ½ log deg ψ,  ψ : J → P
  ...
  · have := (abs_le.mp hvar).1                  -- only  h(P) ≤ h(J) + ½ log deg ψ
    linarith
```

For `φ : A → B` that is `h(B) ≤ h(A) + ½ log deg φ`. From `FaltingsLemma5Printed`
(`h(B) = h(A) + ½ log deg φ − kerOmegaLog/[K:ℚ]`) it follows with the proved `kerOmegaLog_nonneg` alone (w63
TailZ19.lean:368). `RaynaudKernelBound` serves only the unused other side. Better still, this half needs neither
Lemma 5 nor semistability (§faltingsLemma5Printed). The obstacle is purely structural: `ResearchLeaves3.r20` has the
two-sided kernel type `ZInQ.DefFaltings.R20_FaltingsLemma5` (HDecomp/Faltings/Leaves.lean:69), carried through every
generation.

**F4. Spreading-out infrastructure already in the tree** (VERIFIED-READ). It makes `egaIV_8_10_5_openImm` T1 and the
direction of `blr_1_2_4` that is used T2:
- Mathlib `AlgebraicGeometry/AffineTransitionLimit.lean`:
  - `exists_preimage_eq` (L337, Stacks 01Z4(1)): `(U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) : ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U`;
  - `exists_map_preimage_eq_map_preimage` (L290, 01Z4(2));
  - `isLimitOpensCone` (L231).
- Vendor `ZInQKernel/Contrib/CloudW01Spread/StacksFrontier/AlgebraicGeometry/Limits/DescendingMorphisms/`:
  - `Isomorphism.lean:180` `exists_isIso_baseChange_of_isIso_limitBaseChange` (Stacks 081E):
    `… [LocallyOfFinitePresentation f₀.left] [IsIso ((Over.pullback (c.π.app i₀)).map f₀).left] : ∃ (i : I) (g : i ⟶ i₀), IsIso ((Over.pullback (S.map g)).map f₀).left`;
  - `ClosedImmersion.lean:413` `exists_isClosedImmersion_baseChange_of_isLimit` (01ZP);
  - `BaseChange.lean:297` `baseChangeConeIsLimit … : IsLimit (baseChangeCone D c i X)`;
  - `Relative.lean:309` `exists_morphism_after_baseChange` (01ZM(2)) and `:336` `eventually_eq_of_baseChange_eq`
    (01ZM(3));
  - `Smooth.lean:357` `exists_smooth_baseChange_of_smooth_limitBaseChange` (0C0C).
- Vendor `LimitDescentGlueing/Glueing.lean:631` `exists_model_of_finitePresentation_of_essentiallySmall` (01ZM(1)).

**F5. The Néron-model library.**
- `CloudW03NeronSurj` (Anthropic FLT port) proves only the Néron mapping property for **abelian schemes** over a DVR:
  `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof` (CloudW03NeronSurj/Main.lean:35; README VERIFIED-READ:
  "properness at codimension one followed by Weil's extension argument", BLR 1.2/8, 4.4/1).
- No **existence** of Néron models for arbitrary abelian varieties is vendored. The brief's "Néron models over a
  henselian DVR in Anthropic FLT" is not in this tree (SPECULATIVE: possibly upstream, unported).
- `NeronC` provides:
  - the group law from the mapping property: `grpObjOfNeron` and `isMonHom_of_neron`, used in
    `ReductSplit.exists_neron_groupModel` (TailZ7.lean:315);
  - uniqueness of extensions (`neron_extension_injective`, NeronGroup.lean:~95).

**F6. Mathlib heights** (VERIFIED by listing and grep). `Mathlib/NumberTheory/Height/` has:
- `Basic`, `NumberField`, `Projectivization` (`mulHeight`, `logHeight`);
- `MvPolynomial` (`logHeight_eval_le`, `logHeight_linearMap_apply_le`);
- `EllipticCurve` (naive height, `finite_torsion`);
- `Northcott`.

These are Weil heights only. There is no Faltings height, no Arakelov degree on schemes and no Néron model. The
kernel's own Faltings height:
- `ZInQ.DefFaltings.stableFaltingsHeight` (HDecomp/Faltings/Height.lean:59, an `EReal` infimum over `FinExt K` and
  `MetrizedModel`);
- `GroupModel.height` (:235);
- `faltingsHeight` (:295).

The published stable height is `ZInQ.HeightSplit.IsStableFaltingsHeight` (TailY.lean:120). Height-model comparison
lemmas (VERIFIED-READ):
- `HodgeData.modelHeight_eq_add_of_le` (HDecomp/Faltings/HodgeData.lean:454), with exactly Faltings' correction term
  `log relIndex / [K:ℚ]`;
- `modelHeight_le_of_le` (:478);
- `torusMetricSq_comap` (:303);
- `covolume_comap_mul_det` (:227);
- `HeightAntitone` (Contrib/HeightBC/H5GlueMinimal.lean:576), proved:
  `(𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f → IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height`.

**F7. Never-projected uses.** `r8 : PkgI2.GrothendieckMonodromy` is still built at TailZ9.lean:104 (from
`semistableReductionDVR`, `semistableUnipotent` and `neronSchemeModelExistsDVR`). It is never projected from
`ResearchLeaves3` (grep `\.r8\b`: constructors only; frontier §4.10 says the same). Those three fields' live uses are
only through r6, SS1 and SS3.

**F8. Branches.**
- origin/wip/unipotent-b and origin/wip/reduct-b both point at b5ff0474, the w63 merge, with no commits of their own
  (VERIFIED, `git log`). unipotent-b has produced nothing yet.
- origin/wip/c-to-printed (report read) is folded into w63 as TailZ19.

---

## FREE fields

### r9a: `PkgI3.FaltingsSemisimple`

1. **Identity.**
   - Constant: `PkgI3.FaltingsSemisimple`, ZInQKernel/HDecomp/Objects.lean:423:
     `∀ (K) [Field K] [NumberField K] (A : AbVar K) (ℓ) [Fact ℓ.Prime], (A.galRep ℓ).IsSemisimpleRepresentation`.
   - Row: frontier H-6.
   - Form: LEAF, published form (Faltings 1983 Satz 3).
2. **Use.** The field passes unchanged (`r9a := r.r9a`) down to `ResearchLeaves3`. Live consumers (TailD.lean):
   - `g8_g12_of_leaves3` (:129) → `G0Galois.g8_g12` (TailA.lean:2227) → `g8` (TailA:2080). Object: the fibre QM
     surface `A` over a Galois number field, at ℓ = 5.
   - `afterG7_of3` (:156) → `g8_g11` (TailA:2203). Same `A`, at ℓ = 3.
   - `newformLeaves_of3` (:150) → `NewformLeaves.r9a` → `g13`, `commonConstituent_of_attached` (TailA:3418), `c9_core`,
     `jSide`. Objects: the newform quotient `A_f` of `J₁(N)` over ℚ, and `J₁(N)` base-changed to `L`.
   - `hom_of_common3` (:191) → `PkgI3.E1_exists_hom_ne_zero` (HDecomp/I3Linalg/C2.lean:768). Object: `A` over `L'`,
     via the semisimplicity of `V_ℓ(A)` (`hS K A ℓ`).

   Use (b), but over unbounded dimensions and varying fields. Weakest sketch:
   `∀ K [NumberField K] (A : AbVar K) (ℓ ∈ {3,5}), (IsQMSurface A ∨ ∃ N, A is A_f, J₁(N), or their base change to K) → (A.galRep ℓ).IsSemisimpleRepresentation`.
   This is still the full depth of Faltings' theorem (for `J₁(N)` and its quotients over a number field there is no
   shortcut: Ribet's semisimplicity of `V_ℓ(A_f)` itself uses Faltings).
3. **Library.** None in Mathlib or the vendored code. The kernel has the representation objects
   (`AbVar.galRep`, `tateHomZl`: Objects.lean, VERIFIED-READ for the leaf statement only).
4. **Missing.** All of Faltings 1983: Faltings heights, isogeny finiteness, Tate's lemma.
5. **Tier.** T4.
6. **Strategy.** Keep cited.
7. **Notes.** The object restriction does not help.

### r9b: `PkgI3.FaltingsTate`

1. **Identity.**
   - Constant: `PkgI3.FaltingsTate`, Objects.lean:430:
     `∀ K [NumberField K] (A B : AbVar K) ℓ, Function.Injective (tateHomZl ℓ A B) ∧ Set.range (tateHomZl ℓ A B) = {φ | IsGalEquivariant φ}`.
   - Row: H-7.
   - Form: LEAF (Satz 4, Kor. 1).
2. **Use.** The same four consumers as r9a, plus `h10g … hF` inside `g8_g11` (TailA:2224). Pairs it is applied to:
   - `(A, J₁(N)_{L'})` in E1, `exists_hom_ne_zero_of_equivariant hF`;
   - `(A, A)` in C2/G8–G10;
   - `(A_f, J₁(N))` in `jSide`.

   Use (b). Weakest: the Tate isomorphism for `Hom(A, J₁(N)_L)` and `End(A)` with `A` a QM surface, and for `A_f` in
   `J₁(N)`. Still deep.
3. **Library.** None.
4. **Missing.** As for r9a.
5. **Tier.** T4.
6. **Strategy.** Keep cited.

### bostLowerBound: `ZInQ.HeightSplit.BostLowerBound`

1. **Identity.**
   - Constant: TailY.lean:442:
     `∀ K [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = g → ∀ x, IsStableFaltingsHeight A x → -((g:ℝ)/2 * log (2π)) ≤ x + (g:ℝ)/2 * log π`.
   - Row: H-112.
   - Form: LEAF, published form (Bost, Sém. Bourbaki 795; display UNVERIFIED).
2. **Use.**
   - Chain: `heightLeaves_of8.bost` → `r21_of_leaves'` (TailY:497, through `grBostBound_of_bost` :470) → R21 →
     `transfer_core`, which applies `r21 L Z gZ hZd`.
   - The only object is the Poincaré complement `Z` of `A` in `J₁(N)_L`, of dimension `gZ ≤ N²`.
   - Use (b). Weakest: `GRBostBound` restricted to that `Z`:
     `∀ L [NumberField L] (Z : AbVar L) (gZ), Z.dim = gZ → (Z isogenous to a factor of some J₁(N)_L) → ∀ x, IsStableFaltingsHeight Z x → -(3/2)·gZ ≤ x`.
   - This is implied by Bost. It is still deep: no height-free lower bound exists, since a lower bound on a Faltings
     height is a slope or period statement.
3. **Library.** Only the arithmetic (`log_two_pi_add_log_pi_lt_three`, proved, TailY:~449). Nothing on lower bounds.
4. **Missing.** Arakelov slope theory: Bost's slope inequality and Petersson norms.
5. **Tier.** T4.
6. **Strategy.** Keep cited.
7. **Notes.** Normalization risk is recorded in height-split §8 (3).

### javanpeykarBound: `ZInQ.HeightSplit.JavanpeykarBound`

1. **Identity.**
   - Constant: TailY.lean:521. A curve `X/K` with Jacobian `J` (dimension `g ≥ 1`) and a `K`-rational Belyi `t` of
     degree `d` give `x ≤ javanpeykarBound g d` (`= 13·10⁶ g d⁵`) for `IsStableFaltingsHeight J x`.
   - Row: H-109.
   - Form: LEAF, published form (specialization of Javanpeykar 2014 Thm 1.1.1; read by the audit).
2. **Use.**
   - Chain: `r18_of_leaves` (TailY:534) → R18 → `r18Concrete_of` (LPrefix:12034) → `javanpeykarJ1` (LPrefix:12068),
     which applies `hR18 ℚ X P₀ J …` → `glueOutputs_of_leaves3` (`hJb`).
   - Objects: `K = ℚ`, `X` the model of `X₁(N)`, `J = J₁(N)`, `t = j/1728`. Only `g ≤ N²` and `d ≤ N²` are used.
   - Use (b). Weakest: `∀ N ≥ 1, ∀ J, IsJ1 N J → ∀ x, IsStableFaltingsHeight J x → x ≤ 13·10⁶·N¹²`, implied by
     Javanpeykar with `g, d ≤ N²`.
   - Still deep. Any published explicit polynomial bound for `h_F(J₁(N))` would do, provided `transfer_core`'s constant
     `13000000·N^12` is adjusted; candidates are the Edixhoven–Couveignes book bounds for `X₁(p)` (UNVERIFIED), but
     they only cover prime level.
3. **Library.** `x1BelyiOnModel_of_belyiX1` (LPrefix, proved) and `LeafModCurves.dim_J1_le`. Nothing on Arakelov
   invariants.
4. **Missing.** Arakelov theory of curves (Faltings delta, Green functions, Merkl's theorem).
5. **Tier.** T4.
6. **Strategy.** Keep cited. Optionally specialize the leaf to `J₁(N)` (this changes no count).

### pazukiCor13Upper: `ZInQ.HeightSplit.PazukiCor13Upper`

1. **Identity.**
   - Constant: TailY.lean:730. For an abelian surface over `K` with published height `x`, a uniformization, a Siegel
     period matrix and an algebraic theta-null representative `z`:
     `max 1 (absLogHeightL2 z) - max 1 (x + log π)/2 ≤ pazukiC2 * log(min … + 2)`.
   - Row: H-113.
   - Form: LEAF (upper half of Pazuki 2012 Cor. 1.3(2); read by the audit).
2. **Use.**
   - Chain: `r22_of_upper` (TailY:764) → R22 → `r22Concrete_of` (LPrefix:12043) → `thetaPazuki` (LPrefix:12090) →
     `glueOutputs_of_leaves3` (`hPaz`).
   - Object: only the fibre QM abelian surface `A` over `L`, dimension 2, with the theta point from
     `ThetaPointOfFibre`.
   - Use (b). Weakest: the same statement restricted to `A` with `FibreOver Y Φ π u L A`. Still deep.
3. **Library.** `absLogHeight_le_absLogHeightL2` (proved, TailY) and Mathlib `Height.mulHeight`. Nothing on theta or
   Faltings comparison.
4. **Missing.** Theta functions on Siegel space, the Mumford–Bost–David comparison, Arakelov heights of theta divisors.
5. **Tier.** T4.
6. **Strategy.** Keep cited.
7. **Notes.** RISK (height-split §8.1): if Pazuki's coordinates are the second-order theta constants, the row
   overstates the print by about `log 4`. Whether `PazukiOutput`'s slack covers this is unchecked. This is the most
   valuable thing to settle for this field.

### gaudronRemondThm14: `ZInQ.HeightSplit.GaudronRemondThm14`

1. **Identity.**
   - Constant: TailY.lean:786. For isogenous `A`, `B` over `K` with `dim A = g` and published height `x`, there are
     isogenies in both directions of degree `≤ grKappa g [K:ℚ] x`.
   - Row: H-110.
   - Form: LEAF (GR 2014 Thm 1.4; read by the audit).
2. **Use.**
   - `r19_of_leaves` (TailY:794) → R19, which has two consumers:
     - `transfer_core` (LPrefix:12153) uses only the **first** conjunct, on `(J₁(N)_L, P)`: an isogeny `ψ : J → P` with
       the degree bound.
     - `reverseIsogeny_of_leaves3` → `isogenyReverseExists_of_r19` (TailA.lean:945) uses only the **existence**
       of the reverse isogeny.
   - The second use can be served by the already present textbook route `G0RevIsog.reverseIsogeny (hQ : IsogenyQuasiInverse)`
     (TailA.lean:~937; `milneIsogenyQuasiInverse` is already a bundle field). After a consumer edit, GR is then needed
     only in the form
     `∀ L J P g x, J.dim = g → IsStableFaltingsHeight J x → (∃ φ : J → P isogeny) → ∃ ψ : J → P, IsIsogeny ψ ∧ deg ψ ≤ grKappa g [L:ℚ] x`
     (for `J = J₁(N)_L`).
   - Still deep.
3. **Library.** None.
4. **Missing.** The Masser–Wüstholz / GR period theorem.
5. **Tier.** T4.
6. **Strategy.** Keep cited.

### neronSchemeModelExistsDVR: `ReductSplit.NeronSchemeModelExistsDVR`

1. **Identity.**
   - Constant: TailZ7.lean:238. For any field `K`, DVR `O ⊆ K` and abelian variety `A/K`: a smooth, separated,
     quasi-compact `N/O` with `e : N_K ≅ A.X` and the Néron mapping property.
   - Row: H-148.
   - Form: LEAF (BLR 1.4/3, scheme form; "pending the base review").
2. **Use** (TailZ15.lean:98–116). Live:
   - (i) `r6 := ReductGlue.raynaudCriterion_leaves …` (TailZ14:241) → `raynaudCriterion_final` →
     `hasSemistableReduction_of hN O B` (TailZ7:333, 405). r6 is then used in `kernelFieldExists_of_split''`
     (TailC:6919) → `good_of_QML3` (TailC:5947) → `goodReduction_of_QM_rational3_C` (LF4T5:699). There `K` is a
     characteristic-0 field with `τ : K →+* ℂ` (a number field in the actual use), `A` is a QM surface, and m = ℓ = 3.
   - (ii) `semistableReductionThm_final` and `semistablePersists_final` (TailZ7:1290–1300; SS1, SS3), at DVRs `O'`
     of number fields, through `exists_neron_groupModel` (TailZ7:315).
   - Dead: `r8` (F7).
   - Use (b): DVRs of number fields only. Weakest sketch:
     `∀ (L) [Field L] [NumberField L] (O : ValuationSubring L) [IsDiscreteValuationRing O] (A : PkgI3.AbVar L), ∃ N e, Smooth ∧ Separated ∧ QC ∧ Néron property over O`.
   - In the w63 tree this is a theorem of existing fields:
     - N1: `neronSchemeExtensionExists`, then `neronModelExists_of_extension`;
     - plus `blr_1_2_4` (`.mp`), exactly as in `CToPrinted.neronLocalizesDVR_of_printed` (w63 TailZ19:138);
     - plus `ReductGlue.isLocalization_center` (every DVR of `L` is `(𝓞_L)_𝔭`; proved).

     That is project glue (T1). The catch is consumer (i): `PkgI2.RaynaudCriterion` is stated over every field.
     Either state an r6 for number fields, or restate `RaynaudSemistable`'s conclusion as `HasSemistableReduction`
     (∃ form) so that r6 no longer needs this field. The second is the field under review; a reading call for the
     integrator.
3. **Library.**
   - CloudW03 gives the Néron mapping property for abelian schemes over a DVR (F5), so good-reduction places are
     covered.
   - `exists_neron_groupModel` (TailZ7:315, VERIFIED-READ) supplies the group law.
   - No existence in general.
4. **Missing** (general form): BLR's smoothening, the weak Néron model, the extension of the group law (Weil), and
   descent from the strict henselization (BLR ch. 3–6).
5. **Tier.** General: T4. Number-field restriction from N1 + `blr_1_2_4`: T1 glue plus a consumer restatement.
6. **Strategy.** Reduce: derive it from N1 + BLR 1.2/4, which removes one field. Alternatively the reverse: derive N1
   (blocked H-77) from this field, the "if" half of `blr_1_2_4`, spreading out (`abVarSpreadsOut_of_ega4`, used at
   TailZ15:85) and gluing the local models (BLR 1.4/3's last step). That is T3, glue-heavy (gluing Over-schemes).
7. **Notes.**
   - Both N1 and this field are BLR 1.4/3. Keeping both as independent leaves double-counts one theorem.
   - Base-ring reading risk: the print may assume a henselian or strictly henselian DVR (frontier H-148).

### w63 printed leaf `blr_1_2_4`: `CToPrinted.BLR_1_2_4`

1. **Identity.**
   - Constant: w63 TailZ19.lean:63 (namespace `CToPrinted`); field at w63 TailZ19:1843. `IsNeronModelOver` is at :44.
   - No r5 row (it postdates r5).
   - Form: LEAF (BLR 1.2 Prop. 4, the full iff over any Dedekind domain; UNVERIFIED).
2. **Use.**
   - `researchLeaves11_of_open12` (w63 TailZ19:1859) → `neronLocalizesDVR_of_printed` (:138), also inside
     `semistableNeronBaseChange_of_printed_full` (:1632).
   - **Only `.mp` is used** (`(hB (𝓞 L) L 𝒩.G).mp h1` at :145). The base is `R = 𝓞_L` with `L` a number field, `X` a
     Néron group model `𝒩.G`, and the localization at the center of a DVR `O`.
   - Downstream: `neronLocalizesDVR` → `SemistableLocalGlobal` (TailZ14:892, 1070) → SS1, SS3, SS2 → every height
     row (F1).
   - Use (b). Weakest:
     `∀ L [NumberField L] (X : Over (Spec (𝓞 L))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom], IsNeronModelOver (𝓞 L) L X → ∀ 𝔭 [𝔭.IsMaximal] R𝔭 [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 L] [IsScalarTower …], IsNeronModelOver R𝔭 L (X ×_{𝓞 L} R𝔭)`.
     This is implied by the print.
3. **Library** (F4, VERIFIED-READ). The "only if" proof:
   - Smooth, separated and qc are stable under base change (Mathlib).
   - Injectivity comes from schematic density of the generic fibre (`pullback_map_injective`, as used in
     `NeronC.neron_extension_injective`).
   - Surjectivity, for each affine open `V` of a smooth `Y/R_𝔭` (finitely presented):
     - spread `V` out to a smooth `V_s/𝓞_L[1/s]` (`exists_model_of_finitePresentation_of_essentiallySmall`,
       `exists_smooth_baseChange_of_smooth_limitBaseChange`), with `Spec R_𝔭 = lim Spec 𝓞_L[1/s]` (the system already
       built in w63 TailZ19 :483–720: `specConeOIsLimit`);
     - `V_s → Spec 𝓞_L` is smooth, so the Néron property over `𝓞_L` extends `(V_s)_L → X_L`;
     - base change back to `R_𝔭`;
     - glue the extensions over an affine cover of `Y` by uniqueness.
4. **Missing.** The gluing of morphisms over an open cover (Mathlib has `Scheme.Cover` glue for morphisms), and the
   identification `(V_s)_{R_𝔭} ≅ V` from the model lemma.
5. **Tier.** T2 for the "only if" direction (one or two tasks). The full iff is T3 ("if" needs gluing of
   extensions plus EGA IV 8.8.2, which is in the tree as `EGAIV_8_8_2_ii_proof`).
6. **Strategy.** Prove the direction that is used. Replace the field by
   `BLR_1_2_4_onlyIf` (theorem) or prove `NeronLocalizesDVR` directly; this removes one field.
7. **Notes.** The strict-henselization reading risk becomes moot once the direction used is proved.

### w63 printed leaf `faltingsLemma5Printed`: `CToPrinted.FaltingsLemma5Printed`

1. **Identity.**
   - Constant: w63 TailZ19.lean:387 (`kerOmegaLog` at :361); field at :1846.
   - No r5 row. The old field `faltingsLemma5BC` was H-111; its base form `FaltingsLemma5` was H-167.
   - Form: LEAF (Faltings 1983 Lemma 5, the identity with correction term; UNVERIFIED, unread).
2. **Use.**
   - Chain: `researchLeaves11_of_open12` → `faltingsLemma5BC_of_printed` (:449) → `faltingsLemma5_of_printed` (:432)
     → `ReductSplit.faltingsLemma5BC_final` → `faltingsLemma5BC` → `heightLeaves_of8.faltings5` →
     `r20_of_leaves'` (TailY:619) → R20 → `transfer_core` (LPrefix:12153).
   - Objects: `ψ : J₁(N)_L → P = A × Z` from GR, over the compositum of the semistable fields.
   - **Only the upper half is used** (F3). Use (b), and one-sided.
   - Weakest statement implied by the print (with `kerOmegaLog_nonneg`):
     `FaltingsLemma5Upper : … semistable Néron 𝒩A 𝒩B over 𝓞_K, φ𝒩 extending φ → 𝒩B.height = y → 𝒩A.height = x → y ≤ x + ½ log (isogDeg φ)`.
   - A strictly better target is not a consequence of Lemma 5 but provable glue:
     `GroupModelIsogenyUpper : ∀ K A B φ (IsIsogeny φ) L (𝒢A : GroupModel A L) (𝒢B : GroupModel B L) (f : 𝒢A.G ⟶ 𝒢B.G), IsMonHom f → f extends φ_L → 𝒢B.height ≤ 𝒢A.height + ½ log (isogDeg φ)`.
     It has no semistability and no Néron hypothesis.
     - Finite part: `f^*` maps `⋀^g ω_{𝒢B}` into `⋀^g ω_{𝒢A}` (integrality of pullback), giving the
       `modelHeight_eq_add_of_le` correction `≥ 0`.
     - Archimedean part: `‖f^*η‖² = deg φ · ‖η‖²`, by lifting `φ` to `M : ℂ^g → ℂ^g` with `[Λ_B : MΛ_A] = deg φ`.
     - With N1 (Néron model of `B_E` for every `E`, and the Néron extension of `φ_E` from any model of `A_E`) this
       gives `stableFaltingsHeight B ≤ stableFaltingsHeight A + ½ log deg φ` directly on the kernel infimum, without
       SS1/SS2/SS3.
3. **Library** (VERIFIED-READ). Also `CToPrinted.exists_extension` (w63 :407, the Néron extension is a homomorphism)
   and `kerOmegaLog_nonneg` (:368). The rest:

   | finite part | archimedean part |
   |---|---|
   | `HeightAntitone` (proved; the iso-generic-fibre case) and `HodgeData.modelHeight_eq_add_of_le`, `modelHeight_le_of_le` | `torusMetricSq_comap`, `covolume_comap_mul_det`, `det_restrictScalars_complex` (HodgeData.lean) |

   AN3 (`AnalyticUniformizationExists`/`Unique`) is already derived from T35 (TailZ.lean `heightGlue_of_t35`).
4. **Missing.**
   - (a) The isogeny version of `HeightAntitone` (the lattice index and the archimedean scaling).
   - (b) `isogDeg φ = [Λ_B : MΛ_A]`: `#ker φ(K̄) = #ker φ(ℂ)` (memory: abvar-complex-points recipes) and the kernel of
     `φ` on `ℂ^g/Λ_A`.
   - (c) Base-change invariance of `isogDeg`.
   - (d) A new generation with `R20Upper` replacing `R20_FaltingsLemma5` in `ResearchLeaves3.r20` and all older
     bundles, plus a `transfer_core` variant: a prune-like mechanical refactor with hash-guard churn.
5. **Tier.** As a field: T4 (Lemma 5 identity, Néron and differentials). Bypass by (a)–(d): T2.
6. **Strategy.** Reduce/bypass. The quick step is (d) with `FaltingsLemma5Upper` from the printed leaf (drops
   Raynaud). The full step is `GroupModelIsogenyUpper`, which drops this leaf too and removes SS3's only use (SS3 is
   used only by `r20_of_leaves'`).
7. **Notes.** Reading risk: Lemma 5 may be printed for good reduction only (c-to-printed §3). The bypass removes that
   risk.

### w63 printed leaf `raynaudKernelBound`: `CToPrinted.RaynaudKernelBound`

1. **Identity.**
   - Constant: w63 TailZ19.lean:399 (`kerOmegaLog φ𝒩 hφ𝒩 ≤ [K:ℚ] · log (isogDeg φ)`); field at :1848.
   - No r5 row.
   - Form: LEAF (Raynaud, Astérisque 127, VII Cor. 2.1.3; number UNVERIFIED).
2. **Use.** It appears only in `faltingsLemma5_of_printed` (:437, `hub`), which bounds the lower side of `|x − y|`.
   The single consumer `transfer_core` needs only the upper side (F3). **Effectively unused.** Weakest sufficient
   statement: `True`, once `r20` is one-sided.
3. **Library.** n/a.
4. **Missing.** Only the generation refactor (d) of the previous section.
5. **Tier.** T1 (structural removal).
6. **Strategy.** Prune: restate `r20` as its upper half along the chain.
7. **Notes.** This is the cheapest count reduction in groups C and D.

### w63 printed leaf `sga3_VIB_3_10`: `CToPrinted.SGA3_VIB_3_10`

1. **Identity.**
   - Constant: w63 TailZ19.lean:199, `∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom], IsOpen (idCompSet G)`
     (`idCompSet` at :191); field at :1851.
   - No r5 row.
   - Form: LEAF (SGA 3 VI_B 3.10 / EGA IV 15.6.5; UNVERIFIED).
2. **Use** (all inside `semistableNeronBaseChange_of_printed_full`, :1632, so feeding SS2 and then every height row):
   - `idComp_baseChange` (:1220, at `S = Spec O`, `S' = Spec O'`: `h3 S G` at :1226);
   - `idCompSubgroup_of` (:1331);
   - `identityComponentOLRange_of` (:1493, at `S = Spec 𝓞_L`, `G` a group model);
   - `identityComponentBaseChangeDVRRange_of` (:1577, at `𝒩 ×_O O'` over a DVR `O'`; `h3 _ (bcO hO 𝒩.G)` at :787).

   Use (b). Bases are `Spec 𝓞_L` or a DVR of a number field. `G` is smooth, separated and of finite type, with
   connected generic fibre (an abelian variety, or `A_{L'}`). Weakest:
   `∀ (R) [IsDedekindDomain R] (Spec R noetherian, dim ≤ 1) (G : Over (Spec R)) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], ConnectedSpace (generic fibre of G) → IsOpen (idCompSet G)`.
3. **Library.**
   - Mathlib: `Scheme.Hom.fiberHomeo` (cited by c-to-printed; SPECULATIVE, not opened here). Connected components of a
     noetherian space are finite in number and open (Mathlib topology, SPECULATIVE name).
   - Over `𝓞_L`: the kernel's spreading out (`abVarSpreadsOut_of_ega4`, TailZ15:85, with the leaf `egaIV_8_10_5_xii`)
     and Zariski connectedness (`ZariskiConn.ZariskiConnectedness_proof`, proved) give connected fibres outside
     finitely many primes.
4. **Missing.**
   - DVR case: the complement of `G⁰` is `G_s \ G_s⁰`, closed in the closed fibre. This is a topological lemma
     (proper-free, T1).
   - Dedekind case: finiteness of the primes with disconnected fibre for a smooth finite-type group with
     abelian-variety generic fibre (spread properness, then Zariski), then a locally finite union of closed sets.
5. **Tier.** Weakest form: T2 (DVR part T1). General `S`: T3.
6. **Strategy.** Specialize to dimension-1 bases with connected generic fibre and prove.
7. **Notes.** If the `𝓞_L` use (`identityComponentOLRange_of`) can be reorganised to work locally at DVRs only,
   T1 suffices.

### w63 printed leaf `sga7_IX_3_3`: `CToPrinted.SGA7_IX_3_3`

1. **Identity.**
   - Constant: w63 TailZ19.lean:249 (field :1853). `O ⊆ O'` DVRs with `K'/K` finite, `A` semistable at `O`, Néron
     `𝒩`, `𝒩'`, `c : 𝒩 ×_O O' → 𝒩'` a homomorphism with iso generic fibre, and `U = idCompSet(𝒩 ×_O O')`, give
     `IsOpenImmersion (U.ι ≫ c.left) ∧ range = idCompSet 𝒩'`.
   - No r5 row. The ancestor `IdentityComponentBaseChangeDVR` was H-165.
   - Form: LEAF (SGA 7 IX 3.3, second assertion; UNVERIFIED).
2. **Use.** `identityComponentBaseChangeDVRRange_of` (:1577; `h7` at :789) → `semistableNeronBaseChange_of_printed_full`
   → SS2 → the identification `isStableFaltingsHeight_iff` (TailY:209) → R18, R19, R21, R22, `StableHeightFinite`
   (F1).
   - Use (b): `K ⊆ K'` number fields at DVRs over a common prime; `A` is any abelian variety the height rows meet
     (`A`, `J₁(N)_L`, `P`, `Z`). Weakest: the same, with `K` a number field.
   - Still deep: semi-abelian schemes and the Néron lft extension property, SGA 7 IX 3.2 and BLR 7.4/3.
3. **Library.** None (no semi-abelian schemes, no tori over a base).
4. **Missing.** Tori over a base, semi-abelian group schemes, and the extension property of semi-abelian schemes
   (BLR 7.4).
5. **Tier.** T4 (T3 at best).
6. **Strategy.** Keep cited.
7. **Notes.** It is needed only through SS2, i.e. through the independence of the stable height from the field. This
   is inherent to stating Javanpeykar, GR, Bost and Pazuki over the published height.

### w63 printed leaf `egaIV_8_10_5_openImm`: `CToPrinted.EGAIV_8_10_5_openImm`

1. **Identity.**
   - Constant: w63 TailZ19.lean:281 (field :1855). In the kernel's limit setting (directed `J`, affine transitions,
     qcqs stages), a finitely presented `fi : Xi ⟶ Yi` whose base change to the limit is an open immersion is an open
     immersion at some stage.
   - No r5 row.
   - Form: LEAF (EGA IV 8.10.5, open-immersion item; UNVERIFIED).
2. **Use.**
   - `exists_away_of_dvr` (:633, `hE (Idx P) (specDiagP P) (specConeO O) …` at :652) → `openImmersionLocalization`
     (:671) → `ReductGlue.OpenImmersionOfLocal` → SS2.
   - Use (b): only the system `Spec O = lim_{a ∉ 𝔭} Spec 𝓞_L[1/a]` (affine stages), with `X`, `Y` smooth, separated
     and quasi-compact over `𝓞_L`. Weakest: that instance. A finite computation over existing library pieces; no
     published statement is needed.
3. **Library** (F4, VERIFIED-READ for all four):
   - Mathlib `exists_preimage_eq` descends the quasi-compact open image `U = range f_lim` to `V_j ⊆ Y_j`;
   - `exists_map_preimage_eq_map_preimage` makes `f_j⁻¹(V_j) = X_j` eventually;
   - vendor `baseChangeConeIsLimit` presents `Y_lim` as the limit of the `Y_j`;
   - vendor `exists_isIso_baseChange_of_isIso_limitBaseChange` (081E) applied to `X_j → V_j` gives an iso at a later
     stage, hence an open immersion `X_k → Y_k`.
4. **Missing.** Only the assembly, and the index conventions: the leaf uses a `Preorder J` with `Jᵒᵖ ⥤ Scheme`, the
   vendor uses `IsCofiltered I` + `EssentiallySmall`, both fine for `J : Type`.
5. **Tier.** T1.
6. **Strategy.** Prove directly, in the general form as stated.
7. **Notes.** This removes one leaf outright with no statement change.

---

## IN FLIGHT (done in w63; record only)

### neronLocalizesDVR: `ReductGlue.NeronLocalizesDVR`

1. **Identity.** TailZ14.lean:882: a Néron `𝒩` over `𝓞_L` makes `toO 𝒩 O` Néron for every DVR `O` of `L`.
   - No r5 row (added by reduct-glue after r5; leaf-fold10 §1 fold 4).
   - Form: GLUE (c), consequence of BLR 1.2/4.
2. **Use.**
   - `semistableLocalGlobal_of10` (TailZ15:79) → `ReductGlue.semistableLocalGlobal_of` (TailZ14:892, uses at :899 and
     :903) → `semistableReductionThm_final` and `semistablePersists_final` (TailZ15:111, 115) → SS1, SS3 → height rows.
   - Use (b): DVRs of number fields; the full Néron predicate is needed because `hs _ (hL …)` feeds
     `SemistableNeronModels`.
   - **Replaced in w63** by `blr_1_2_4` (`neronLocalizesDVR_of_printed`, w63 TailZ19:138).
3–6. See `blr_1_2_4`: T2, prove the "only if" direction.

### faltingsLemma5BC: `ZInQ.HeightSplit.FaltingsLemma5BC`

1. **Identity.** TailY.lean:609. Row H-111. Form: GLUE (c).
2. **Use.** `heightLeaves_of8.faltings5` (TailZ4:166) → `r20_of_leaves'` (TailY:619) → R20 → `transfer_core` (upper
   half only, F3). **Replaced in w63** by `faltingsLemma5Printed` + `raynaudKernelBound` (`faltingsLemma5BC_of_printed`,
   w63 TailZ19:449).
3–6. See those two leaves: the bypass is T2 and Raynaud is prunable at T1.

### semistableNeronBaseChange: `ZInQ.HeightSplit.SemistableNeronBaseChange`

1. **Identity.** TailY.lean:145. Row H-107. Form: GLUE (c) (SGA 7 IX 3.3 in the open-subgroup form of N2).
2. **Use.**
   - `heightLeaves_of8.ss2` (TailZ4:162) → `isStableFaltingsHeight_iff` (TailY:209) and
     `stableFaltingsHeight_eq_of_semistable` (:162) → all six rows (F1).
   - Applied to every abelian variety the rows meet: `A`, `J₁(N)_L`, `P`, `Z`.
   - **Replaced in w63** by `blr_1_2_4`, `sga3_VIB_3_10`, `sga7_IX_3_3`, `egaIV_8_10_5_openImm` and the textbook field
     `geomConnOfRationalPoint` (`semistableNeronBaseChange_of_printed_full`, w63 TailZ19:1632).
3–6. Of the four printed leaves, two are provable now (EGA T1; BLR "only if" T2), SGA 3 is T2 in the weakest form,
   and SGA 7 is kept.

---

## UNDER REVIEW (not ranked)

Status: origin/wip/unipotent-b and origin/wip/reduct-b have no commits beyond the w63 merge (F8).

### semistableReductionDVR: `ReductSplit.SemistableReductionDVR`

1. **Identity.** TailZ7.lean:278. Row H-146. Form: LEAF (SGA 7 IX 3.6 over a DVR; base-ring review pending).
2. **Use.**
   - Live: `semistableReductionThm_final` (TailZ15:111) → SS1 → the identification (all height rows, F1) and
     `stableHeightFinite_of'`.
   - Dead: `r8` (F7).
   - Use (b): DVRs of number fields, any `A`.
3–6. No library support. T4, keep cited.

### semistableUnipotent: `ReductSplit.SemistableUnipotent`

1. **Identity.** TailZ7.lean:253. Row H-147. Form: LEAF (SGA 7 IX 3.5, one σ at a time).
2. **Use.**
   - Live: r6 via `raynaudCriterion_leaves` (TailZ15:98) → `kernelFieldExists_of_split''` (TailC:6919) →
     `good_of_QML3`. Objects: QM surfaces, ℓ = 3, characteristic-0 `K ⊂ ℂ`.
   - Dead: `r8`.
3–6. T3/T4, keep cited.

### raynaudSemistable: `ReductSplit.RaynaudSemistable`

1. **Identity.** TailZ7.lean:265. Row H-160. Form: LEAF (SGA 7 IX 4.7).
2. **Use.** r6 only (as above). Objects: m = 3, QM surfaces over number fields.
3–6. T4, keep cited.
7. **Note.** Restating its conclusion in the ∃ form `HasSemistableReduction` would free r6 from
   `neronSchemeModelExistsDVR`.

### semistablePersistsDVR: `ReductSplit.SemistablePersistsDVR`

1. **Identity.** TailZ7.lean:710. Row H-162. Form: LEAF (SGA 7 IX 3.3, first assertion).
2. **Use.**
   - `semistableReductionThm_final` (SS1) and `semistablePersists_final` (SS3), TailZ15:111–116.
   - SS3's only consumer is `r20_of_leaves'`. If R20 is bypassed as in §faltingsLemma5Printed, its SS3 use disappears
     and only the SS1 use remains.
3–6. T3/T4, keep cited.

---

## BLOCKED

### neronSchemeExtensionExists: `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (textbook, TailZ11)

1. **Identity.** Contrib/NeronC/NeronGroup.lean:82 (VERIFIED-READ). Row H-77. Form: LEAF (BLR 1.4/3, weakened: no
   group law; surjectivity only).
2. **Use.**
   - `heightLeaves_of8.n1` (TailZ4:160, `neronModelExists_of_extension`) → the identification and all six rows.
   - `t41` (TailN:232 and TailO:2958 `t41_of_extension5`) → `heightAdditivity_of_h5neron` (TailD:204) for
     `h(A) + h(Z) ≤ h(P)`.
   - Use (a), in effect: every abelian variety over every number field that the rows meet.
3–6.
   - Blocked (H-77; no existence theorem in the tree, F5). T4 as stated.
   - Possible reduction (T3): glue local Néron models (`neronSchemeModelExistsDVR`) with the spread-out abelian
     scheme, using `blr_1_2_4.mpr`. Or the reverse direction, see §neronSchemeModelExistsDVR.
   - Keeping both N1 and the DVR leaf double-counts BLR 1.4/3.

### r7a: `PkgI2.NeronOggShafarevich`

1. **Identity.** Objects.lean:861. Row H-5. Form: LEAF (Serre–Tate 1968 Thm 1).
2. **Use.**
   - `gluePieces_of_open2` (TailE:6660) → `kernelFieldExists_of_split''` (TailC:6919) → `good_of_QML3` (TailC:5947) →
     `goodReduction_of_QM_rational3_C` (LF4T5:699).
   - Only `(hNOS K O w hw A).2.mpr` is used ("inertia trivial on infinitely many `A[m]` ⇒ good reduction"), with
     `m = 3^k`, `A` a QM abelian surface, `K ⊂ ℂ` of characteristic 0.
   - Use (b). Weakest: "(c) ⇒ (a)" for QM surfaces with `m = 3^k`. Still needs Néron models.
3–6.
   - Tau Ceti has good reduction for elliptic curves only (Contrib/TauCeti/.../EllipticCurve/Affine/Point/GoodReduction.lean;
     file listing only, SPECULATIVE content).
   - T4, keep cited (blocked, H-5).

---

## Summary table

| field | consumers | use (a/b) | tier | strategy | best attack idea (one line) |
|---|---|---|---|---|---|
| r9a | TailD `g8_g12_of_leaves3`, `afterG7_of3`, `newformLeaves_of3`, `hom_of_common3` (→ `E1_exists_hom_ne_zero`) | b: QM surface A (ℓ=3,5), J₁(N), A_f | T4 | keep cited | none; Faltings is essential for E1/G8 |
| r9b | same as r9a, plus `h10g` in `g8_g11` | b: (A, J₁(N)_L), (A, A), (A_f, J₁(N)) | T4 | keep cited | none |
| bostLowerBound | `r21_of_leaves'` → `transfer_core` | b: Poincaré complement Z ⊂ J₁(N)_L | T4 | keep cited | none (lower bounds on h_F need slope theory) |
| javanpeykarBound | `r18_of_leaves` → `javanpeykarJ1` | b: J₁(N)/ℚ, deg ≤ N², g ≤ N² | T4 | keep cited | could specialize to J₁(N) (no count change) |
| pazukiCor13Upper | `r22_of_upper` → `thetaPazuki` | b: fibre QM surface A (dim 2) | T4 | keep cited | settle the theta-coordinate (log 4) reading risk |
| gaudronRemondThm14 | `r19_of_leaves` → `transfer_core` (1st half), `reverseIsogeny_of_leaves3` (existence only) | b: (J₁(N)_L, P) | T4 | keep cited | serve reverse existence by `reverseIsogeny (IsogenyQuasiInverse)` |
| neronSchemeModelExistsDVR | r6 (`raynaudCriterion_leaves`), SS1, SS3 (TailZ15:98–116); r8 dead | b: DVRs of number fields | T1 (NF form, from N1 + BLR) / T4 general | reduce | derive from N1 + `blr_1_2_4.mp` (as `neronLocalizesDVR_of_printed`); restate r6 or Raynaud ∃-form |
| blr_1_2_4 (w63) | `neronLocalizesDVR_of_printed` → SemistableLocalGlobal, SS2 | b: `.mp` only, R = 𝓞_L | T2 | prove direction used | spread out affine pieces of Y to 𝓞_L[1/s] with vendor 01ZM/0C0C, extend, glue by uniqueness |
| faltingsLemma5Printed (w63) | `faltingsLemma5_of_printed` → R20 → `transfer_core` | b, one-sided (upper half only) | T4 as is; T2 bypass | reduce/bypass | `GroupModelIsogenyUpper`: integrality of f^*ω plus volume scaling by deg φ (HeightAntitone + torusMetricSq_comap) |
| raynaudKernelBound (w63) | `faltingsLemma5_of_printed` (unused side only) | effectively unused | T1 | prune | make r20 one-sided (`(abs_le.mp hvar).1` is all `transfer_core` uses) |
| sga3_VIB_3_10 (w63) | `idComp_baseChange`, `idCompSubgroup_of`, `identityComponentOLRange_of`, `…DVRRange_of` → SS2 | b: bases Spec 𝓞_L / DVR, connected generic fibre | T2 (DVR T1) / T3 general | specialize + prove | over a DVR, G \ G⁰ = G_s \ G_s⁰ is closed; over 𝓞_L, finitely many bad fibres via spread-out + Zariski |
| sga7_IX_3_3 (w63) | `identityComponentBaseChangeDVRRange_of` → SS2 → identification | b: number-field DVRs, all A in the rows | T4 | keep cited | none (semi-abelian extension theory) |
| egaIV_8_10_5_openImm (w63) | `exists_away_of_dvr` → `openImmersionLocalization` → SS2 | b: Spec O = lim Spec 𝓞_L[1/a] | T1 | prove directly | Mathlib 01Z4 `exists_preimage_eq` + vendor 081E `exists_isIso_baseChange_of_isIso_limitBaseChange` + `baseChangeConeIsLimit` |
| neronLocalizesDVR (in flight) | `semistableLocalGlobal_of10` → SS1, SS3 | b | (→ blr_1_2_4) T2 | superseded | prove "only if" BLR |
| faltingsLemma5BC (in flight) | `r20_of_leaves'` → `transfer_core` | b, one-sided | (→ two w63 leaves) T2 | superseded | as faltingsLemma5Printed |
| semistableNeronBaseChange (in flight) | identification → all six height rows | b (all A in rows) | (→ four w63 leaves) | superseded | EGA (T1) + BLR (T2) now; SGA 3 weakest T2; SGA 7 kept |
| semistableReductionDVR (review) | SS1 (+ dead r8) | b | T4 | (not ranked) | — |
| semistableUnipotent (review) | r6 (+ dead r8) | b | T3/T4 | (not ranked) | — |
| raynaudSemistable (review) | r6 | b | T4 | (not ranked) | ∃-form conclusion frees r6 from the DVR Néron leaf |
| semistablePersistsDVR (review) | SS1, SS3 | b | T3/T4 | (not ranked) | SS3 use vanishes if R20 is bypassed |
| neronSchemeExtensionExists (blocked) | n1 → all rows; t41 → `heightAdditivity_of_h5neron` | a (all AVs over number fields) | T4 (T3 via gluing DVR models) | keep cited | glue local Néron models + spread-out abelian scheme with BLR 1.2/4 "if" |
| r7a (blocked) | `kernelFieldExists_of_split''` → `good_of_QML3` | b: `.2.mpr`, QM surfaces, m = 3^k | T4 | keep cited | — |
