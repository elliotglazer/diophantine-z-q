# gap-triage, group A: Shimura curves and QM abelian surfaces (agent A)

Base e38375b3 (w62). I only read files: no Lean, no lake, no network. Names are in `HDec.HSyn` unless marked `_root_`.

Marks: **VERIFIED-READ** means I opened the file and saw the declaration, and the line is quoted or located.
**SPECULATIVE** means a judgement. **UNVERIFIED** means a theorem number recalled from memory.

## 0. Common facts (apply to every section)

* **The objects are already the construction's own.**
  * `B = QuaternionAlgebra ℚ 2 0 (-3)` (`ZInQKernel/HDecomp/QM/Structures.lean:30`), and `O` is its fixed maximal
    order (`Structures.lean:57`).
  * Every moduli field (`r1r2`, `shimuraFamily`, `gonzalezRotgerCountX6`, `deligneComponentsY3Printed`,
    `x6ConicModel`, `shimuraGoodReductionNoGuard`) is an existential statement about *one* `Y₃`, `X₆` for this `O`
    at level 3. `qmCentralizerCMC` and `shimuraTaniyamaQbar` quantify over all QM surfaces by this `O`.
  * Only `yuThm11` is stated for arbitrary `(a, b)` and an arbitrary algebraically closed field.
* **The bundle chain for these fields:**
  * `sixContactMin_of_open12` (TailZ15:131) → `_open11` (TailZ13:68) → `_open10` (TailZ11:61) → `_open9` (TailZ9:153)
    → `_open8` (TailZ4:259) → `_open7` (TailX:287) → `_open6` (TailO:3011) → `_open4` (TailK:356);
  * then `sixContactMin_of_leavesR3` (TailD:255) and `glueOutputs_of_leaves3` (TailD:200).
  * The real consumers sit in `gluePieces_of_open4` (TailK:291-345), `glue4_of_open6` (TailO:2999),
    `cmDescends_of6` (TailO:~2958) and `glueOutputs_of_leaves3` (TailD:200-246).
* **w63 form (route-a-fold, VERIFIED-READ `git show origin/wip/w63:...`).**
  * Four fields are restated with `R1fpProps ↦ R1fpPropsAb` (TailZ16:145). Their definitions:
    * `R1R2fpRepAb` (TailZ17:66);
    * `ShimuraFamilyAb` (TailZ17:82);
    * `GonzalezRotgerCountX6Ab` (TailZ17:31);
    * `DeligneComponentsY3PrintedAb` (TailZ17:54).
  * There is one new field, `mumfordRigidityCore : LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (TailZ16:463):
    "`∃ _G : GrpObj F, η[F].left = e ∧ (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f)`" for proper smooth geometrically
    connected `F → S` with section `e`, all of whose field fibres are abelian varieties.
  * **Their only consumers:**
    * `researchLeaves10_of_open11` (TailZ17:220-248), which builds `r1r2`, `shimuraFamily` and
      `gonzalezRotgerCountX6` by `(…_iff_ab (mumfordRigidity_of11 r)).mpr`;
    * `addedLeaves9_of_open10` (TailZ17:255-271), which builds `deligneComponentsY3Printed`;
    * pass-throughs in TailZ18:1231 and TailZ19:1859.
  * So the w63 consumers are exactly the w62 consumers below. `MumfordRigidityCore` is used only to convert the four
    fields.
* **`R1pi0Props` is unused (VERIFIED-READ).**
  * `R1R2fp_of_rep` (LPrefix:5228) discards the last clause of `r1r2`:
    `obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h`.
  * Every consumer reads `r1r2` only through `R1R2fp_of_rep`. I grepped every `R1R2fpRep` occurrence. The only other
    readers are TailO's `descend_main` and `cmDescends_of`, which take `hRep` and never destructure it.
* **`R1recProps` is probably unused (SPECULATIVE).** Its only explicit reader is `r1rec_of_rep` (TailZ5:260), which
  feeds the field `r1rec`. That field is not consumed: `r.r1rec` appears only in pass-throughs in TailD:92, TailE,
  TailN, TailX and LPrefix. `residue_unramified_over_branch` has no user in the chain (grep).
  * **Check:** a clause-level dependency scan, i.e. replace the clause by `True` in a copy of `R1R2fpRep` and rebuild.
  * **If confirmed:** the only non-printed leaf of x6-glue's split (`RayClassCM`, which exists only to prove
    `R1recProps`) drops out of `r1r2`.

---

## 1. `r1r2 : HDec.LeafAdopt.R1R2fpRep` (research, TailZ15:24)

1. **Identity.**
   * `def R1R2fpRep` is at `ZInQKernel/OneProof/H/LPrefix.lean:5218`.
   * Row H-1 (r4 split rows: H-137, H-138, H-140, H-141, H-142).
   * leaf-fold10 §2 form: GLUE (comp), a composite of Shimura 1967 MT I-II, Deligne 1971, Baba–Granath 2008 Thm 2.1,
     González–Rotger 2006 Prop. 5.6 and Thm 5.12, and Lemma QP.
   * Statement: `∃ Y Φ X Ψ fY π₆, R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props … ∧ R2X6PropsIff X Ψ π₆ ∧ R1recProps Y Φ ∧
     X6Surj … ∧ R5ptProps X Ψ ∧ R1pi0Props X`.
   * w63: `r1r2Ab : LeafAdopt.R1R2fpRepAb`, the same text over `R1fpPropsAb`.
2. **Use.** Everything goes through `R1R2fp_of_rep`. The consumers:
   * `glueOutputs_of_leaves3` (TailD:209): `exists_fibre_object` (`HDecomp/QM/Leaves.lean:479`) gives a fibre object
     over `J(u)`. It uses `R1fpProps`, `X6Props`, `R2X6Props`, `CMExists` and `X6Surj`.
   * `gluePieces_of_open4` (TailK:297-300): FS5 NoCM via `r1r2fpFull_of` (TailD:534) and
     `fibreComTrivialFull_of_leaves''` (TailC:2288).
     * `nocm_on_witness` (TailC:1371) destructures `R1fpProps`, `X6Props` (forgetful clause), `R2X6Props`
       (fibre = twist class) and `R5ptProps` (residue degree).
     * This happens only at `ℚ̄`-points over `J(u)`, `u ∈ ℚ \ contactSet`.
   * Also in `gluePieces_of_open4`:
     * TailK:316-317: `fibreQMPeriod_main_rep` (TailC:8450) and `periodMapGlue_of_leaves4` (TailK:73), using the own
       triple `ownY/ownΦ/ownπ` (`own_spec`: R1fp, R1hecke, R2fp);
     * TailK:323: `propTSAll_of_pieces3` (TailI:78), for Hecke covers on `Y₃`.
   * `glue4_of_open6` (TailO:2999): `heckeVertWitness_of_leaves5` (TailN:38).
   * `addedLeaves6_of_open7` (TailX:276): `shimuraGoodReduction_of_noGuard`, which uses only `CMObjectsExist`
     (TailL:250), i.e. that `QML3 ℚ̄` is nonempty.
   * Unused clauses: `R1pi0Props` (VERIFIED, §0) and probably `R1recProps` (SPECULATIVE, §0).
   * **Kind of use: (b), at the specific objects.** The statement is already about the one `Y₃`, `X₆` of `O ⊂ (2,−3)`.
     Uses are at arbitrary points of that `Y₃` (Hecke, period map), and at points over rational values `J(u)` (NoCM).
   * **Weakest sufficient statement:** the same text without the last two clauses.

     ```lean
     def R1R2fpUsed : Prop := ∃ Y Φ X Ψ fY π₆, R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧
       R2X6PropsIff X Ψ π₆ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ   -- R1recProps only if the scan finds a reader
     ```

     It is implied by `R1R2fpRep`. It is still deep: the moduli theorem, Baba–Granath, González–Rotger.
3. **Library coverage.**
   * x6-glue (origin/wip/x6-glue, `scratch/x6-glue/parts/X6New.lean`; VERIFIED-READ by grep):
     `theorem r1r2_of_published (hD : ShimuraGlue.DeligneComponentsX6Printed) (hE : GeomConnOfAlgClosure) (hT :
     PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational) (hR : ShimuraGlue.Ray.RayClassCM) (hG :
     GonzalezRotgerX6) : LeafAdopt.R1R2fpRep` (line 60). The report says it compiles.
   * In the base (VERIFIED-READ, TailZ12):
     * `deligneComponentsX6_of_printed (h : DeligneComponentsX6Printed) : HDec.QMSplit.Moduli.DeligneComponentsX6`
       (TailZ12:1372);
     * the double coset `pi0_Kfull_eq_one` (TailZ12:984), so the cloud task "DeligneComponentsX6" is already reduced to
       the printed leaf;
     * `PairsLift` from T5 (shimura-split).
   * w63: `MumfordRigidityCore` and `QMAbScheme` (TailZ16:107), so abelian schemes over a base are now statable.
4. **Missing.** These are research theorems, not missing definitions: the integral PEL moduli theorem on `R1fpPropsAb`,
   Baba–Granath's `π₆`, GR Thm 5.12, and (if `R1recProps` is used) the adelic uniformization of `Y₃` with its moduli
   dictionary (needed for `RayClassCM`).
5. **Tier.** T4.
6. **Strategy.** Keep cited, in x6-glue's split form (6 printed leaves plus `RayClassCM`). First drop `R1pi0Props`, and
   `R1recProps` if the scan confirms.
7. **Notes.**
   * The open human check "specialization of Deligne's PEL model to this functor" is inherited by every field in this
     group that carries `R1fpProps(Ab)`.
   * x6-fold (origin/wip/x6-fold) is at step 0: it merged x6-glue and dumped constants (`scratch/x6-fold/log.md`).
     Nothing is folded yet.

## 2. `shimuraFamily : HDec.QMSplit.Moduli.ShimuraFamily` (research)

1. **Identity.**
   * `def ShimuraFamily` is at `ZInQKernel/OneProof/H/TailU.lean:1952`:
     `∃ Y Φ, R1fpProps Y Φ ∧ ∀ π : ToP1 Y.left, R1bFamily Y Φ π`.
   * Row H-139 (split row H-154 `ShimuraHolFamily`).
   * Form: GLUE (c), Shimura 1967 MT I composed with every algebraic `π` (the composition step is proved:
     shimura-split `holP1_of_isHolFamily`).
   * w63: `shimuraFamilyAb` (TailZ17:82).
2. **Use.**
   * `researchLeaves5_of_open7` (TailX:198): `r1b := QMSplit.Moduli.r1b_of' r.shimuraFamily` (TailU:2273), i.e.
     `r1b_of` plus `r1bTransport_proof`.
   * Then `r.r1b r.r1r2` in `gluePieces_of_open4` (TailK:317) is the `hR` argument of `fibreQMPeriod_main_rep`
     (TailC:8450), giving `thetaPoint`.
   * **Kind of use: (b).** Only `R1bFamily (ownY) (ownΦ) (ownπ)` for the one `π = π₆ ∘ fY` of `r1r2`'s witness.
     * The object clause: the object at `y_τ` is `ℂ²/ι(𝒪)(τ,1)ᵀ` (TailC:7663).
     * Plus continuity and holomorphy of `τ ↦ π(y_τ)`.
   * **Weakest:**

     ```lean
     def ShimuraFamilyUsed : Prop := ∀ h : LeafAdopt.R1R2fpRep,
       G0Split.FibreQM.R1bFamily (ownY (R1R2fp_of_rep h)) (ownΦ (R1R2fp_of_rep h)) (ownπ (R1R2fp_of_rep h))
     ```

     This is `r1b_of'`'s conclusion, the old field `r1b`. It is implied via `R1bTransport` (proved). It is still deep:
     holomorphy of the period map is Shimura MT I, and the existence of algebraic `ℂ²/Λ_τ` needs Riemann's theorem.
     The pointwise choice of `y_τ` would be easy given `Φ_ℂ`, but holomorphy is the content.
3. **Library coverage.**
   * shimura-cft (origin/wip/shimura-cft, `scratch/shimura-cft/ShimuraCFT.lean`; VERIFIED-READ by grep):
     * `def ShimuraMainThmIDeligneY3Ab` (l.1102), `def ShimuraDeligneBody` (l.1062);
     * `theorem shimuraFamilyAb_of_mainThmI` (l.1121), `theorem shimuraFamily_of_mainThmIAb` (l.1144).
   * The report says Parts A/B compile and Part C/D (`exists_artinCondC`, non-vacuity) is not compiled, blocked on a
     build tree (log Step 4).
   * Holomorphy notion: shimura-split `IsHolFamily` and `holP1_of_isHolFamily` (proved, per the report).
4. **Missing.** Analytification of `Y₃` and its universal family, Riemann's algebraization of polarized tori, and
   holomorphic dependence of the moduli point. None of these is in Mathlib.
5. **Tier.** T4.
6. **Strategy.** Keep cited. Replace the field by shimura-cft's `ShimuraMainThmIDeligneY3Ab` (a stronger printed leaf,
   which also yields c-to-printed's `ShimuraMainThmIY3`) only if the same leaf also serves other fields.
7. **Notes.**
   * The stated `∀ π` is more than is used (one `π`), but the transport makes the two equivalent, so there is no gain.
   * Possible synergy: clause 4 (reciprocity at CM points) of shimura-cft's leaf could also prove `R1recProps` and
     `RayClassCM`, if they are used (SPECULATIVE).

## 3. `gonzalezRotgerCountX6 : _root_.ShimuraSplit.GonzalezRotgerCountX6` (research)

1. **Identity.**
   * `def GonzalezRotgerCountX6` is at `ZInQKernel/OneProof/H/TailZ8.lean:44`: some witness `(Y, Φ, X, Ψ, fY)` with
     `R1fpProps`, `X6Props` and, for every imaginary quadratic `k` and every order `R` of conductor prime to 6 that
     occurs, `Nat.card {x : X(ℚ̄) | CM by R} = 2 ^ inertCount6 k * Nat.card (CommRing.Pic R)`.
   * Row H-145.
   * Form: leaf-fold10 has LEAF (published form, specialization of GR 2006 Prop. 5.6 at `(D,N) = (6,1)`). The r5 /
     fork ruling has GLUE (composite).
   * w63: `gonzalezRotgerCountX6Ab` (TailZ17:31).
2. **Use.**
   * `researchLeaves8_of_open9` (TailZ9:102): `r5count := r5fpCount_of_points r.gonzalezRotgerCountX6` (TailZ8:57).
   * `r.r5count` goes to `gluePieces_of_open4` (TailK:300), then `fibreComTrivialFull_of_leaves''` (TailC:2288), then
     `nocm_on_witness` (TailC:1371). The only read is `hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩` (TailC:1403).
   * **Kind of use: (b).**
     * It is used for one order `R`: the CM order of a QM pair at a point `x` of `X₆` over `J(u)`, where `ℚ(x) = ℚ(i)`
       has degree 2.
     * The proof forces `2^{b(k)}·#Pic R = 2`: either `b = 0` and `h(R) = 2`, or `b = 1`, `k ≅ ℚ(i)` and `h(R) = 1`.
     * It then contradicts the four distinct fibre points (TailC:1404-1445).
     * Only the upper bound `#CM(R) ≤ 2` is needed (`≤ 3` would do).
   * **Weakest:**

     ```lean
     def GonzalezRotgerCountX6Used : Prop := ∃ Y Φ X Ψ fY, R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧
       ∀ (k) [Field k] [NumberField k] [IsTotallyComplex k], finrank ℚ k = 2 → ∀ R : Subring k,
         R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
         2 ^ inertCount6 k * Nat.card (CommRing.Pic R) = 2 →
         Nat.card {x : fieldPt Qbar ⟶ X // ∃ P, Ψ x = ⟦P⟧ ∧ Nonempty (com P.q ≃+* R)} ≤ 3
     ```

     NoCM also has to be retouched: from `hcard2 = 2` to `≤ 3`, with a finiteness side condition.
   * **This is a computation plus classical theorems (SPECULATIVE):**
     * The orders with conductor prime to 6 that embed optimally in `O` and have `2^b h = 2` should be `ℤ[i]` and
       `ℤ[√−6]`.
       * For `b = 1`, `h(R) = 1`: class number formula for orders in `ℚ(i)`.
       * For `b = 0`: 2 and 3 are not inert, and cannot split (no optimal embedding into the division algebra at 2, 3).
         So both ramify, `24 | disc k`, and genus theory forces `t = 2`, i.e. `k = ℚ(√−6)` and `R = ℤ[√−6]`.
     * Then `CM(ℤ[i]) = π₆⁻¹(0)` and `CM(ℤ[√−6]) = π₆⁻¹(−16/27)`. This uses `R2X6PropsIff` (CM ↔ value), plus the
       fact that `HasCM4` forces `com = ℤ[i]` because `ℤ[i]` is maximal; `ℤ[√−6]` is also maximal.
     * Each fibre has 2 points on the conic (`x6ConicModel`: fixed points of `X ↦ −X` and `Y ↦ −Y`).
4. **Library coverage.**
   * Mathlib has `CommRing.Pic` (used in the statement).
   * No class number formula for orders and no genus theory found (SPECULATIVE, not searched exhaustively).
   * The kernel has `cmConductorCoprime6_of` (TailC:~2276, VERIFIED-READ), `not_dvd_conductor_of_optimal`, and
     `two_not_prime_of_sqrt_neg_one` (TailC, VERIFIED-READ).
5. **Missing (specialized route), in order:**
   * (i) `#Pic(R) = h_k·f·∏(1 − (d/p)/p)/[𝒪_k^× : R^×]` for orders, or direct non-principal ideals;
   * (ii) genus theory: `2^{t−1} | h_k`;
   * (iii) the fibre-size computation on the conic, together with `R2X6PropsIff`.
6. **Tier.** T3 for the specialized route; T4 for the printed count.
7. **Strategy.** Specialize and compute, or keep cited. The specialized form is a real reduction, from "all orders" to
   two maximal orders plus classical class-number facts, but it needs class-group infrastructure.

## 4. `deligneComponentsY3Printed : _root_.ShimuraGlue.DeligneComponentsY3Printed` (added, TailZ13)

1. **Identity.**
   * `def DeligneComponentsY3Printed` is at `ZInQKernel/OneProof/H/TailZ12.lean:1324`:
     `∃ Y Φ, R1fpProps Y Φ ∧ DelignePi0 Y K3`, where `DelignePi0` (TailZ12:~1296) is a Galois-equivariant
     `π₀(Y_ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd(K₃)` with the cyclotomic idele.
   * No r5 row; it was added by leaf-fold10 and replaces H-59 `y3Connected` and H-155 `DeligneComponentsY3`.
   * Form: LEAF (published form, specialization); strict GLUE under the fork ruling.
   * w63: `deligneComponentsY3PrintedAb` (TailZ17:54).
2. **Use.**
   * `addedLeaves8_of_open9` (TailZ13:55-56): `y3Connected := y3Connected_of_deligne (deligneComponentsY3_of_printed …)`.
     These are proved at TailZ12:1207 and 1346. The double coset `pi0K3Equiv : Pi0 K3 ≃* (ZMod 3)ˣ` (TailZ12:995) is
     proved.
   * `l.y3Connected` goes to `propTSAll_of_pieces3` (TailK:323, TailI:78) as `hconn`, then
     `coverModelOfHecke_of_heckeRest`, then `heckeNormalization_of` / `heckeIrreducible_of_connected` (TailG:8753).
   * **Kind of use: (b).** The only fact used is that `Y₃` is connected **over ℚ**, for one fine witness:
     `TSHecke.Y3Connected` (TailG:8352) = `∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`. Transport to every witness
     is proved (`connectedSpace_of_R1fp`).
   * **Weakest:** `TSHecke.Y3Connected` (or its Ab form). It is implied, and it is much weaker than the `π₀` display
     with Galois action, but it is still arithmetic: the two geometric components must be swapped by
     `Gal(ℚ(√−3)/ℚ)`, a reciprocity statement on `π₀`.
3. **Library coverage (all VERIFIED-READ in TailZ12):**
   * `nrd_K3_le` (l.470), `U3_le` (l.624), `chi_ker` (l.958), `pi0K3Equiv` (l.995);
   * `y3Connected_of_deligne` (the orbit computation);
   * Mathlib objects: `FiniteAdeleRing`, `QuaternionAlgebra`, `cyclotomicCharacter`, `ConnectedComponents`.
4. **Missing.** Deligne's theorem itself (canonical models, the `π₀` of Shimura varieties with the Galois action).
   * Alternative (SPECULATIVE): a Weil-pairing invariant `Y(ℚ̄) → μ₃^prim` that is locally constant and
     Galois-equivariant would give connectedness directly. It needs polarizations of QM surfaces, which are not in
     the tree.
5. **Tier.** T4.
6. **Strategy.** Keep cited.
   * Option: restate the field as the weaker `Y3Connected(Ab)` (consequence of Deligne, GLUE (c)). That is a count
     question, not a proof gain.
   * Option (SPECULATIVE): restructure `heckeIrreducible_of_connected` to work per connected component, which would
     remove the need.
7. **Notes.** shimura-cft's `ShimuraMainThmIDeligneY3Ab` clauses 1 and 4 give `π₀` and its Galois action. If that leaf
   enters the bundle for `shimuraFamily`, this field could be derived from it (SPECULATIVE; not compiled).

## 5. `x6ConicModel : X6Kummer.X6ConicModel` (added)

1. **Identity.**
   * `def X6ConicModel` is at `ZInQKernel/OneProof/H/TailE.lean:901`:
     `∃ Y Φ X Ψ fY π₆, R1R2fpFullProps … ∧ ConicModel X π₆`, a Galois-equivariant `X(ℚ̄) ≃ C(ℚ̄)` for
     `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X²+Z²)/(27Z²)`.
   * Row H-43 (r4 H-143; split H-153 `ElkiesConicX6`).
   * Form: GLUE (c), Kurihara 1979 and Elkies 1998 §3.
2. **Use.**
   * `gluePieces_of_open4` (TailK:299): `X6Kummer.x6KummerFibre_of_conic hMob l.x6ConicModel` (TailE:993), then
     `X6KummerFibre` (TailC:1258), then `fibreComTrivialFull_of_leaves''`, then `nocm_on_witness` (TailC:1386-1395).
   * **Kind of use: (b).** It is used only at `j₀ = J(u)`, `u ∈ ℚ \ contactSet`, for:
     * (i) `residueImage x = ℚ(a, b)`, which with the Elkies identities `elkies_sq` (TailC:~1340) becomes `ℚ(i)`, of
       degree 2;
     * (ii) four distinct `ℚ̄`-points over `J(u)`.
   * **Weakest:** `X6KummerFibre` restricted to `j₀ ∈ Jmap '' (ℚ \ contactSet)`. Equivalently:

     ```lean
     ∀ witness …, ∀ u ∉ contactSet, ∀ x : fieldPt Qbar ⟶ X, π₆(x) = J(u) →
       residueImage x = IntermediateField.adjoin ℚ {i}          -- (i), with i² = −1
     ∧ ∃ f : Fin 4 ↪ X(ℚ̄), ∀ j, π₆ (f j) = J(u)                 -- (ii)
     ```

     * (ii) should follow from `r1r2` plus `ALFixedPoints`: the four twists `P^{rep m}` are pairwise non-isomorphic
       unless `P` is CM, and CM happens only at `π₆ ∈ {0, ∞, −16/27}` (SPECULATIVE, T1-T2).
     * (i) is the genuine content of Elkies' function field `ℚ(t)(√−t, √(3(t−1)))`. It is not a finite computation
       because `u` ranges over `ℚ`.
3. **Library coverage.**
   * x6-glue (VERIFIED-READ by grep, `scratch/x6-glue/parts/X6New.lean`):
     * `def ElkiesEquationsX6` (l.28), a printed scheme-charts leaf;
     * `theorem x6ConicModel_of_published` (l.68);
     * `X6Glue.conicModelT_of_charts`, plus generic `ev_injective`, `ev_surjective` and `ev_comp` lemmas (points of
       affine opens correspond to ring homs).
   * The report says these compile: 0 errors and 82 standard axiom lines. They are not folded.
4. **Missing.**
   * For the printed route: Elkies' theorem.
   * For a proof: the Kummer theory of the `(ℤ/2)²`-cover `X₆ → P¹` over the function field of the witness, plus the
     moduli meaning of `W`. Neither is in the tree (shimura-split §3.6).
5. **Tier.** T4 (printed); T3 (proof).
6. **Strategy.** Keep cited as `ElkiesEquationsX6` (x6-glue). Optionally prove (ii) from existing leaves and keep only
   (i).
7. **Notes.** In flight: x6-fold will fold x6-glue (`r1r2`, `x6ConicModel` from 7 leaves; the counts are in x6-glue
   §4). The fibre clause of `ElkiesEquationsX6` is still a composite (x6-glue §5.2).

## 6. `shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard` (added)

1. **Identity.**
   * `def ShimuraGoodReductionNoGuard` is at `ZInQKernel/OneProof/H/TailW.lean:739`:
     `∀ p [Fact p.Prime], 324 < p → ∃ 𝒴 𝒜, IsShimuraModelNoGuard p 𝒴 𝒜`.
     This is a smooth proper `𝒴/ℤ_(p)` with a `QMFamily` and fibre, `ℚ̄`-moduli and Hecke clauses (TailW:717).
   * Row H-119.
   * Form: GLUE (comp), from Kottwitz 1992, Buzzard 1997, Morita 1981 and Carayol 1986; not statable in printed form
     at w62.
2. **Use.**
   * `addedLeaves6_of_open7` (TailX:276-277): `shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) l.…`
     (TailW:743).
   * Then `glue4_of_open6` (TailO:2999-3002): `heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 …` (TailN:38),
     which gives `HeckeVertWitness` (TailG:10216).
   * Then `propTSAll_of_pieces3 … hV` (TailK:323-325), which gives `heckeNoVertRam_of_witness` (TailG:~10232).
   * **Kind of use: (b).** It is used for `Y₃` only, at every prime `p > 324` (infinitely many). The only conclusion
     used: for the Galois function-field cover `E/ℚ(t)` attached to `(Y₃, π)` and each `p > 324`, some prime over
     `pℤ[X]` has `e = 1` (`VertUnramWitness E p`).
   * **Weakest:** `HeckeVertWitness` (glue), or `HeckeNoVertRam` (TailG:3963) directly. That is a statement about
     vertical ramification of an explicit cover, and is implied (via `heckeVertWitness_of_curveBijIso`).
   * Alternative route NV (Lemma NV, h-b1 §3; TailG:3960 docstring): tameness (`deg E < p`), unramified branch fibres,
     Abhyankar at `(p, X − b)`, the `W`-quotient.
     * The `X₆ → P¹` part is explicit from the conic.
     * The `Y₃ → X₆` part needs control of the level-3 cover mod `p`.
     * Still deep (SPECULATIVE T3).
3. **Library coverage.**
   * w63 `QMAbScheme` (TailZ16:107) now gives items 1-3 of curve-split §3.6 (abelian schemes with `𝒪`-action and level
     3 over a base).
   * Item 4 (polarizations over `S`) and item 5 (representability) are still absent.
   * `ZInQ.SmoothFibre.*` and `Contrib/SmoothFibre` give the special-fibre DVR facts used by model-glue (per memory
     notes; not re-read).
4. **Missing.** An Ab-form statement over `ℤ_(p)` (a `QMAbScheme` over `𝒴` with the universal property over
   `ℤ_(p)`-schemes, so that Yoneda yields the Hecke clauses), and the integral moduli theorem itself.
5. **Tier.** T4.
6. **Strategy.** Keep cited. Restating it in an Ab form over `ℤ_(p)` with `QMAbScheme` would make it "printed form"
   (a count gain, not a proof).
7. **Notes.** No `origin/work/cloud-*` branch for this statement exists: the six cloud branches are w01, w02, w03, w06,
   w07, w08. So the cloud worker's result is not visible.

## 7. `shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (added)

1. **Identity.**
   * `def ShimuraTaniyamaQbar` is at `ZInQKernel/OneProof/H/TailU.lean:1603`: an `A/ℂ` of dimension 2 with an
     injective `E →ₐ[ℚ] End0 A`, `[E:ℚ] = 4`, is `≅ A₀ ×_{ℚ̄,ιe} ℂ`.
   * Row H-130.
   * Form: LEAF (published form, specialization), from Shimura–Taniyama 1961 §12.4 and Milne CM §7 (UNVERIFIED
     numbers).
2. **Use.**
   * `addedLeaves6_of_open7` (TailX:271): `stQM := stQM_lf7 l.shimuraTaniyamaQbar` (TailX:61), which is `stqm_of`
     (TailU:1727).
   * Then `cmDescends_of6` (TailO:~2958), then `LeafQCheck.cmDescends_of` (TailO:1302) / `descend_main` (TailO:1177),
     which gives `CMDescends` (TailJ:1426).
   * Then `periodMapGlue_of_leaves4 … hD` (TailK:73, via `piCMC_of`), giving `thetaPoint`.
   * **Which surfaces (VERIFIED-READ `stqm_of`):** only `A = Q.A` for `Q : QML3 ℂ` with `HasCM4`, `HasCM3` or
     `HasCM24`, i.e. QM by `O` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`. In those cases
     `E = E_d = ℚ(√2)(√d)`, `d ∈ {−1, −3, −6}` (`Ed`, `embed_Ed`).
   * Up to isomorphism of QM pairs these are 2 + 2 + 2 points of `X₆` (Eichler/GR count, R2 fibres).
   * **Weakest:** the old row `LeafQCheck.STQM` (TailU:1589):

     ```lean
     def STQM : Prop := ∀ (A : AbVar ℂ) (q : QMStr A), A.dim = 2 → (HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) →
       ∃ ιe A₀ e e', e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _
     ```

     It is implied, and only six isomorphism classes are concerned. Equivalently, `CMDescends` (TailJ:1426) itself,
     which is what the consumer reads.
3. **Library coverage.**
   * `descend_main` already handles endomorphisms and level structure given `STQM`, `T11b_Rigidity` and
     `TorsionDescends` (TailO:977).
   * `T11b_Rigidity` (`HDecomp/LeafPush2/T.lean:56`, VERIFIED-READ) is a textbook field.
   * No CM theory of abelian varieties and no algebraicity of `j(τ)` at CM `τ` in Mathlib (SPECULATIVE).
4. **Missing / attack ideas (all SPECULATIVE).**
   * (a) **Fixed points.** If `HasCM4 Q ⟹ Q ≅ Q.twist(rep 1)` over `ℂ` (the converse of `ALFixedPoints`), then the
     CM `ℂ`-points of `Y₃` lie in the fixed locus of a nontrivial automorphism of the curve `Y₃` over `ℚ`
     (`R1heckeProps`).
     * That locus is a finite `ℚ`-scheme, so its `ℂ`-points are `ℚ̄`-points.
     * `R1fpProps` naturality plus `T11b` then give `CMDescends` without Shimura–Taniyama.
     * Risk: the converse needs an explicit automorphism such as `ι(i)(1+φ)/2`, whose integrality is not checked.
     * It also needs nontriviality of the automorphism on each component, and the level structure on `Y₃`.
   * (b) **Explicit models.** `A ≅ E × E'` with `E` CM by `ℤ[√d]`, with explicit `ℚ̄`-equations
     (`j = 1728`, `0`, `2417472 ± 1707264√2`; UNVERIFIED). This needs the structure theorem for `End⁰ = M₂(k)`
     surfaces (Shioda–Mitani). Large.
5. **Tier.** T3. Route (a) may be T2 if the converse of `ALFixedPoints` holds.
6. **Strategy.** Specialize: replace the field by `STQM`/`CMDescends` (six objects) and try route (a). Otherwise keep
   cited.
7. **Notes.** x6-glue §5.1 records that `ShimuraTaniyamaQbar` gives no Galois action, so it does not help
   `RayClassCM`.

## 8. `qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC` (added)

1. **Identity.**
   * `def QMCentralizerCMC` is at `ZInQKernel/OneProof/H/TailU.lean:1484`: for `A/ℂ`, `dim 2`, `q : QMStr A`,
     `com q ≃+* ℤ ∨ ∃ k imaginary quadratic, ∃ Φ : k →ₐ[ℚ] B, com q ≃+* O.comap Φ`.
   * Row H-129.
   * Form: LEAF (published form), from Shimura 1967 §§1-3, Jordan 1981 §3 and GR 2006 §5.
2. **Use.**
   * `qmRows_of7` (TailX:251-252): `rows_of_C l.qmCentralizerCMC (t11b_of_exists5 t.t11bExists)` (TailU:1526),
     using `qmCentralizerCM_of` (TailU:~1495, transfer `ℚ̄ → ℂ` by T11b).
   * It yields three rows:
     * `QMAutCard` (TailG:9459) and `ALFixedPoints` (TailG:9485), consumed by `propTSAll_of_pieces3` (TailK:323), for
       the Hecke cover of `Y₃`, at all its `ℚ̄`-points;
     * `CMOptimalEmbedding` (TailC:2270), consumed by `fibreComTrivialFull_of_leaves''` (TailK:299), then
       `cmConductorCoprime6_of`, then `nocm_on_witness` `hB`, at the QM pair over `J(u)`.
   * **Which surfaces:** QM surfaces by the fixed `O` over `ℚ̄` (via `ℂ`). Through `X6Surj`, all QM pairs occur as
     fibres, so in effect this is (a), full generality for this `O`, including CM by every order.
   * **Weakest:** the field as stated (or the `ℚ̄` form `QMCentralizerCM`, TailU:977).
3. **Library coverage (VERIFIED-READ):**
   * `qmComplexUnif_of_textbook (hE : UniformizationExistsT35) (hR : T11aRiemannEnd) (hL : QMLatticeAlgebra) :
     QMComplexUnif` (TailC:7944): every `Q : QML3 ℂ` is `ι`-compatibly `ℂ²/ι(𝒪)(τ,1)ᵀ`.
   * `qmLatticeFree_of (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne)` (TailC:8207).
   * `theorem qmSkolemNoetherC_proof : QMSkolemNoetherC` (TailC:8076).
   * `theorem qmClassNumberOne_proof : …QMClassNumberOne` (TailU:260).
   * `cmFixedHasCM_of (hR : T11aRiemannEnd) : CMFixedHasCM` (TailJ:1270), the reverse direction "fixed by elliptic
     `x` ⟹ CM".
   * `HomLatticeCorr` (`Contrib/HomUnify/Corr.lean:84`) and `t11a_riemannEnd_of_corr`.
   * Textbook fields feeding these: `uniformizationLeafAll` (H-103), `gagaMorphism` (H-105),
     `mumfordTorsionAlgClosed`.
4. **Missing (a lattice proof), in order:**
   * (1) a `QMStr` version of `qmComplexUnif_of_textbook`. The proof reads only `Q.A`, `Q.surface` and `Q.q.iota`.
   * (2) The commutant of `{qmMat a}` in `M₂(ℂ)` is `ℂ`: `qmMat i`, `qmMat j` generate `M₂(ℂ)`, an explicit matrix
     computation.
   * (3) Via `T11aRiemannEnd`: `com q ≅ {λ ∈ ℂ : λΛ_τ ⊆ Λ_τ} ≅ {x ∈ O : ι(x)v_τ ∈ ℂv_τ}`.
   * (4) `C(τ) = {x ∈ B : ι(x)v_τ ∈ ℂv_τ}` is a commutative subfield (its eigenvalue map to `ℂ` is injective).
     * Either `C(τ) = ℚ`, or `C(τ) = ℚ(x)` with `x ∉ ℚ`: the centralizer of a noncentral element of a quaternion
       division algebra is `ℚ(x)`.
     * `ℚ(x)` is imaginary quadratic because `v_τ` is not a real multiple, so the eigenvalue is not real.
   * (5) `com q ≅ O ∩ C(τ) = O.comap Φ`.
   * Everything is finite linear algebra over in-tree theorems.
5. **Tier.** T2 (perhaps T1 for an experienced agent).
6. **Strategy.** Prove directly, from the textbook fields plus the proved lattice theorems (it becomes a theorem, and
   the field disappears).
7. **Notes.**
   * The result is used for all QM surfaces by `O`, so there is no specialization gain. The gain is proof, not
     narrowing.
   * The same lattice set-up also serves `yuThm11` (§9).

## 9. `yuThm11 : QMSplit.Yu.YuThm11` (textbook, TailZ11)

1. **Identity.**
   * `def YuThm11` is at `ZInQKernel/OneProof/H/TailU.lean:443`: for `k` algebraically closed of characteristic 0, `A`
     of dimension 2, and `(a, b)` indefinite division with `ℍ[ℚ,a,b] →ₐ End0 A`, `End0 A ≅ ℍ[ℚ,a,b]` or
     `End0 A ≅ M₂(ℚ(√d))`, `d < 0`, with `ℚ(√d)` splitting `B`.
   * Row H-128.
   * Form: LEAF (published form), Yu 2013 Thm 1.1 with case labels dropped.
2. **Use.**
   * `textbookLeaves6_of_open7` (TailX:237): `t27 := qmDichotomyYu_of_yu t.yuThm11`. This **drops the splitting
     clause** (TailU:~460, VERIFIED-READ).
   * `t.t27` is used in `gluePieces_of_open4` (TailK):
     * FS5 NoCM (TailK:299): `comIntOrQuadOrder_of_leaves` (TailC:2064), via
       `PkgI3.qmDichotomy_B6 t27 Qbar P.A …` (TailC:1700);
     * `kernelFieldExists_of_split''` (TailK:~327);
     * `linkedTateLocal_of_leaves3 … t.t27` (TailK:~342), which gives `qmEndRank_of` (TailF:4058) with
       `hT27 Ω A'' hdimA'' 2 (-3) …` at `Ω = AlgebraicClosure L'`, `L' : IF` a number field inside `ℚ̄` (TailF:4082,
       TailF:2426).
   * Also `TailC:6827` and `TailA:1158` (FibreSimple chain), via `qmDichotomy_B6 t27 Qbar …`.
   * **Which objects (VERIFIED-READ):**
     * always `(a, b) = (2, −3)`, via `qmDichotomy_B6` (`HDecomp/Objects.lean:497`) or explicit `2 (-3)`;
     * `k` is `ℚ̄` or `AlgebraicClosure L'`, so algebraic over `ℚ`;
     * `A` carries an injective `O →+* End A`;
     * the splitting clause is never used.
   * **Weakest:**

     ```lean
     def YuB6Alg : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
       (A : AbVar k), A.dim = 2 → ∀ φ : O →+* AbVar.End A, Function.Injective φ →
       Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) ∨ ∃ d : ℚ, d < 0 ∧
         Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (X ^ 2 - C d)))
     ```

     It is implied by Yu (or by Shimura's classical char-0 result). It is still a theorem, but one with an in-tree
     route.
3. **Library coverage.**
   * The lattice set-up of §8 (VERIFIED-READ as listed there).
   * `T11b_Rigidity` (`LeafPush2/T.lean:56`) transports between `k` and `ℂ`, since `k` algebraic over `ℚ` embeds in
     `ℂ` (`IsAlgClosed.lift`).
   * Kernel glue `QMSplitCaseRank` (TailF:~4047) and FS4's `centralizerOfMatrixEnd0_of_homFree` (named in TailC
     docstrings; not opened).
   * Mathlib `Algebra/Azumaya/Basic.lean` has `AlgHom.mulLeftRight_bij [IsAzumaya R A]` and `tensorEquivEnd`
     (VERIFIED-READ names). Whether a quaternion division algebra is `IsAzumaya` in Mathlib is SPECULATIVE.
4. **Missing (lattice proof), in order:**
   * (1) `End⁰(A_ℂ) = {M ∈ End_ℚ(Λ_ℚ) : M_ℝ ℂ-linear}` from `HomLatticeCorr`, with `Λ = O·v_τ` (§8 step 1).
   * (2) `com⁰ = C(τ) ∈ {ℚ, imaginary quadratic k}` (§8 steps 2-4). Real quadratic is excluded because
     `M₂(ℝ)×M₂(ℝ) ↪ M₂(ℂ)` is impossible.
   * (3) `End⁰ = ι(B)·com⁰`, by the double centralizer, or via `End_ℚ(B) ≅ B ⊗ B^op`.
   * (4) `B ⊗ k ≅ M₂(k)` explicitly for `k ⊂ B^op ≅ B`. Splitting for a maximal subfield, possibly via t-skolem-kw's
     CSA work (memory notes; not re-read).
   * (5) Transport to `k ≅` a subfield of `ℂ` by `T11b`.
5. **Tier.** T2.
6. **Strategy.** Specialize to `YuB6Alg`, then prove it by the lattice route, together with §8 (shared steps 1-2).
7. **Notes.**
   * The consumers only need either "`com` is `ℤ` or an imaginary-quadratic order" (which `QMCentralizerCM` already
     gives) or `rank End = 4` / the split-case analysis.
   * A consumer-side refactor could replace `t27` in NoCM and FibreSimple by `QMCentralizerCM`, leaving Yu only in
     `qmEndRank_of` (SPECULATIVE).

---

## Summary table

| field | consumers (file:line) | use (a/b) | tier | strategy | best attack idea (one line) |
|---|---|---|---|---|---|
| `r1r2` (w63 `r1r2Ab`) | TailD:209 `glueOutputs_of_leaves3`; TailK:297-325 (NoCM, period map, propTS); TailO:3001 `heckeVertWitness_of_leaves5`; TailX:276 | b (one `Y₃`, `X₆`; points over `J(u)` and all of `Y₃`) | T4 | keep cited (x6-glue split) | drop the unused `R1pi0Props` (VERIFIED) and probably `R1recProps` (scan), which removes `RayClassCM` from x6-glue's split |
| `shimuraFamily` (w63 `shimuraFamilyAb`) | TailX:198 `r1b_of'` → TailK:317 `fibreQMPeriod_main_rep` | b (own `π` only) | T4 | keep cited | shimura-cft's `ShimuraMainThmIDeligneY3Ab` (Deligne-form MT I with reciprocity), shared with `Y3`/`R1rec` uses |
| `gonzalezRotgerCountX6` (w63 `…Ab`) | TailZ9:102 → TailK:300 → TailC:1403 `nocm_on_witness` | b (orders with `2^b·h(R) = 2`; upper bound only) | T3 (spec.) / T4 | specialize and compute | genus theory plus the class number formula force `R ∈ {ℤ[i], ℤ[√−6]}`; then 2 points each = the conic fibres over 0 and −16/27 |
| `deligneComponentsY3Printed` (w63 `…Ab`) | TailZ13:55 → TailK:323 `propTSAll_of_pieces3` (`hconn`) → TailG:8753 | b (only "`Y₃` connected over ℚ") | T4 | keep cited | weaken to `Y3Connected`; or derive from shimura-cft's leaf (clauses 1, 4) if adopted |
| `x6ConicModel` | TailK:299 `x6KummerFibre_of_conic` → TailC:1386 | b (fibres over `J(u)`, `u ∈ ℚ`) | T4 (T3 proof) | keep cited (x6-glue's `ElkiesEquationsX6`) | prove the "4 distinct points" half from `r1r2` + `ALFixedPoints`; keep only the residue field `ℚ(i)` half |
| `shimuraGoodReductionNoGuard` | TailX:277 → TailO:3001 → TailG:10216 `HeckeVertWitness` → TailK:325 | b (`Y₃`, every `p > 324`) | T4 | keep cited | restate on w63 `QMAbScheme` for printed form; route NV (Abhyankar, explicit conic) as a T3 alternative |
| `shimuraTaniyamaQbar` | TailX:271 `stQM_lf7` → TailO:1302 `cmDescends_of` → TailK:317 `periodMapGlue_of_leaves4` | b (QM surfaces with CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`: 6 classes; `E = ℚ(√2, √d)`) | T3 | specialize | CM `ℂ`-points are fixed points of an AL automorphism of `Y₃`, hence `ℚ̄`-points (needs the converse of `ALFixedPoints`) |
| `qmCentralizerCMC` | TailX:252 `rows_of_C` → `QMAutCard`/`ALFixedPoints` (TailK:323), `CMOptimalEmbedding` (TailK:299) | a (all QM surfaces by `O`) | T2 | prove directly | `Λ = O·v_τ` (proved `qmComplexUnif_of_textbook`), commutant of `ι(O)` = scalars, so `com = O ∩ C(τ)` |
| `yuThm11` | TailX:237 → `t27`: TailC:1700 (NoCM), TailK `kernelFieldExists`, TailF:4082 `qmEndRank_of` | b (`(a,b) = (2,−3)`, `k` algebraic over ℚ, splitting clause unused) | T2 | specialize, then prove | same lattice route as `qmCentralizerCMC`, plus the double centralizer `End⁰ = B·com⁰`, `B⊗k ≅ M₂(k)`, transport by T11b |

In flight (recorded, not planned for):
* **route A:** r1univ-rigid, folded by route-a-fold into w63.
* **x6-glue:** `r1r2` and `x6ConicModel` from 7 leaves. It compiles; `RayClassCM` is the remaining consequence.
* **x6-fold:** step 0 only.
* **shimura-cft:** MT I leaf; Part C/D not compiled.
* **Cloud workers** (`ShimuraGoodReductionNoGuard`, `DeligneComponentsX6`): no branch on origin. `DeligneComponentsX6`
  is already a theorem from `DeligneComponentsX6Printed` (TailZ12:1372).
