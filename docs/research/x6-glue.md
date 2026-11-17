# x6-glue: `r1r2` and `x6ConicModel` from published-form leaves; Elkies' equations as a scheme statement

Task x6-glue, 2026-11-14. Base e38375b3 (wip/w62). Lean: `scratch/x6-glue/` (results log `log.md`).
No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model work, no human
review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number, locator or display recalled without a
source (there is no network on this host).

## 1. Main result

**Both `X₆` fields are theorems from seven leaves.** Six of the leaves are in published form (printed, or a
weakened textbook statement). One is a consequence of a printed theorem: `RayClassCM`, Shimura reciprocity in
ray-class form. VERIFIED: compiled, standard axioms (`scratch/x6-glue/X6Glue.lean`, 0 errors, 82
`#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`).

```lean
theorem HDec.QMSplit.Moduli.r1r2_of_published (hD : ShimuraGlue.DeligneComponentsX6Printed)
    (hE : GeomConnOfAlgClosure) (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRep

theorem HDec.QMSplit.Moduli.x6ConicModel_of_published (hD …) (hE …) (hT …) (hB …) (hR …) (hG …)
    (hC : ElkiesEquationsX6) : X6Kummer.X6ConicModel

theorem HDec.QMSplit.Moduli.x6Rows_of_leaves (L : X6Leaves) : LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel
```

`X6Leaves` is the structure with these seven fields. `rows_of_shimuraGlueLeaves4` gives shimura-glue's six rows
(`r1r2`, `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel`) from `ShimuraGlueLeaves4`, which is
`ShimuraGlueLeaves3` with `ElkiesEquationsX6` in place of `ElkiesConicT`.

**What this task adds:**

1. **Elkies' leaf in equations form** (new, §3). `ElkiesEquationsX6` replaces shimura-glue's `ElkiesConicT`.
   * The old leaf asserted the conic model only on `ℚ̄`-points (`ConicModelT`: a Galois-equivariant bijection
     `X₆(ℚ̄) ≃ C(ℚ̄)`). That was the reason it counted as a consequence.
   * The new leaf asserts the model as a statement about the scheme: `ElkiesCharts X t`.
     * Over `t ≠ ∞`, `X₆` is the affine curve `s² = −t, r² = 3(t − 1)`. That is, `t.U` is affine and
       `Γ(t.U) ≅ ℚ[t,s,r]/(s² + t, r² − 3(t − 1))` with `t ↦ t.f`.
     * Over `t ≠ 0` the chart is the same, with `a = 1/s`, `b = r/s`, `u = 1/t`.
     * On the overlap the charts are glued by `s·a = 1`, `r·a = b`.
   * In other words, `X₆ = X*(6)(√−t, √(3(t − 1)))` over the `t`-line.
   * **Glue (proved):** `X6Glue.conicModelT_of_charts : ElkiesCharts X t → ConicModelT X t`. It rests on new
     Mathlib-level lemmas: the `K`-points of a scheme lying in an affine open `U` are in bijection with the
     ring homs `Γ(U) → K` (`ev_injective`, `ev_surjective`), and evaluation is natural in `K`.
2. **The Deligne leaf for `X₆` and its double coset** are the work of shimura-glue (§2). This task
   recompiled them unchanged in its own tree (`DeligneX6.lean`, a verbatim copy).
   * `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×)` is a point: `nrd(𝒪̂^×) = ℤ̂^×` by local Hensel representations at every
     prime, and `𝔸_f^× = ℚ^×_{>0} ℤ̂^×`.
   * `deligneComponentsX6_of_printed : DeligneComponentsX6Printed → DeligneComponentsX6`.
   * The task statement asked for this computation. It was already in the base (`scratch/shimura-glue/`), so
     it was re-verified rather than redone.
3. **One theorem for each field, from the leaves only** (`r1r2_of_published`, `x6ConicModel_of_published`),
   with the leaf table (§4).

**Still a consequence (not printed form):**
* `RayClassCM`, a field of `r1r2` and so also an input of `x6ConicModel` (§5.1);
* the fibre clause inside `ElkiesEquationsX6` (§5.2).

## 2. The double coset for `𝒪̂^×` (shimura-glue, re-verified)

The leaf is `ShimuraGlue.DelignePi0 X Kfull`, Deligne's display for `G = B^×`, `B = (2, −3 | ℚ)`. It gives a
bijection `π₀(X ×_ℚ ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd(K)`, Galois-equivariant through the cyclotomic idele, with
`K = 𝒪̂^×`. The level is `Kfull`, the units of `𝒪̂ = 𝒪 ⊗ ℤ̂`, using the kernel's basis of the maximal order
`1, i, (1+j)/2, (i+k)/2`.

The objects are all Mathlib's:
* `FiniteAdeleRing ℤ ℚ`;
* `QuaternionAlgebra 𝔸_f 2 0 (−3)`;
* `ConnectedComponents` of the scheme `X ×_{Spec ℚ} Spec ℚ̄`.

The computation (`scratch/shimura-glue/Adelic.lean`, Mathlib only; VERIFIED again in this tree):
* `rep_unit`: in the coordinates of the basis, `nrd = (n₀² + n₀n₂ + n₂²) − 2(n₁² + n₁n₃ + n₃²)`. This represents
  every unit of `ℤ_p`, at every prime `p`, by Hensel's lemma:
  * `p = 2`: `a² + a + 1`;
  * `p = 3`: `x² − 2y²`;
  * `p ≥ 5`: `(2a + b)² + 3b²`, using `FiniteField.exists_root_sum_quadratic`.
* `nrd_Kfull_le`, `ZhatU_le`: `nrd(𝒪̂^×) = ℤ̂^×`.
* `exists_decomp`, `decomp_unique`: `𝔸_f^× = ℚ^×_{>0} · ℤ̂^×`, with unique factors.
* `pi0_Kfull_eq_one`: the double coset is a point.
* `deligneComponentsX6_of_printed`:
  * `π₀(X_ℚ̄)` is a subsingleton;
  * `X_ℚ̄` is nonempty, because `X6Props` gives a `ℚ̄`-point;
  * so `X_ℚ̄` is connected. That is shimura-split's `DeligneComponentsX6`.

Check in this tree: `scratch/x6-glue/DeligneX6.lean` (a copy of `scratch/shimura-glue/Deligne.lean`) compiles
with 0 errors in 1 min 29 s, with 6 standard axiom lines. `X6Glue.lean` contains the same code.

## 3. Elkies' equations (`parts/Charts.lean`, `parts/ConicProof.lean`, `parts/X6New.lean`)

### 3.1 The printed statement

Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), §3, on `X*(6)`. The locators and the exact
display are UNVERIFIED (recalled; no network).
* `X*(6) = X₆/W` is a genus-0 curve over `ℚ` with a coordinate `t`.
* `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`.
* `X₆` is the `(ℤ/2)²`-cover `X*(6)(√−t, √(3(t − 1)))`. Kurihara (1979) gives `X₀(6,1) : x² + y² + 3 = 0` as a
  check. Both conics correspond to `(−1, −3)_ℚ`.

### 3.2 The Lean statement

```lean
noncomputable def elkiesIdeal : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {X 1 ^ 2 + X 0, X 2 ^ 2 - 3 * (X 0 - 1)}      -- t = X 0, s = X 1, r = X 2
abbrev ElkiesRing := MvPolynomial (Fin 3) ℚ ⧸ elkiesIdeal

def ElkiesCharts (X : Over (Spec ℚ)) (t : ToP1 X.left) : Prop :=
  IsAffineOpen t.U ∧ IsAffineOpen t.V ∧
  ∃ (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V)),
    φU eT = t.f ∧ φV eT = t.g ∧
    res (φU eS) * res (φV eS) = 1 ∧ res (φU eR) * res (φV eS) = res (φV eR)   -- on t.U ⊓ t.V
```

`ElkiesEquationsX6` says that some witness of the moduli clause lists (`R1fpProps`, `X6Props`) carries
`t : ToP1 X.left` with three properties:
* the fibre clause and the three CM clauses of shimura-glue's `ElkiesConicT`, verbatim;
* `ElkiesCharts X t`.

The kernel's `ToP1` forces `t.U = {t ≠ ∞}` and `t.V = {t ≠ 0}`: a point of `t.U ∪ t.V` outside `t.U` lies in
`t.V` with `1/t = 0`.

**Reading (SPECULATIVE, standard reasons).**
* Elkies prints the function field `ℚ(X₆) = ℚ(t)(√−t, √(3(t − 1)))`.
* The affine curve `s² = −t, r² = 3(t − 1)` is `r² + 3s² + 3 = 0` after eliminating `t = −s²`, and it is smooth.
  So it is the normalization of the `t`-line in that field, and the two charts are the smooth projective model:
  the conic `Y² + 3X² + 3Z² = 0`, with `t.U = {Z ≠ 0}` and `t.V = {X ≠ 0}`.
* A smooth projective curve is determined by its function field (Hartshorne I.6.12, and II.6.8 for the finiteness of `t`;
  UNVERIFIED numbers). So `ElkiesCharts` is the printed statement in the language of schemes, and not stronger than it.
* Chart algebra, checked by hand: on the overlap, `a = 1/s`, `b = r/s`, `u = 1/t` satisfy `a² + u = 0` and
  `b² − 3(u − 1) = 0`.

### 3.3 The proof of the points form (`conicModelT_of_charts`, VERIFIED)

**Generic part** (`parts/EvalAffine.lean`, Mathlib and the kernel's `specToEquivOfField_comp`):
* `ev U y h : Γ(X, U) →+* K` is the value of sections at a `K`-point `y` in `U`. It uses the same recipe as
  the kernel's `ToP1.val`.
* `eq_specMap_psi`: `y = Spec.map ψ_y ≫ hU.fromSpec`, from Mathlib's `SpecMap_appLE_fromSpec` and
  `fromSpec_top`.
* `ev_eq_psi`: `ev = ψ_y`, from `germ_stalkClosedPointTo`.
* `ev_injective`, `ev_surjective`: `K`-points in an affine `U` correspond to ring homs `Γ(U) → K`. The inverse
  is `ψ ↦ Spec.map ψ ≫ fromSpec`; `range_fromSpec` and `fromSpec` being a mono do the rest.
* `ev_comp`: naturality in `K`.
* `specQ_hom_ext`: morphisms `Spec K → Spec ℚ` are unique. So a scheme map `Spec ℚ̄ → X` is automatically a
  `ℚ̄`-point over `ℚ`.

**Conic part** (`parts/ConicProof.lean`). The map `conicMapL` sends a point `y`:
* in `t.U` to `inl (s(y), r(y))`;
* outside `t.U` to `inr b(y)`. There `1/t` vanishes (`t.basicOpen_g`), so `a(y) = 0` and `b(y)² = −3`.

Its properties:
* *Injective*: points in an affine open are determined by their ring homs, and those by the generators
  (`elkies_hom_ext`).
* *Surjective*: `elkiesLift` builds the ring hom of a solution, and `ev_surjective` gives a point. For `inr`,
  the vanishing of `1/t` puts the point outside `t.U`.
* *Galois-equivariant*: by `ev_comp`.
* *Values*: `t = −s²` on `t.U`, and `t = ∞` off it, by `ToP1.val`.

## 4. The leaf table for `r1r2` and `x6ConicModel`

Kernel row types: `LeafAdopt.R1R2fpRep` (LPrefix) and `X6Kummer.X6ConicModel` (TailE).

| leaf | form | source (locators UNVERIFIED unless "audit") | used by |
|---|---|---|---|
| `ShimuraGlue.DeligneComponentsX6Printed` | **printed** (Deligne's display at level `𝒪̂^×`; the double coset is computed in Lean) | Deligne, Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; Milne 2005 Thms 5.17, 13.6 | both |
| `GeomConnOfAlgClosure` | **textbook, weakened** (adds `IsProper`, `CharZero k`) | EGA IV 4.5; Stacks 0389 | both |
| T5 `PkgI2.TorsionStructure` | **textbook** | `A(k̄)[n] ≅ (ℤ/n)^{2g}`, Mumford, *Abelian varieties* §4 | both (also `MobiusGlue`, `PairsLift`) |
| `BabaGranathRational` | **printed**, conditional on one reading (the CM assignment read from the §3.1 table, which locators.md grades NO for its ramification column) | Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1 (audit YES) | both |
| `GonzalezRotgerX6` | **printed** (on the canonical model) | González–Rotger 2006, Thm 5.12 (audit YES) | both |
| `ShimuraGlue.Ray.RayClassCM` | **consequence** (§5.1) | Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3 | both |
| `ElkiesEquationsX6` | **printed (equations as a scheme)**, with the fibre clause read as Elkies' "`t` is a coordinate on `X₆/W`" together with the moduli meaning of `W` (§5.2) | Elkies, ANTS-III (1998) §3 | `x6ConicModel` |

Every leaf on the moduli witness carries `R1fpProps`, as before. That is the open human check on the
specialization of Deligne's PEL moduli to `R1fpProps` (frontier.md).

**Glue (all proved, compiled in `X6Glue.lean`):**
* this task: `conicModelT_of_charts` and the `ev` lemmas;
* shimura-glue: `deligneComponentsX6_of_printed` with `Adelic.lean`, `mobiusCompose`,
  `babaGranathX6'_of_rational'`, `elkiesConicX6_of_t'`, `reciprocityCanonical_of_rayClass`;
* shimura-split: `r1r2fpRep_of_printed_t5` (`PairsLift` from T5, surjectivity of `π₆`, the bridge, the coarse
  comparison) and `x6ConicModel_of_elkies_t5` (`MobiusGlue` from T5).

**Counts for the two fields.**

| | strict LEAF (published form) | consequences |
|---|---|---|
| shimura-split | 2: `GonzalezRotgerX6`, `GeomConnOfAlgClosure` (+ T5) | 4: `DeligneComponentsX6`, `BabaGranathX6'`, `ReciprocityCanonical`, `ElkiesConicX6` |
| shimura-glue | 4: + `DeligneComponentsX6Printed`, `BabaGranathRational` | 2: `RayClassCM`, `ElkiesConicT` |
| **x6-glue** | **5: + `ElkiesEquationsX6`** (+ T5) | **1: `RayClassCM`** |

## 5. What remains

### 5.1 `RayClassCM` (consequence)

The printed law is Shimura reciprocity at CM points of `Sh_{K₃}`: for `x = [h_k, g]`, `k(x)` is the class
field of `k^× k_∞^× {s : ι(s) ∈ gK₃g⁻¹}`. Two steps lead from it to the leaf.

1. **Subgroup inclusion.** `ι(1 + 3𝒪̂_k) ⊆ g(1 + 3𝒪̂)g⁻¹` for an optimal embedding of the maximal order into
   `gÔg⁻¹ ∩ B`. Once the embedding is in that order, this is one line of algebra: `ι(1 + 3x) = 1 + 3ι(x)`.
2. **The dictionary.** "`(A, ι, η)` has CM by `𝒪_k`" must be matched with "the point is `[h_k, g]` with
   `ι(𝒪_k) ⊆ gÔg⁻¹`". This needs the adelic uniformization `Y₃(ℂ) ≅ B^×\(ℍ^± × B̂^×/K₃)` together with its
   moduli interpretation. Neither is in the kernel.

Other routes were considered and not pursued:
* The kernel's `ShimuraTaniyamaQbar` (TailU) gives only a model over `ℚ̄`, not the Galois action.
* A good-reduction route (Serre–Tate potential good reduction, Raynaud, NOS) controls the ramification of
  `F(A[3])/F`, not of `F/ℚ`. Unramifiedness of `F` needs the uniqueness of the canonical CM lift
  (SPECULATIVE: large).

### 5.2 The fibre clause of `ElkiesEquationsX6`

The clause says `t(x) = t(x') ↔` the QM pairs are `Aut(𝒪)`-twists. It is Elkies' "`t` is a coordinate on
`X₆/W`" combined with the moduli meaning of the Atkin–Lehner group, `W ≅ Aut(𝒪)` acting by twists (as in
Baba–Granath Thm 2.1). So it is a composite of two published statements.

It cannot be dropped:
* the transport to the row's `π₆` (`HauptmodulUniqueX6S`, from `MobiusGlue`) needs it;
* deriving it from `BabaGranathRational` would need `W` as automorphisms of the scheme `X₆`, which is not
  defined.

The charts do determine the fibres of `t`: they are the orbits of `(s, r) ↦ (±s, ±r)`. A split would be:
* Elkies: `W` acts by these sign changes;
* the moduli meaning of `W`.

Not attempted.

### 5.3 Non-vacuity of `ElkiesCharts`

No Lean model of the conic was built. Mathematically, the conic `Y² + 3X² + 3Z² = 0` with `t = −X²/Z²` satisfies
`ElkiesCharts`: its standard affine charts `{Z ≠ 0}` and `{X ≠ 0}` have exactly these coordinate rings (§3.2).
The independent review (§7) checked this.

## 6. Files and checks (VERIFIED: `lake env lean`, one Lean process at a time)

| file | content | check |
|---|---|---|
| `DeligneX6.lean` | `scratch/shimura-glue/Deligne.lean` verbatim (X₆ double coset, printed Deligne leaves) | 0 errors, 1 min 29 s, 6 standard axiom lines |
| `parts/EvalAffine.lean` | §3.3 generic part (`ev`, `ev_injective`, `ev_surjective`, `ev_comp`, `specQ_hom_ext`) | via `ConicDev.lean`, `X6Glue.lean` |
| `parts/Charts.lean` | `elkiesIdeal`, `ElkiesRing`, `rel1`, `rel2`, `elkies_hom_ext`, `elkiesLift`, `ElkiesCharts` | same |
| `parts/ConicProof.lean` | `conicMapL`, its properties, `conicModelT_of_charts` | same |
| `parts/X6New.lean` | `ElkiesEquationsX6`, `elkiesConicT_of_equations`, `elkiesConicX6_of_equations`, `r1r2_of_published`, `x6ConicModel_of_published`, `X6Leaves`, `x6Rows_of_leaves`, `ShimuraGlueLeaves4`, `rows_of_shimuraGlueLeaves4` | via `X6Glue.lean` |
| `parts/DevCopy.lean` | verbatim copies of `ConicPt`, `conicGal` (TailE) and `ConicModelT` (shimura-glue), for the light check | via `ConicDev.lean` |
| `ConicDev.lean` | DevCopy + EvalAffine + Charts + ConicProof over `ZInQKernel.HDecomp.QM.Leaves` | 0 errors, ~10 s, standard axioms |
| `X6Glue.lean` | generated by `mk_x6glue.py`: `scratch/shimura-glue/RowsGlue.lean` verbatim (over `TailK`; contains shimura-split's `Rows.lean`) + the four parts | **0 errors, 2 min 4 s; `x6glue_result.txt`: 82 axiom lines, all standard** |

**Build note.** This worktree had no build of the upstream `lean/` package (`ZInQ.*`), which `TailK` needs.
`lean/.lake` was reflink-copied from `~/dzq-prune`, whose `lean/ZInQ` sources are identical (`diff -rq` is
empty).

**Integration.**
* `parts/EvalAffine.lean`, `parts/Charts.lean` and `parts/ConicProof.lean` need only
  `ZInQKernel.HDecomp.QM.Leaves` plus the definitions `ConicPt`, `conicGal` and `ConicModelT`. They could move to
  `ZInQKernel/Contrib/` once `ConicModelT` has a home.
* `X6New.lean` sits on top of shimura-glue's `RowsGlue.lean`, over `TailK`.

## 7. Independent statement review (model, read-only, no Lean; no human review)

A separate model review read `Charts.lean`, `ConicProof.lean`, `EvalAffine.lean`, `X6New.lean`, the kernel's
`ToP1`, `ConicPt` and `ConicModel`, and shimura-glue's `ConicModelT` and `ElkiesConicT`. It found no false,
vacuous or too-strong statement.

1. **`ElkiesCharts` holds for the genuine conic.**
   * `t = [−X² : Z²]` is a morphism.
   * `ToP1` pins `U = {Z ≠ 0}` and `V = {X ≠ 0}`.
   * The `U`-chart ring is `ℚ[s,r]/(r² + 3s² + 3) ≅ ElkiesRing`; the `V`-chart has `a = Z/X`, `b = Y/X`.
   * The gluing relations hold, and both opens are affine.
2. **Not stronger than Elkies' function-field statement, and not vacuous.**
   * The affine curve is smooth, hence normal and integral over `ℚ[t]`. So it is the integral closure of
     `ℚ[t]` in `ℚ(t)(√−t, √(3(t−1)))`, and likewise over `ℚ[1/t]`.
   * There is no universe or encoding trap: a ring iso is automatically `ℚ`-linear.
   * By Riemann–Hurwitz and the residue fields `ℚ(i)` at `t = 1` and `ℚ(√−3)` at `t = 0`, the constants
     `−1` and `3` are forced.
   * The leaf's truth does not depend on Elkies' `0`/`∞` orientation. The field is invariant under `t ↦ 1/t`,
     with charts swapped. Only the CM labels depend on it, and they are marked UNVERIFIED.
3. **`ConicProof.lean` is sound as an argument.**
   * Points off `U` lie in `V` with `1/t = 0`.
   * Points of an affine open correspond to ring homs.
   * Off `U`: `T = 0 ⇒ S = 0`, `R² = −3`, which is `[1 : b : 0]` with `b = Y/X`, matching `ConicPt`.
   * Galois equivariance holds.
   * The over-`ℚ` condition is automatic.
4. **No clause mismatch.** The fibre and CM clauses are identical to `ElkiesConicT`'s. The residue-field check
   (`t = 1 ↔ D = −4`; `0` and `∞` both give `ℚ(√−3)`) and `j = 16(t − 1)/27 ↦ −16/27, 0, ∞` agree with
   `R2X6Props`.

**Points raised:**
* (a) The two gluing conjuncts are not used by `conicModelT_of_charts`. They are true and fix `a = 1/s`,
  `b = r/s`, and they are kept so that the leaf is the full model statement.
* (b) The Hartshorne locator was changed to I.6.12 / II.6.8 (UNVERIFIED).
* (c) The reviewer recalls (UNVERIFIED) Elkies' `X*(6)` as signature `(0; 2, 4, 6)` with the elliptic points
  at discriminants `−24, −4, −3`, at `t = 0, 1, ∞`, and `X(6) = X*(6)(√−t, √(3(t−1)))`. This agrees with the
  leaf. The display, section number and orientation remain unchecked against the paper.
