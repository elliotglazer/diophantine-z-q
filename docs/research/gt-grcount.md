# gt-grcount: `gonzalezRotgerCountX6Ab` without the bundled model

## Verdict

**I reduced `ShimuraSplit.GonzalezRotgerCountX6Ab` (TailZ17 L31, field `gonzalezRotgerCountX6Ab` of
`OpenResearchLeaves16`) in Lean to one new published-form leaf plus an open LEAF that is already in the bundle.
It is not proved outright.** The composite flag goes away: the moduli objects now come only from the existing leaf
`HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (González–Rotger Thm 5.12 on the canonical `X₆`). The count is a separate
leaf, `GRCountX6.GonzalezRotgerProp56X6`: González–Rotger Prop. 5.6 at `(D,N) = (6,1)`, stated for *every* witness of
the moduli description, with no existence claim. Under the strictest reading the fold takes the count from 45/16 to 46/15
(`autofold.py --dry-run`, VERIFIED); the lenient count stays 47/14.

**The count is not a finite computation** (VERIFIED by reading the definitions). `R5fpCount` and its forms quantify
over every order `R` in every imaginary quadratic field, and `h(R)` is unbounded. The left side counts isomorphism
classes of QM abelian surfaces over `ℚ̄`, so nothing is left for `decide` or `norm_num` even with the moduli
data unfolded. The only finite arithmetic in it is the local factor: `2^{inertCount6 k} = ∏_{p ∣ 6} (1 − (k/p))`
when no `p ∣ 6` splits. This identity is proved in Lean (`eichlerFactor6_eq`). §3 splits the count further into
Eichler's theorem, which is pure quaternion-order algebra, and the CM-point/optimal-embedding correspondence.

Every theorem below compiles with no `sorry` and only `[propext, Classical.choice, Quot.sound]`
(`ZInQKernel/Contrib/OneProof/GRCountX6.lean`, namespace `GRCountX6`).

## 1. Findings about the target (VERIFIED, read in the build)

* **The chain only uses `R5fpCount`.** The field's one consumer is `r5count := ShimuraSplit.r5fpCount_of_points
  r.gonzalezRotgerCountX6` (`TailZ9` L97; `TailZ23` L804 converts the Ab form to the `R1fpProps` form). The
  existential witness `(Y, Φ, X, Ψ, fY)` plays no part in the chain.
* **The count clause sees the witness only through the bijection `Ψ`** (`card_points_eq`). So the kernel's model-free
  `LeafQM.AV.R5fpCount` (HDecomp/QM/Leaves.lean L599) plus any witness of `R1fpPropsAb ∧ X6Props` gives the field.
  Such witnesses come with the open LEAFs `GonzalezRotgerX6Ab`, `DeligneComponentsX6PrintedAb`,
  `ElkiesEquationsX6Ab` and `BabaGranathRationalAb` (TailZ22).
* **Nothing is false, vacuous or inert.** Given a witness, the new leaf is equivalent to `R5fpCount`, which counts
  CM points (4 at disc −19, unlike the false `h(R)` count). The cross-checks are in §4.

## 2. The reduction (compiled)

| Lean name | statement | role |
|---|---|---|
| `GonzalezRotgerProp56X6` | for every `(Y, Φ, X, Ψ, fY)` with `R1fpPropsAb Y Φ`, `X6Props Y Φ X Ψ fY`, and every `R` of conductor prime to 6 in an imaginary quadratic `k` that occurs as some `End_𝒪(A)`: `#{x ∈ X(ℚ̄) : End_𝒪(A_x) ≅ R} = 2^{inertCount6 k}·#Pic(R)` | **new LEAF** (GR 2006 Prop. 5.6, p. 943, read by the audit, at `(6,1)`, on `X₀(6,1)`; printed form without the model's existence) |
| `gonzalezRotgerCountX6Ab_of_printed` | `GonzalezRotgerProp56X6 → GonzalezRotgerX6Ab → GonzalezRotgerCountX6Ab` | discharges the field |
| `gonzalezRotgerCountX6Ab_of_printed'` | same with `DeligneComponentsX6PrintedAb` as the model | alternative |
| `prop56X6_of_r5fpCount` | `R5fpCount → GonzalezRotgerProp56X6` | the new leaf is never stronger than the kernel's count |
| `r5fpCount_of_prop56X6` | `GonzalezRotgerProp56X6 → GonzalezRotgerX6Ab → R5fpCount` | converse |
| `gonzalezRotgerCountX6Ab_of_r5fpCount` | `R5fpCount → GonzalezRotgerX6Ab → GonzalezRotgerCountX6Ab` | alternative with the existing kernel leaf |

Why the new leaf is the printed statement and not a composite: it states the printed count on `X₀(6,1)`, where
`X₀(6,1)` is identified by its moduli description, and it claims nothing about whether the model exists. Witnesses
are unique up to unique isomorphism (`CoarseCompare`, shimura-split §2), so "for every witness" and "for the
canonical model" say the same thing. The existence of the model is a separate open LEAF that is already in the bundle.

## 3. Splitting the count: Eichler plus the CM correspondence (compiled glue, two leaves)

Here `B = ℍ[ℚ, 2, 0, −3] = (2, −3 | ℚ)` (Mathlib's `QuaternionAlgebra`, discriminant 6) and `𝒪 = LeafQM.O`
(the kernel's maximal order `ℤ⟨1, i, (1+j)/2, (i+k)/2⟩`).

* `OptEmb k R`: the maps `Φ : k →ₐ[ℚ] B` with `Φ⁻¹(𝒪) = R` (the convention of `QMCentralizerCMC`, TailU).
  `ConjRel R` is conjugation by `𝒪^×`. `conjRel_equivalence` proves it is an equivalence relation, so
  `Quot (ConjRel R)` is the set of `𝒪^×`-classes.
* `eichlerLocal k p` is `2` if `p𝒪_k` is prime, `1` if `p𝒪_k = 𝔓²`, and `0` otherwise, i.e. `1 − (k/p)`.
  `eichlerFactor6 k = eichlerLocal k 2 · eichlerLocal k 3`.
* **`EichlerOptEmbCount6`** (LEAF; Eichler, Crelle 195 (1955); Vignéras LNM 800 Ch. III Thm 5.11 and Cor. 5.12;
  Voight, *Quaternion Algebras*, Thm 30.7.3; theorem numbers UNVERIFIED). For `R` of conductor prime to 6 in an
  imaginary quadratic `k`, `Quot (ConjRel R)` is finite and has `#Pic(R) · eichlerFactor6 k` elements. Because
  `B` is indefinite over `ℚ`, `𝒪` has one left ideal class, so the sum in the trace formula has one term. The leaf
  is pure algebra over genuine definitions and could be formalized from Mathlib by the local–global theory of
  quaternion orders, which Mathlib does not have yet.
* **`CMPointsOptEmb6`** (consequence; Shimura 1967 §§1–3, Jordan 1981 §3, González–Rotger 2006 §5; locators
  UNVERIFIED). It asserts a bijection between the classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R` and
  `Quot (ConjRel R)`. The printed correspondence is with `𝒪^1`-classes of *normalized* optimal embeddings. Passing
  to `𝒪^×`-classes of all of them is elementary: `𝒪` has the norm −1 unit `1 + i` (`one_add_i_mem_units`, compiled),
  and an element of the indefinite `B` that normalizes `Φ(k)` non-trivially has negative norm. Passing from `ℂ` to
  `ℚ̄` holds for CM points. Under the strict convention this is a consequence (GLUE).
* `r5fpCount_of_eichler : EichlerOptEmbCount6 → CMPointsOptEmb6 → R5fpCount`. If `R` occurs, the class set is
  nonempty; since it is finite, its cardinality is positive, so `eichlerFactor6 k ≠ 0` (no `p ∣ 6` splits), and
  then `eichlerFactor6_eq` gives `2^{inertCount6 k}`.
* `gonzalezRotgerCountX6Ab_of_eichler : EichlerOptEmbCount6 → CMPointsOptEmb6 → GonzalezRotgerX6Ab →
  GonzalezRotgerCountX6Ab`.

This split does not lower the strict count further (`CMPointsOptEmb6` is a consequence). The fold should use §2. §3
shows where the arithmetic is: Eichler's count is the part a crowdsourcer could formalize from Mathlib's quaternion
algebras, while the correspondence needs complex uniformization of QM surfaces.

## 4. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/GRCountX6.lean`: 0 errors. `lake build +ZInQKernel.OneProof.Main
  +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GRCountX6` succeeds (12926 jobs).
* `#discharges` (`scratch/gt-grcount/Discharges.lean`; output in `scratch/gt-grcount/discharges_output.txt`):

```
DISCHARGES [OpenResearchLeaves16.gonzalezRotgerCountX6Ab] by GRCountX6.gonzalezRotgerCountX6Ab_of_eichler
  still assumes: [GRCountX6.EichlerOptEmbCount6, GRCountX6.CMPointsOptEmb6, HDec.QMSplit.Moduli.GonzalezRotgerX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.gonzalezRotgerCountX6Ab] by GRCountX6.gonzalezRotgerCountX6Ab_of_printed
  still assumes: [GRCountX6.GonzalezRotgerProp56X6, HDec.QMSplit.Moduli.GonzalezRotgerX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.gonzalezRotgerCountX6Ab] by GRCountX6.gonzalezRotgerCountX6Ab_of_printed'
  still assumes: [GRCountX6.GonzalezRotgerProp56X6, ShimuraGlue.DeligneComponentsX6PrintedAb]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.gonzalezRotgerCountX6Ab] by GRCountX6.gonzalezRotgerCountX6Ab_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount, HDec.QMSplit.Moduli.GonzalezRotgerX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 511 theorems checked, 4 discharge one
```

* Fold: `scratch/gt-grcount/autofold-spec.json` (field `gonzalezRotgerCountX6Ab` → leaf `gonzalezRotgerProp56X6`,
  proof `gonzalezRotgerCountX6Ab_of_printed {n}.gonzalezRotgerProp56X6 {n}.gonzalezRotgerX6Ab`). `--dry-run` reports
  "strictest 45/16 -> 46/15". The generated module (`scratch/gt-grcount/FoldCheck.lean`) compiles, and
  `sixContactMin_of_open21` uses only the standard axioms. Nothing under `ZInQKernel/` was changed except the new
  contribution file.
* Consistency checks of the statements (by hand, not proofs). `h(R)·∏_{p∣6}(1 − (k/p))` gives 2, 2, 2 points at
  discriminants −4, −3, −24, matching Elkies' fibres `s² = −t, r² = 3(t − 1)` over `t = 1, ∞, 0`. It gives 4 at
  −19, as in locators.md. With `D = 1` the same `𝒪^×` convention gives forms modulo `GL₂(ℤ)`, that is `h(R)` CM
  points on `X(1)`. This supports the `𝒪^×` normalization shared by `EichlerOptEmbCount6` and `CMPointsOptEmb6`
  (SPECULATIVE until the printed theorems are read).

## 5. What remains

* `GonzalezRotgerProp56X6` (or equally `R5fpCount`): published, cited, open. It can be split as in §3.
* `EichlerOptEmbCount6`: published (Eichler/Vignéras/Voight; numbers UNVERIFIED). This is the natural Lean target
  once Mathlib has orders in quaternion algebras.
* `CMPointsOptEmb6`: consequence of Shimura's correspondence (complex uniformization), locators UNVERIFIED.
* Not done: a non-vacuity check that `OptEmb k R` is nonempty for some explicit `k` (this would need an explicit
  imaginary quadratic field with its `NumberField` instances in Lean).
