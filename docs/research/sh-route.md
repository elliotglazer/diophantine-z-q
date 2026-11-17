# sh-route: the three strict-henselization leaves of reduct-glue from one Néron leaf

Task sh-route, 2026-11-14. Base e38375b3 (wip/w62). Lean: `scratch/sh-route/ShRoute.lean`. `mk.sh` assembles
it from:
- `Base.lean` + `Body.lean`, verbatim copies of `scratch/reduct-glue/{Base,Body}.lean` (`diff` is empty);
- `Top.lean`, `CA1.lean`, `CA2.lean`, `CA3.lean`, `Final.lean` (namespace `ShRoute`).

`chk.sh` runs `lake env lean scratch/sh-route/ShRoute.lean`: 68 s, 7.75 GB, no errors. The file has no `sorry` and
no `axiom`. All 58 `#print axioms` lines report `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`scratch/sh-route/axioms.txt`). Results log: `scratch/sh-route/log.md`. Nothing under `ZInQKernel/` or
`blueprint/` was edited. This is model work with no human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = my
own judgement or argument. **UNVERIFIED** = a theorem number recalled without a source. There is no network on
this host, so every BLR, SGA and EGA locator below is UNVERIFIED.

## 1. Main result

**Over fields of characteristic 0 whose DVR has a perfect residue field, all three strict-henselization leaves of
reduct-glue are now theorems from a single Néron base-change leaf.** The commutative algebra is proved in Lean
from Mathlib, with no further leaf.

```
strictHenselizationNeron0_final  : NeronBaseChangeSH → StrictHenselizationNeron0
strictHenselizationPair0_final   : NeronBaseChangeSH → StrictHenselizationPair0
strictHenselizationInside0_final : NeronBaseChangeSH → StrictHenselizationInside0
route_final : RaynaudSemistableSH → SemistablePersistsSH → SemistableUnipotentSH →
  AvSplit.T4.MulEtaleAbelianScheme → NeronBaseChangeSH →
  RaynaudSemistable0 ∧ SemistablePersistsDVR0 ∧ SemistableUnipotent0
```

**How the statements differ from reduct-glue's.** Each `…0` Prop is reduct-glue's (or reduct-split's) statement
word for word, with two instance hypotheses added after the DVR: `[CharZero K]` and
`[PerfectField (IsLocalRing.ResidueField O)]`.
- `char0_of_general` checks in Lean that each `…0` Prop is a specialization of the original.
- The task allowed adding characteristic 0.
- The perfect-residue-field hypothesis is my addition (§5). Number fields and their completions satisfy both
  hypotheses: they have characteristic 0 and finite residue fields.

The commutative-algebra Props (`SHExists0`, `SHInside0`, `SHPair0`) are all theorems, so no glue is left on this
route.

## 2. The statements (Lean, `Top.lean`)

**`IsSHUnram O O₁ hO`** says that `O₁ ⊇ O` is an unramified strictly henselian extension. It has four parts:
- `O₁` is a strictly henselian DVR (reduct-glue's `IsStrictlyHenselianDVR`);
- `K₁/K` is algebraic;
- every uniformizer of `O` stays irreducible in `O₁` (ramification index 1);
- `κ(O₁)/κ(O)` is separable (via `resMap`).

**LEAF `NeronBaseChangeSH`** (BLR, *Néron models*, §7.2 Thm. 1 and §1.2 Prop. 2; UNVERIFIED). Take `K` of
characteristic 0, `O ⊆ K` a DVR, and `IsSHUnram O O₁ hO`. Then for every abelian variety `A/K` and every Néron
model `𝒩` of `A` over `O`, the base change `bcDVR hO 𝒩` is a Néron model of `A_{K₁}` over `O₁`. The statement uses
only reduct-glue's genuine objects (`GroupModelO`, `IsNeronModel`, `bcDVR`), with no new structures.

**The three leaves, now theorems** (characteristic 0, perfect `κ(O)`):

| reduct-glue leaf | char-0 theorem | proof |
|---|---|---|
| `StrictHenselizationNeron` | `strictHenselizationNeron0_final` | `isSHNeronExt_of` + `shExists0` |
| `StrictHenselizationPair` (with `IsSHNeronExt`) | `strictHenselizationPair0_final` | `isSHNeronExt_of` + `shPair0` |
| `StrictHenselizationInside` | `strictHenselizationInside0_final` | `isSHNeronExt_of` + `shInside0` |

`isSHNeronExt_of : NeronBaseChangeSH → IsSHUnram O O₁ hO → IsSHNeronExt O O₁ hO`: separable implies algebraic,
and the Néron part is the leaf.

## 3. Why `NeronBaseChangeSH` is a consequence of the print (never stronger)

**Statement of the argument.** In characteristic 0 the hypotheses `IsSHUnram O O₁ hO` force `O → O₁` to be
isomorphic over `O` to `O → O^sh`, the strict henselization for the separable closure `κ(O₁)` of `κ(O)`. The
argument is mine (SPECULATIVE); the facts it uses are STANDARD (EGA IV₄ §18.8; Stacks, "strictly henselian local
rings", tags UNVERIFIED).

**The argument.**
1. `κ(O₁)` is separably closed and separable algebraic over `κ(O)`, so it is a separable closure of `κ(O)`.
2. The universal property of `O^sh` gives a local `O`-homomorphism `j : O^sh → O₁` that is the identity on
   residue fields.
3. `O^sh` is a DVR with uniformizer `ϖ`, and `j(ϖ) = ϖ ≠ 0`. So `ker j` is a prime ideal not containing `ϖ`,
   hence zero, and `j` is injective.
4. The valuation ring `O₁ ∩ K^sh` dominates the DVR `j(O^sh)` in the same field, so `O₁ ∩ K^sh = j(O^sh)`.
5. Take `x ∈ K₁` and put `L = K^sh(x)`, which is finite and separable because the characteristic is 0. Then:
   - `O₁ ∩ L` has ramification index 1 and residue degree 1 over `O^sh`;
   - `O^sh` is henselian, so the integral closure `B` of `O^sh` in `L` is local, and `B = O₁ ∩ L`;
   - `B` is free over `O^sh` of rank `[L : K^sh]` (finite because the characteristic is 0);
   - `B/ϖB = κ(B) = κ(O^sh)` has dimension 1.

   Hence `L = K^sh`, so `K₁ = K^sh` and `O₁ = j(O^sh)`.

So the leaf is the printed statement "Néron models commute with strict henselization" (BLR 7.2/1 or 1.2/2),
transported along an isomorphism of bases.

**Where characteristic 0 is used.** Without it, step 5 can fail: a henselian DVR may have an immediate (defect)
extension with `e = f = 1` that is not trivial. The hypothesis removes that reading, as the task anticipated.

**A Lean check of the other direction.** `neronBaseChangeSH_of_unramified : NeronBaseChangeUnramifiedDVR →
NeronBaseChangeSH` proves that the new leaf is a specialization of reduct-glue's general-unramified form. That
form is BLR 7.2/1, if BLR prints it for every local extension of DVRs with `e = 1` and separable residue
extension (UNVERIFIED).

## 4. Leaf table for the route to `raynaudSemistable` and `semistablePersistsDVR` (and 3.5)

| general-DVR field (char 0, perfect `κ`) | Lean | leaves it rests on |
|---|---|---|
| `RaynaudSemistable0` (SGA 7 IX 4.7) | `raynaudSemistable0_of` | `RaynaudSemistableSH`, `NeronBaseChangeSH`, `MulEtaleAbelianScheme` |
| `SemistablePersistsDVR0` (SGA 7 IX 3.3a) | `semistablePersistsDVR0_of` | `SemistablePersistsSH`, `NeronBaseChangeSH` |
| `SemistableUnipotent0` (SGA 7 IX 3.5) | `semistableUnipotent0_of` | `SemistableUnipotentSH`, `NeronBaseChangeSH` |

| leaf | source (UNVERIFIED locators) | published form? |
|---|---|---|
| `RaynaudSemistableSH` | SGA 7 I, Exp. IX, Prop. 4.7, over a strictly henselian trait | yes, if SGA 7 IX is printed over a strictly henselian base (reduct-glue's printed-base form); it is a specialization of the general-DVR form (`printed_of_general`) |
| `SemistablePersistsSH` | SGA 7 I, Exp. IX, Prop. 3.3 (first assertion), strictly henselian base | same remark |
| `SemistableUnipotentSH` | SGA 7 I, Exp. IX, Prop. 3.5, strictly henselian base | same remark |
| `NeronBaseChangeSH` | BLR §7.2 Thm. 1 / §1.2 Prop. 2 | yes in characteristic 0 (§3): it is the strict-henselization statement up to isomorphism of bases, and a specialization of the general `e = 1` form |
| `AvSplit.T4.MulEtaleAbelianScheme` | BLR 7.3/2 (`[m]` is étale for `m` invertible) | bundle leaf, unchanged |

The commutative algebra is all proved. Whichever base SGA 7 IX is printed over, both fields are covered:
- **strictly henselian base:** the SH forms are the print and the table holds;
- **arbitrary trait:** the general-DVR form is the print, and each SH form is a specialization of it.

So in characteristic 0 neither field depends on the base question any more.

## 5. Statement review and what remains

**Characteristic 0 and perfect residue field.** Characteristic 0 is used in three places:
- separability of every algebraic extension (finite Galois subextensions of `Ω`; integral closures of `O` are
  finite);
- the infinite-Galois-free construction;
- §3.

The perfect residue field is used because Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`
(`|I_P| = e`) needs `Algebra.HasSeparableResidueFieldsAt`. With an imperfect residue field `|I| = e·p^s`, so the
Mathlib route breaks. The classical theorem (the inertia field is unramified with separable residue field) still
holds, but it is not proved here.

**The kernel rows quantify over every field.** `PkgI2.RaynaudCriterion` (and reduct-split's `ReductLeaves`) range
over every field `K`, so the char-0 theorems do not discharge reduct-glue's general-`K` fields
`sga7_4_7`/`sga7_3_3a`/`sga7_3_5` as stated. To use this route, the consumer rows must be restricted to
characteristic-0 fields with perfect residue fields. The project applies them at number fields and their
completions, per the task statement (SPECULATIVE, not checked consumer by consumer). The alternative is to extend
this route to the general case, which needs:
- in characteristic `p`: `E := T ∩ K^sep`, and integral closures that are finite only under a Japanese
  hypothesis;
- for imperfect residue fields: `|I| = e·p^s` in place of Mathlib's `card_inertia`;
- for §3 in characteristic `p`: a defect-free reading.

**No statement is false or vacuous.** Each hypothesis is satisfied: `shExists0` constructs an `IsSHUnram`
extension. The conclusions are statements about genuine Néron models.

## 6. Proof notes (all VERIFIED by compilation)

### `CA1.lean` (Mathlib only)

- **`exists_of_mem`.** A valuation ring `W ⊇ R` of `Frac R` (`R` Dedekind) with nonzero center is the localization
  of `R` at its center. This generalizes reduct-glue's `mem_iff_exists`.
- **`key_finite` (finite level).** Take `M/K` finite Galois, `A ⊆ K` a DVR with perfect residue field, and `W` a
  valuation ring of `M` over `A`. If `x ∈ W∖0` is fixed by every `σ` that acts trivially modulo `𝔪_W` on `W`, then
  `x = ϖⁿ · (a unit of W)`. Proof:
  1. Set `S = integralClosure A M`, `P = S ∩ 𝔪_W`, `H = Ideal.inertia P`, `E = Fix H`,
     `R = integralClosure A E` and `𝔮 = P ∩ R`.
  2. Apply `card_inertia_eq_ramificationIdxIn` twice: over `A` with group `Gal(M/K)`, and over `R` with group `H`,
     where the inertia of `P` in `H` is all of `H`. With `ramificationIdx_tower` this gives `e(𝔮|p) = 1`.
  3. `ramificationIdx_eq_multiplicity` then gives `p𝓞_E = 𝔮·J` with `J ⊄ 𝔮`.
  4. `unit_mul_pow_of_div` runs an induction on the `𝔮`-adic order.
  5. Elements of `H` act trivially modulo `𝔪_W` on all of `W` (by `exists_of_mem`), so `x ∈ E`.

### `CA2.lean`

- **`inertiaField w`.** The set of `x ∈ Ω` such that, for some finite Galois `M ∋ x`, every `τ ∈ Aut(Ω/K)` acting
  trivially modulo `𝔪_w` on `w ∩ M` fixes `x`. It is an `IntermediateField` (closure under operations by directed
  unions of normal closures).
- **`inertia_fixes`.** If `IsInertia w σ` (Mathlib's `inertiaSubgroup`), then `σ` fixes the inertia field.
- **Core lemma `mem_inertiaField_of_simple_root`.** A root of `g` over `wE = w ∩ E` whose residue is a simple root
  of `g mod 𝔪_w` lies in `E`: an admissible `τ` sends it to a root with the same residue, and two such distinct
  roots would give a double root (`derivative_eval_eq_zero_of_two_roots`).
- **`henselian_wE`.** Uses `exists_root_near` (a root of a monic polynomial near an approximate root, since `Ω` is
  algebraically closed and `w` integrally closed) and the core lemma.
- **`isSepClosed_wE`.** Lift the polynomial, take any root in `Ω`, and apply the core lemma.
- **`isDVR_wE` and `irreducible_comapHom`.** From `key_finite` through `unit_pow` (`AlgEquiv.liftNormal`), then
  `ofHasUnitMulPowIrreducibleFactorization`.
- **`res_isAlgebraic`.** Scale the minimal polynomial by its coefficient of largest valuation. Separability then
  follows from the perfect residue field.
- **`exists_comap_eq`.** Valuation rings extend, by `IsLocalRing.exists_factor_valuationRing`.
- `shInside0` and `shExists0`.

### `CA3.lean`

- **`inertiaField_le`.** `E_K ⊆ E_{K'}`, using a finite generating set and a normal closure over `K'`.
- **`inertiaField_le_adjoin`.** `E_{K'} ⊆ E_K(t')` for a finite `t'` generating `K'`. It uses the finite Galois
  correspondence `Fix(I ∩ Gal(M/K')) = Fix(I) ⊔ K'` in a finite Galois `M`, where `inertM` is a submonoid of a
  finite group and hence a subgroup.
- **`shPair0`.** `[E_{K'} : E_K]` is finite through an injective `E_K`-linear map into `E_K(t')`. The residue field
  `κ(O')` is perfect because it is algebraic over `κ(O)`.

### Lean pitfall

The file-level opens of `Base.lean`/`Body.lean` (`MonObj`, `Polynomial`) make `mul_one`, `one_mul`, `eval_map`
and `eval` ambiguous in appended code. They are qualified (`_root_.`, `Polynomial.`).
