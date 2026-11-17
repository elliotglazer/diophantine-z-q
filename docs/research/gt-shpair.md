# gt-shpair: `ReductGlue.StrictHenselizationPair` from one Néron leaf, with the commutative algebra in Lean

Task gt-shpair, 2026-11-14. Base a454ad64 (wip/leaf-fold16, top module `TailZ26`). This is model work; no human
has reviewed it.

Marks used below:
- **VERIFIED**: compiled, or read in a file.
- **STANDARD**: a published result with a reference.
- **SPECULATIVE**: my own argument.
- **UNVERIFIED**: a theorem number recalled from memory. There is no network on this host, so every BLR/EGA/Stacks
  locator below is UNVERIFIED.

## 1. Verdict

**The GLUE field `strictHenselizationPair` reduces to a single printed-form leaf.** The commutative-algebra half of
the composite is proved in Lean from Mathlib, for every field (any characteristic) and every residue field
(perfect or not). The remaining leaf is "Néron models commute with strict henselization" (BLR §1.2 Prop. 2).

Contribution: `ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean`, namespace `GapSHPair`. It imports only
`ZInQKernel.OneProof.H.TailZ14` and `Mathlib`. Main declarations:

```
GapSHPair.NeronBaseChangeStrictHenselization : Prop                      -- the LEAF
GapSHPair.strictHenselizationPair_of_neron :
  NeronBaseChangeStrictHenselization → ReductGlue.StrictHenselizationPair
GapSHPair.neronBaseChangeStrictHenselization_of_unramified :
  ReductGlue.NeronBaseChangeUnramifiedDVR → NeronBaseChangeStrictHenselization
GapSHPair.strictHenselizationPair_of_unramified :
  ReductGlue.NeronBaseChangeUnramifiedDVR → ReductGlue.StrictHenselizationPair
GapSHPair.shPair    -- commutative algebra, no hypotheses (see §3)
```

- Axioms: `[propext, Classical.choice, Quot.sound]`. There is no `sorry`. (VERIFIED: `#print axioms` and
  `#discharges`, §5.)
- The statement of `StrictHenselizationPair` is not changed. It is neither false nor vacuous: `shPair` builds the
  objects it asks for, and the Néron clause is the only non-algebraic content.
- Count effect if folded: one strict GLUE (composite) is replaced by one LEAF (published, modulo the
  isomorphism-of-bases remark in §2).

## 2. The leaf

**`IsSHSep O O₁ hO`** says four things:
- `O₁` is a strictly henselian DVR (the chain's `IsStrictlyHenselianDVR`);
- `K₁/K` is separable algebraic;
- every uniformizer of `O` stays irreducible in `O₁` (ramification index 1);
- `κ(O₁)/κ(O)` is separable (via the chain's `resMap`).

**LEAF `NeronBaseChangeStrictHenselization`.** For every field `K`, every DVR `O ⊆ K` and every `O₁` with
`IsSHSep O O₁ hO`: if `𝒩` is a Néron model of `A` over `O`, then `bcDVR hO 𝒩` is a Néron model of `A_{K₁}`. It is
stated only over the chain's genuine objects (`GroupModelO`, `IsNeronModel`, `bcDVR`); no new structure is introduced.

**Why the leaf is the printed theorem (SPECULATIVE argument from STANDARD facts).** The hypotheses `IsSHSep` force
`O → O₁` to be isomorphic over `O` to `O → O^sh`. This holds in every characteristic. The argument:

1. `κ₁` is separably closed and separable algebraic over `κ`, so it is a separable closure of `κ`.
2. The universal property of the strict henselization gives a local `O`-map `j : O^sh → O₁` (EGA IV₄ 18.8.8,
   UNVERIFIED).
3. `j` is injective. Indeed, `O^sh` is a DVR with uniformizer `ϖ`, and `j(ϖ) ≠ 0`.
4. `O₁ ∩ K^sh` dominates the DVR `j(O^sh)` in the same field, so `O₁ ∩ K^sh = j(O^sh)`.
5. Take `x ∈ K₁` and put `L = K^sh(x)`. It is finite and separable over `K^sh` because `K₁/K` is separable.
   - The integral closure `B` of `O^sh` in `L` is local, because `O^sh` is henselian. So `B = O₁ ∩ L`.
   - `B` is finite free of rank `[L : K^sh]`, by separability (the trace form).
   - `e = 1`, since `ϖ` uniformizes `O₁`. `f = 1`, since `κ(B) = κ(O^sh) ≅ κ₁`.
   - Hence `[L : K^sh] = dim B/ϖB = 1`, so `K₁ = K^sh`.

So the leaf is BLR §1.2 Prop. 2 ("Néron models commute with `R → R^sh`"), transported along an isomorphism of bases.

**Where separability is used.** Separability of `K₁/K` is what excludes defect extensions in step 5. That is why the
leaf asks for it, and the construction supplies it.

**Relation to the chain.** The leaf is also a specialization of the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR`
(BLR 7.2/1 form; VERIFIED in Lean). So whichever of the two the maintainers prefer, the reduction holds.

## 3. The commutative algebra (all VERIFIED by compilation)

`shPair`: for `K'/K` finite and DVRs `O' ⊆ K'` over `O ⊆ K`, there are `P ⊆ E` and `P' ⊆ E'` with:
- `IsSHSep O P`;
- `IsSHSep O' P'`;
- `E'/E` finite;
- `P'` over `P`.

**Construction.** Put `Ω = K̄'` and choose a valuation ring `w ⊆ Ω` over `O'`. Then `E` is the inertia field of `w`
over `K`, and `E'` is the inertia field of `w` over `K'`. The inertia field over a base is the set of `x` lying in
some finite Galois `M` and fixed by every automorphism acting trivially modulo `𝔪_w` on `w ∩ M`. This is task
sh-route's construction, which had characteristic 0 and a perfect residue field. Three generalizations were needed.

1. **`key_finite` without separable residue fields** (`GTCA1.lean`). Mathlib's `card_inertia_eq_ramificationIdxIn`
   needs `HasSeparableResidueFieldsAt`. It is replaced by:
   - `card_inertia_mul_card_gal`: `|I_P|·|Aut(κ(P)/κ(p))| = e·f`. This uses Mathlib's fundamental identity,
     orbit–stabilizer and `Ideal.Quotient.stabilizerQuotientInertiaEquiv`.
   - `eq_one_and_isSeparable_of_card`: a separable-degree count. For normal residue extensions,
     `|Aut| = [ : ]_s` (`Normal.algHomEquivAut`).

   Together these give `inertia_unram`: for `𝔮 = P ∩ (inertia ring)`, `e(𝔮|p)·f(𝔮|p) = [κ(𝔮):κ(p)]_s ≤ f(𝔮|p)`.
   Hence `e(𝔮|p) = 1` and `κ(𝔮)/κ(p)` is separable. `key_finite` then also returns a polynomial over `O` with
   separable reduction that kills the residue of `x` (`exists_sep_poly`, via `scaleRoots`).

2. **The inertia field in characteristic `p`** (`GTCA2.lean`, `GTCA3.lean`).
   - Normal closures are taken of separable extensions only.
   - A root with a simple residue root is separable (`isSeparable_of_simple_root`).
   - This yields henselian, separably closed residue field, DVR, `e = 1` (`irreducible_comapHom`), `E/K` separable
     (`inertiaField_isSeparable`), and residue extension separable (`res_isSeparable`).

3. **`E_{K'} ⊆ E_K(K')` in characteristic `p`** (`inertiaField_le_adjoin`). Take `x ∈ E_{K'}` and let `N` be a finite
   Galois closure of the separable part of the witness `M'`.
   - Some power `x^(p^n)` lies in `N`.
   - It is fixed by the inertia subgroup of `Gal(N/K)` meeting `Fix(K' ∩ N)`. Extensions of such automorphisms fix
     `K'`, by injectivity of Frobenius, and act trivially mod `𝔪_w` on `M'`, since `(τy − y)^(p^n) = τ(y^(p^n)) − y^(p^n)`.
   - So `x^(p^n) ∈ E_K(K')`.
   - `x` is separable over `E_K(K') ⊇ K'`, hence `x ∈ E_K(K')` (`mem_range_of_pow_mem`, purely inseparable plus
     separable gives the trivial extension).

## 4. Files

- `ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean` (81 KB, 1647 lines): the deliverable. It is generated by
  `scratch/gt-shpair/mkcontrib.py` from the scratch parts.
- `scratch/gt-shpair/GTCA1.lean`:
  - the counting lemmas;
  - the localization lemmas copied from sh-route's `CA1`;
  - the general `key_finite`.
- `GTCA2.lean`: the inertia field (adapted from sh-route's `CA2`).
- `GTCA3.lean`: residue separability, and the nesting.
- `GTFinal.lean`: the leaf, `shPair`, and the main theorem.
- `mk.sh`: out-of-tree compile with oleans in `scratch/gt-shpair/build/` (not committed).
- `T1.lean`, `T2.lean`: first versions of the counting and polynomial lemmas.
- `Discharges.lean`: the check in §5.
- `log.md`: the results log.

## 5. Checks

**Build.** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.StrictHenselizationPair` completed successfully (12926 jobs, about 10 minutes, because the
copied build tree was missing some modules). The contribution module alone builds in about 30 s. (VERIFIED)

**`#discharges` output** (`lake env lean scratch/gt-shpair/Discharges.lean`):

```
DISCHARGES [OpenResearchLeaves16.strictHenselizationPair] by GapSHPair.strictHenselizationPair_of_neron
  still assumes: [GapSHPair.NeronBaseChangeStrictHenselization]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.strictHenselizationPair] by GapSHPair.strictHenselizationPair_of_unramified
  still assumes: [ReductGlue.NeronBaseChangeUnramifiedDVR]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 593 theorems checked, 2 discharge one
```

## 6. What remains

- **The one leaf, `NeronBaseChangeStrictHenselization`.** It is not formalizable today: Néron models are not in
  Mathlib.
- **The locators.** The BLR §1.2 Prop. 2 locator and the EGA IV₄ 18.8 facts used in §2's argument are UNVERIFIED (no
  network).
- **Two further leaves are within reach but not stated here.** The same machinery would give the general forms of
  reduct-glue's `StrictHenselizationNeron` and `StrictHenselizationInside`, which sh-route had only in
  characteristic 0. Neither is an open field at leaf-fold16, so neither is done here.
