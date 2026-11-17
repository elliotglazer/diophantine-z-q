# gt-elkies: `elkiesEquationsX6Ab` reduced to Elkies' theorem on `X*(6) = X₆/W` in printed form; the moduli step is proved

Task gt-elkies, 2026-11-14/15. Base a454ad64 (leaf-fold16, top module `TailZ26`, 61 H fields). Lean:
`ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean` (the contribution; imports only `ZInQKernel.OneProof.H.TailZ22`);
`scratch/gt-elkies/` (log, verbatim statement copy, `#discharges` check, autofold spec and dry-run, axiom check).
No other file under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network).

## 1. Main result

**The research field `elkiesEquationsX6Ab` is a theorem from one new published leaf, `ElkiesX6StarPrinted`
(Elkies' theorem: `t` is a coordinate on `X₆/W`, plus the CM values and the charts), and the moduli step is
proved in Lean from the chain.** VERIFIED: compiled, standard axioms only.

```
DISCHARGES [OpenResearchLeaves16.elkiesEquationsX6Ab] by HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed
  still assumes: [HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 499 theorems checked, 1 discharge one
```

(`scratch/gt-elkies/Discharges.lean`, output `scratch/gt-elkies/discharges.txt`, run after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ElkiesX6Star`.)

The new leaf is **equivalent** to the field it replaces (`elkiesX6StarPrinted_iff`, proved), so it is not
stronger. The autofold dry-run (`scratch/gt-elkies/autofold-spec.json`) reports
`strict count: 47/14 on 61 -> 48/13 on 61; strictest 45/16 -> 46/15`: one strict GLUE field fewer. Its generated
module `scratch/gt-elkies/FoldDryRun.lean` (`OpenResearchLeaves17`, `sixContactMin_of_open21`) compiles with
standard axioms. VERIFIED.

## 2. The Lean statements (namespace `HDec.QMSplit.Moduli.ElkiesX6Star`)

```lean
/-- w_m (m = 1,2,3,6 for k = 0..3) by its moduli action: [(A, ι)] ↦ [(A, ι ∘ Ad μ_m)], μ_m = 1, i, j, ij. -/
def IsAtkinLehner (X) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (k : Fin 4) (g : X ≅ X) : Prop :=
  ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
    Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist (_root_.HDec.LeafQM.AV.Pin.Exact.rep k))

def atkinLehnerW (X) (Ψ) : Set (X ≅ X) := {g | ∃ k : Fin 4, IsAtkinLehner X Ψ k g}

/-- LEAF: Elkies 1998 §3 (UNVERIFIED locator), on the canonical witness. -/
def ElkiesX6StarPrinted : Prop :=
  ∃ Y Φ X Ψ fY (t : ToP1 X.left),
    R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ x x', t.val x.left = t.val x'.left ↔ ∃ g ∈ atkinLehnerW X Ψ, x ≫ g.hom = x') ∧      -- t is a coordinate on X₆/W
    (∀ x P, Ψ x = ⟦P⟧ → (HasCM24 P.q → t.val x.left = 0) ∧ (HasCM4 P.q → t.val x.left = 1) ∧
                        (HasCM3 P.q → t.val x.left = ∞)) ∧                                   -- CM values
    X6Glue.ElkiesCharts X t                                                                  -- s² = −t, r² = 3(t − 1)

theorem orbit_iff_twist (h6 : X6Props Y Φ X Ψ fY) (x x' P Q) (hP : Ψ x = ⟦P⟧) (hQ : Ψ x' = ⟦Q⟧) :
    (∃ g ∈ atkinLehnerW X Ψ, x ≫ g.hom = x') ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)
theorem elkiesEquationsX6Ab_of_printed (h : ElkiesX6StarPrinted) : ElkiesEquationsX6Ab
theorem elkiesX6StarPrinted_of_ab (h : ElkiesEquationsX6Ab) : ElkiesX6StarPrinted
theorem elkiesX6StarPrinted_iff : ElkiesX6StarPrinted ↔ ElkiesEquationsX6Ab
```

(Exact text in the file; the binders shown here are abbreviated.)

## 3. The three steps

**(1) The leaf `ElkiesX6StarPrinted` (published).** Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423
(1998), §3 on `X*(6)` (locators, display and `0/∞` orientation UNVERIFIED, as in the chain before):
`X*(6) := X(6)/W` with `W = {1, w₂, w₃, w₆}`, a coordinate `t` on `X*(6) ≅ P¹` taking the values `0, 1, ∞` at
the CM points of discriminant `−24, −4, −3`, and `X(6)` over the `t`-line as `ℚ(t)(√−t, √(3(t − 1)))`.
* "`t` is a coordinate on `X₆/W`" enters in its `ℚ̄`-point form: the fibres of `t` on `X₆(ℚ̄)` are the
  `W`-orbits. This is a consequence of `X₆/W ≅ P¹_t`, because the `ℚ̄`-points of the quotient of a curve by a
  finite group are the orbits. STANDARD (SGA 1 V.1; Mumford, *Abelian varieties* §7; locators UNVERIFIED).
* The CM clauses are the field's text verbatim.
* The chart clause is the field's `X6Glue.ElkiesCharts X t`, unchanged. This is the smooth projective model of
  Elkies' function field, as x6-glue explained.
* The witness quantifier (`∃ Y Φ X Ψ fY t` with `R1fpPropsAb` and `X6Props`) is the field's, the same pattern
  as every moduli leaf of the chain.

**`W` is a genuine definition, not a hypothesis.** `IsAtkinLehner X Ψ k g` says that the automorphism `g` of
`X/ℚ` acts on moduli as `w_m`. The moduli definition of `w_m` on `X₀(D, 1)` is `(A, ι) ↦ (A/A[I_m], ι_m)`, where
`I_m` is the two-sided ideal of reduced norm `m`. STANDARD: Rotger, Trans. AMS 356 (2004); Baba–Granath, Canad.
J. Math. 60 (2008) §2; locators UNVERIFIED.

For `D = 6` the ideal is principal, `I_m = μ_m𝒪`, so the definition becomes the twist used here:
* the chain's `tt` gives `μ_m = 1, i, j, ij`, of reduced norms `1, −2, 3, −6`;
* `A[I_m] = ker ι(μ_m)`, so `ι(μ_m)` identifies `A/A[I_m]` with `A`;
* under that identification `ι_m` becomes `ι ∘ Ad μ_m`;
* `Ad μ_m = Ad μ_m⁻¹`, because `μ_m² ∈ ℚ^×`.

The definition takes that description directly. Proving it from the ideal-quotient form would need quotients of
abelian varieties by finite subgroup schemes, which the chain does not have (SPECULATIVE: it would be one more
piece of glue if a reviewer insists on the ideal-quotient definition).

**(2) The moduli step `orbit_iff_twist` (proved, VERIFIED).** Two `ℚ̄`-points are in one `W`-orbit iff their QM
pairs are isomorphic up to a twist by some `α ∈ Aut 𝒪`. The proof uses only these inputs:
* `X6Props`: `Ψ` is a bijection, and each twist `α` is induced by an automorphism of `X` (fifth clause);
* the chain's explicit computation `HDec.LeafQM.AV.Pin.Exact.rep_cover`: every `α ∈ Aut 𝒪` is
  `Ad v ∘ Ad μ_m` with `v ∈ 𝒪^×`. That computation comes from Skolem–Noether (T13, proved in t-skolem-kw) and
  the normalizer descent `N_B(𝒪) = ℚ^×𝒪^×{1, i, j, ij}`;
* the chain's `HDec.G0ModField.innerIso`: an inner twist is isomorphic to the untwisted pair, by `ι(w(u))⁻¹`.

The two directions:
* (⇒) If `g = w_m`, then `Ψ(x ≫ g) = [P.twist(Ad μ_m)]`, so `x ≫ g = x'` gives `P.twist(Ad μ_m) ≅ Q`.
* (⇐) Write `α = Ad v ∘ Ad μ_m`. Then `P.twist(Ad μ_m) ≅ P.twist α ≅ Q`. X6Props gives the automorphism `g` for
  `Ad μ_m`, and `Ψ(x ≫ g) = Ψ(x')`, so `x ≫ g = x'` by injectivity of `Ψ`.

**No published input is needed for (2).** `R1fpPropsAb` and `mumfordRigidityCore` are not used.

**(3) `elkiesEquationsX6Ab_of_printed` (proved, VERIFIED).** The proof is the same witness and the same `t`:
* the fibre clause is the orbit clause composed with `orbit_iff_twist`;
* the CM and chart clauses are copied.

The converse `elkiesX6StarPrinted_of_ab` uses `Ψ x = ⟦(Ψ x).out⟧` and the same step.

## 4. Leaf and glue table

| statement | kind | source | strict |
|---|---|---|---|
| `ElkiesX6StarPrinted` | published, printed form on the canonical witness (`ℚ̄`-point form of `X₆/W ≅ P¹`) | Elkies 1998 §3 (UNVERIFIED locator, display, `0/∞`) | LEAF |
| `IsAtkinLehner`, `atkinLehnerW` | definitions (moduli action of `w_m`, D = 6) | Rotger 2004; Baba–Granath 2008 §2 (UNVERIFIED) | — |
| `orbit_iff_twist`, `exists_rep_iso` | glue, proved | chain: `rep_cover`, `innerIso`, `X6Props` | proved |
| `elkiesEquationsX6Ab_of_printed`, converse, iff | glue, proved | — | proved |

## 5. What remains, and caveats

* **The `0/∞` orientation.** `t(−24) = 0` and `t(−3) = ∞` is still an UNVERIFIED reading of Elkies (as in the
  chain before). Two internal checks cannot detect a swap (computed by hand):
  * In the charts, the fibres over `t = 0` (`s = 0`, `r² = −3`) and over `t = ∞` (`a = 0`, `b² = −3`) both have
    residue field `ℚ(√−3)`. González–Rotger 5.12 predicts degree 2 for both the `D = −24` and the `D = −3` points,
    so it is consistent with either orientation (gt-x6facts computed the same).
  * The three quadratic subcovers `ℚ(t)(√−t)`, `ℚ(t)(√(3(t − 1)))` and `ℚ(t)(√(−3t(t − 1)))` are all `P¹` over
    `ℚ`, so local points do not separate them.
  * The chart's conic `r² + 3s² + 3 = 0` has Hilbert symbol `(−3, −3)_v = −1` exactly at `v = 3, ∞`
    (computed with PARI `hilbert`, VERIFIED), the same as `x² + y² + 3 = 0`, which is Kurihara's equation for `X₆`
    as recalled (UNVERIFIED). So no real points, as `X₆` must have. This checks the equations only, not the
    orientation.
  * Checking the orientation needs the paper.
* **Modelling of `W`.** As explained in §3(1). The leaf is about the automorphisms acting on moduli as twists by
  `Ad μ_m`; this agrees with Elkies' `W` (defined through the normalizer acting on `𝔥`) under the standard moduli
  interpretation of the canonical model.
* **The leaf is equivalent to the old field.** So the fold changes the classification, not the mathematical
  content: the twist meaning of `W` that made the field composite is now proved Lean glue (`orbit_iff_twist`,
  resting on the chain's proved Aut(𝒪) computation), and what is assumed is Elkies' printed statement.
* gt-x6facts (origin/wip/gt-x6facts) uses `ElkiesEquationsX6Ab` as an input. After this fold, its theorem would
  take `elkiesEquationsX6Ab_of_printed hE'` with `hE' : ElkiesX6StarPrinted`. The two contributions are
  independent and both import `TailZ22` only.

## 6. Files

* `ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean`: the contribution (≈ 8 KB). It reuses the chain's `rep`,
  `rep_cover`, `innerIso`, `X6Props`, `ElkiesCharts`, `R1fpPropsAb`, and copies none of them.
* `scratch/gt-elkies/Statements.lean`: verbatim copy of the target and of `ElkiesCharts` (reference, not compiled).
* `scratch/gt-elkies/Discharges.lean`, `discharges.txt`: the check.
* `scratch/gt-elkies/autofold-spec.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`: the fold, dry run, compiles.
* `scratch/gt-elkies/Axioms.lean`, `axioms.txt`: the axioms of the four theorems.
* `scratch/gt-elkies/log.md`: results log.
