# gap-triage: the six top hypotheses of `ZInQ.OneProof.frozenTarget`

Agent TOP, 2026-11-14. Read-only (no Lean, no lake, no network). Base e38375b3 (wip/gap-triage).
Marks: VERIFIED-READ = file opened, the signature seen (quoted); SPECULATIVE = not checked;
UNVERIFIED = theorem numbers from memory.

## 0. Common facts (all VERIFIED-READ)

- `ZInQKernel/OneProof/Main.lean:41-51`:
  ```lean
  theorem _root_.ZInQ.OneProof.frozenTarget (r …) (t …) (l …) (g …)
      (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
      (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
      (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget :=
    ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves (HDec.HSyn.sixContactMin_of_open12 r t l g)
      (tyzThm35ReadingA_of_leaves h11 h29 hS (TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
      ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3
  ```
  None of the six goes through the OneProof/H bundles. No renames and no older bundle generations.
  The consumers are `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` (`Contrib/TYZChain/Main.lean:56`)
  for h11, h29, hS and h33, and `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves`
  (`Contrib/GZDecomp/Decomp.lean:404`) for hL2 and hL3.
- Where both chains end: `GZDecomp.certifiedRankTYZClRk_of_readingA_grossZagierCd` (`Contrib/GZDecomp/Scope.lean`)
  produces `RouteK.Rank.CertifiedRankTYZClRk` (`RouteK/Rank/Statements.lean:74`):
  `∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 → ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P`.
  This is consumed by `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl`
  (`RouteK/Rank5bSec3.lean:77`), universally in `d`.
  - The only objects that occur are the curves C_d, d ≡ 5 (mod 8) squarefree, together with X₀(32) and the ring class
    fields that TYZ's proof needs.
  - No finite list of `d` is visible. The hypothesis is universally quantified. I did not check whether the Route K
    argument needs infinitely many `d` (SPECULATIVE: it needs an infinite family). So **none of the six reduces to a
    finite computation.**
- "Reading A" (`TYZThm35ReadingA`): for squarefree n ≡ 5 (mod 8) with `ord_{s=1} L(C_n,s) ≥ 2`, `T5a(n) = T5b(n) = 0`
  mod 2. It is proved from TYZ's inputs through Proposition N (`RouteK/PropN.lean:1488`
  `tyzThm35ReadingA_of_tyzInputs`).

---

## 1. h11 : `TYZThm11Integral` (IN FLIGHT: cloud worker on T-1)

1. **Identity.**
   - `ZInQ.Contrib.TYZDecomp.TYZThm11Integral`, `ZInQKernel/Contrib/TYZDecomp/Leaves.lean:259`, frontier r5 **T-1**.
   - Form: LEAF, published form (TYZ Thm 1.1, first assertion, restricted to odd m; the tyz-lcal audit says it is
     faithful).
   - Statement: `∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ ℓ : ℤ, (ℓ : ℂ) ^ 2 = lcalSq m`.
   - Here `lcalSq m = lValOne m / (2^(2·#primeFactors m − 3) · omegaTYZ m)` (`Leaves.lean`, §2), with `lValOne` the
     value at 1 of the unique entire continuation of Mathlib's `L(C_m,s)`.
2. **Use.**
   - `lcalChoice h11` (`Leaves.lean`, §4) picks an integer square root of `lcalSq m` for every squarefree m ≡ 1, 3.
     `isTYZLcal_lcalChoice` then gives the pinned `𝓛`.
   - `TYZLcal.lcalOne_of_leaves` (`Contrib/TYZChain/Lcal.lean:149`) uses h11 at m = 1 and m = 3 to prove `𝓛(1) = 1`.
   - Through `IsTYZLcal`, `𝓛` is read at every divisor d₁ ≡ 1, 3 of every squarefree n ≡ 5. That covers every
     squarefree m ≡ 1, 3 (multiply by a prime ≡ 5 (mod 8) not dividing m).
   - **Use (a): full generality on classes 1, 3.** No weaker specialization serves.
3. **Library coverage.**
   - Hecke's continuation of `L(C_m,s)`, proved: `theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation`
     (`Contrib/HeckeAll/Provider.lean:10`, VERIFIED-READ).
   - Positivity of the period: `omegaInt_pos` (`Leaves.lean`, VERIFIED-READ).
   - Bound on `L(C₁,1)`: `lValOneBound` (`Lcal.lean:901`, VERIFIED-READ).
   - Missing from Mathlib and the tree: Waldspurger's formula, Tunnell's theorem, half-integral weight forms, genus
     periods.
4. **Missing infrastructure.**
   - Waldspurger or Gross's formula for toric periods: `L(C_m,1)` equals a squared toric period over ℚ(√−m) (or Tunnell's
     ternary-theta formula). This needs Shimura–Waldspurger correspondence or quaternionic automorphic forms.
   - Then TYZ's 2-adic analysis of the genus period.
5. **Tier: T4.**
6. **Strategy:** keep cited.
7. **Notes.**
   - In flight.
   - Each instance at a fixed m would be a computation plus a published theorem: Tunnell 1983 (UNVERIFIED) gives
     `L(C_m,1)/Ω` through ternary-form counts. Useless for the universal statement.
   - If false, every downstream hypothesis that quantifies over `IsTYZLcal ℓ` (h29, h33) becomes vacuous. So h11 is
     what keeps them non-vacuous (TYZSplit docstring).

## 2. h29 : `TYZLemma29Mod2` (IN FLIGHT: cloud worker on T-3)

1. **Identity.**
   - `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`, `Leaves.lean:273`, frontier r5 **T-3**.
   - Form: GLUE, a mod-2 composite of TYZ Lemma 2.9 and Prop. 2.3 (tyz-lcal audit: faithful).
   - Statement: `∀ ℓ : ℕ → ℤ, (∀ m, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ))^2 = lcalSq m) → LemmaTwoEight ℓ`.
   - `LemmaTwoEight` (`Hypotheses/TYZInputs.lean:99`): for squarefree m ≡ 1, `Σ_{d∣m, d≡1, d²<m} L d · L (m/d) ≡ g(m)`
     (mod 2). For m ≡ 3, `Σ_{d∣m, d≡1} L(m/d) L d ≡ g(m)`. Here `g = gNat`, the 2-part of the class number.
2. **Use.**
   - `lcalOne_of_leaves` uses it at m = 3 (`ell_three_mul_ell_one_odd`).
   - `PropN.lemmaN1` uses it to get `𝓛 ≡ Λ` (mod 2) on all of classes 1, 3. The result feeds `parity_sums_eq` for every
     n ≡ 5 (`genusData_nonempty_iff`, `Leaves.lean`; `tyzInputs_of_leaves`).
   - **Use (a): full generality.**
   - The sign choice is immaterial: `lemma29Mod2_iff (h11) : TYZLemma29Mod2 ↔ LemmaTwoEight (ellOf h11)`
     (`Lcal.lean:893`, VERIFIED-READ).
   - Equivalent alternative leaf: `TYZThm11Mod2` (`𝓛(m) ≡ Λ(m)` mod 2), with `lemma29Mod2_of_thm11Mod2` proved
     (`Leaves.lean`).
3. **Library coverage.**
   - Genus theory, `gCl`/`gNat` and Rédei's formula are in the tree (`RouteK.Redei.redeiFormula`).
   - Nothing toward the parity of central L-values.
4. **Missing infrastructure.** The same as h11 (Waldspurger/Gross toric period formula), plus TYZ's induction on the
   number of prime factors (TYZ §2).
5. **Tier: T4.**
6. **Strategy:** keep cited.
7. **Notes.**
   - **Not a finite computation.** It is mod 2 only in its conclusion. The parities of `𝓛(d)` at infinitely many d are
     parities of normalized central values `L(C_d,1)/Ω_d`.
   - Each m is decidable given certified L-values, but the chain needs every m.

## 3. hS : `Shimura.ShimuraReciprocityModFn`

1. **Identity.**
   - `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn`, `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean:76`.
   - Frontier: old row T-5. In r5 it is split into **T-13** `CMModuli` and **T-14** `X0RatStructure`
     (`scratch/tyz-split/T5.lean:92,118`).
   - Form: textbook LEAF (Shimura 1971 Thm 5.4 with torsion plus the canonical model of X₀(N), in Gross's form;
     UNVERIFIED numbers).
   - Statement (quoted):
     ```lean
     ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g → ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
       ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar), ιC (e (… omega)) = I * √m →
       ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
         (∀ x : ringClassField (conductorOrder (QNeg m) f), ρ (e x) = e (ringClassArtinEquiv … (picClass J) x)) →
       ∀ D, D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
         idealLat m f J * Q'.lat = Q.lat.map (mulLeft c) → idealLat m f J * Q'.latN = Q.latN.map (mulLeft c) →
         ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'
     ```
2. **Use** (VERIFIED by reading).
   - Every application has `N = 32` and `g ∈ {X0.xC, X0.yC}`, the eta quotients of `X0.lean:88,91`. Their
     `IsRatModFn 32` is proved (`isRatModFn_xC_of` with `etaModelInvariant`, `etaCuspGrowth`, `xQExpRational`).
   - (i) `shimuraReciprocityPic_of` (`ShimuraModFn.lean:122`) gives `ShimuraReciprocityPic` (`ShimuraRecip.lean:72`).
     It is used with **non-trivial** J:
     - `TYZSigmaFixesZn`: class of `(3+2√−n)𝓞_K ∩ O_{n,4}` (`ShimuraZn`);
     - `TYZThm36Seven`: class `[𝔭₂]^{−5}` (`Bridge.lean:3122`).
   - (ii) `cmValueRingClass_of_modFn` (`ShimuraMain.lean:131`, J = 1) gives `CMValueRingClass`, hence
     `CMFieldOfDefinition ringClassFieldD`, `CMAlgebraic` and `znOverH4_of` (`L321.lean:1988`: `z_n ∈ A(H_{n,4})`).
   - The only Heegner forms that occur (grep over `TYZGenus`, `TYZChain`):
     - `tyzForm n : HeegnerForm 32 (-64*n)` for n ≡ 5 (`CM.lean:431`): m = n, f = 4, order ℤ[4√−n], `H_{n,4}`;
     - `tyzForm7 n : HeegnerForm 32 (-n)` for n ≡ 7 (`Bridge.lean:129`): m = n, f = 1, Hilbert class field.
     - `Q'` runs over the forms of the same discriminant.
   - **Use (b).**
   - Weakest sufficient statement (implied by the original, never stronger):
     ```lean
     def ShimuraRecip32TYZ : Prop :=
       ∀ g ∈ ({fun τ => X0.xC τ, fun τ => X0.yC τ} : Set (UpperHalfPlane → ℂ)),
       ∀ (n f : ℕ) [NeZero n] [NeZero f], Squarefree n →
         ((n % 8 = 5 ∧ f = 4) ∨ (n % 8 = 7 ∧ f = 1)) →
       ∀ e (he : normalized) (J : integralIdealsPrimeTo (conductorOrder (QNeg n) f).conductorModulus) (ρ : GalQ),
         (ρ acts on e(H_O) as Art(J ∩ O)) →
       ∀ D, D = discOf n f → ∀ (Q Q' : HeegnerForm 32 D) (c : ℂ), (lattice relations as above) →
         ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'
     ```
     Equivalently: `ShimuraReciprocityPic` restricted to these (m, f), plus `CMValueRingClass` at N = 32,
     D ∈ {−64n, −n}.
   - Still deep: it is the main theorem of CM with level structure, at infinitely many orders. Not a computation.
   - shimura-modfn §0 (VERIFIED-READ) shows that it cannot be reduced to the j-form. At non-isolated points, e.g.
     `[32,10,1]` with D = −28, and at `tyzForm7 n` for n = 7, 15, 47, the j-values do not determine x(τ).
3. **Library coverage.**
   - Mathlib: `PeriodPair`, `weierstrassP` (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60,268`,
     VERIFIED-READ). `ModularForm.eta` (`Mathlib/NumberTheory/ModularForms/DedekindEta.lean:57`
     `noncomputable def eta (z : ℂ) := 𝕢 24 z * ∏' n, (1 - eta_q n z)`, VERIFIED-READ). `FiniteAdeleRing`, `IdeleGroup`.
     No modular curves, no CM theory, no Heegner points: grep for "Heegner" finds only `Analysis/Real/Pi/Chudnovsky.lean`.
   - Tau Ceti (vendored, `ZInQKernel/Contrib/TauCeti/`), VERIFIED-READ:
     - `def ringClassField : IntermediateField K (SeparableClosure K)` (`…/ClassFields/RingClass/Field.lean:112`);
     - `def ringClassArtinEquiv : Pic O ≃* Gal(ringClassField O/K)` (`Field.lean:179`);
     - `def ringClassIdeleQuotient : IdeleClassGroup (𝓞 K) K →* Pic O` (`RingClass/Quotient.lean:71`);
     - `def rayClassField (𝔪 : Modulus K)` (`ClassFields/RayClassField.lean:114`);
     - `rayClassArtinMap` and `isArithFrobAt_rayClassArtinMap_idealClass` (`Global/AdmissibleModulus/Reciprocity.lean:132,204`);
     - `theorem denseRange_absoluteArtinMap : DenseRange cf.absoluteArtinMap` (`Formation/AbsoluteArtinMap.lean:399`).
     - So the class field theory side (ring class fields and the Artin map) is complete.
   - Tree, VERIFIED-READ by name:
     - X₀(32) eta model (`TYZGenus/X0.lean`);
     - `etaModelInvariant : X0.EtaModelInvariant` (`ShimuraTheta.lean:318`), `etaModelFricke`;
     - Heegner forms and lattices (`CM.lean:149-221`).
   - **t5-glue, merged on main** (`docs/research/t5-glue.md` @ a486689f; Lean in `scratch/t5-glue/T5Glue.lean`, not a
     kernel module):
     - `T5Glue.shimuraReciprocityModFn_of_final (hCM : ShimuraMainCM) (hX : X0ModuliGalois) (hA : AbsArtinSurjectiveQNeg)
       (hS : IdeleLatticeScale)`;
     - `x0RatStructure_of_leaf : X0ModuliGalois → X0RatStructure`.
   - **origin/wip/t5-glue tip 39bb3cd2, NOT merged into main or w63** (VERIFIED by `git merge-base`):
     - `shimuraReciprocityModFn_of_t5'' (hCM : ShimuraMainCM) (hX : X0ModuliGalois) (hA : RingClassLattice)`;
     - `AbsArtinSurjectiveQNeg`, `IdeleLatticeScale` up to `RingClassLattice`, and `InvertibleColon` are proved there.
   - **origin/wip/t5-glue2** (536d44b0, log read):
     - `absArtinSurjective_of_noReal` and `absArtinSurjectiveQNeg : AbsArtinSurjectiveQNeg`, proved with standard axioms
       (duplicates t5-glue's tip);
     - `Lattice.lean`: verbatim copies plus the start of an `IdeleLatticeScale` reduction. Superseded by t5-glue's tip.
4. **Missing infrastructure, in order.**
   1. Merge t5-glue's tip: T-13 becomes `ShimuraMainCM + RingClassLattice`, T-14 becomes `X0ModuliGalois`.
   2. `RingClassLattice`: Tau Ceti's congruence `Pic O` against the idelic lattice class. No CM. The review's estimate is
      500–1000 lines: `Pic O ≅ Kˣ\𝔸_f^×/Ô^×`, `mem_ker_ringClassIdeleQuotient_iff`, `latHat O = O + f𝒪̂`, `K ∩ 𝒪̂ = 𝒪`.
   3. `X0ModuliGalois` (canonical model of X₀(N), q-expansion principle). Needs modular curves as ℚ-schemes or the
      Shimura canonical-model theory.
   4. `ShimuraMainCM` (Shimura Thm 5.4 with torsion). Needs CM elliptic curves over number fields, reduction mod 𝔭
      (Deuring), and the action on torsion.
5. **Tier:** T2 for the remaining glue (`RingClassLattice`); T4 (T3 at best) for the two printed leaves.
6. **Strategy:** reduce to smaller printed statements, which t5-glue has done, then keep `ShimuraMainCM` and
   `X0ModuliGalois` cited.
7. **Notes.**
   - The X₀(N) leaf is only needed at N = 32 and g ∈ {x, y}. A specialized `X0ModuliGalois32` could be stated. A route
     through explicit algebraic relations between x, y and the Weber coordinates on X₀(32) is SPECULATIVE and large.
   - Watch for duplicated work: t5-glue2 and t5-glue's tip both prove `AbsArtinSurjectiveQNeg`.

## 4. h33 : `TYZSplit.TYZThm33`

1. **Identity.**
   - `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`, `ZInQKernel/OneProof/TYZSplit.lean:157`, frontier r5 **T-12**.
   - Form: LEAF, published form (TYZ Thm 3.3, "Gross–Zagier formula", L1299-1311). It is carried along the eta model and
     restricted to n ≡ 5, 7. `𝒫(d)` is existential, as `Q d / m d` with `Q d ∈ A(K_d)^-`.
2. **Use.**
   - `tyzThm33Pinned_of_tyzThm33` (`TYZSplit.lean:520`) gives `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ`
     (`TYZChain/Thm35.lean:105`).
   - `TYZ35.thm35First_of_lcal_thm33` (`Thm35.lean:718`) with `thm35First_of_thm33` then gives
     `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`.
   - That is consumed by `T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First` (`L321.lean:2156`).
   - `thm35First_of_thm33` runs a strong induction over every squarefree d ≡ 5, 7 with all its divisor pairs.
   - **Use (a) on classes 5, 7** (the objects are fixed: X₀(32) ≅ `A : y² = x³+4x`, Heegner points of discriminant −64n
     and −n). No finite specialization.
   - Weakest sufficient statement on this path (implied by the printed theorem via the proved glue): the hypothesis of
     `L321.lean:2156`.
     ```lean
     ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Package.Thm35First ℓ CMBridge.tyzZ
     -- Thm35First ℓ Z := ∀ n, n % 8 = 5 → Squarefree n →
     --   ∃ ε, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))   (Package.lean:289)
     ```
     This is TYZ Thm 3.5 first assertion for the pinned genus points: if `𝓛(n) = 0` then `P(n)` is torsion. It is still
     deep: a GZ-type vanishing statement for every n. Only `ℓ 1 = 1` and the zero set at n are read
     (`thm35First_of_thm33` docstring).
3. **Library coverage.**
   - Tree: genus points, `Pchi`, genus characters `chiT`, `h2G = h2`, `IsPhi`; all glue proved (`TYZSplit.lean` §3).
   - Tau Ceti: `canonicalHeight_eq_zero_iff_isOfFinAddOrder` (`…/EllipticCurve/CanonicalHeight/Basic.lean:333`,
     VERIFIED-READ; needs a `[Northcott …]` instance).
   - Nothing toward the explicit Gross–Zagier formula (Yuan–Zhang–Zhang) or Néron–Tate heights of Heegner points.
4. **Missing infrastructure.**
   - Yuan–Zhang–Zhang's general Gross–Zagier formula, needed because conductor 4 at level 32 violates the classical
     Heegner hypothesis.
   - Néron–Tate heights on `A(H)`, modular parametrization, Kolyvagin.
5. **Tier: T4.**
6. **Strategy:** keep cited. Optionally weaken the leaf to `Thm35First` pinned, though that is no longer a printed
   display and is not recommended.
7. **Notes.**
   - The `[i]`-sign convention is load-bearing: with the other sign the leaf is false (TYZSplit docstring).
   - HUMAN CHECK items are listed in the `TYZThm33Pinned` docstring (independence of the lifts).

## 5. hL2 : `GZDecomp.FHNonvanishing`

1. **Identity.**
   - `ZInQ.GZDecomp.FHNonvanishing`, `ZInQKernel/Contrib/GZDecomp/Decomp.lean:109`, frontier **Z-1**.
   - Form: GLUE, a literature composite: Friedberg–Hoffstein 1995 (UNVERIFIED "Thm B") plus the root number of a twist.
   - Statement: `∀ N [NeZero N] (f : Newform N 2) (hχ : f.χ = 1), rootNumber f hχ = -1 → ∀ B : ℕ, ∃ D : ℤ, D < -B ∧
     IsOddImagFundDisc D ∧ HeegnerHyp N D ∧ ∀ G, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0`.
2. **Use.**
   - The only call is `hL2 N f hχ hw 4` in `grossZagierCd_of_leaves` (`Decomp.lean:279`):
     - f is the newform of C_d from `modular_cd` (d ≡ 5 (mod 8) squarefree);
     - its level is forced to `N = 32 d²` by `level_eq_of_coeff_cd` (`GZStatements/Level.lean:45`, VERIFIED-READ:
       `… : N = 32 * d ^ 2`);
     - B = 4.
   - **Use (b).**
   - Weakest form, already in the tree and compiled: `ZInQ.GZStatements.FHNonvanishingCd`
     (`ZInQKernel/Contrib/GZStatements/Weak.lean:46`, VERIFIED-READ). It is implied by the original
     (`fhNonvanishingCd_of_fhNonvanishing`).
     ```lean
     def FHNonvanishingCd : Prop := ∀ d : ℕ, d % 8 = 5 → Squarefree d →
       ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
         (∀ n, n ≠ 0 → coeff f n = ((shortCurve (-(d:ℚ)^2)).LFunction n : ℂ)) → rootNumber f hχ = -1 →
         ∃ D : ℤ, D < -4 ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧ ∀ G, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0
     ```
   - `HeegnerHyp (32d²) D` means: D ≡ 1 (mod 8), and D is a nonzero square mod each p ∣ d (`heegnerHyp_32_iff`,
     `heegnerHyp_iff_split`).
   - Not finite.
3. **Library coverage.**
   - Tau Ceti `Newform`, `frickeCompletedL_sub_eq` (`…/ModularForms/LFunction/Sign.lean:186`, VERIFIED-READ:
     `CuspForm.frickeCompletedL f.toCuspForm … (k - s) = I ^ k * f.frickeSign hχ * CuspForm.frickeCompletedL … s`).
   - `CuspForm.twist` (`…/ModularForms/Twist/Basic.lean:213`).
   - Mathlib `CuspForm` `differentiable_L` (`Mathlib/NumberTheory/ModularForms/LFunction.lean:191`).
   - Tree: G3 `signOfSimpleZero`, G6 `exists_isEntireCont_twist`, the Heegner/compat lemmas (`GZStatements/Compat.lean`,
     `Hensel.lean`), `heckeThetaNewform` (`GZTheta/NewCMFinal.lean:71`), `exists_newform_level32` (`Level.lean:29`).
   - Mathlib: Dirichlet's theorem `Nat.forall_exists_prime_gt_and_eq_mod` (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean:443`).
   - Missing: anything on nonvanishing of twisted central values (no multiple Dirichlet series, no half-integral weight,
     no Waldspurger).
4. **Missing infrastructure.**
   - FH's double Dirichlet series and its analytic continuation, or Waldspurger plus Kohnen–Zagier type nonvanishing.
     Research-scale.
5. **Tier: T4.** Swapping the leaf for `FHNonvanishingCd` is T1: the theorem
   `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` already compiles in
   `Weak.lean`.
6. **Strategy:** specialize (swap to `FHNonvanishingCd`) and keep cited.
7. **Notes.**
   - The open human check is whether FH's printed theorem covers the even, non-squarefree level 32d² and dihedral π
     (gz-statements §6 H1).
   - **Attack idea (SPECULATIVE, not checked in Lean):** f is CM by ℚ(i). So for D ≡ 1 (mod 8), coprime to 2d, the twist
     coefficients `a_n(C_d)·(n/|D|)` should be exactly `a_n(C_{d|D|})`: the twist of C_d by ℚ(√D) is C_{d|D|}, and the
     bad Euler factors at p ∣ 2dD are all 1.
     - Then FHNonvanishingCd would reduce to: ∃ D < −4, D ≡ 1 (mod 8), D a square mod every p ∣ d, with
       `L(C_{d|D|},1) ≠ 0`. Here d|D| ≡ 3 (mod 8).
     - By h11/h29, `L(C_m,1) ≠ 0` holds when `𝓛(m)` is odd, i.e. `Λ(m) = 1`.
     - That leaves an elementary-looking choice of a prime q = −D ≡ 7 (mod 8) with prescribed residues (Dirichlet, in
       Mathlib) such that `Λ(dq)` is odd. Whether such a q always exists is unclear: `Λ(dq)` depends on the class groups
       of all divisors.
     - If it works, Z-1 disappears in favour of TYZ inputs already assumed.

## 6. hL3 : `GZDecomp.GrossZagierHeegner`

1. **Identity.**
   - `ZInQ.GZDecomp.GrossZagierHeegner`, `Decomp.lean:131`, frontier **Z-2**.
   - Form: GLUE, a literature composite: Gross–Zagier 1986 formula, Gross 1984 `ȳ = −εy`, modular parametrization
     (Eichler–Shimura plus Faltings), and nondegeneracy of ĥ.
   - Statement: for elliptic E/ℚ with `a_n(E) = a_n(f)`, D an odd imaginary fundamental discriminant with D < −4 and
     `HeegnerHyp N D`, a simple zero of `L(f,s)` at 1 and `L(f⊗χ_D,1) ≠ 0`: every quadratic K = ℚ(√D) has
     `y ∈ E(K)` of infinite order with `σy − y` torsion.
2. **Use.**
   - The only call is in `grossZagierCd_of_leaves` (`Decomp.lean:279`), with E = C_d, the same N = 32d² and f, D from
     hL2, F the continuation of `L(C_d,s)`, and `K = AdjoinRoot (X² − D)`.
   - Descent (G4, `exists_rat_point_of_heegner`, proved) turns y into a rational point of infinite order.
   - **Use (b).**
   - Weakest form in the tree: `ZInQ.GZStatements.GrossZagierRankCd` (`Weak.lean:83`, VERIFIED-READ).
     Recommended: `GrossZagierHeegnerCd` (`Weak.lean:64`).
     ```lean
     def GrossZagierRankCd : Prop := ∀ d : ℕ, d % 8 = 5 → Squarefree d →
       ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 → (aₙ(f) = aₙ(C_d)) →
       ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
       ∀ F G, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G → analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
         ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P
     ```
     Both are implied by `GrossZagierCd` (`grossZagierRankCd_of_grossZagierCd`, `grossZagierHeegnerCd_of_grossZagierCd`),
     hence by `Literature.GrossZagier`.
   - Weakest single replacement for hL2 ∧ hL3 together: `GZDecomp.GrossZagierCd` (`Scope.lean:28`). It is implied by
     `FHNonvanishingCd ∧ GrossZagierRankCd` with proved glue (`grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd`).
   - Not finite.
3. **Library coverage.**
   - Tau Ceti canonical height and `canonicalHeight_eq_zero_iff_isOfFinAddOrder` (see §4).
   - Tau Ceti Galois descent of points (`…/EllipticCurve/GaloisDescent`, used by G4).
   - Mathlib `WeierstrassCurve.LFunction` and `.LSeries` (`Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean:79,84`,
     VERIFIED-READ).
   - Missing: modular curves X₀(N) as curves over ℚ, Heegner points in general, modular parametrization, Néron–Tate
     local heights, Green's functions and the archimedean height computation, Hecke correspondences on Jacobians.
     The tree's X₀(32) eta model (`TYZGenus/X0.lean`) covers only N = 32.
4. **Missing infrastructure.** All of Gross–Zagier: modular parametrization X₀(32d²) → C_d (Shimura's for CM curves),
   Heegner divisors, local heights at every place, and the L-function side (Rankin–Selberg). Research-scale.
5. **Tier: T4.** The statement swap to `GrossZagierHeegnerCd`/`RankCd` is T1 (compiled).
6. **Strategy:** specialize (swap) and keep cited.
7. **Notes.**
   - Gross–Zagier's Heegner condition D ≡ □ (mod 4N) follows from `HeegnerHyp` (`GZStatements/Hensel.lean:105`,
     `exists_sq_mod_four_mul_of_heegnerHyp`).
   - SPECULATIVE architectural alternative: Tian's 2-descent nontriviality of Heegner/genus points (Tian 2014,
     UNVERIFIED) gives rank ≥ 1 for C_n without Gross–Zagier. It probably covers only TYZ's first sum `T5a`, not the
     `T5b` that `CertifiedRankTYZClRk` uses, so it would not replace Z-2 as the chain stands.

---

## Summary table

| field | consumers | use (a/b) | tier | strategy | best attack idea (one line) |
|---|---|---|---|---|---|
| h11 `TYZThm11Integral` (T-1) | `TYZChain.tyzThm35ReadingA_of_leaves` (Main.lean:56) → `lcalChoice`, `lcalOne_of_leaves` (Lcal.lean:149), PropN | a (all squarefree m ≡ 1, 3) | T4 | keep cited (in flight) | none short of Waldspurger/Tunnell; per-m checks useless for ∀m |
| h29 `TYZLemma29Mod2` (T-3) | same; `lemmaN1`, `ell_three_mul_ell_one_odd`, `lemma29Mod2_iff` (Lcal.lean:893) | a | T4 | keep cited (in flight) | not a finite computation (parities of infinitely many central values); keep TYZThm11Mod2 as the equivalent alternative |
| hS `ShimuraReciprocityModFn` (T-13 + T-14) | `shimuraReciprocityPic_of` (ShimuraModFn.lean:122), `cmValueRingClass_of_modFn` (ShimuraMain.lean:131) via Bridge.lean:3136, L321.lean:1988 | b (N = 32, g ∈ {x, y}, D = −64n with n ≡ 5, f = 4; D = −n with n ≡ 7, f = 1; all J) | glue T2 / leaves T4 | reduce to printed leaves (done) + cite | merge origin/wip/t5-glue tip (2 leaves + `RingClassLattice`), prove `RingClassLattice` (500–1000 lines, no CM); drop t5-glue2 duplicate |
| h33 `TYZThm33` (T-12) | `tyzThm33Pinned_of_tyzThm33` (TYZSplit.lean:520) → `thm35First_of_lcal_thm33` (Thm35.lean:718) → L321.lean:2156 | a (all squarefree d ≡ 5, 7) | T4 | keep cited | weakest on path is `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ` (TYZ 3.5(1)); keep printed 3.3 |
| hL2 `FHNonvanishing` (Z-1) | `grossZagierCd_of_leaves` (Decomp.lean:279), call `hL2 N f hχ hw 4` | b (newform of C_d, level 32d², d ≡ 5, B = 4) | T4 (swap T1) | specialize + cite | swap to `GZStatements.FHNonvanishingCd` (compiled); SPECULATIVE: twist of CM form = C_{d\|D\|}, so derive from h11 + h29 + a Dirichlet choice of D |
| hL3 `GrossZagierHeegner` (Z-2) | `grossZagierCd_of_leaves` (Decomp.lean:279) | b (E = C_d, N = 32d², D from hL2) | T4 (swap T1) | specialize + cite | swap to `GrossZagierHeegnerCd`/`GrossZagierRankCd` (compiled), or to the single `GrossZagierCd` for hL2 ∧ hL3 |
