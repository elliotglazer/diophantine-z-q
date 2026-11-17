# shimura-cft results log

Build: `.lake/build` and `lean/.lake/build` are symlink trees (`cp -rs`) of ~/dzq-check2 (e38375b3) builds;
check with `scratch/shimura-cft/run.sh <file>` (= `lake env lean`).

## Step 1 (11-14 17:23): verbatim copies compile
- `ShimuraCFT.lean` Part A = R1UnivLeaves.lean lines 10-564 (R1UnivRigid core) + c-to-printed Shimura.lean
  (minus import) + `ShimuraFamilyAb` def. Imports TailZ12 + R1UnivLeaves' imports + Tau Ceti
  `Global.Reciprocity`, `Adeles.FiniteBaseChange`. COMPILED 13 s, 8.6 GB, 3 axiom lines standard. VERIFIED.

## Step 2 (11-14 17:30): printed leaf stated, fields proved — COMPILED (11 s, 8.6 GB), axioms standard. VERIFIED
- Defs (ShimuraCFT): `AQ = FiniteAdeleRing (𝓞 ℚ) ℚ`, `BAQ = (2,−3 | AQ)`, `ZhatQ`, `OhatQ`, `K3Q` (kernel's
  `ShimuraGlue.K3` with 𝓞 ℚ for ℤ), `bEmb : B →ₐ[ℚ] BAQ`, `qT`, `qHat : 𝔸_{K,f} →+* BAQ` via Tau Ceti
  `finiteAdeleBaseChangeAlgEquiv ℚ K`, `qHatU : 𝕀_K →* BAQˣ`, `ArtinCondC κ σ s` (Tau Ceti
  `ideleClassArtinMap K L` on every finite abelian `L` with `K`-embedding into ℂ), `galPt`, `IsCMPoint`, `DCRel`.
- `ShimuraDeligneBody Y Φ`: Ψ : ℍ → BAQˣ → Y(ℂ) onto, fibres = DCRel (B^×_+ \ ℍ×G(𝔸_f) / K₃), holomorphic in τ,
  moduli at g=1 (IsShimuraHolFamily verbatim), reciprocity σΨ(z,g)=Ψ(z, q̂(s_f)^ε g) (ε, δ existential).
- LEAF `ShimuraMainThmIDeligneY3Ab` (R1fpPropsAb) and `ShimuraMainThmIDeligneY3` (R1fpProps).
- `shimuraFamilyAb_of_mainThmI`, `shimuraFamily_of_mainThmI`, `mainThmI_iff_ab` (MumfordRigidityCore),
  `shimuraFamily_of_mainThmIAb`.

## Step 3 (11-14 17:34): checks on the definitions — COMPILED (12.9 s), axioms standard. VERIFIED
- `qHat_algebraMap`: q̂(k) = q(k) for k ∈ K ⊂ 𝔸_{K,f} (q̂ extends q).
- `rat_mem_zhat_iff`: r ∈ ℚ lies in ℤ̂ iff r ∈ ℤ (Mathlib `mem_integers_of_valuation_le_one`).
- `dcRel_one_iff`: DCRel τ 1 τ' 1 ↔ ∃ x, InGamma3 x ∧ ι(x)·τ = τ' (K₃ ∩ B^×_+ = Γ(3)).
- `mainThmIY3_of_mainThmI : ShimuraMainThmIDeligneY3 → CToPrinted.Shimura.ShimuraMainThmIY3` (new leaf implies
  c-to-printed's leaf).

## Step 4 (11-14 17:40): Part C draft `E.lean` (not yet compiled)
- Copies from t5-glue: `mem_range_of_isAlgebraic`, `AbsArtinSurjective`, section `AbsArtin` (absArt surjective
  for no real places). New: `exists_tau`, `exists_iota`, `exists_artinCondC_of_abs`, `exists_artinCondC`
  (every σ ∈ Aut(ℂ) fixing κ(K) satisfies ArtinCondC κ σ s for some idele s, K totally complex).
- Needs import `ZInQKernel.Contrib.TYZGenus.ShimuraModFn`. BLOCKED: ~/dzq-check2 (the build my symlink tree points
  to) is being rebuilt in place at b5ff0474 (LPrefix.olean missing during rebuild). Waiting for it to finish, then
  copy the build (real copy, not symlinks).

## Independent review (model subagent, read-only, 11-14 ~17:50)
- No PROBLEM. All of DCRel, reciprocity conventions (ε, δ cover q̂(s)^{±1}, q̂(s̄)^{±1}), ArtinCondC, qHat,
  IsCMPoint, K3Q judged OK. Reviewer constructed Ψ(τ,g) = ℂ²/ι(B ∩ 𝒪̂g⁻¹)(τ,1)ᵀ meeting clauses 1-4 together.
- RISK (wording): "comparison is clause 1" too quick — FIXED: docstring and report now say "via clauses 1 and 4
  and Deligne's comparison".
- Minor: global Artin normalization only checked locally (absorbed by ε). Suggested `#print axioms` on the leaf
  def itself — ADDED.

## Step 5 (11-14 18:02): Parts C, D merged — whole file COMPILED (20.5 s, 8.8 GB), 0 errors, 17 `#print axioms`
lines all `[propext, Classical.choice, Quot.sound]` (incl. the leaf def `ShimuraMainThmIDeligneY3Ab`). VERIFIED
- Build: `.lake/build`, `lean/.lake/build` are now real copies of ~/dzq-check2 builds (b5ff0474 rebuild, finished
  17:55); sources here are e38375b3, the imported modules are unchanged between the two.
- Import added: `ZInQKernel.Contrib.TYZGenus.ShimuraModFn` (for t5-glue's AbsArtin copy).
- Part C: `exists_artinCondC` (K totally complex: every σ fixing κ(K) is [s,K] on K^ab, via t5-glue's proved
  `absArtinSurjective_of_noReal`); helpers `exists_tau`, `exists_iota`, `exists_artinCondC_of_abs`.
- Part D: `q3 : ℚ(√−3) → B` (√−3 ↦ j), `z3 = i√3`, `isCMPoint_q3`, instance `IsTotallyComplex (QNeg 3)`,
  `recip_hyp_nonempty δ` (hypotheses of clause 4 met for either δ, and ArtinCondC satisfiable for all σ).
