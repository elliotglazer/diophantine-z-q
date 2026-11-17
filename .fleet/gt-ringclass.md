# gt-ringclass (2026-11-14/15)

**Result: `T5Glue.RingClassLattice` is proved in Lean** (`T5Glue.ringClassLattice`, standard axioms, no new
hypothesis), so hypothesis `hS : Shimura.ShimuraReciprocityModFn` of `ZInQ.OneProof.frozenTarget` now rests on the two
printed leaves alone:
`T5Glue.shimuraReciprocityModFn_of_printed (hCM : ShimuraMainCM) (hX : X0ModuliGalois) : ShimuraReciprocityModFn`
(Shimura 1971 Thm. 5.4; canonical model of `X₀(N)`: Shimura §6.7, Deligne–Rapoport VI–VII; numbers UNVERIFIED).

Proof: `Ô_O = ℤ + 𝔣̂` (closed open subgroup; density of `K`), a local computation `K ∩ y⁻¹Ô_O = J ∩ O` from three
local conditions, and Tau Ceti's ray-class API (`exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`,
`rayClassQuotient_mk_of_mem`, `mem_ker_rayClassToPic`, `mem_ray_iff`, `toFractionalIdeal_le_one_iff`). ~420 lines.

**Compiles:** `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` (t5-glue's body verbatim + the proof; imports
`TYZGenus.ShimuraModFn/ShimuraMain`, not `Main`; 169 KB, over the ~150 KB guideline because t5-glue's body is 141 KB,
all used). `lake build` OK; `#discharges`: `DISCHARGES [hS] by T5Glue.shimuraReciprocityModFn_of_printed, still
assumes: [T5Glue.ShimuraMainCM, T5Glue.X0ModuliGalois], axioms: [propext, Classical.choice, Quot.sound]`.
Duplicate scan vs `Main`'s environment: 0 copies. `scratch/gt-ringclass/Headline.lean`: `frozenTarget` with `hS`
replaced by the two leaves, standard axioms.

**Remains:** the two printed leaves; the fold (hS is a plain argument of `frozenTarget`, not a bundle field, so
autofold.py does not apply: hand edit of `Main.lean`). Report: `docs/research/gt-ringclass.md`.
