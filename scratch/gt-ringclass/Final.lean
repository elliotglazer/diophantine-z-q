
/-! ## Row T-5 from the two printed leaves alone -/

namespace T5Glue

open ZInQ.Contrib.TYZGenus.Shimura

/-- **The kernel's CM hypothesis `Shimura.ShimuraReciprocityModFn` (hypothesis `hS` of
`ZInQ.OneProof.frozenTarget`) from two printed leaves.** `ringClassLattice` closes the last glue
Prop of t5-glue's `shimuraReciprocityModFn_of_t5''`, so `hS` rests on
* `ShimuraMainCM`: the main theorem of complex multiplication with torsion, idelic form (Shimura
  1971, *Introduction to the arithmetic theory of automorphic functions*, Thm. 5.4; Lang,
  *Elliptic functions*, Ch. 10, Thm. 3; Silverman, *Advanced topics*, Thm. II.8.2 for `𝒪_K`;
  theorem numbers UNVERIFIED);
* `X0ModuliGalois`: the canonical model of `X₀(N)` over `ℚ` at algebraic points (Shimura 1971,
  §6.7 with Thm. 6.6 and Prop. 6.9; Deligne–Rapoport, LNM 349, VI.6 and VII; Diamond–Shurman,
  §7.5–7.7; theorem numbers UNVERIFIED). -/
theorem shimuraReciprocityModFn_of_printed (hCM : ShimuraMainCM) (hX : X0ModuliGalois) :
    ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_t5'' hCM hX ringClassLattice

end T5Glue
