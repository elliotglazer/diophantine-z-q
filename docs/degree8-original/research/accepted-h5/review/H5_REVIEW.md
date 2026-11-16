# Independent review of the five-contact reduction

I read `height/five-contact-height.tex` in full. It correctly leaves two obligations open. They cannot be removed by the successful finite checks.

1. Q must identify the four exact genus-one quartics as the claimed quotients of the discriminant-210 Shimura curve. Computing their invariants and recovering the unique cross-ratio solves the algebraic reconstruction problem after that identification; it does not prove modular identification. A permitted source or a complete independent computation is still needed.
2. A must supply the explicit arithmetic height bound over the normal fiber field, with the stated degree, reduction support and coefficient. Passing to a GL2-type variety over Q requires a dimension bound and control of bad reduction. An existence theorem without those bounds is insufficient. A splitting cochain on the absolute Galois group cannot be evaluated on the finite field Galois group unless its descent to that quotient is proved.

The conditional reductions appear internally consistent. The four known fixed-point sets, genus formula and cyclic stabilizers force the five labeled branch points. Once Q is supplied, the quartic-invariant calculation recovers the claimed contact line. The level-change group has order 36, and combining it with the 16-element Atkin--Lehner group gives the 576-point torsor. The proof explicitly uses the entire canonical model and its central action, rather than silently fixing a complex component. The tame fixed-point and even-contact arguments are consistent with the asserted ramification support.

The full three-torsion marking gives an injection of Hom modulo three into Hom on torsion; the finite Galois action and torsion-free principal congruence subgroup then give the stated Hom-field conclusion. This conclusion alone does not imply bounded descent of an abelian variety.

The bicanonical section orders, vertical denominator budget, curvature estimate and Hodge-metric sign have been checked at the level of the displayed argument. In particular the positive log210 term agrees with the fact that the induced sublattice 210 times a line has height lower by log210. The final additive budget is a separate exact numerical inequality and does not conceal an enlarged H.

The explicit upper bound log2(H)<4,783,227 is a true assertion about the specified number once its finite product is computed. It is not evidence that this number bounds the desired arithmetic height. The scalar fifth-factor detector correctly includes infinity and introduces no collision outside the fixed exceptional set.

Until Q and A are closed by accepted arguments, I approve only the conditional deduction of H5 and the original polynomial's conditional arithmetic interpretation. I do not approve an unconditional H5 or a claim that the original 15,671-witness polynomial has been proved to define Z from the presently established inputs.

## CM branch follow-up

The separate `height-cm/cm-height-proof.tex` passes this review under its explicit field, ramification and endomorphism hypotheses. Its saturation is defined over the same L: the image of E[f] under f alpha_i is alpha_i Lambda/Lambda, so the sum is precisely O_F Lambda/Lambda. The resulting quotient has maximal CM order. The tangent action embeds the quadratic field in L, giving the stated fundamental-discriminant bound without bounding the conductor of the original order.

The individual-embedding eta-product estimate bounds the stable height of the maximal-order elliptic factor. I checked the definition of Xi, the original stable-height normalization, and Theorem 1.9(1) in the published [Gaudron--Rémond monograph](https://smf.emath.fr/system/files/filepdf/smf_mem_176_0.pdf), printed pages 7–8. The general Xi-squared estimate applies over L with g=2 and requires no additional MM property. The isogeny-height comparison gives h_F(A)<854R, within the original CM allowance.

This repaired the CM branch only at that review stage. Subsequent update: `Q_ACCEPTANCE.md` closes Q using the published González–Rotger 2006 quotient theorem and exact branch recovery. The remaining unresolved H5 obligation is the bounded non-CM descent in A. `ALTERNATIVE_REVIEW.md` verifies a larger conditional numerical budget; it does not construct the required bounded, unramified splitting map.
