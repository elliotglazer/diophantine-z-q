# Conductor and primitive level

Verdict: the published Carayol and Casselman results justify the conductor-level step for the stated weight-two primitive newform, with arbitrary nebentypus and arbitrary prime-power level. The integrating proof is `conductor-level.tex`. Both bibliography keys already occur in the baseline.

The check read the original printed pages, including Casselman's character convention and the continuation of his conductor remark across pages 306–307. It did not rely only on the frequently quoted one-dimensional newvector statement.

## Exact sources

William Casselman, *On some results of Atkin and Lehner*, Mathematische Annalen 201 (1973), 301–314. Theorem 1 is on page 302. Its concluding remark starts on page 306 and continues at the top of page 307: the exponent of the local epsilon factor is the conductor ideal defined by the newvector. The classical setup on page 309 allows an arbitrary character modulo the level. Theorem 4 on page 313 and its following paragraph identify the minimal global level with the conductor and characterize the newforms. [Author's publication list](https://personal.math.ubc.ca/~cass/research/publications.html), [research-hosted original scan](https://lesesvre.perso.math.cnrs.fr/newforms-references/casselman.pdf).

Pinned local PDF: `work/astra-t3-opus-reconciliation-001/primary/casselman-1973.pdf`. SHA256 `7f91ebae1a8f5e695800f4afb9fc06d0e2ea0b3a476751a31a7c8c3f38ad537d`. Read original images for printed pages 302, 306–307, and 309–313. This is the published 1973 article, not a later note about newforms.

Henri Carayol, *Sur les représentations l-adiques associées aux formes modulaires de Hilbert*, Annales scientifiques de l'École Normale Supérieure, series 4, 19 (1986), 409–468, DOI [10.24033/asens.1512](https://doi.org/10.24033/asens.1512). Theorem A in section 0.7 runs across pages 410–411. Sections 0.3–0.6 state the archimedean hypotheses, reciprocity, Hecke normalization, and unequal-residue-characteristic requirement. [Published scan](https://www.numdam.org/item/10.24033/asens.1512.pdf).

Pinned local PDF: `work/astra-t3-opus-reconciliation-001/primary/carayol-1986.pdf`. SHA256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`. Read the original pages 409–411. Theorem A covers every finite prime distinct from the coefficient characteristic. It has no restriction that the square of that prime not divide the level. In particular the exceptional dyadic cases omitted from the intermediate Theorem B are included in Theorem A.

## Hypothesis and convention checks

- The modular form is primitive after the finite character twist has been absorbed. Applying a primitive-level assertion before this last step would not suffice.
- Casselman permits arbitrary nebentypus. On the classical group, his epsilon(a)^(-1) equals epsilon(d), since ad is 1 modulo the level. There is no induced conductor shift.
- The automorphic representation is cuspidal, and its local components meet Casselman's irreducible admissible infinite-dimensional hypotheses.
- Carayol is applied over Q, whose degree is odd; no auxiliary discrete-series place is needed.
- The coefficient characteristic is five except at p=5, where it is three. The companion compatible-system argument must identify both with the same primitive f. This audit checks the subsequent local theorem application, not a new proof of that identification.
- Duality between Tate modules and cohomology, and the unramified norm twists in the normalization, preserve the conductor. The full local monodromy remains part of the conductor calculation.
- Carayol's remark cites an unpublished irreducibility observation, but that observation is not needed here. The constructed r_l is already irreducible; good trace matching and semisimplification identify it with Carayol's representation and force the latter to be irreducible.

The result is `a_p(r_5)=v_p(N)` for p different from 5, and `a_5(r_3)=v_5(N)`. There is no need to invoke a p-adic local-global compatibility theorem at equal characteristics.

No full paper was added to the repository by this check. The existing local source pins supply the evidence, and only original application notes were written. No heavy computation or build was performed.
