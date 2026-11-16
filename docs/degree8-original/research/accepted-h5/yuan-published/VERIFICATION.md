# Yuan source verification and normalization

Status: the author-attested English translation of the published article has been obtained and checked. The Chinese journal PDF has not been obtained or independently compared. The publisher currently returns a human-CAPTCHA response to the direct request. Do not describe this record as verification of the Chinese typeset text or assign Chinese page numbers to the English theorem locations below.

## Publication and translation evidence

The publisher identifies Xinyi Yuan's article as *Explicit Kodaira-Spencer Maps over Shimura Curves*, Acta Mathematica Sinica, Chinese Series **67**(2) (2024), 227–249, DOI [10.12386/A20220154](https://actamath.cjoe.ac.cn/Jwk_sxxb_cn/CN/10.12386/A20220154). Its Chinese title is 志村簇上的Kodaira—Spencer映射的具体公式.

In the automorphic-forms section of his [publication list](https://faculty.bicmr.pku.edu.cn/~yxy/publications.html), Yuan explicitly describes the linked PDF as an English translation of the published Chinese version. The page also has a general warning that linked files may differ slightly from published versions; this audit preserves that qualification.

The linked [English translation](https://faculty.bicmr.pku.edu.cn/~yxy/preprints/explicit_KS.pdf) is dated April 30, 2024 and has 32 pages. It is saved as `primary/yuan-author-translation.pdf`, SHA256 `ad751f65ac5730b437adbabba78cc6bc1fe1f2249367c74566fe0a495100740e`. The saved publication-list HTML is `primary/author-publications.html`, SHA256 `1353fa42f9436a51275726fd3f17c05670e1423328bcde501a4946879c28be5a`.

The previously checked arXiv v2 PDF has SHA256 `660f05465fd04f23c0458f6ed182c843341a0a4cfa69d4caa1812d0eb3920f14`. `compare_translation.py` compares all 32 pages after Unicode and whitespace normalization. Its full residual differences are recorded in `translation-comparison.json` and `translation-arxiv-diff.txt`: the arXiv banner and date, alternate extraction of epsilon and an injection arrow, and a stray extracted accent before a displayed identity on p.14. None changes a mathematical assertion. In particular, the main theorem and metric comparison have the same mathematical contents. This is a comparison of two English files, not an assertion that either file is byte-identical to the journal article.

## Exact locators and hypotheses

All page numbers in this section refer to the English translation.

1. Pages 1–2 fix an indefinite quaternion algebra B over Q, its discriminant d_B, a maximal order O_B, and an open subgroup U of the finite adelic units. The base is Z[1/n(U)], where n(U) is the product of primes at which U is not maximal. The moduli objects are abelian surfaces with O_B action satisfying the determinant condition and U level structure. An element mu with mu^2=-d_B specifies the positive involution and compatible principal polarization.
2. Section 2.1, pp.4–6, describes the regular Deligne–Mumford integral stack, semistability, smoothness away from d_B, and properness when B is division. The level U(3) scheme is used only over Z[1/3]. The printed sentence on p.6 saying a scheme results when U *contains* U(N) cannot be used literally for arbitrary U: even the maximal group contains U(N). Our application takes U=U(3), for which the usual level-three rigidity applies. No inference for a larger U is made from that sentence.
3. Page 7 defines the coarse Q-line bundle L_U as the relative dualizing bundle plus the horizontal orbifold divisor with coefficient 1-1/e_P at each ramified point. Lemma 2.1, pp.8–10, identifies its pullback with the corresponding bundle at a normal finer scheme level, and its stack pullback with the stack dualizing bundle. Page 10 states compatibility with the Petersson metric. Normality and the indicated integral bases must be retained when applying this statement.
4. Theorem 1.1, p.3, says that the determinant Kodaira–Spencer morphism from the square of the Hodge bundle to the square of the relative dualizing bundle is injective, has image d_B times that square, and is an isometry with the specified tensor metrics. Section 3 proves the integral statement; Sections 4.2–4.3, pp.20–26, compute the archimedean map and metrics.

## Constants in the H5 application

For an abelian surface and an invariant two-form alpha, p.2 defines the squared Hodge norm as

    ||alpha||_Y^2 = (2*pi)^(-2) * |integral alpha wedge conjugate(alpha)|.

Page 3 defines `||d tau||_Pet = 2 Im(tau)`. These are the conventions required in the H5 argument. With the original Faltings squared norm `2^(-2) * |integral alpha wedge conjugate(alpha)|`, one has `||.||_Y = pi^(-1) ||.||_F`, hence `h_Y = h_F + log(pi)` for a surface. This conversion is our elementary metric calculation; it is not a new theorem attributed to Yuan.

Set d_B=210. The image is the sublattice `210 * omega_base^2` with the metric induced from `omega_base^2`. Its height is `h(omega_base^2) - log(210)`: multiplication by 210 makes the local integral generator's archimedean norm larger by 210. The isometry therefore gives

    h(omega_base^2) = 2*h_F(A) + 2*log(pi) + log(210).

In particular the last sign is positive. The integral multiplier is 210, not its square or square root. One must not divide the Kodaira–Spencer map by 210 while retaining its isometry assertion unchanged.

The maximal integral stack exists over Z. The fine level-three object is over Z[1/3]; extension of a point at 3 must be justified using the maximal stack and potential good reduction. This source check does not replace that descent argument, the independent quotient-identification proof, or the non-CM modularity and height transfer.

## Recommended citation wording

“Yuan, Acta Math. Sinica (Chinese Ser.) 67 (2024), 227–249, Theorem 1.1 and Lemma 2.1; checked in the author's English translation, dated April 30, 2024, pp.2–10.”

The remaining provenance limitation is direct inspection of the Chinese journal text. The author's explicit translation attestation supplies a stronger published-source link than merely citing an unqualified arXiv preprint, but is recorded as an attestation rather than an independent translation audit.
