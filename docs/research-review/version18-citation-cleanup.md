# Version 18 citation and prose-cleanup delta

This additive record describes the cleanup candidate `manuscripts/quartic_v18.tex`, SHA256 `dfdc13b3d184c0f94658f15311bebaa9aa1e863f8b198a09f8caa6e4f45dc32b`, relative to the mathematical text merged in PR98, SHA256 `8f4a6a99ce63b1bf6c7ab2fe71507795507a94281a775bf02fa07ca2be9359ae`. Line numbers below refer to the candidate. It leaves the historical PR98 dependency record intact. It is a review submission, not an independent-acceptance record.

## How to review this delta

The [complete change map](version18-cleanup-changes.md) locates every changed block. Its index gives base-manuscript lines, head-manuscript lines, and the lines to read within the map itself. Read the paired ranges at `base` and `head` to compare the exact text. The inventory is generated from the two source hashes above; a local reconstruction check covers the full diff. Categories are author navigation aids, not reviewer judgments. The first-round concern that reviewers had to discover the changes in a 45,000-line file was justified.

The added source locators and the short arguments below require source-to-consumer review. The broader change map also contains prose, notation, status and archival-link edits; none is silently excluded from this PR's scope. Unchanged proofs need not be read anew merely because they are adjacent to a changed paragraph, but the mathematical effect of every changed block must still be assessed.

## Source applications and short explanations

| Passage | Source and hypotheses | What the text uses |
|---|---|---|
| Local control, lines 19094-19129 and 19168-19197 | Nekovar, *Selmer complexes*, Asterisque 310 (2006), Corollary 8.4.8.2(i), p.215; Kato, Asterisque 295 (2004), (12.2.3), p.220. The actual coefficient is a finite free quadratic twist over the local real cyclotomic Z2 tower. | The specialization injection, local duality, and Nakayama show that the local characteristic element has no factor at the augmentation prime. Inverting 2 permits the fixed finite-sign decomposition. The two repeated applications now use the same argument. No new global H3 assertion is made. |
| Atkin–Lehner, lines 8969-8989 and 20428-20462 | Atkin–Lehner, *Hecke operators on Gamma_0(m)*, Math. Ann.185 (1970), Lemma8 p.138, Lemma9 p.139, Theorem3(iii) p.147, Lemma33(iii) p.156 and Theorem6 p.157. Divisors of the level are exact; the twist conductor actually used is odd and prime to the old level. | Cusp permutation and the differential give the translation formula. An explicit weight-two Mellin calculation supplies the global minus sign. Successive Legendre twists give the existing odd quadratic-twist formula. This is not a claim covering an arbitrary even twist conductor. |
| Quadratic Gauss sums, lines 18859, 18892 | Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem9.17, p.300. Primitive quadratic character and signed fundamental discriminant, with the manuscript's positive-exponential convention. | The existing signed square identity, including even discriminants. |
| Kummer pairing, lines 9644-9680 | Guillot, *A Gentle Course in Local Class Field Theory* (2018), Lemma1.20 and Theorem1.22, pp.11–13. Characteristic zero, the required roots of unity, and the finite radical subgroup. | The pairing for the actual possibly dependent radicands; no independence of the radicands is assumed. |
| Split-cubic halving, lines 22297-22325 | Direct tangent-line argument over a field of characteristic different from two with distinct split roots. | Only the necessary implication that halving a nonzero two-torsion point makes both root differences squares. No unavailable Bekker–Zarhin theorem number is imported. |

The relevant final source pages were inspected in local preparation, including the publisher-formatted Montgomery–Vaughan chapter and Guillot preview that contains the required pages. This statement records preparation scope, not a substitute for this PR's two reviewers. Public access points are [Nekovar](https://www.numdam.org/item/AST_2006__310__R1_0.pdf), [Kato](https://www.numdam.org/article/AST_2004__295__117_0.pdf), [Atkin–Lehner](https://doi.org/10.1007/BF01359701), [Montgomery–Vaughan chapter](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf), and [Guillot preview](https://api.pageplace.de/preview/DT0400.9781108389860_A35309221/preview-9781108389860_A35309221.pdf).

The remaining source changes are as follows. These are source-to-consumer statements for review, not claims to have independently verified each paper's full proof.

| Existing application | Citation or clarification | Retained limits |
|---|---|---|
| Surface Tate determinant and coefficient-prime-independent trace, lines 2589-2589, 2601-2612, 2642-2654, 5735-5743, 6567-6597, 13516-13539 | Milne, *Abelian varieties* (1986), Section16 for the polarization pairing and Proposition12.9 for the endomorphism characteristic polynomial. [source 1](https://www.jmilne.org/math/articles/1986b.pdf) | The Tate-module convention is unchanged. The rank-four symplectic determinant is the square of the multiplier. |
| Division-polynomial recursion, lines 5372-5402 | Silverman, *The Arithmetic of Elliptic Curves*, ExerciseIII.3.7, with the author's 2015 correction for pp.105–106. [source 1](https://www.math.brown.edu/johsilve/AEC/AECErrata2015.pdf) | The actual formulas are unchanged; the citation now identifies the corrected numerator convention. |
| Primitive-form extraction, lines 2581-2595, 5661-5677, 5745-5775 | Deligne–Serre (1974), Sections1.6–1.9, pp.509–510, and the existing PartI modularity argument. [source 1](https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/) | The primitive twisting character uses its least conductor. Li's uniqueness and Fricke statements remain separate inputs. Chebotarev and semisimplicity identify the same representation. |
| Pan local-ring inputs, lines 2579-2579, 5778-5797 | Allen–Newton–Thorne (2020), Section3.1, Proposition3.1. [source 1](https://doi.org/10.1112/S0010437X20007484) | The published correction concerns the nilreduction of the trivial-character local ring. The separate project argument for distinct-character integral flatness is still identified as such. The final-Pan-body access limitation remains. |
| Dyadic character restriction, lines 6617-6642 | Serre, *Local class field theory*, Section2.4, p.141, norm functoriality. | The restriction is composition with the norm. The norm of a unit is a unit, and the quadratic local character has conductor at most four. The existing ramification argument then applies. |
| Ring-class fields and conductor kernels, lines 8865-8877, 8918-8926, 9068-9086, 9209-9213, 9673-9689 | Cox (1989), Sections7 and9, Proposition7.22, the proof of Theorem7.24, and Lemma9.3. [source 1](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf); [source 2](https://dacox.people.amherst.edu/primes/typos2.pdf); [source 3](https://dacox.people.amherst.edu/primes/typos3.pdf) | Cox prints the order-to-maximal-order sequence; the relative sequence is derived in the manuscript by comparing its two idelic quotients. The order conductor remains arbitrary. The arguments explicitly account for the only global units, plus or minus one, and for rational principal ideals prime to the conductor. |
| Unramified reduction and local cocycles, lines 7009-7026, 9135-9168, 12474-12487, 14863-14879 | Silverman VII.2.1–VII.2.2 and Lang (1956), Theorem1 and its corollary. | The model is minimal integral, the extension is unramified, and the connected smooth special fibre is the object to which Lang applies. |
| Global-to-local Brauer comparison, lines 2553-2555, 6495-6514, 13443-13465 | Milne, *Arithmetic duality theorems*, I.1.6(b), and proof of II.2.1, p.164. [source 1](https://www.jmilne.org/math/Books/ADTnot.pdf) | This repeats the source already used for the same comparison elsewhere in the manuscript. |
| Product decomposition at no greater stable height, lines 3214-3232, 36192-36230 | Remond (2017), Theorem1.6, p.1175, as a structural input to the existing Gaudron–Remond construction. [source 1](https://ems.press/content/serial-article-files/38664?nt=1) | This is not a claim that the 2017 theorem itself proves height monotonicity. The unverified final-2022-source comparison is still explicit. |
| Rooted-forest minors, lines 22444-22471 | Chaiken (1982), the all-minors matrix-tree identity. [source 1](https://epubs.siam.org/doi/10.1137/0603033) | This is a polynomial identity and does not require an invertible Laplacian. The manuscript's separate symbol and contraction identities still need their own proofs. |
| Natural-valued arguments to the precision circuit, lines 11944-11957, 12236-12253 | Direct traversal of the frozen arithmetic circuit, SHA256 `f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`. | All three arguments of each of 15,845 calls were checked using nonnegative constants, natural variables, addition and multiplication. Call outputs were not assumed nonnegative to prove their own arguments. |
| Maximal-stack height comparison and singular moduli, lines 13271-13282, 35691-35695 | Existing stack argument and a distinct Gross–Zagier (1985) singular-moduli bibliography key. [source 1](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1515/crll.1985.355.191/fulltext.pdf) | No coarse-model pullback is imported from Yuan's Lemma2.1. The separate Gross–Zagier Heegner-points reference remains unchanged. |
| Waldspurger locator correction, lines 19657-19673 | Waldspurger (1981), Proposition 17 and proof pp.461–465; Proposition 18 and proof pp.466–476; Lemma 41 and proof p.476. [source 1](https://mate.dm.uba.ar/~nsirolli/files/waldspurger.pdf) | Changed 19669–19673. These exact pages were visually compared in the local source comparison. The existing ICM citation is retained; this is not a new whole-theta-lift audit. |
| Deligne homogeneous-polarization bibliography correction, lines 6080-6087, 6093-6105, 44836-44839 | Deligne, Travaux de Shimura (1971), Variante 4.8, p.146. [source 1](https://www.numdam.org/item/SB_1970-1971__13__123_0.pdf) | The bibliography range now includes §4.8 at 44839, matching the existing consumer 6087. Page146 was visually compared in the local source comparison. |

An unused Berger citation is removed. Uncompared final source editions and other qualifications remain explicit. Proposed changes to the local GI proof's all-limit convention were withheld; this PR does not adopt them.

## Primary-source access and remaining limits

For Atkin-Lehner, the [official Göttingen article PDF](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0185/LOG_0035.pdf) was downloaded again during this repair and matches the checked scan exactly: 2,659,681 bytes, SHA256 `18ca10d80324eeba53190fe06ebbfcd0a3d981e9a643e0e1b753b416b0ee1c91`. The [institutional IIIF manifest](https://manifests.sub.uni-goettingen.de/iiif/presentation/PPN235181684_0185/manifest) identifies the article as `LOG_0035`. The PDF has one library cover, then printed pages 134-160. The following institutional text endpoints also returned HTTP 200 during preparation. Their OCR needs comparison with the scan for mathematical symbols.

| Required result | Printed page | Institutional OCR |
|---|---:|---|
| Lemma 8 | 138 | [Page 138](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000148.xml) |
| Lemma 9 | 139 | [Page 139](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000149.xml) |
| Theorem 3(iii) | 147 | [Page 147](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000157.xml) |
| Lemma 33(iii) | 156 | [Page 156](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000166.xml) |
| Theorem 6, converse | 157 | [Page 157](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000167.xml) |

Successful local access does not establish that a review provider can fetch the same endpoint. No scan or long excerpt is included in this PR. The exact manuscript consumers and the weight-two sign computation are indexed above.

Nekovar's book erratum is [selerr.pdf](https://webusers.imj-prg.fr/~jan.nekovar/pu/selerr.pdf), linked under *Selmer complexes* on his [publications page](https://webusers.imj-prg.fr/~jan.nekovar/pu/). It is not the separate erratum for the parity paper. The retrieved author-indexed first page lists corrections starting at 9.5.6.1 and in chapters 11-12, with no entry for 8.4.8.2. Fresh requests for the complete file returned 403 or timed out. Thus no relevant correction was found in the material obtained, but a full-current-file erratum check remains incomplete. The printed local-control corollary itself was checked in preparation and by Astra in round one; that does not resolve this narrower access limitation.

The first-round reports also record failed access to Guillot and Cox by Fable. The source URLs and exact consumers in this note are offered for a new attempt, not as evidence that those access failures have already been resolved. A reviewer who still cannot verify a required source should preserve that limitation in the decision.

## P01 and preserved mathematical scope

P01, line 2236, now names the printed row specification. The original private residual-system blob and the public blob are both `de0593d2d8629fc6fc29d47a3f5e7030b295f6e2`, SHA256 `b15d6477439c3e4be1e98723b69053244debce59e8715683c28fee82aa847ca4`. Their expanded-polynomial blobs also agree, SHA256 `9f461531df52ac73e02cf7a4ce270422715642c0d3112952cad4968d9a7e24ea`. Parsing the candidate checked all 214 coordinates, all 188 residuals and all 1,008 terms against that exact system. This justifies the locator change; it does not prove the arithmetic theorem.

Every theorem, proposition, lemma, corollary and definition environment and every label is byte-identical to PR98's mathematical text. The polynomial and variable count are unchanged. The existing local GI proof remains present, including its bounded-normalization and increment-group arguments. No Candela–Szegedy replacement is adopted here. Neither Version16 nor Version17 is edited; the official-record selector is unchanged.

The prose pass replaces task names and internal review references with existing mathematical sections, removes administrative history from the exposition, and repairs converted text and notation. It preserves the AI-use statement and attribution. The source catalogue retains source-version limitations. These prose changes do not turn an unverified source or conditional input into a proved assertion.

Seventeen existing supplement/index targets were checked byte-for-byte between the PR98 merge commit and archive commit `005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f`. Their bibliography links now name `review-archive-v17`, so removing archived evidence trees from main does not break the citations. This verifies identity of the linked files, not correctness of their mathematical content.

For the precision-argument assertion, the saved object is `construction/precision-natural-polynomial.json`, SHA256 `f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`. The preparation traversed all 293,620 nodes in topological order. It certified a node only if it was a nonnegative integer constant, a source natural variable, or an addition/multiplication of already certified nodes. Power-call outputs were not marked certified merely because they were outputs. It then checked all three input references of each of the 15,845 calls against that certificate set. There were no malformed references and no uncertified call arguments. This describes a reproducible finite check, not an independent mathematical acceptance.

## Review status moved out of the exposition

The owner requested removal of review-process language from the manuscript body. This includes qualifications about historical review status, not only file paths and typesetting. The first PR description did not make that distinction sufficiently explicit. This section carries those qualifications forward; deleting their repeated sentences from the exposition neither resolves an open finding nor promotes a component to accepted status.

The complete change map locates the exact removed sentences and their surrounding text in both versions. The table below indexes every changed block containing old review, acceptance or author-status language, including blocks where the wording was merely moved or rephrased. It is deliberately broader than the five examples in Fable's finding; no historical review file is edited.

In particular, the abstract's statement that this is an author proposal conferring no release acceptance is removed from the exposition, as are the separate pending-review sentences for the 214 assembly and the uniform-existence note. The mean-two/LP13 bibliography's pending independent acceptance and the tautification bibliography's independent scope decision are also removed. The provenance paragraphs no longer repeat that the reviews were internal model reviews rather than human peer review or formal verification. Each of those limitations is retained explicitly below. This is a relocation of review-status information, not evidence that any pending review was completed.

The following limits continue to apply to the submitted Version 18 draft:

- It is an author assembly submitted for review. The finite checks establish the specified algebraic and computational facts, not the full arithmetic theorem, universal completeness, or a numerical defining parameter.
- Historical source, component and Version 16/17 acceptances retain only their original scope and bindings. They do not independently accept the new 214-variable assembly, its changed applications, or this complete TeX/PDF.
- The geometry/modularity source carries, the uniform-existence argument, height and aggregate applications, and every changed source-to-consumer join still require the review appropriate to this submission. The old text's pending status is not treated as a new mathematical objection, nor as an already completed review.
- The local inverse proof remains present. In particular, the mean-two join, LP13 and related applications, and the tautification unit do not gain independent acceptance from this prose edit. The planned inverse-theorem adoption is a separate PR and is not assumed here.
- Existing source-version and access limits remain, including the final Pan comparison and the final 2022 Remond source comparison. The new access limits above are explicit too.
- Historical model reviews are not independent human peer review or full formal verification. Neither is claimed for this manuscript. The official-record selector and published Version 16/17 files are unchanged; this PR does not promote a new official release.

A later Protocol B decision must be read at its stated source and dependency scope. It does not automatically close every inherited historical item. The original status wording remains reachable in the PR98 merge, and older records remain at `review-archive-v17` where already archived.

| Change-map block | Old manuscript lines | Candidate lines | Status carried forward |
|---|---|---|---|
| [H001](version18-cleanup-changes.md#h001) | 75-82 | 75-81 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H002](version18-cleanup-changes.md#h002) | 183-202 | 182-194 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H003](version18-cleanup-changes.md#h003) | 1993-2015 | 1985-2007 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H004](version18-cleanup-changes.md#h004) | 2050-2076 | 2042-2065 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H005](version18-cleanup-changes.md#h005) | 2085-2105 | 2074-2096 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H006](version18-cleanup-changes.md#h006) | 2111-2155 | 2102-2150 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H010](version18-cleanup-changes.md#h010) | 2212-2241 | 2207-2239 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H011](version18-cleanup-changes.md#h011) | 2244-2254 | 2242-2258 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H013](version18-cleanup-changes.md#h013) | 2274-2282 | 2278-2286 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H016](version18-cleanup-changes.md#h016) | 2326-2370 | 2330-2374 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H019](version18-cleanup-changes.md#h019) | 2422-2464 | 2426-2476 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H020](version18-cleanup-changes.md#h020) | 2466-2524 | 2478-2542 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H022](version18-cleanup-changes.md#h022) | 2554-2584 | 2572-2602 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H024](version18-cleanup-changes.md#h024) | 2614-2622 | 2632-2640 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H026](version18-cleanup-changes.md#h026) | 2638-2664 | 2656-2684 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H028](version18-cleanup-changes.md#h028) | 2762-2768 | 2782-2788 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H029](version18-cleanup-changes.md#h029) | 2780-2802 | 2800-2819 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H031](version18-cleanup-changes.md#h031) | 2846-2866 | 2863-2883 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H032](version18-cleanup-changes.md#h032) | 2892-2944 | 2909-2959 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H033](version18-cleanup-changes.md#h033) | 2968-2992 | 2983-3008 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H036](version18-cleanup-changes.md#h036) | 3036-3053 | 3052-3074 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H044](version18-cleanup-changes.md#h044) | 3186-3202 | 3207-3227 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H045](version18-cleanup-changes.md#h045) | 3216-3222 | 3241-3247 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H046](version18-cleanup-changes.md#h046) | 3252-3271 | 3277-3296 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H048](version18-cleanup-changes.md#h048) | 3300-3374 | 3325-3408 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H059](version18-cleanup-changes.md#h059) | 3648-3674 | 3682-3710 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H060](version18-cleanup-changes.md#h060) | 4252-4275 | 4288-4314 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H062](version18-cleanup-changes.md#h062) | 4311-4358 | 4350-4389 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H064](version18-cleanup-changes.md#h064) | 4386-4644 | 4415-4643 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H066](version18-cleanup-changes.md#h066) | 4704-4745 | 4703-4742 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H068](version18-cleanup-changes.md#h068) | 5004-5010 | 5001-5006 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H069](version18-cleanup-changes.md#h069) | 5012-5018 | 5008-5013 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H070](version18-cleanup-changes.md#h070) | 5020-5026 | 5015-5020 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H071](version18-cleanup-changes.md#h071) | 5028-5034 | 5022-5027 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H072](version18-cleanup-changes.md#h072) | 5036-5042 | 5029-5034 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H073](version18-cleanup-changes.md#h073) | 5044-5050 | 5036-5041 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H074](version18-cleanup-changes.md#h074) | 5052-5058 | 5043-5048 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H075](version18-cleanup-changes.md#h075) | 5060-5066 | 5050-5055 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H076](version18-cleanup-changes.md#h076) | 5068-5074 | 5057-5062 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H077](version18-cleanup-changes.md#h077) | 5076-5082 | 5064-5069 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H079](version18-cleanup-changes.md#h079) | 5117-5161 | 5104-5131 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H083](version18-cleanup-changes.md#h083) | 5787-5813 | 5759-5777 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H100](version18-cleanup-changes.md#h100) | 15282-15288 | 15277-15283 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H103](version18-cleanup-changes.md#h103) | 17987-17996 | 17982-17991 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H114](version18-cleanup-changes.md#h114) | 26468-26474 | 26497-26503 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H128](version18-cleanup-changes.md#h128) | 28209-28222 | 28238-28251 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H149](version18-cleanup-changes.md#h149) | 29523-29530 | 29552-29559 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H150](version18-cleanup-changes.md#h150) | 29555-29564 | 29584-29593 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H151](version18-cleanup-changes.md#h151) | 29623-29629 | 29652-29658 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H152](version18-cleanup-changes.md#h152) | 29734-29740 | 29763-29769 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H153](version18-cleanup-changes.md#h153) | 29780-29786 | 29809-29815 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H154](version18-cleanup-changes.md#h154) | 29936-29942 | 29965-29971 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H156](version18-cleanup-changes.md#h156) | 31126-31137 | 31154-31164 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H161](version18-cleanup-changes.md#h161) | 31592-31598 | 31619-31625 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H162](version18-cleanup-changes.md#h162) | 31600-31612 | 31627-31638 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H165](version18-cleanup-changes.md#h165) | 31842-31849 | 31868-31874 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H169](version18-cleanup-changes.md#h169) | 33679-33694 | 33702-33716 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H170](version18-cleanup-changes.md#h170) | 33721-33732 | 33743-33750 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H171](version18-cleanup-changes.md#h171) | 33744-33750 | 33762-33768 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H172](version18-cleanup-changes.md#h172) | 33867-33873 | 33885-33891 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H173](version18-cleanup-changes.md#h173) | 33964-33971 | 33982-33989 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H178](version18-cleanup-changes.md#h178) | 38786-38792 | 38805-38811 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H179](version18-cleanup-changes.md#h179) | 38795-38801 | 38814-38820 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H203](version18-cleanup-changes.md#h203) | 44851-44857 | 44888-44894 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H205](version18-cleanup-changes.md#h205) | 45029-45037 | 45066-45074 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H207](version18-cleanup-changes.md#h207) | 45209-45238 | 45246-45273 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H208](version18-cleanup-changes.md#h208) | 45333-45339 | 45368-45374 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H210](version18-cleanup-changes.md#h210) | 45408-45431 | 45440-45455 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H211](version18-cleanup-changes.md#h211) | 45433-45442 | 45457-45463 | Exact historical qualification in the removed text; no new acceptance inferred. |
| [H213](version18-cleanup-changes.md#h213) | 45455-45463 | 45502-45510 | Exact historical qualification in the removed text; no new acceptance inferred. |

## First-round findings

At head `9b34ffb9902f8a0086e5f2efa434bb6076e4eda5`, both reviewers requested changes. Their original reports remain public: [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/107#issuecomment-6887125044) and [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/107#issuecomment-6887128932). This repair is submitted against all five findings:

| Finding | Repair offered; limitation retained |
|---|---|
| `43661223026-1-astra-S107` | Official Atkin-Lehner scan and five exact institutional page endpoints, plus complete consumer ranges. Provider access still requires the reviewer to test it. |
| `43661223026-1-astra-C107` | Complete change map and exact application ranges, P01 identity evidence, and a reproducible description of the precision-argument check. The earlier incomplete review is not reused as acceptance. |
| `43661223026-1-fable-F107-1` | Every source application is located; the change map includes every changed block with both source and map line ranges. |
| `43661223026-1-fable-F107-2` | Better primary access and explicit remaining source-access limits. No claim that an inaccessible source was verified by Fable. |
| `43661223026-1-fable-F107-3` | Exact locators for removed status text in the change map and the continuing component/assembly qualifications above. The PR description now discloses the removal of review-status language. |

These are proposed dispositions for fresh reviewer decisions, not author-issued closure of the findings.

## Validation and acceptance limits

The full candidate builds in three LaTeX passes with no undefined reference or citation and no further cross-reference run requested. Its PDF SHA256 is `dd2aadbe8cbf95c907a9a4a75d180c0d0d51a70afcf60a8ec6aafaeeb0918009`. Statement/label comparison and the independent printed-row parser passed on the same source hash. The PDF is a local validation artifact; this PR updates the draft source, not the official TeX/PDF release pair.

This record has not approved itself. Protocol B must review the source-application and prose changes at the final PR head. The old PR98 reviews and override remain historical and do not stand in for this review.
