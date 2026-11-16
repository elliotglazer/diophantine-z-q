# Arithmetic proof packets and assumptions

The parity, anchor, sieve, and published quotient packets supply proofs for the unchanged original polynomial. Their small programs check finite identities and local constants. The parity proof uses the baseline restricted-converse theorem RC at the baseline manuscript's stated proof status. The accepted V4 manuscript proves the original five-contact height assertion H5, using a level bound for the non-CM fibers and a same-field estimate for the CM fibers. Successful checker output does not establish H5 or independently reprove the baseline arithmetic results.

Run only the small computations, without rebuilding or expanding the polynomial:

```sh
python degree8-original/check.py --tiny-only
```

The same checks also run as part of the ordinary package check. Each component script runs independently from any working directory, uses only the Python standard library, and writes no files unless `--output PATH` is supplied.

| Packet | Proof and assumptions | Small computation |
| --- | --- | --- |
| `parity/` | The four literal seven-witness residuals have the required one-sided valuation property. Completeness uses the baseline RC theorem at its stated proof status after constructing parameters in its exact domain; it introduces no stronger simultaneous-realization assumption. | All four literal module rows, 128 local square classes, 256 signed multipliers, and exact rescaling identities |
| `anchor/` | Koenigsmann's published Proposition 6 gives the semilocal predicate. The stated generator input and local formal-group calculations give the exact nonzero index set `2*3^(2^23-1) Z`. The accepted H5 theorem supplies the fixed numerical constant required by the height cutoff. | Six literal anchor rows, 25 shared-chain rows, root wiring, curve change, local valuations, and the numerical cutoff implication |
| `sieve/` | The original 41-position prime pattern and common-J construction follow from the stated published prime-distribution and elliptic-curve inputs, with the baseline's recorded correction/version convention for the inverse theorem. No Sun cross-prime order theorem is used. | Exact lattice constants, collision exclusions, and local admissibility witnesses at 31, 37, and 41 |
| `geometry/` | Gonzalez–Rotger's published Theorem 4.2 identifies the four labeled quotient curves. This closes the quotient-identification input Q without the Padurariu–Saia preprint. | Quartic and Jacobian invariants, and all 36 cross-ratio pairs giving the unique labeled branch configuration |

The baseline generator input is `2E(K) = Z P` for `K=Q(sqrt(2))`, `E: y^2=x(x^2-(11-6sqrt(2)))`, and `P=(57/8-(7/2)sqrt(2), -165/8+(417/32)sqrt(2))`, together with its stated height and formal-group consequences. The baseline manuscript is pinned by SHA-256 `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`.

RC is the baseline restricted-converse theorem for `E_l: y^2=x(x-l)(x+3l)`: for every positive squarefree integer `l` congruent to 11 modulo 12, two-primary Selmer corank one implies analytic rank one. Its use here preserves the baseline manuscript's stated proof status. Parity completeness also uses the standard descent, Kummer, Cassels–Tate, and forward analytic-rank-one results recorded in `parity/AUDIT.md`. That document identifies the exact baseline labels and source lines. The small computational checks do not independently reprove RC.

## Exact H5 theorem in the current proof

Let `S*` be the primes at most 76176, `B*` their product, and

```text
H = 2 (4608^165888 + 6^100) B*^24 + 128.
```

For a reduced rational `s=U/V` outside `{infinity,0,1,2401,-343/32}`, let `M(s)` be the product of primes outside `S*` at which one of `V, U, U-V, U-2401V, 32U+343V` has odd valuation. The accepted theorem proves `h(s) <= H M(s)^24`, for absolute logarithmic Weil height. The numerical bound `log2(H) < 4783227` concerns this specified number; it does not prove that H bounds these heights.

The current non-CM proof obtains this estimate through a modular level bound and arithmetic height comparisons. It allows the scalar-character order and coefficient field to vary; it does not assume bounded same-field descent to a rational GL2-type variety. The same-field CM estimate supplies the other branch. The excluded von Känel–Kret preprint is not used. The exact accepted manuscript is pinned in [current-proof.json](current-proof.json), together with the independent acceptance record. This is a mathematical and source review, not formal proof certification.

The former quotient-identification obligation Q is closed by Gonzalez–Rotger, *Non-elliptic Shimura curves of genus one*, Journal of the Mathematical Society of Japan 58(4) (2006), Theorem 4.2 and Tables 2–3. The theorem identifies the quotient curves, while the small computation verifies the exact labeled branch recovery. The source ledger separates these two roles. Closing Q does not by itself establish H5.

`assumption-status.json` records these distinctions in machine-readable form. It is a status record, not an extra certificate accepted by the checker.

## Source records

`packet-provenance.json` pins the received packet files and the portable copies. Component ledgers retain publication URLs, exact theorem locations and hashes of inspected sources. Historical local source identifiers in those ledgers are evidence records, not runtime paths or a claim that the publication files are bundled. No full publication PDF is included. `reference-*.json` files preserve the authors' original small-check receipts; new runs compute their own results. The source archive and polynomial coefficients remain unchanged.

## Current and historical records

The current manuscript proves the H5 theorem under label `hyp:o8-height`, uses the non-CM level argument under `sec:h5-level-repair`, and states the original polynomial's arithmetic interpretation under `thm:o8-conditional`. The last label is retained for reference stability; its name does not make the current theorem conditional. The baseline arithmetic results retain their previously stated proof status.

The component proof packets and their receipts remain unchanged as received. Their earlier references to H5 as an assumption describe the scope of those component arguments. The accepted current H5 proof discharges that input in the assembled manuscript. [Earlier package status documents](history/pre-h5-v4/index.json) are preserved byte for byte and explicitly marked historical. The small-check output still describes its finite computational scope; it does not replace the mathematical proof.
