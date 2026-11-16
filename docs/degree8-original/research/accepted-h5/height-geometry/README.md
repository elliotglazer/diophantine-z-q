# Published closure of quotient input Q

The original five-contact quotient is identified by a published theorem: Gonzalez--Rotger, *Non-elliptic Shimura curves of genus one*, JMSJ 58(4) (2006), Theorem 4.2 and Table 2, pp. 938--939. The four required discriminant-210 quotients occur explicitly. Their exact modular identity comes from that theorem, not from matching numerical invariants.

[published-identification.tex](published-identification.tex) derives the original branch configuration from these published models. [check_published_quotients.py](check_published_quotients.py) checks the four rational j invariants twice (quartic and Jacobian equations) and tests all 36 cross-ratio pairs. The sole normalized pair is `(2401, -343/32)`. Its report is [published-quotient-check.json](published-quotient-check.json).

Run the checker with ordinary Python 3; it uses only `fractions`, `pathlib`, and `json` and takes less than one second in the audit environment. [source-application-ledger.json](source-application-ledger.json) records the exact publication, notation, theorem pages and hash of the downloaded publisher PDF. The PDF is a local research copy and need not be copied into a distributable package.

This closes Q without the newer Padurariu--Saia preprint. It does not close the separate arithmetic, integral-model, or Hodge-comparison obligations in the original H5 proof, and does not transfer approval to the complete 15,671-witness theorem.
