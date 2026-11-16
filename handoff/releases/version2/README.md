# Version 2 release evidence

The [published release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-12504-version-2)
contains the manuscript and two verified research handoffs.

| Archive | Bytes | Current tracked files |
| --- | ---: | ---: |
| Full handoff | 359,074,015 | 442 |
| Current-only handoff | 19,212,873 | 442 |

Both archives contain the exact public snapshot
`39e49cc9a7bebdb0569920824aec332e9e533efa`, plus the selected mathematical
history described in the handoff guide. This evidence directory was added
after that snapshot. It is not part of the archives and does not change
their contents.

- [Build receipt](BUILD_RECEIPT.json): both archives passed every member's
  CRC and SHA-256 checks, with an externally pinned plan.
- [Extraction receipt](EXTRACTION.json): the current-only archive also
  passed verification and extraction into a fresh directory.
- [Packaging tests](PACKAGING_TESTS.json): 34 malformed-input cases and
  successful self-scans of the scanner and test source.
- [Public asset check](PUBLIC_ASSET_CHECK.json): all seven uploaded asset
  digests agree with the reviewed files and build receipts.

The plan's SHA-256 is
`8ade1c2b1579a555c42e81645ebc8aa7f8bad50c488bb8419be71d422f5f0c1b`.
The release supplies the plan and checksums separately for authentication.

Public workflow records:

- [Archive build and verification](https://github.com/elliotglazer/diophantine-z-q/actions/runs/42153665225)
- [Complete quartic reproduction and manuscript build](https://github.com/elliotglazer/diophantine-z-q/actions/runs/42153648219)
- [Existing construction and Lean helper checks](https://github.com/elliotglazer/diophantine-z-q/actions/runs/42153648140)

These archive checks establish the integrity and stated contents of the
handoff. Mathematical review and certificate replay have the separate
scopes recorded in the manuscript's verification directory.
