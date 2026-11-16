# Independent review of the Version 2 handoff

Static verdict: PASS for the versions below. No unresolved blocking design
or implementation issue was found after the repairs described here.
Archive construction, the small negative tests and clean extraction have
not been executed by this reviewer. They remain required remote checks.
This review changes neither the mathematical claims nor their proof scope.

| Reviewed file in `handoff/` | SHA256 |
| --- | --- |
| `prepare_handoff.py` | `043e550538c97ec20439193dec6de0cfed94d3083177b5c75d38baee5f56eed4` |
| `build_handoff.py` | `91cced122167e5d480d6112b5c74a8a0c87bc9847c18492f6f4691787a61a10a` |
| `verify_handoff.py` | `c9c8d47dbc934bd7c4695bd040c018e7f41bab39a8eb5076e99b05dbe73e1373` |
| `test_handoff.py` | `ca3b3fb848e2ff38c353fd3aecbd9b0f124e18711f68572dde8fba79fa8b6bdd` |
| `selection.json` | `33e18317dcfae645718d58cc5398f0b7a8b3a0129355dd8c04d150de5c1492b8` |

## Coverage and provenance

The current collection is the complete regular-file tree of one immutable
public Git commit. The preparer reads the Git tree and blobs rather than
copying an uncommitted working directory. The builder independently compares
the complete path/blob mapping with that commit. It requires each Git item
to appear at exactly `current/` followed by its original path. Missing Git
files, duplicate sources, changed blobs and remapped destinations fail.

The current snapshot must contain the manuscript TeX/PDF, the current proof
inventory and a passing full reproduction receipt. Every file named by the
quartic reproducibility manifest must match its exact size and digest.
The archive verifier additionally pins the final polynomial, named checker,
certificate, source residual stream, source entry, source audit and
construction map. It requires every audited source file listed in the
byte-pinned source entry, even if someone reduces the separate package
manifest. It also checks all package-manifest entries against the outer
archive inventory.

The full archive carries the public November 4 revision-2 ZIP unchanged,
with 339,860,770 bytes and SHA256
`827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`.
The builder checks that identity before copying it with ZIP_STORED, and
the verifier rechecks its bytes. The current-only archive omits it and
provides the public retrieval URL and exact identity. Neither archive
claims to contain the private-v5 handoff or every later research file.

The historical baseline retains its recorded filtering and mathematical
scope. It is not represented as a freshly audited current source. The older
local `VALIDATION_RECEIPT.json` under the November 4 work directory binds
revision 1, so it is correctly not used to validate revision 2 here.

The selection has 20 files: 18 mathematical history files and two new
orientation notes. A lightweight independent size/hash comparison confirmed
all 20 payload files agree with their selection records and named original
files. In particular, no source proof or historical verdict was rewritten
to make its former status agree with the present result.

## Content and scope

The selected history contains standalone mathematical proofs, reviews,
circuit programs and one finite-check summary. It contains no conversation
transcripts. A focused path-only pattern scan found no serialized dialogue,
credential marker or private-repository URL in those payload files. This
review did not rescan the large historical baseline or an as-yet-unbuilt
current archive. The preparer scans every actual new Git/payload byte before
freezing the plan, including bounded decompression of gzip text.

The explicit selection excludes unpublished third-party comparison inputs,
private source collections, access records, job payloads and unrelated
working files. Original local path references in mathematical reviews are
provenance locators, not credentials or a claim those paths exist after
extraction. Public Git content and the selected history are distinct from
the private-v5 inventory that informed the selection.

`COVERAGE.md`, `RESEARCH_NOTES.md`, the generated start page and current-state
record distinguish the exact 12,504-variable result from the former
15,671-witness source, the November 4 baseline and unadopted low-precision
circuits. They preserve the separation between algebraic verification,
source arithmetic and the incomplete Lean formalization. The low-precision
rerun commands point to the included frozen builder and programs, use
`-E -B`, and do not claim a different accepted integer-defining source.

The snapshot commit is distinguished from any later metadata-only commit
adding archive checksums or receipts. The notes do not claim that an archive
contains the later commit that records its own hash. "Self-contained" is
qualified to the included collections, not all research history or every
external mathematical reference.

## Integrity and recovery

The archive manifest covers every entry other than itself. The verifier
checks exact entry-set equality, entry sizes and SHA256 digests, and ZIP CRCs
by reading each entry to completion. It compares embedded-plan paths and
hashes with the outer inventory. The builder passes an external plan digest
to this verification, and the public CLI supports that same check.

An embedded manifest alone cannot authenticate a claimed Git origin. The
start page and coverage note correctly require a separately obtained
published archive checksum or plan digest. The verifier reports whether
the plan was externally bound and states this limitation explicitly.

Extraction first verifies the archive, requires a new destination, rejects
absolute paths, traversal, drive/backslash names, nonregular entries,
symlinks, duplicate and case-colliding names, trailing dot/space components
and ordinary Windows device names. Each output path must remain inside the
destination, is created exclusively, and is checked against its recorded
digest after writing. The current snapshot and nested baseline are restored
to distinct locations. No proof script, historical worker or network
operation is automatically launched by recovery.

## Repairs reviewed and remaining execution

The initial draft omitted credential-field checks on decompressed gzip
content, allowed a modified plan to remap Git blobs to other archive paths,
and checked only a self-described current inventory. Those issues were
repaired with one shared content scan, bounded decompression, exact Git
source/destination checks, package closure checks, embedded-plan matching
and optional external plan authentication. Windows device and trailing
dot/space names are now rejected as well.

The 16 small negative fixtures cover unsafe paths, swapped or missing Git
files, raw and gzip credential fields, case collisions and a symlink.
They require the intended ValueError reason, so an unrelated exception is
not silently counted as success. The actual archive builder performs a
complete positive verification for both produced ZIPs and records their
external hashes.

Before publication, run the small tests, build from the final committed
public snapshot and its fresh reproduction receipt, verify both archives
with the frozen plan digest, and perform a fresh extraction check. Confirm
that uploaded asset hashes match the build receipt and publish the archive
and plan identities with links identifying the full and current-only
variants. These are execution and publication checks, not new permission
requirements.
