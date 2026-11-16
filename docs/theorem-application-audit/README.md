Historical inventory. Its decisions bind only source/audited-baseline.tex at SHA256 cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b. The current manuscript is ../../quartic_12504.tex; see ../quartic-12504/baseline-bridge.json for exact unchanged excerpts and ../quartic-12504/theorem-applications.json for the current quartic source.

# Theorem application inventory, November 5, 2026

The inventory records 82 scoped source/application decisions. Each decision identifies the external result, the manuscript passages that use it, the relevant hypotheses and conventions, and the evidence for the recorded translation. The decisions include the repairs and dependency qualifications linked in the records.

This is an audit of theorem applications, not an independent proof of every internal lemma or a formal verification of the manuscript's main theorem. An accepted application may consume explicitly listed internal premises. An empty open-items field means that no unresolved item remains within that application's recorded review scope; it does not remove those premises.

[DEPENDENCIES.md](DEPENDENCIES.md) explains the main dependency boundaries. The manuscript hash and anchors in the inventory identify the version reviewed. Earlier reports remain historical evidence; where a later repair supersedes an earlier finding, the record identifies that repair and its review.

## Read the audit

| File | Contents |
| --- | --- |
| [Inventory](INVENTORY.md) | 82 application families with exact sources, maps, hypotheses, conventions, translations and review evidence |
| [Findings](FINDINGS.md) | Errors found, repairs applied and limits of the audit |
| [Sources](SOURCES.md) | 72 source records, version identities, file hashes and recorded retrieval URLs |
| [Dependencies](DEPENDENCIES.md) | Internal premises and the order of finite-model, duality and arithmetic deductions |
| [Open items](OPEN_ITEMS.md) | No unresolved review item within the recorded application scopes |
| [Authoring](authoring/README.md) | Reviewed input data and reproducible generator |
| [Build receipt](MANUSCRIPT_BUILD.json) | Matching TeX/PDF hashes, pinned toolchain and build result |

The frozen manuscript has 11,259 lines and SHA256 `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`. It has 147 explicit citation occurrences, comprising 134 application citations, 10 summaries, one provenance citation and two source-scope declarations. Their 163 keys refer to 62 works. The inventory contains 443 anchored contexts and all 228 internal references resolve uniquely. A context is not necessarily a distinct theorem invocation.

All 82 families have explicit scoped decisions. The final five-reviewer wave supplied 43 additional acceptance records, rather than treating an empty open-items field as approval. Earlier bounded closures cover the other 39. The machine-readable [applications](applications.json) retain these decisions, their original baseline identities and their internal premises. Sixty records also retain a separately named `fresh_source_check` field; that historical field is not the total number of acceptance decisions.

Seventy-one source records have byte pins, covering 97 file entries. The unpinned record is the OpenAI provenance citation, from which no theorem is imported in this inventory. Sources include published articles, corrected editions, preprints and lecture notes. The audit does not assert that every input is published or that every author version equals a journal version.

## What was repaired

The de Rham step now uses a sufficiently strong comparison theorem, its corrigendum, and explicit finite descent. Other repairs include the local restriction/corestriction and homotopy justification, local Hecke and Frobenius conventions, formal-logarithm precision, correct forward rank theorem citations, and previously unrecorded Mertens and quaternion-embedding inputs. [The findings](FINDINGS.md) distinguish these repairs from withdrawn criticisms and metadata corrections.

The source history remains visible. Earlier reports can describe a gap later repaired; [dependency phase metadata](DEPENDENCY_PHASES.json) records the supersession. Their line numbers refer to the stated historical baseline. [The rebind ledger](ANCHOR_REBIND.json) and [53 text edits](MANUSCRIPT_EDITS.json) connect that evidence to this manuscript. The subsequent [date-only update](DATE_REBIND.json) changes the title-page date to November 5 and leaves all citation and context line numbers unchanged.

## Reproduce the checks

From the repository root:

```console
python docs/theorem-application-audit/validate.py
python docs/theorem-application-audit/validate.py --workspace /path/to/research-workspace
```

The first command checks manuscript, excerpt and evidence hashes, citation classification, source links, and internal references. The second also verifies the primary files at the paths in [sources.json](sources.json). Neither checks mathematical proofs. The [validation receipt](VALIDATION.json) records the final workspace check.

The older research handoff is a dated snapshot and does not contain every new audit source. [SOURCE_RESTORATION.json](SOURCE_RESTORATION.json) lists the required files, hashes, recorded URLs and versions. [source_manifest.py](source_manifest.py) can verify or copy these inputs from an existing research workspace into a fresh directory. It does not download copyrighted sources or grant redistribution rights. Some exact-file retrieval URLs are unknown; an original pinned copy is needed in those cases. The [restoration check](RESTORATION_CHECK.json) records our fresh-directory verification.

The [JSON citation list](citations.json) is mechanically exhaustive for explicit `\cite` commands in this frozen TeX. Semantic exhaustiveness is not certified: further implicit theorem uses may exist. The [named-input index](named-input-index.json) helps locate them. An accepted external application does not independently prove all its internal premises or the final theorem. Lean remains incomplete.
