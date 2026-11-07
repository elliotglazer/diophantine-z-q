# Build the Version 7 handoff

Use Python 3.10 or newer, Node.js 18 or newer, and Git. The commands below run from the repository root. All output paths must be new and outside the repository.

Complete the source inventory and independent reviews, copy the successful fourteen-stage reproduction receipt to `handoff/releases/version7/REPRODUCTION.json`, and finalize `handoff/release.json`. The descriptor must be `READY` and bind the complete research selection, manuscript, PDF, package, wrapper, reviews and preserved files. Commit that exact tree before preparing the plan.

Run the packaging tests:

```sh
python -E -B handoff/test_handoff.py
```

Freeze the plan using the full immutable commit ID:

```sh
python -E -B handoff/prepare_handoff.py --repo . --commit FINAL_COMMIT --verification-receipt handoff/releases/version7/REPRODUCTION.json --output ../version7-handoff-plan.json
```

Supply the unchanged Version 6 full archive, with SHA-256 `93b53944ea93de08dc653beb70202797c1cbbdf19602ae583940bbf137dd43bc`:

```sh
python -E -B handoff/build_handoff.py --repo . --plan ../version7-handoff-plan.json --baseline ../z-in-q-version6-full-handoff.zip --output ../version7-handoff-output
```

The builder verifies every member of both resulting archives and writes `BUILD_RECEIPT.json` and `SHA256SUMS`. Use their actual plan and current-archive hashes in the authenticated extraction command:

```sh
python -E -B handoff/replay_extracted_current.py ../version7-handoff-output/z-in-q-version7-current-handoff.zip --expected-plan-sha256 PLAN_SHA --expected-archive-sha256 CURRENT_ZIP_SHA --extract ../version7-extracted --replay-output ../version7-replay --report ../version7-handoff-output/EXTRACTED_REPLAY.json
```

Run the source-inventory validator and its adversarial tests from the extracted `current/` tree using the exact commands and source-input hash recorded in `docs/quartic-962/README.md`. Final publication requires all checks to pass. Publishing is a separate action and does not belong to these scripts.

The complete archive hash and final build receipt cannot be committed inside the archive they identify. Record them in the release or a subsequent metadata commit. Never overwrite an earlier version's asset.

Version 7 adds the four Gaussian audits and exact repairs under `docs/quartic-962/evidence/gaussian-four-audit-20261106/`, with an overview in `research/version7/README.md`. `V6_RESEARCH_MANIFEST.json` continues to describe the unchanged Version 6 research collection; `V7_AUDIT_MANIFEST.json` binds the new audit collection.
