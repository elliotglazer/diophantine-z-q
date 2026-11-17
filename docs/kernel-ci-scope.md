# When the required kernel job can skip its build

`Complete kernel build and exact-target audit` reports on every pull request.
There is no trigger path filter. Its first step obtains the complete paginated
PR file list, binds it to the event's base and head commits, and rechecks those
commits after classification. Renames include both names. Only an explicit
successful `full_build=false` result skips subsequent steps, including checkout,
Lean installation and the full audit artifact upload. The small scope-decision
artifact is preserved before checkout. A failed classifier step runs the build.
Pushes to main and manual runs always build.

The first step embeds `scripts/kernel_pr_scope.py`; it does not check out or
execute a PR's copy of that script. The offline test checks that the embedded
source and the maintained source match.

## Input inventory

| Consumer | Inputs that require the full build |
| --- | --- |
| `check_kernel_contract.py:validate` | `KERNEL_CONTRACT.json`, every path pinned in either the base or head contract, every tracked `.lean` file anywhere, and every `lakefile.lean` or `lakefile.toml`. The global Lean-file rule is necessary because the bypass-option scan is not limited to kernel modules. |
| `check_kernel_contract.py:lean_modules` | `ZInQKernel.lean`, `ZInQKernel/**`, `ThirdParty/GreenTao/**`, `lean/ZInQ.lean`, `lean/ZInQ/**`. The classifier covers all of `ThirdParty/**` and `lean/**`. |
| `check_kernel.py` and Lake | The root and nested `lake-manifest.json`, `lakefile.toml`, `lakefile.lean` and `lean-toolchain`; all sources above; the local `lean/` package; pinned dependency revisions; `scripts/check_kernel_contract.py`, `scripts/check_target.py`, `scripts/audit_kernel.lean`; and `build/kernel-ci/**`. |
| `check_target.py` | `lean/Frozen/BoundedIntegerPolynomial.lean` and `ZInQKernel/Target.lean`. |
| `kernel_base_report.py` | The base commit's `KERNEL_CONTRACT.json`, `.github/workflows/kernel-lean.yml`, authenticated main-push `kernel-audit` artifacts and generated `build/kernel-ci/base-*.json`. External artifacts are not PR files; main pushes still always build. |
| `test_kernel_contract.py` | `check_kernel_contract.py` and its inline temporary repository fixtures. |
| `test_kernel_audit.py` | `scripts/audit_kernel.lean`, `lean-toolchain`, the pinned Lean executable and inline temporary Lean fixtures. |
| Workflow, checkout and caching | `.github/workflows/kernel-lean.yml`, `.gitattributes`, `.gitmodules`, `.lake/**`, the root and nested toolchain/manifests, and all `scripts/**`, including every `scripts/*kernel*` file and the new classifier/tests. |

Unknown paths also build. The only skip candidates are `.md`, `.tex`, `.bib`
and `.pdf` documentation outside protected locations, plus the independent
Protocol B workflow, reviewer instructions and `tests/protocol_b/*.py` files.
Contract membership takes precedence even for a document. Other files under
`.github/`, `tests/` or `build/` build; executables, data and archives build.

An unavailable or malformed contract, API failure, changed PR revision,
missing/duplicate file rows, unknown change status or a diff exceeding GitHub's
3,000-file API limit requests the full build. This is deliberately conservative.

## Validation and review

Run `python -B scripts/test_kernel_pr_scope.py -v`. The tests demonstrate that
`docs/guide.md` skips and `ZInQKernel/Contrib/Proof.lean` builds, and cover pinned
documents, all current contract entries, renames, pagination, unknown files,
incomplete lists, revision changes, API failures, push/manual runs and the
unchanged required job name. The skip writes its reason to the step summary.

This change updates the workflow and line-ending rules' contract hashes and
adds the classifier and its tests to the contract; it does not change mathematical targets or Lean
sources. Jack McCarthy (`Deicyde`) is being asked to confirm this inventory, and
Fable will review the follow-up PR before merge. Neither confirmation is
claimed by these offline tests.

## Reusing a full audit after an unrelated merge

A PR updated from main may reuse a completed full kernel run when its kernel
inputs are unchanged. This affects the required PR check only. Pushes to main,
including post-merge builds, and manual runs still perform the full build and
audit. The Lean review profile still needs its separate direct-head evidence.
No compiled files or other build outputs are restored by this reuse path.

Before checkout, the scope step records the execution commit supplied by GitHub,
its event base and head, the workflow hash, and a digest of the complete kernel
input set. The digest includes each selected path, Git mode, object type and
object ID. Selection uses the input inventory above, including contract-pinned
documents, all scripts, the workflow and conservative unknown-file handling.
The `kernel-scope-<attempt>` artifact is uploaded before candidate code runs.

Reuse requires a successful full PR run in this repository, with the same
workflow bytes as both the current execution and its protected base. Its head
must be an ancestor of the current PR head. The prior execution commit comes
from the pre-checkout artifact, never from `audit.json` alone. The validator
checks GitHub's artifact digest, run, attempt and creation time against the
upload and checkout steps, then re-derives the input digest from Git objects.
The prior synthetic merge must have the recorded head as its second parent and
the same complete tree as that head. A prior head that was behind its base and
built a different tree is deliberately not reused.

The source-contract, invalid-proof, full-build and audit steps must all have
succeeded. Both project-cache steps must have been skipped. The final audit
must agree with the pre-checkout execution commit and actual contract bytes.
Missing or expired artifacts, changed inputs or producers, unsupported tree
entries, ambiguous timing and API errors all cause a full build.

The job summary and scope artifact identify the original full run, its execution
commit, the current execution commit and the matching digest. An original base
progress comparison remains historical. A reuse-only run cannot supply another
reuse because its build step was skipped. Repeated documentation-only base
advances may continue to reuse the same original full run while it remains
available and all checks still pass.

A two-second pause separates the pre-checkout upload from checkout, so their
second-resolution API timestamps can be ordered strictly. The search considers
the latest 20 successful PR runs; an older supplier outside that window causes
a full build. Duplicate audit artifacts across rerun attempts also cause a full
build. The first run under a changed workflow always builds.

This relies on GitHub's runner and artifact records, not isolation from a
complete runner compromise during later candidate execution. The post-merge
full build on main remains in place.

Run `python -B scripts/test_kernel_reuse.py` with the existing scope and cache
tests. The tests include changed inputs, expired or substituted artifacts,
post-checkout replacement, a crafted merge commit, changed producers,
reuse-chain rejection, repeated base advances and full push/manual behavior.
