#!/bin/bash
# Reproduce the registration simulation with the UNCHANGED trusted checker of the base commit.
# Usage, from the repository root:  bash docs/h-targets/validation/simulate_registration.sh [BASE]
# It works in a throw-away `git clone --shared` under a temporary directory (the repository is only
# read), copies this working tree's ZInQKernel/Targets and docs/h-targets onto BASE, and runs:
#   stage 1  candidate as committed (manifest unchanged)            -> expected: rejected
#   stage 2  a maintainer applies registration-proposal.json        -> expected: valid, statement review
#   stage 3  a Contrib/H-only change on the stage-2 base (demo file, -> expected: proof_only_astra_review
#            `theorem … : True`, not a provider)
set -euo pipefail
ROOT=$(pwd)
BASE=${1:-9bf9ad8aa99168060cd0f770a007a30ff2c31aca}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
git clone -q --shared --no-checkout "$ROOT" "$TMP/repo"
cd "$TMP/repo"
git checkout -q "$BASE"
git switch -q -c sim
export GIT_AUTHOR_NAME=sim GIT_AUTHOR_EMAIL=sim@localhost GIT_COMMITTER_NAME=sim GIT_COMMITTER_EMAIL=sim@localhost
rm -rf ZInQKernel/Targets docs/h-targets
cp -r "$ROOT/ZInQKernel/Targets" ZInQKernel/
cp -r "$ROOT/docs/h-targets" docs/
git add -A
git commit -qm "sim: candidate, manifest unchanged"
set +e
python3 -B scripts/check_kernel_contract.py --root . --base-ref "$BASE" > "$TMP/stage1.json" 2> "$TMP/stage1.err"
S1=$?
set -e
python3 - <<'PY'
import json
c = json.load(open('KERNEL_CONTRACT.json'))
p = json.load(open('docs/h-targets/registration-proposal.json'))
c['files'].update(p['manifest_additions']['files'])
c['targets'] += p['manifest_additions']['targets']
c['files'] = dict(sorted(c['files'].items()))
open('KERNEL_CONTRACT.json', 'w').write(json.dumps(c, indent=2, ensure_ascii=False) + '\n')
PY
git add -A
git commit -qm "sim: maintainer applies the registration proposal"
S2BASE=$(git rev-parse HEAD)
python3 -B scripts/check_kernel_contract.py --root . --base-ref "$BASE" > "$TMP/stage2.json"
mkdir -p ZInQKernel/Contrib/H
printf 'namespace ZInQ.Contrib.H\n\n/-- Simulation-only helper (not a provider). -/\ntheorem simDemo : True := trivial\n\nend ZInQ.Contrib.H\n' \
  > ZInQKernel/Contrib/H/SimDemo.lean
git add -A
git commit -qm "sim: Contrib-only change"
python3 -B scripts/check_kernel_contract.py --root . --base-ref "$S2BASE" > "$TMP/stage3.json"
cmp -s scripts/check_kernel_contract.py <(git show "$BASE:scripts/check_kernel_contract.py")
S1="$S1" TMP="$TMP" BASE="$BASE" python3 - <<'PY'
import json, os
t = os.environ['TMP']
r2 = json.load(open(f'{t}/stage2.json')); r3 = json.load(open(f'{t}/stage3.json'))
out = {
  'base': os.environ['BASE'], 'checker': 'scripts/check_kernel_contract.py of the base commit (unchanged)',
  'stage1_candidate_manifest_unchanged': {'exit': int(os.environ['S1']), 'stderr': open(f'{t}/stage1.err').read().strip()},
  'stage2_proposal_applied': {'status': r2['status'], 'acceptance': r2['acceptance'], 'files': r2['files'],
      'targets': len(r2['targets']), 'route': r2['review']['route'], 'lock_changed': r2['review']['lock_changed']},
  'stage3_contrib_only_on_registered_base': {'status': r3['status'], 'route': r3['review']['route'],
      'changed': r3['review']['changed'], 'lock_changed': r3['review']['lock_changed']},
}
print(json.dumps(out, indent=1))
PY
