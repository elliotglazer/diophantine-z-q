"""Replay the fixed-member contribution without modifying its data."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
if sys.flags.optimize:
    raise SystemExit("Run with assertions enabled")

def blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

manifests = ("source-blobs.json", "annex-blobs.json", "foundations-blobs.json",
             "repair-proof-blobs.json", "repair-parent-blobs.json", "repair-lineage-blobs.json")
seen = {}
for name in manifests:
    for rel, expected in json.loads((HERE / name).read_text(encoding="utf-8")).items():
        require(rel not in seen or seen[rel] == expected, "Conflicting pin: " + rel)
        data = (HERE / "source" / rel).read_bytes()
        require(blob(data) == expected, "Git blob mismatch: " + rel)
        seen[rel] = expected
require(set(seen) == {str(f.relative_to(HERE / "source")).replace("\\", "/")
                      for f in (HERE / "source").rglob("*") if f.is_file()},
        "Source manifest coverage")
ancestor = ROOT / "research/version21/construction/inputs/brox229/source/quadratic195.json"
source = HERE / "source/computation/quartic/seven_units193_v74/source/source195.json"
require(ancestor.read_bytes() == source.read_bytes(), "Receiving v21 ancestor mismatch")
require(blob(ancestor.read_bytes()) == "5d6c4a4b482a4065b87a79d03426b0dcfff0f593", "Receiving v21 pin")
print(f"Verified {len(seen)} source blob pins and common receiving source", flush=True)
for script, receipt in (("check-v74.js", "v74-replay.json"),
                        ("check-v78.js", "v78-replay.json"),
                        ("check-v82-bb.js", "v82-bb-replay.json"),
                        ("check-tail.js", "tail-replay.json"),
                        ("check-poles.js", "poles-replay.json")):
    result = subprocess.run(["node", str(HERE / script)], check=True, capture_output=True, text=True)
    observed = json.loads(result.stdout)
    expected = json.loads((HERE / receipt).read_text(encoding="utf-8"))
    # Receipts include provenance fields as well as the exact result.
    require(all(expected.get(k) == v for k, v in observed.items()), "Receipt mismatch: " + script)
    print(script + ": " + json.dumps(observed, sort_keys=True), flush=True)
subprocess.run([sys.executable, "-B", str(HERE / "check.py")], cwd=HERE, check=True)
print("PASS: fixed 175-variable lineage, native poles and exact final expansion")
