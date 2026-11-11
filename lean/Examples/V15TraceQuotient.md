# V15 retained contact and the actual trace quotient

This standalone application formalizes the existing V15 contact-domain argument
and its proposed trace quotient. The external-open-problem KPI is zero.
Independent source review and protocol acceptance remain pending. No manuscript,
accepted helper, frozen target, existing application contract or earlier review
disposition is changed.

`V15RetainedContact.lean` proves, for every rational `t,q`, that
`(1+q) P5((t-1)^2) = ((t-1)^2)^5` implies `q != 0`. Both the expanded
polynomial and its five literal contact factors are checked. It then proves
`x102 != 0` for every rational raw224 tuple satisfying the ten specified rows
and every rational `A != 0`. The parameter-family endpoint allows every integer
`N`, using nonvanishing of `149^(2*N+1)`; it introduces no effective threshold.

`V15RawRows.lean` contains every literal summand of the 197 parent residuals
and 196 target residuals. Small row definitions and lookup blocks are only
their representation. `V15TraceQuotient.lean` applies the ten-row result to
the actual parent coordinates, derives `Q != 0` from row 47, proves the
substitution identity for every parent row, and constructs an equivalence
between the full rational solution sets of these two explicit row families.
The points have types `Fin 223 -> Q` and `Fin 222 -> Q`; `coord` exposes the
source's one-based indices without adding a free coordinate. Both maps fix
all 221 retained coordinates, including physical input coordinate 1.

## Mathematical sources and exact bindings

All source paths below are under
`research/version15/quartics/quartic-222/provenance/` at
`elliotglazer/diophantine-z-q@511529bbe9d635194f0c9d925709e77a5d3afa64`.

| Source | SHA-256 |
| --- | --- |
| `detector-q-nonzero-107/PROOF.md` | `d1d33a5a937fe00df6b008835c058759ccb6c575ee547e297dffc55064da16e5` |
| `detector-q-nonzero-107/REQUIRED-ROWS.json` | `6d04f2f063e3d903abdcf5c769180389a716fa360a0ced6467287aed9451977f` |
| `shared-T-redundancy224-006/candidate224-ir.json` | `6b961988414509ff6619fb674b696c745b098d00ad2af326df43e4db5aa5d39f` |
| `joint-root-factor-110/candidate223-ir.json` | `0839eb623c76ba462eec8842dc5b8c85fef85cc924c9daa98f35a83ae61948e0` |
| `trace-quotient222-116/raw222-ir.json` | `34974cb8e9c274fa7612d93603224fa02fd0fc13ceb37f55eb0be8dce91b7bce` |

The consumer is `trace-quotient222-116/PROOF.md`, which explicitly describes
an author proposal pending independent acceptance. Formal verification of
this local chart does not supply that protocol acceptance.

| Application obligation | Constructed inputs and derivation |
| --- | --- |
| Source hypotheses | `Raw224Ten` is exactly rows 9,43,44,45,46,56,57,68,71,73, with the sole parameter hypothesis `A != 0`. No root or trace row is used for contact nonvanishing. |
| Constructed objects | `P5`, `obstruction`, `Retained`, the two literal residual families, `coord`, and the two coordinate maps are explicit definitions in the three modules. |
| Domain and index coverage | The contact variables and every source coordinate range over all rationals. The solution predicates quantify over all 197 and 196 row IDs, respectively. `row_substitution` covers every parent ID 1 through 197. |
| Transition maps | Raw224 slots 98,99,100,101,102,113,114,125,126,128 bind to parent slots 92,93,94,95,96,107,108,119,120,122; slots 1 and 55 are fixed. The parent-to-target map sets new slot 222 to `Z/Q`; the reverse sets old slots 222 and 223 to `R2*U` and `Q*U`. |
| Consumed-object identity | Parent `q=x96`, `Q=x98`, `R2=x119`, `G=x222`, `Z=x223`. Row 47 is `q^2-Q=0`. Row 186 is `Q*G-R2*Z=0`. Rows 196 and 197 are the literal special-trace and other-trace definitions, not arbitrary predicates. |
| Coefficients and normalization | The obstruction is `3813373161796*(P5(S^2)-S^10)`. Rows 56 and 57 yield the scalar quartic with five positive coefficients. Row 71 forces `R != 0` before row 68 supplies `T=R^2 != 0` and division by `T` is used. Mathlib's `den_dvd_of_is_root` and `num_isRoot_scaleRoots_of_aeval_eq_zero` are applied directly, with `IsFractionRing.den`; no identification with `Rat.den` is asserted. |
| Local conditions | All 1,061 parent and 1,059 target coefficient terms are represented. The checked substitution makes precisely parent row 186 the zero polynomial, and shifts subsequent row IDs down by one. |
| Exceptional cases | No trace or `U` is inverted. There is no positivity hypothesis on `q`, no `q+1 != 0` hypothesis and no added inverse guard. The audit includes the valid normalized local contact `t=1,q=-1`; it is not a full-system existence witness. |
| Downstream consumption | `raw223_retained`, `raw223_q_nonzero` and `raw223_Q_nonzero` discharge the denominator used by `to222`. `row_substitution`, `reverse_solution`, both inverse identities and `forward_solution` are consumed by `solutionEquiv`. |

## Scope and proof shape

These are independently authored applications of the cited mathematical
equations and pinned Mathlib results, not transplants of external Lean code.
Coefficient expansion, positivity, row normalization, rational-root
applications, finite arithmetic and the quotient identities follow the reuse
route. No new local escape witness, local freezing eligibility or mathematical
novelty is claimed. No implementation from the unlicensed third-party search
hits is imported or copied. The new source files have the accompanying Apache
2.0 license; source mathematics retains its original attribution.

This does not prove the complete Z-in-Q defining theorem, a final polynomial
identity, a coefficient-height bound, SixContactMin or CertifiedRank. It does
not identify the weighted sum-of-squares zero set, formalize the earlier
raw224-to-raw223 construction as a whole, or establish full-system existence.
The accepted 48-module snapshot is outside this application's import closure.

## Scoped reproduction

Use Lean 4.35.0 and the unchanged `lean/lake-manifest.json`; Mathlib is pinned
to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Materialize the pinned dependency
caches as described in `lean/README.md`. The default `ZInQ` library does not
select these application modules. From the repository root, compile these
three modules and their scoped axiom audit into fresh project output:

```python
import json, os, subprocess, tempfile
from pathlib import Path

p = Path("lean").resolve()
manifest = json.loads((p / "lake-manifest.json").read_text())
libraries = []
for package in manifest["packages"]:
    folder = p / ".lake/packages" / package["name"]
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip()
    assert revision == package["rev"]
    subprocess.run(["git", "diff", "--quiet", "HEAD", "--"],
                   cwd=folder, check=True)
    libraries.append(folder / ".lake/build/lib/lean")
version = subprocess.check_output(["lean", "--version"], cwd=p, text=True)
assert "version 4.35.0," in version
(p / ".checks").mkdir(exist_ok=True)
out = Path(tempfile.mkdtemp(prefix="v15-", dir=p / ".checks"))
env = os.environ.copy()
env.pop("LEAN_SRC_PATH", None)
env["LEAN_PATH"] = os.pathsep.join(map(str, [out / "lib", *libraries]))
modules = ["Examples/V15RetainedContact", "Examples/V15RawRows",
           "Examples/V15TraceQuotient", "Checks/V15TraceQuotientAxioms"]
for module in modules:
    target = out / "lib" / (module + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lean", "-j1", "-Ddebug.skipKernelTC=false",
                    "-o", str(target), module + ".lean"],
                   cwd=p, env=env, check=True)
print(out)
```

The audit checks every declaration originating in the three application
modules, including generated declarations, and rejects any axiom outside
`propext`, `Quot.sound` and `Classical.choice`. It prints the closure of each
main endpoint. This is a scoped application check, not a rebuild or audit of
the accepted snapshot, Lean, or Mathlib itself.
