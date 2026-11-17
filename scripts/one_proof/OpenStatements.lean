import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-!
# The open hypotheses of the single proof, as data

Writes `docs/one-proof/open-statements.json`: one entry per open hypothesis of `ZInQ.OneProof.frozenTarget`
(the fields of its bundle arguments and its other `Prop` arguments, as `#discharges` reads them), with the
exact Lean type, the pretty-printed statement and the field's docstring. `scripts/one_proof/render_open.py`
joins it with `docs/one-proof/kinds.tsv` and `claims.tsv` into `docs/one-proof/OPEN.md`.

Run from the repository root after `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`:

    lake env lean scripts/one_proof/OpenStatements.lean
-/

open Lean Elab Command Meta ZInQ.OneProof.Discharges

run_cmd do
  let env ← getEnv
  let hyps ← liftTermElabM openHyps
  let mut entries : Array Json := #[]
  for h in hyps do
    let pp ← liftTermElabM do
      let fmt ← ppExpr h.type
      pure (toString fmt)
    let full ← liftTermElabM do
      let fmt ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr h.type)
      pure (toString fmt)
    -- a bundle field's docstring sits on its projection `Bundle.field`
    let doc ← match h.label.splitOn "." with
      | [b, f] =>
        let bundle := (`HDec.HSyn).str b
        let d ← findDocString? env (bundle.str f)
        pure (d.getD "")
      | _ => pure ""
    -- otherwise the docstring of the definition the statement names
    let doc ← if doc != "" then pure doc else match h.type.getAppFn with
      | .const c _ => do pure ((← findDocString? env c).getD "")
      | _ => pure ""
    let (bundle, field) := match h.label.splitOn "." with
      | [b, f] => (b, f)
      | _ => ("frozenTarget", h.label)
    entries := entries.push <| Json.mkObj [
      ("field", Json.str field), ("bundle", Json.str bundle), ("statement", Json.str pp),
      ("type", Json.str full), ("docstring", Json.str doc)]
  let out := Json.mkObj [("root", Json.str "ZInQ.OneProof.frozenTarget"), ("count", toJson entries.size),
    ("hypotheses", Json.arr entries)]
  IO.FS.createDirAll "docs/one-proof"
  IO.FS.writeFile "docs/one-proof/open-statements.json" (out.pretty ++ "\n")
  logInfo m!"wrote docs/one-proof/open-statements.json: {entries.size} open hypotheses"
