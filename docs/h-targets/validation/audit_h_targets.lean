/- h-targets draft audit: a copy of PR36 `scripts/audit_kernel.lean` (unchanged checker logic for
   import isolation, kernel replay against the external base, axiom closure over actual bodies,
   closed-`Prop` targets and exact provider types). Differences, all for a statement-only draft:
   * no headline/exports (the H targets are not premises of the headline yet);
   * a target's provider must be ABSENT (this draft declares no provider);
   * reports owned `opaque` and `axiom` constants (the axiom closure is the global one over all
     owned declarations, as in the original). -/
import Lean
import Lean.Replay

/- Run as a separate process after building the submitted modules. Do not import
   candidate modules into this executable or execute their initializers. -/
open Lean

def checked {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def field (j : Json) (k : String) : IO Json := checked (j.getObjVal? k)
def stringField (j : Json) (k : String) : IO String := do
  checked ((← field j k).getStr?)

def prettyType (env : Environment) (e : Expr) : IO String := do
  let (f, _, _) ← (Meta.ppExpr e).toIO
    { fileName := "<kernel-audit>", fileMap := default,
      options := ({} : Options).set `pp.width (120 : Nat) } { env }
  return f.pretty

-- Walk actual bodies, including opaque bodies, instead of trusting an imported
-- cached axiom summary. A global visited set keeps this linear in the closure.
partial def auditClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (axioms : NameSet := {}) : IO NameSet := do
  match todo with
  | [] => return axioms
  | n :: rest =>
    if seen.contains n then return ← auditClosure env rest seen axioms
    let some ci := env.find? n | throw (IO.userError s!"Missing dependency {n}")
    let mut ax := axioms
    if ci.isAxiom then
      unless n == `propext || n == `Quot.sound || n == `Classical.choice do
        throw (IO.userError s!"Forbidden axiom {n}")
      ax := ax.insert n
    auditClosure env (ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n) ax

def exactType (env : Environment) (proof : Name) (expected : Expr) : IO Unit := do
  let some ci := env.find? proof | throw (IO.userError s!"Missing proof {proof}")
  unless ci.levelParams.isEmpty do
    throw (IO.userError s!"Unexpected universe parameters on {proof}")
  match ci with
  | .thmInfo _ => pure ()
  | .defnInfo _ =>
    if ci.isUnsafe || ci.isPartial then throw (IO.userError s!"Unsafe/partial proof {proof}")
  | _ => throw (IO.userError s!"Expected a theorem or definition with proof body: {proof}")
  match Kernel.isDefEq env {} ci.type expected with
  | .ok true => pure ()
  | _ => throw (IO.userError s!"Wrong full type of {proof}. Additional hypotheses are not allowed.")

def main (args : List String) : IO Unit := do
  let [specPath, outputPath] := args |
    throw (IO.userError "usage: audit_kernel SPEC.json REPORT.json")
  let spec ← checked (Json.parse (← IO.FS.readFile specPath))
  let modules ← (← checked ((← field spec "modules").getArr?)).mapM fun x => do
    return (← checked x.getStr?).toName
  unless !modules.isEmpty do throw (IO.userError "Empty module list")
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m, importAll := true }) {}
  let mut owned : Std.HashMap Name ConstantInfo := {}
  let mut owner : Std.HashMap Name Name := {}
  let mut external : NameSet := {}
  let mut found : NameSet := {}
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    if modules.contains m then
      found := found.insert m
      let data := env.header.moduleData[i]!
      for imp in data.imports do
        unless modules.contains imp.module do external := external.insert imp.module
      for n in data.constNames do
        let some ci := env.find? n | throw (IO.userError s!"Missing declaration {n} in {m}")
        owned := owned.insert n ci
        owner := owner.insert n m
  for m in modules do
    unless found.contains m do throw (IO.userError s!"Module not imported: {m}")
  let base ← importModules (external.toArray.map fun m => { module := m, importAll := true }) {}
  for (n, _) in owned.toList do
    if base.contains n then throw (IO.userError s!"Project declaration leaked into external base: {n}")
  -- This checks project declarations even on a root build-cache hit.
  let replayed ← base.toKernelEnv.replay owned
  let verified := Environment.ofKernelEnv replayed
  let axioms ← auditClosure env (owned.toList.map Prod.fst)
  let mut results : Array Json := #[]
  for t in (← checked ((← field spec "targets").getArr?)) do
    let n := (← stringField t "declaration").toName
    let p := (← stringField t "provider").toName
    let some ci := verified.find? n | throw (IO.userError s!"Missing target {n}")
    unless ci.levelParams.isEmpty && ci.type == .sort .zero do
      throw (IO.userError s!"Target {n} must be a closed Prop declaration")
    let status := "open"
    if env.contains p then throw (IO.userError s!"Draft must not declare provider {p}")
    results := results.push (Json.mkObj [
      ("declaration", toJson n.toString), ("provider", toJson p.toString),
      ("status", toJson status),
      ("type", toJson (← prettyType env (ci.value?.getD (.const n []))))])
  let skipped := owned.toList.filter fun (_, c) => c.isUnsafe || c.isPartial
  let report := Json.mkObj [
    ("schema", toJson "kernel-audit/v1"), ("status", toJson "passed"),
    ("modules", toJson (modules.map Name.toString)),
    ("declarations", toJson owned.size),
    ("runtime_declarations_not_replayed", toJson (skipped.map fun (n, _) => n.toString)),
    ("allowed_axioms_used", toJson (axioms.toList.map Name.toString)),
    ("owned_opaque", toJson ((owned.toList.filter fun (_, c) => c matches .opaqueInfo _).map fun (n, _) => n.toString)),
    ("owned_axioms", toJson ((owned.toList.filter fun (_, c) => c.isAxiom).map fun (n, _) => n.toString)),
    ("targets", Json.arr results), ("protocol_acceptance", toJson false)]
  IO.FS.writeFile outputPath (report.pretty ++ "\n")
  IO.println s!"H-targets draft audit passed: {modules.size} modules, {owned.size} declarations"
