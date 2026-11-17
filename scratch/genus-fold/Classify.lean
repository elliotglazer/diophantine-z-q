import ZInQKernel.OneProof.Main
import Lean
/-! genus-fold: kind of each changed constant (theorem / definition with Prop type / data definition / other),
and whether it lies in `frozenTarget`'s closure. Reads changed_names.txt, writes changed_kinds.txt. -/
open Lean Elab Command Meta
def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen
run_cmd do
  let env ← getEnv
  let cl := closureOf env `ZInQ.OneProof.frozenTarget
  let txt ← IO.FS.readFile "scratch/genus-fold/changed_names.txt"
  let mut out : Array String := #[]
  for l in txt.splitOn "\n" do
    if l.isEmpty then continue
    let n := l.toName
    let some ci := env.find? n | out := out.push s!"{n} MISSING"; continue
    let isProp ← liftTermElabM do
      try return (← isProp ci.type) catch _ => return false
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => if isProp then "def(proof)" else "def(data)"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec"
      | .opaqueInfo _ => "opaque"
      | _ => "other"
    out := out.push s!"{n} {kind} {if cl.contains n then "inClosure" else "offClosure"}"
  IO.FS.writeFile "scratch/genus-fold/changed_kinds.txt" ("\n".intercalate out.toList ++ "\n")
