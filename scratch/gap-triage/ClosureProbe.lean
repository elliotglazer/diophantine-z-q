import ZInQKernel.OneProof.H.TailZ15
import Lean

/-! gap-triage: which consumers of `t23` (from `bdRInvariants`) are in the closure of the H top
`HDec.HSyn.sixContactMin_of_open12`? Prints every closure constant whose last name component is in the list. -/

open Lean

def gtClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      match ci with
      | .defnInfo v => todo := todo ++ v.value.getUsedConstants
      | .thmInfo v => todo := todo ++ v.value.getUsedConstants
      | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
      | _ => pure ()
  return seen

def gtTargets : List String :=
  ["g8_g12_of_leaves", "newformG12Out_of_galois", "afterG7_of", "g8_g12_of_leaves3", "afterG7_of3",
   "g8_g11", "g8_g12", "g9Glue_of_fieldEmb", "t23_all_of_bdrInvariants", "transfer_core",
   "heckeIrreducible_of_connected", "y3Connected_of_deligne"]

run_cmd do
  let env ← getEnv
  let s := gtClosure env `HDec.HSyn.sixContactMin_of_open12
  logInfo m!"closure size: {s.size}"
  for t in gtTargets do
    let hits := s.toList.filter fun n => n.componentsRev.head? == some (.str .anonymous t)
    logInfo m!"{t}: {hits}"
