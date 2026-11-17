import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
open Lean Elab Command Meta

/-- For every declaration of the contribution module, list declarations of other modules with the
same type (theorems) or the same type and value (definitions): copies of existing declarations. -/
elab "#dupCheck" : command => do
  let env ← getEnv
  let some midx := env.getModuleIdx? `ZInQKernel.Contrib.OneProof.RingClassLattice | throwError "no module"
  let mut byType : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some midx then continue
    if n.isInternalDetail then continue
    let h := ci.type.hash
    byType := byType.insert h ((byType.getD h #[]).push n)
  let mut hits : Nat := 0
  let mut checked : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some midx then continue
    if n.isInternalDetail then continue
    checked := checked + 1
    for d in byType.getD ci.type.hash #[] do
      let some cd := env.find? d | continue
      if cd.type != ci.type then continue
      let same := match ci, cd with
        | .thmInfo _, .thmInfo _ => true
        | .defnInfo a, .defnInfo b => a.value == b.value
        | _, _ => false
      if same then
        hits := hits + 1
        let mi := (env.getModuleIdxFor? d).map (fun i => env.header.modules[i.toNat]!.module)
        logInfo m!"DUP {n} == {d} ({mi})"
  logInfo m!"checked {checked} declarations, {hits} duplicates"

#dupCheck
