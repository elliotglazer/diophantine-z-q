import ZInQKernel.OneProof.H.TailZ26
open Lean Meta Elab Command

/-- Constants reachable from `root` through values/types, expanding only constants defined in
`ZInQKernel` / `ZInQ` / `GreenTaoVendor` modules (Mathlib constants are leaves). -/
def reach (root : Name) : CommandElabM (Std.HashSet Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let local? : Bool := match env.getModuleIdxFor? n with
      | some idx => let m := env.header.moduleNames[idx.toNat]!
                    (`ZInQKernel).isPrefixOf m || (`ZInQ).isPrefixOf m
      | none => true
    if !local? then continue
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    for c in used do
      if !seen.contains c then stack := stack.push c
  return seen

elab "#reachQM " root:ident : command => do
  let s ← reach root.getId
  let env ← getEnv
  let mut carriers : Array Name := #[]
  let mut users : Array Name := #[]
  for n in s.toArray do
    let some ci := env.find? n | continue
    if ci.type.getUsedConstants.contains `PkgI3.QMDichotomyYu then carriers := carriers.push n
    if let some v := ci.value? (allowOpaque := true) then
      if v.getUsedConstants.contains `PkgI3.qmDichotomy_B6 then users := users.push n
  logInfo m!"carriers ({carriers.size}): {carriers.qsort (·.toString < ·.toString)}"
  logInfo m!"users of qmDichotomy_B6: {users}"

elab "#reachProj " root:ident : command => do
  let s ← reach root.getId
  let env ← getEnv
  let projs : List Name := [`HDec.HSyn.OpenTextbookLeaves2.t27, `HDec.HSyn.OpenTextbookLeaves3.t27,
    `HDec.HSyn.OpenTextbookLeaves4.t27, `HDec.HSyn.OpenTextbookLeaves6.t27, `HDec.HSyn.TextbookLeaves.t27,
    `HDec.QMSplit.Yu.qmDichotomyYu_of_yu]
  for n in s.toArray do
    let some ci := env.find? n | continue
    if let some v := ci.value? (allowOpaque := true) then
      let u := v.getUsedConstants
      let hits := projs.filter u.contains
      if !hits.isEmpty then logInfo m!"{n} uses {hits}"

#reachQM HDec.HSyn.sixContactMin_of_open20
#reachProj HDec.HSyn.sixContactMin_of_open20
