import ZInQKernel.Contrib.OneProof.RingClassLattice
open Lean Elab Command Meta

/-- List declarations of the contribution module not in the dependency closure of the roots,
with their line ranges (docstring included). -/
elab "#deadDecls" : command => do
  let env ← getEnv
  let modName := `ZInQKernel.Contrib.OneProof.RingClassLattice
  let some midx := env.getModuleIdx? modName | throwError "no module"
  let roots := #[`T5Glue.shimuraReciprocityModFn_of_printed, `T5Glue.ringClassLattice]
  let mut used : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if used.contains n then continue
    used := used.insert n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
    for c in cs do
      if env.getModuleIdxFor? c == some midx && !used.contains c then todo := c :: todo
  let mut dead : Array (Name × Nat × Nat) := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some midx then continue
    if n.isInternalDetail then continue
    -- count as used if some used constant has n as prefix or n has a used prefix
    let isUsed := used.contains n || used.toList.any (fun u => n.isPrefixOf u || u.isPrefixOf n)
    if isUsed then continue
    let r? ← liftTermElabM <| findDeclarationRanges? n
    match r? with
    | some r => dead := dead.push (n, r.range.pos.line, r.range.endPos.line)
    | none => pure ()
  let sorted := dead.qsort (fun a b => a.2.1 < b.2.1)
  for (n, a, b) in sorted do
    logInfo m!"DEAD {n} {a} {b}"
  logInfo m!"used: {used.size}, dead: {dead.size}"

#deadDecls
