import ZInQKernel.OneProof.Main

/-! leaf-fold14 uses check (after unipotent-b's `Deps.lean`): BFS over the constants used (types and values) from the
H top `HDec.HSyn.sixContactMin_of_open18`, skipping Mathlib and core; then, for each Prop that the fold's new leaves
feed, the constants of the closure whose type mentions it, excluding structure projections and the bundle maps. A
non-bundle theorem taking the Prop as a hypothesis means the Prop is consumed (not inert). -/

open Lean Elab Command

elab "#uses_check " root:ident keys:ident* : command => do
  let env ← getEnv
  let skip (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      let s := (env.header.moduleNames[idx.toNat]!).toString
      s.startsWith "Mathlib" || s.startsWith "Init" || s.startsWith "Lean" || s.startsWith "Std" ||
        s.startsWith "Batteries" || s.startsWith "Aesop" || s.startsWith "Qq" || s.startsWith "Plausible"
    | none => false
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root.getId]
  while _h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if skip n then continue
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      if let .inductInfo ii := ci then cs := cs ++ ii.ctors.toArray
      for c in cs do
        unless seen.contains c do stack := stack.push c
  logInfo m!"closure size {seen.size}"
  let bundleLike (n : Name) : Bool :=
    let s := n.toString
    (s.splitOn "researchLeaves").length > 1 || (s.splitOn "addedLeaves").length > 1 ||
      (s.splitOn "textbookLeaves").length > 1 || (s.splitOn "sixContactMin_of_").length > 1 ||
      (s.splitOn "Leaves").length > 1 && (s.splitOn ".mk").length > 1
  for k in keys do
    let mut users : Array Name := #[]
    for n in seen.toList do
      if skip n then continue
      if let some ci := env.find? n then
        if ci.type.getUsedConstants.contains k.getId && (env.getProjectionFnInfo? n).isNone &&
            !bundleLike n && n != k.getId then
          users := users.push n
    logInfo m!"{k.getId}: {users.size} non-bundle users in the closure: {users.toList.take 8}"

#uses_check HDec.HSyn.sixContactMin_of_open18
  ZInQ.HeightSplit.SemistableReductionThm ZInQ.HeightSplit.SemistablePersists PkgI2.RaynaudCriterion
  HDec.WeilPairing.T09_SymmIsogenyExists ReductSplit.SemistableReductionDVR ReductSplit.RaynaudSemistable
  ReductB.SemistablePersistsSHcp ReductGlue.RaynaudSemistableSH ReductGlue.StrictHenselizationPair
  T09Pic.PicRepresentableAbVar T09Pic.PicZeroAbVar T09Pic.PhiAmpleIsogeny T09Pic.WeilPairingMumford
