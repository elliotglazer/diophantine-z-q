import ZInQKernel.OneProof.H.TailZ19
import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.HDecomp.A6.A6

open Lean Elab Command

/-- BFS over the constants used (types and values) from `root`, skipping Mathlib/core modules. -/
elab "#deps_check " root:ident targets:ident* : command => do
  let env ← getEnv
  let skip (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      let s := m.toString
      s.startsWith "Mathlib" || s.startsWith "Init" || s.startsWith "Lean" || s.startsWith "Std" ||
        s.startsWith "Batteries" || s.startsWith "Aesop" || s.startsWith "Qq" || s.startsWith "Plausible"
    | none => false
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root.getId]
  while h : stack.size > 0 do
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
  for t in targets do
    logInfo m!"{t.getId}: {seen.contains t.getId}"
  let keys : List Name := [``PkgI2.RaynaudCriterion, ``PkgI2.GrothendieckMonodromy,
    ``ReductSplit.SemistableUnipotent]
  for n in seen.toList do
    if skip n then continue
    if let some ci := env.find? n then
      let used := ci.type.getUsedConstants
      for k in keys do
        if used.contains k then
          let isProj := (env.getProjectionFnInfo? n).isSome
          logInfo m!"TYPEUSES {k} :: {n} proj={isProj}"

#deps_check HDec.HSyn.sixContactMin_of_open15
  HDec.HSyn.ResearchLeaves.r8 HDec.HSyn.ResearchLeaves.r6
  ReductSplit.grothendieckMonodromy_final' ReductGlue.raynaudCriterion_leaves
  ReductSplit.raynaudCriterion_of_leaves ReductSplit.grothendieckMonodromy_of_leaves
  PkgI2.D2_fixed_of_raynaud PkgI2.goodReduction_of_QM_rational3' PkgI2.goodReduction_of_QM_rational3_of_alg
  GlueA6Alg.goodReduction_of_QM_rational3_of_alg
  G0ModField.KernelField.kernelFieldExists_of_split''
  ReductSplit.SemistableUnipotent ReductGlue.SemistableUnipotentSH
