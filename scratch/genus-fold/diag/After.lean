import ZInQKernel.OneProof.H.TailE
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [`HDec.ZInQ.Contrib.AbVarBC.abVarBaseChange_of_torsionDescends, `HDec.ZInQ.Contrib.AbVarBC.diagT] do
    if let some ci := env.find? n then
      let cs := ci.type.getUsedConstants
      logInfo m!"{n} hash {ci.type.hash} consts {cs.size}: {cs}"
      for c in cs do
        if let some idx := env.getModuleIdxFor? c then
          logInfo m!"  {c} : {env.header.modules[idx.toNat]!.module}"
