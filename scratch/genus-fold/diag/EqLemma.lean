import ZInQKernel.OneProof.H.TailR
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let n := `topologicalKrullDim.eq_1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"{n} in {env.header.modules[i.toNat]!.module}"
  | none => logInfo m!"{n} not imported (realized on demand: {(env.find? n).isSome})"
