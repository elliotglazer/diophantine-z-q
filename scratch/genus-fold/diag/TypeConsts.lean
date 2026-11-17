import ZInQKernel.OneProof.H.TailE
import Lean
/-! genus-fold diagnostic: the constants in the types of the two theorems whose type hash changed
(run in the base tree and in this tree, then diff). -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [`HDec.ZInQ.Contrib.AbVarBC.abVarBaseChange_of_torsionDescends,
            `HDec.ZInQ.Contrib.AbVarBC.abVarBaseChangeK_of_torsionDescends] do
    if let some ci := env.find? n then
      let cs := ci.type.getUsedConstants.qsort (·.toString < ·.toString)
      IO.println s!"{n} typeHash {ci.type.hash}"
      for c in cs do IO.println s!"  {c}"
