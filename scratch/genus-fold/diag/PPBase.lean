import ZInQKernel.OneProof.H.TailE
import Lean
/-! genus-fold diagnostic, run in the base tree: the types of the two theorems in `pp.all` form. -/
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  for n in [`HDec.ZInQ.Contrib.AbVarBC.abVarBaseChange_of_torsionDescends,
            `HDec.ZInQ.Contrib.AbVarBC.abVarBaseChangeK_of_torsionDescends] do
    let some ci := env.find? n | throwError "missing"
    let f ← liftTermElabM do
      withOptions (fun o => (o.setBool `pp.all true).setBool `pp.fullNames true) do
        ppExpr ci.type
    IO.FS.writeFile s!"scratch/genus-fold/diag/base_type_{n.getString!}.txt" (toString f)
