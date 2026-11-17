import ZInQKernel.OneProof.H.TailZ19
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
/-! x6-fold: op-compact's DumpCompact.lean over the base top (TailZ19 and Main's other imports, without Main): a hash of
the type and value of every constant declared in the `ZInQKernel.OneProof` modules, written to
`scratch/x6-fold/hashes_before.txt`. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`ZInQKernel.OneProof).isPrefixOf m then
        let vh := match ci.value? (allowOpaque := true) with | some v => v.hash | none => 0
        out := out.push s!"{n} {m} {ci.levelParams} {ci.type.hash} {vh}"
  out := out.qsort (· < ·)
  IO.FS.writeFile "scratch/x6-fold/hashes_before.txt" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} constants hashed"
