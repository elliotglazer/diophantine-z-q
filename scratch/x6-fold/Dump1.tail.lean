

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out := ""
  for (n, ci) in env.constants.map₂.toList do
    if n.isInternal then continue
    let r ← findDeclarationRanges? n
    let (a, b) := match r with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    out := out ++ s!"{n}\t{hash ci.type}\t{a}\t{b}\t{ci.isTheorem}\n"
  IO.FS.writeFile "scratch/x6-fold/x6names.tsv" out
