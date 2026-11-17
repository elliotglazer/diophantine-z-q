

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out := ""
  for (n, ci) in env.constants.map₂.toList do
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
    if let .ctorInfo cv := ci then cs := cs.push cv.induct
    let cs2 := cs.filter fun c => (env.constants.map₂.find? c).isSome
    let r ← findDeclarationRanges? n
    let (a, b) := match r with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    out := out ++ s!"{n}\t{a}\t{b}\t{" ".intercalate (cs2.toList.eraseDups.map toString)}\n"
  IO.FS.writeFile "scratch/x6-fold/x6edges.tsv" out
