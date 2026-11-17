import ZInQKernel.OneProof.H.TailZ19
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Dominant
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.Mobius.ImagePlane
import ZInQKernel.Contrib.Mobius.Glue
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NoncommRing
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import ZInQKernel.HDecomp.QM.Polar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Different

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let rows := (← IO.FS.readFile "scratch/x6-fold/x6names.tsv").splitOn "\n"
  let mut out := ""
  for r in rows do
    match r.splitOn "\t" with
    | n :: h :: a :: b :: _ =>
      let nm := n.toName
      match env.find? nm with
      | some ci =>
        let mod := match env.getModuleIdxFor? nm with
          | some i => (env.header.moduleNames[i.toNat]!).toString
          | none => "?"
        out := out ++ s!"{n}\t{if toString (hash ci.type) == h then "same" else "DIFF"}\t{mod}\t{a}\t{b}\n"
      | none => out := out ++ s!"{n}\tNEW\t-\t{a}\t{b}\n"
    | _ => pure ()
  IO.FS.writeFile "scratch/x6-fold/x6dups.tsv" out
