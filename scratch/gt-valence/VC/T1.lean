import ZInQKernel.OneProof.H.TailZ2
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println (env.header.moduleNames.contains `Mathlib)
  for m in [`Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts, `Mathlib.MeasureTheory.Constructions.HaarToSphere, `Mathlib.Geometry.Manifold.PartitionOfUnity, `Mathlib.Analysis.Meromorphic.FactorizedRational, `Mathlib.Analysis.Complex.UpperHalfPlane.Measure, `Mathlib.MeasureTheory.Group.FundamentalDomain, `Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions, `Mathlib.Analysis.SpecialFunctions.Pow.Integral, `Mathlib.MeasureTheory.Topology, `Mathlib.Analysis.InnerProductSpace.Laplacian] do
    IO.println s!"{m}: {env.header.moduleNames.contains m}"
