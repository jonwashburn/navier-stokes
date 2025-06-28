import NavierStokesLedger.PDEOperators
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace NavierStokes

/-- A time-dependent Navier-Stokes system with viscosity ν -/
structure NSSystem (ν : ℝ) where
  u : ℝ → VectorField  -- velocity field as function of time
  p : ℝ → (Fin 3 → ℝ) → ℝ  -- pressure as function of time and space

end NavierStokes
