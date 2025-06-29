/-
Navier-Stokes Equations
=======================

Basic definitions for the Navier-Stokes equations.
-/

import NavierStokesLedger.PDEOperators
import NavierStokesLedger.BasicDefinitions

namespace NavierStokes

open Real

/-- Solution to the Navier-Stokes equations -/
structure NSE (ν : ℝ) where
  /-- The velocity field u(x,t) -/
  u : ℝ → VectorField
  /-- Initial data -/
  initial_data : VectorField
  /-- Initial condition -/
  h_initial : u 0 = initial_data
  /-- Incompressibility -/
  h_div_free : ∀ t, divergence (u t) = fun _ => 0
  /-- Navier-Stokes equation (simplified) -/
  h_nse : ∀ t, deriv u t = fun x => fun i => -convectiveDerivative (u t) (u t) x i + ν * laplacianVector (u t) x i

/-- Vorticity of a vector field -/
noncomputable def vorticity (u : VectorField) : VectorField := curl u

end NavierStokes
