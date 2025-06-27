/-
Supremum Norm Definition
========================

This file defines the supremum norm for vector fields.
-/

import NavierStokesLedger.PDEOperators

namespace NavierStokes

/-- L∞ norm of a vector field (using supremum) -/
noncomputable def supNorm (u : VectorField) : ℝ :=
  LinftyNorm u  -- From PDEOperators - supremum over all points

end NavierStokes
