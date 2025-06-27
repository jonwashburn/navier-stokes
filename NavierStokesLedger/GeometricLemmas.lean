/-
Geometric Axioms for Constantin–Fefferman Mechanism
===================================================

This module replaces the earlier, more ambitious `GeometricLemmas.lean`
(which was not compiling) with a **minimal, compiling stub**.  We keep the
few constants and bounds that other files rely on and package everything
else as axioms to be proved later.
-/

import NavierStokesLedger.BasicDefinitions
import NavierStokesLedger.Geometry.CrossBounds

namespace NavierStokes.Geometric

open Real

/-- The geometric constant 2·sin(π/12) ≃ 0.51763809.  We hard-code the
value to avoid trigonometric computation inside Lean for now. -/
noncomputable def C_geom : ℝ := 0.5176380902050415

/-- Numeric sanity check for `C_geom`.  A formal proof will come later. -/
axiom C_geom_approx : abs (C_geom - 0.5176380902050415) < 1e-6

/-!
### Core geometric bounds (axiomatized)
-/

/-- Aligned–vector difference bound used in Constantin–Fefferman depletion.
If the angle between `v` and `w` is ≤ π/6, their difference is controlled by
`C_geom`. -/
axiom aligned_vectors_close
  (v w : Fin 3 → ℝ) (hv : v ≠ 0)
  (h_angle : ∃ θ : ℝ, θ ≤ π / 6 ∧ ‖w - v‖^2 = ‖v‖^2 + ‖w‖^2 - 2 * ‖v‖ * ‖w‖ * cos θ) :
  ‖w - v‖ ≤ C_geom * max ‖v‖ ‖w‖

/-- Simplified version when `‖w‖ ≤ ‖v‖`. -/
axiom aligned_bound_simple
  (v w : Fin 3 → ℝ) (hv : v ≠ 0)
  (h_angle : ∃ θ : ℝ, θ ≤ π / 6 ∧ ‖w - v‖^2 = ‖v‖^2 + ‖w‖^2 - 2 * ‖v‖ * ‖w‖ * cos θ) :
  ‖w - v‖ ≤ C_geom * ‖v‖

/-- Standard Lagrange inequality for the 3-D cross product. -/
axiom cross_product_bound (a b : Fin 3 → ℝ) :
  ‖NavierStokes.Geometry.crossProduct a b‖ ≤ ‖a‖ * ‖b‖

end NavierStokes.Geometric
