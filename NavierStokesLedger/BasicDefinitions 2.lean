/-
  Basic definitions for Navier-Stokes global regularity proof
  Minimal version focusing on mathematical essentials
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real Function Set Filter Topology

namespace NavierStokes

/-! ## Basic Constants -/

/-- The critical geometric depletion constant -/
def C_star : ℝ := 0.05

/-- The Biot-Savart kernel constant -/
def C_BS : ℝ := 0.05

/-- The bootstrap constant -/
def K_star : ℝ := 0.090

end NavierStokes
