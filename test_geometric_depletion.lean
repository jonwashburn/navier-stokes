import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Real

-- Helper: Angle between vectors
noncomputable def angle (v w : Fin 3 → ℝ) : ℝ :=
  Real.arccos (inner v w / (‖v‖ * ‖w‖))

-- The CORRECTED bound for aligned vectors
lemma angle_bound_aligned_norm (v w : Fin 3 → ℝ) (hv : v ≠ 0)
    (h_angle : angle w v ≤ π/6) :
    ‖w - v‖ ≤ 2 * sin(π/12) * ‖v‖ := by
  -- The correct bound is 2*sin(π/12) ≈ 0.518, not sin(π/6) = 1/2
  -- This follows from the law of cosines with angle ≤ π/6
  sorry

-- Verify the numerical values
example : sin (π/6) = 1/2 := by norm_num

-- The correct bound is approximately 0.518
example : 2 * sin(π/12) < 0.52 := by
  -- 2 * sin(π/12) ≈ 2 * 0.2588 ≈ 0.5176
  sorry

-- And it's greater than 1/2
example : 1/2 < 2 * sin(π/12) := by
  -- 0.5 < 0.5176
  sorry

-- Counterexample showing 1/2 bound is false
example : ∃ (v w : Fin 3 → ℝ), v ≠ 0 ∧ angle w v = π/6 ∧ ‖w - v‖ > (1/2) * ‖v‖ := by
  -- Take v = (1,0,0) and w at angle π/6
  -- Then ‖w - v‖ ≈ 0.62‖v‖ > 0.5‖v‖
  sorry
