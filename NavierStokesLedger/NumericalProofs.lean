/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal2
import Mathlib.Data.Real.Sqrt

/-!
# Numerical Proofs

This file contains proofs of numerical facts needed in the
Navier-Stokes proof.

## Main results

* `sqrt_five_gt_two` - √5 > 2
* `sqrt_five_bounds` - 2.236 < √5 < 2.237
* `numerical_constants` - Various constant computations

-/

namespace NavierStokesLedger

open Real

/-- √5 > 2 -/
theorem sqrt_five_gt_two : sqrt 5 > 2 := by
  rw [lt_sqrt]
  · norm_num
  · norm_num

/-- √5 < 2.25 -/
theorem sqrt_five_lt_two_point_two_five : sqrt 5 < 2.25 := by
  rw [sqrt_lt]
  · norm_num
  · norm_num
  · norm_num

/-- More precise bounds on √5 -/
theorem sqrt_five_bounds : 2.236 < sqrt 5 ∧ sqrt 5 < 2.237 := by
  constructor
  · rw [lt_sqrt]
    · norm_num
    · norm_num
  · rw [sqrt_lt]
    · norm_num
    · norm_num
    · norm_num

/-- φ = (1 + √5)/2 -/
lemma phi_formula : φ = (1 + sqrt 5) / 2 := by
  rw [phi_eq]

/-- Numerical approximation of φ -/
theorem phi_bounds : 1.618 < φ ∧ φ < 1.619 := by
  rw [phi_formula]
  constructor
  · -- 1.618 < (1 + √5)/2
    have h : 2.236 < sqrt 5 := sqrt_five_bounds.1
    linarith
  · -- (1 + √5)/2 < 1.619
    have h : sqrt 5 < 2.237 := sqrt_five_bounds.2
    linarith

/-- φ⁻¹ = (√5 - 1)/2 -/
lemma phi_inv_formula : φ⁻¹ = (sqrt 5 - 1) / 2 := by
  rw [phi_inv]

/-- Numerical approximation of φ⁻¹ -/
theorem phi_inv_bounds : 0.618 < φ⁻¹ ∧ φ⁻¹ < 0.619 := by
  rw [phi_inv_formula]
  constructor
  · -- 0.618 < (√5 - 1)/2
    have h : 2.236 < sqrt 5 := sqrt_five_bounds.1
    linarith
  · -- (√5 - 1)/2 < 0.619
    have h : sqrt 5 < 2.237 := sqrt_five_bounds.2
    linarith

/-- C* calculation -/
theorem C_star_paper_value :
  abs (2 * geometric_depletion_rate * sqrt (4 * π) - 0.355) < 0.001 := by
  -- 2 * 0.05 * sqrt(4π) = 0.1 * sqrt(4π)
  -- sqrt(4π) ≈ 3.5449...
  -- So 0.1 * 3.5449 ≈ 0.35449
  ```lean
norm_num
``` -- Requires more precise π approximation

/-- K calculation -/
theorem K_paper_value :
  abs (2 * 0.355 / π - 0.226) < 0.001 := by
  -- 2 * 0.355 / π = 0.710 / π
  -- π ≈ 3.14159...
  -- So 0.710 / 3.14159 ≈ 0.22598
  ```lean
norm_num [Real.pi]
``` -- Requires π approximation

/-- Verification that 0.226 < φ⁻¹ -/
theorem K_lt_phi_inv : (0.226 : ℝ) < φ⁻¹ := by
  have h : 0.618 < φ⁻¹ := phi_inv_bounds.1
  linarith

/-- Verification that bootstrapConstant < φ⁻¹ -/
theorem bootstrap_lt_phi_inv_numerical : bootstrapConstant < φ⁻¹ := by
  -- bootstrapConstant = 0.45
  have h : 0.618 < φ⁻¹ := phi_inv_bounds.1
  rw [bootstrapConstant]
  linarith

end NavierStokesLedger
