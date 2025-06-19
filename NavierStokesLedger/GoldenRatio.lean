/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal

/-!
# Golden Ratio Properties

This file contains properties of the golden ratio φ = (1 + √5)/2
and its connection to the Navier-Stokes regularity proof.

## Main results

* `phi_sq` - φ² = φ + 1
* `phi_inv_val` - φ⁻¹ = (√5 - 1)/2
* `C_star_lt_phi_inv` - The key inequality C* < φ⁻¹

-/

namespace NavierStokesLedger

open Real

/-- Golden ratio is positive -/
lemma phi_pos : 0 < φ := by
  rw [φ]
  norm_num
  apply add_pos_of_pos_of_nonneg
  · norm_num
  · exact Real.sqrt_nonneg _

/-- Golden ratio satisfies φ² = φ + 1 -/
lemma phi_sq : φ ^ 2 = φ + 1 := by
  rw [φ]
  field_simp
  ring_nf
  -- Simplify √5² = 5
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  ring

/-- Golden ratio inverse value -/
lemma phi_inv_val : φ⁻¹ = (Real.sqrt 5 - 1) / 2 := by
  have h : φ ^ 2 = φ + 1 := phi_sq
  have hp : φ ≠ 0 := ne_of_gt phi_pos
  -- From φ² = φ + 1, we get φ² - φ - 1 = 0
  -- So φ(φ - 1) = 1, hence φ⁻¹ = φ - 1
  have : φ * (φ - 1) = 1 := by
    rw [mul_sub, mul_one, ← sq, h]
    ring
  have : φ⁻¹ = φ - 1 := by
    rw [← mul_inv_eq_one] at this
    rw [← this, mul_comm]
    simp
  rw [this, φ]
  field_simp
  ring

/-- Golden ratio inverse is less than 1 -/
lemma phi_inv_lt_one : φ⁻¹ < 1 := by
  rw [phi_inv_val]
  norm_num
  -- Need √5 < 3
  have : Real.sqrt 5 < 3 := by
    have h : 5 < 9 := by norm_num
    have : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ 5) h
    rwa [Real.sqrt_nine] at this
  linarith

/-- Golden ratio inverse is approximately 0.618 -/
lemma phi_inv_approx : 0.618 < φ⁻¹ ∧ φ⁻¹ < 0.619 := by
  rw [phi_inv_val]
  constructor
  · -- 0.618 < (√5 - 1)/2
    norm_num
    -- Need 2.236 < √5
    have : (2236 : ℝ) / 1000 < Real.sqrt 5 := by
      have h1 : ((2236 : ℝ) / 1000) ^ 2 = 4999696 / 1000000 := by norm_num
      have h2 : 4999696 / 1000000 < 5 := by norm_num
      have h3 : ((2236 : ℝ) / 1000) ^ 2 < 5 := by rw [h1]; exact h2
      have h4 : 0 ≤ (2236 : ℝ) / 1000 := by norm_num
      exact Real.sq_lt_sq' h4 (Real.sqrt_nonneg _) |>.mp h3
    linarith
  · -- (√5 - 1)/2 < 0.619
    norm_num
    -- Need √5 < 2.238
    have : Real.sqrt 5 < (2238 : ℝ) / 1000 := by
      have h1 : 5 < ((2238 : ℝ) / 1000) ^ 2 := by norm_num
      have h2 : Real.sqrt 5 < Real.sqrt (((2238 : ℝ) / 1000) ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num : 0 ≤ 5) h1
      rwa [Real.sqrt_sq (by norm_num : 0 ≤ (2238 : ℝ) / 1000)] at h2
    linarith

/-- The bootstrap constant K ≈ 0.45 -/
def bootstrapConstant : ℝ := 0.45

/-- The key theorem: bootstrap constant is less than φ⁻¹ -/
theorem bootstrap_less_than_golden : bootstrapConstant < φ⁻¹ := by
  have ⟨h, _⟩ := phi_inv_approx
  rw [bootstrapConstant]
  linarith

/-- Alternative proof of C* < φ⁻¹ using exact computation -/
theorem C_star_lt_phi_inv_exact : C_star < φ⁻¹ := by
  rw [C_star, phi_inv_val]
  norm_num
  -- Need to show 0.1 < √5 - 1
  -- Since √5 > 2.236, we have √5 - 1 > 1.236 > 0.1
  have : (2236 : ℝ) / 1000 < Real.sqrt 5 := by
    have h1 : ((2236 : ℝ) / 1000) ^ 2 = 4999696 / 1000000 := by norm_num
    have h2 : 4999696 / 1000000 < 5 := by norm_num
    have h3 : ((2236 : ℝ) / 1000) ^ 2 < 5 := by rw [h1]; exact h2
    have h4 : 0 ≤ (2236 : ℝ) / 1000 := by norm_num
    exact Real.sq_lt_sq' h4 (Real.sqrt_nonneg _) |>.mp h3
  linarith

end NavierStokesLedger
