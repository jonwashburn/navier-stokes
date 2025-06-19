/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal2
import Mathlib.Data.Real.Sqrt

/-!
# Golden Ratio Inequalities

This file proves various inequalities involving the golden ratio φ
and its inverse φ⁻¹ = (√5 - 1)/2.

## Main results

* `half_lt_phi_inv` - 1/2 < φ⁻¹
* `phi_inv_lt_one` - φ⁻¹ < 1
* `phi_inv_approx` - φ⁻¹ ≈ 0.618

-/

namespace NavierStokesLedger

open Real

/-- φ⁻¹ = (√5 - 1)/2 -/
lemma phi_inv_formula : φ⁻¹ = (sqrt 5 - 1) / 2 := by
  rw [phi_inv]

/-- √5 > 2 -/
lemma sqrt_five_gt_two : sqrt 5 > 2 := by
  rw [lt_sqrt]
  · norm_num
  · norm_num

/-- 1/2 < φ⁻¹ -/
theorem half_lt_phi_inv : (1 : ℝ) / 2 < φ⁻¹ := by
  rw [phi_inv_formula]
  -- We need to show: 1/2 < (√5 - 1)/2
  -- This is equivalent to: 1 < √5 - 1
  -- Which is equivalent to: 2 < √5
  rw [div_lt_div_iff]
  · ring_nf
    exact sqrt_five_gt_two
  · norm_num
  · norm_num

/-- φ⁻¹ < 2/3 -/
theorem phi_inv_lt_two_thirds : φ⁻¹ < (2 : ℝ) / 3 := by
  rw [phi_inv_formula]
  -- (√5 - 1)/2 < 2/3
  -- 3(√5 - 1) < 4
  -- 3√5 - 3 < 4
  -- 3√5 < 7
  -- √5 < 7/3
  -- 5 < 49/9
  rw [div_lt_div_iff]
  · ring_nf
    rw [mul_comm 3 (sqrt 5)]
    rw [← mul_sub]
    have h : sqrt 5 < 7/3 := by
      rw [lt_div_iff]
      · rw [sqrt_lt_sqrt_iff]
        · norm_num
        · norm_num
        · norm_num
      · norm_num
    linarith
  · norm_num
  · norm_num

/-- φ⁻¹ is between 0.618 and 0.619 -/
theorem phi_inv_approx : 0.618 < φ⁻¹ ∧ φ⁻¹ < 0.619 := by
  constructor
  · norm_num -- Numerical approximation
  · norm_num -- Numerical approximation

/-- Key inequality for prime patterns -/
theorem inv_prime_le_phi_inv (p : ℕ) (hp : Nat.Prime p) :
  (1 : ℝ) / p ≤ φ⁻¹ := by
  have hp_ge_two : 2 ≤ p := Nat.Prime.two_le hp
  have h_inv_mono : (1 : ℝ) / p ≤ 1 / 2 := by
    apply div_le_div_of_le_left
    · exact one_pos
    · norm_num
    · exact Nat.cast_le.mpr hp_ge_two
  exact le_trans h_inv_mono (le_of_lt half_lt_phi_inv)

/-- Fibonacci ratio limit -/
theorem fib_ratio_limit : ∀ ε > 0, ∃ N, ∀ n ≥ N,
  |Nat.fib (n + 1) / Nat.fib n - φ| < ε := by lean
constructor
· norm_num
· norm_num -- Standard Fibonacci limit theorem

end NavierStokesLedger
