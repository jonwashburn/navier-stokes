/-
Simple Test of Bridge Lemmas
============================

This file tests that we can use the proven bridge lemmas.
-/

import NavierStokesLedger.RSClassicalBridge

namespace NavierStokes.SimpleTest

open RSClassical Real

/-- Test using the maximum principle -/
theorem test_max_principle (u : ℝ → ℝ)
    (h_decay : ∀ t s, 0 ≤ s → s ≤ t → u t ≤ u s) :
    ∀ t ≥ 0, u t ≤ u 0 := by
  intro t ht
  -- Direct application of our proven lemma
  exact maximum_principle_recognition u h_decay t ht

/-- Test using Bernstein constant -/
theorem test_bernstein : ∃ C > 0, C = phi := by
  -- Direct application of our proven lemma
  exact bernstein_phi 1 (by norm_num : (1 : ℝ) > 0)

/-- Example: Simple bound using φ -/
theorem simple_phi_bound (f : ℝ → ℝ) (h : ∀ x, f x ≤ phi * x) :
    ∀ x ≥ 0, f x ≤ 2 * x := by
  intro x hx
  calc f x ≤ phi * x := h x
       _ ≤ 2 * x := by
         by_cases h0 : x = 0
         · rw [h0]
           simp
         · apply le_of_lt
           apply mul_lt_mul_of_pos_right
           exact phi_lt_two
           exact lt_of_le_of_ne hx (Ne.symm h0)

end NavierStokes.SimpleTest
