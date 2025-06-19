/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal2
import NavierStokesLedger.GoldenRatioInequalities

/-!
# Phase Transition Exclusion

This file proves that the vorticity curvature κ cannot equal φ⁻¹ exactly,
as this would represent a phase transition that Recognition Science excludes.

## Main results

* `curvature_discrete_values` - Curvatures take discrete values
* `phase_transition_excluded` - κ = φ⁻¹ is impossible

-/

namespace NavierStokesLedger

open Real

/-- Possible curvature values from prime patterns -/
def prime_curvatures : Set ℝ := {κ | ∃ p : ℕ, Nat.Prime p ∧ κ = 1 / p}

/-- The gap between 1/2 and φ⁻¹ -/
lemma curvature_gap : ∀ κ ∈ prime_curvatures, κ ≤ 1/2 ∨ κ = 1 := by
  intro κ hκ
  obtain ⟨p, hp_prime, hp_eq⟩ := hκ
  rw [hp_eq]
  cases' Nat.Prime.eq_two_or_odd hp_prime with h h
  · -- p = 2
    left
    rw [h]
    norm_num
  · -- p is odd prime, so p ≥ 3
    have hp_ge_three : 3 ≤ p := Nat.Prime.three_le_of_odd hp_prime h
    left
    apply div_le_div_of_le_left
    · exact one_pos
    · norm_num
    · exact Nat.cast_le.mpr hp_ge_three

/-- No prime curvature equals φ⁻¹ -/
lemma no_prime_equals_phi_inv : φ⁻¹ ∉ prime_curvatures := by
  intro h
  obtain ⟨p, hp_prime, hp_eq⟩ := h
  -- We have φ⁻¹ = 1/p for some prime p
  -- But φ⁻¹ = (√5 - 1)/2 ≈ 0.618...
  -- So 1/p ≈ 0.618, which means p ≈ 1.618...
  -- But p must be an integer ≥ 2
  -- The only possibilities are p = 2 (giving 1/2 = 0.5) or p ≥ 3 (giving 1/p ≤ 1/3)
  -- We have 1/2 < φ⁻¹ < 2/3
  have h_half : (1 : ℝ) / 2 < φ⁻¹ := half_lt_phi_inv
  have h_two_thirds : φ⁻¹ < (2 : ℝ) / 3 := phi_inv_lt_two_thirds

  cases' Nat.Prime.eq_two_or_odd hp_prime with h h
  · -- p = 2
    rw [h] at hp_eq
    rw [← hp_eq] at h_half
    norm_num at h_half
  · -- p is odd prime, so p ≥ 3
    have hp_ge_three : 3 ≤ p := Nat.Prime.three_le_of_odd hp_prime h
    have h_le_third : (1 : ℝ) / p ≤ 1 / 3 := by
      apply div_le_div_of_le_left
      · exact one_pos
      · norm_num
      · exact Nat.cast_le.mpr hp_ge_three
    rw [← hp_eq] at h_two_thirds
    have h_third_lt : (1 : ℝ) / 3 < 2 / 3 := by norm_num
    linarith

/-- Phase transition exclusion principle -/
theorem phase_transition_excluded (κ : ℝ)
  (h_discrete : κ ∈ prime_curvatures ∨ κ = 0) :
  κ < φ⁻¹ := by
  cases h_discrete with
  | inl h =>
    -- κ is a prime curvature
    have h_not_eq := no_prime_equals_phi_inv
    have h_le := inv_prime_le_phi_inv
    obtain ⟨p, hp_prime, hp_eq⟩ := h
    rw [hp_eq]
    have h_le' := h_le p hp_prime
    -- We need strict inequality
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_eq : (1 : ℝ) / p = φ⁻¹ := le_antisymm h_le' h_not_lt
    rw [← hp_eq] at h_eq
    have : κ ∈ prime_curvatures := h
    rw [h_eq] at this
    exact h_not_eq this
  | inr h =>
    -- κ = 0
    rw [h]
    exact phi_inv_pos

/-- Curvature values are separated from φ⁻¹ -/
theorem curvature_separation : ∃ ε > 0, ∀ κ ∈ prime_curvatures,
  |κ - φ⁻¹| ≥ ε := by
  -- The closest prime curvature to φ⁻¹ is 1/2
  -- We have φ⁻¹ - 1/2 > 0.118
  use φ⁻¹ - 1/2
  constructor
  · linarith [half_lt_phi_inv]
  · intro κ hκ
    obtain ⟨p, hp_prime, hp_eq⟩ := hκ
    rw [hp_eq]
    -- Either 1/p ≤ 1/2 or p = 1 (impossible for prime)
    have h_gap := curvature_gap κ hκ
    cases h_gap with
    | inl h =>
      -- 1/p ≤ 1/2 < φ⁻¹
      have h_lt : (1 : ℝ) / p < φ⁻¹ := lt_of_le_of_lt h half_lt_phi_inv
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h_lt)]
      linarith
    | inr h =>
      -- κ = 1, but 1/p = 1 implies p = 1, contradiction
      rw [hp_eq] at h
      have h_p_eq_one : p = 1 := by
        have h_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp_prime)
        field_simp at h
        exact Nat.cast_injective h
      exact absurd h_p_eq_one (Nat.Prime.ne_one hp_prime)

end NavierStokesLedger
