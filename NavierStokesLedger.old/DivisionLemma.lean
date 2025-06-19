/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal2
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Division Manipulation Lemma

This file proves the simple division manipulation lemma that was left
as a simp in the main proof.

## Main results

* `div_lt_iff_lt_mul` - Division inequality manipulation
* `vorticity_div_bound` - The specific lemma needed in the proof

-/

namespace NavierStokesLedger

open Real

/-- Basic division inequality: a/b < c ↔ a < b*c for b > 0 -/
theorem div_lt_iff_lt_mul {a b c : ℝ} (hb : 0 < b) :
  a / b < c ↔ a < b * c := by
  constructor
  · intro h
    rw [div_lt_iff hb] at h
    rw [mul_comm] at h
    exact h
  · intro h
    rw [div_lt_iff hb]
    rw [mul_comm]
    exact h

/-- The specific form needed in our proof -/
lemma vorticity_div_bound {a b c : ℝ} (hb : 0 < b) (h : a * b < c) :
  a < c / b := by
  rw [div_lt_iff_lt_mul hb] at h
  rw [mul_comm] at h
  exact h

/-- Alternative form with explicit steps -/
lemma vorticity_div_bound_explicit {a b c : ℝ} (hb : 0 < b) (h : a * b < c) :
  a < c / b := by
  -- We have a * b < c
  -- Divide both sides by b (valid since b > 0)
  have h1 : a < c / b := by
    rw [← mul_lt_iff_lt_div hb] at h
    exact h
  exact h1

/-- The bound used in the main theorem -/
theorem omega_bound_from_product {ω ν K : ℝ} (hν : 0 < ν)
  (h : ω * sqrt ν < K) : ω < K / sqrt ν := by
  have hsqrt : 0 < sqrt ν := sqrt_pos.mpr hν
  exact vorticity_div_bound hsqrt h

/-- Useful corollary for the bootstrap -/
theorem bootstrap_bound_manipulation {Ω ν C : ℝ} (hν : 0 < ν) :
  Ω * sqrt ν ≤ C ↔ Ω ≤ C / sqrt ν := by
  have hsqrt : 0 < sqrt ν := sqrt_pos.mpr hν
  constructor
  · intro h
    rw [← mul_le_iff_le_div hsqrt] at h
    exact h
  · intro h
    rw [← mul_le_iff_le_div hsqrt]
    exact h

/-- The golden ratio bound in the required form -/
theorem golden_ratio_vorticity_bound {Ω : ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
  (h : ∀ t ≥ 0, Ω t * sqrt ν < φ⁻¹) :
  ∀ t ≥ 0, Ω t < φ⁻¹ / sqrt ν := by
  intro t ht
  exact omega_bound_from_product hν (h t ht)

end NavierStokesLedger
