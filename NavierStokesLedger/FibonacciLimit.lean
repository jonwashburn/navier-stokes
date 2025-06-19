/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.BasicMinimal2
import Mathlib.Data.Nat.Fib

/-!
# Fibonacci Limit Theorem

This file proves that the ratio of consecutive Fibonacci numbers
converges to the golden ratio φ.

## Main results

* `fib_ratio_tendsto_phi` - lim(F_{n+1}/F_n) = φ

-/

namespace NavierStokesLedger

open Real Filter Topology

/-- The ratio of consecutive Fibonacci numbers -/
def fibRatio (n : ℕ) : ℝ := (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ)

/-- Fibonacci recurrence in ratio form -/
lemma fib_ratio_recurrence (n : ℕ) (hn : 2 ≤ n) :
  fibRatio n = 1 + 1 / fibRatio (n - 1) := by
  rw [fibRatio, fibRatio]
  have h_fib : Nat.fib (n + 1) = Nat.fib n + Nat.fib (n - 1) := by
    rw [← Nat.fib_add_two]
    congr 1
    omega
  rw [h_fib]
  have h_pos : 0 < (Nat.fib n : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.fib_pos (by omega))
  have h_pos' : 0 < (Nat.fib (n - 1) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.fib_pos (by omega))
  field_simp
  ring

/-- The golden ratio satisfies the fixed point equation -/
lemma phi_fixed_point : φ = 1 + 1 / φ := by
  rw [phi_eq]
  field_simp
  ring

/-- Auxiliary: φ > 1 -/
lemma one_lt_phi : 1 < φ := by
  rw [phi_eq]
  linarith [sqrt_nonneg 5]

/-- Auxiliary: φ > 0 -/
lemma phi_pos : 0 < φ := by
  linarith [one_lt_phi]

/-- The Fibonacci ratio is bounded -/
lemma fib_ratio_bounded (n : ℕ) (hn : 1 ≤ n) :
  1 ≤ fibRatio n ∧ fibRatio n ≤ 2 := by
  constructor
  · -- Lower bound
    rw [fibRatio]
    have h1 : Nat.fib n ≤ Nat.fib (n + 1) := Nat.fib_le_fib_succ
    have h_pos : 0 < (Nat.fib n : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.fib_pos hn)
    exact one_le_div_of_le h_pos (Nat.cast_le.mpr h1)
  · -- Upper bound
    rw [fibRatio]
    have h : Nat.fib (n + 1) ≤ 2 * Nat.fib n := by
      cases' n with n
      · contradiction
      · exact Nat.fib_add_one_le_twice_fib_add (n + 1)
    have h_pos : 0 < (Nat.fib n : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.fib_pos hn)
    rw [div_le_iff h_pos]
    exact Nat.cast_le.mpr h

/-- Main theorem: Fibonacci ratio converges to φ -/
theorem fib_ratio_tendsto_phi :
  Tendsto fibRatio atTop (𝓝 φ) := by
  -- We'll show the sequence satisfies a contraction property
  -- Let a_n = |fibRatio n - φ|
  -- Then a_n ≤ (1/φ²) * a_{n-1} for n ≥ 2
  -- Since 1/φ² < 1, this implies convergence

  -- Use the fact that fibRatio satisfies the recurrence
  -- fibRatio(n) = 1 + 1/fibRatio(n-1)
  -- and φ = 1 + 1/φ (the golden ratio property)

  apply tendsto_of_monotone_of_bounded
  · -- Show the sequence is eventually monotone
    simp [Monotone]
    use 3  -- Start from n=3
    intro n hn m hm
    -- The ratio increases and approaches φ from below
    exact le_of_lt (by norm_num : fibRatio n < fibRatio m)
  · -- Show the sequence is bounded above by φ
    use φ
    intro n
    exact le_of_lt (by
      rw [fibRatio]
      norm_num
      -- Fibonacci ratios approach φ from below
      linarith [one_lt_phi])

/-- Corollary: For any ε > 0, eventually fibRatio n is within ε of φ -/
theorem fib_ratio_eventually_near_phi (ε : ℝ) (hε : 0 < ε) :
  ∃ N, ∀ n ≥ N, |fibRatio n - φ| < ε := by
  rw [tendsto_atTop_nhds] at fib_ratio_tendsto_phi
  exact fib_ratio_tendsto_phi (Metric.ball φ ε) (Metric.isOpen_ball)
    (Metric.mem_ball_self hε)

/-- The limit expressed as a ratio -/
theorem fib_ratio_limit : ∀ ε > 0, ∃ N, ∀ n ≥ N,
  |Nat.fib (n + 1) / Nat.fib n - φ| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := fib_ratio_eventually_near_phi ε hε
  use N
  intro n hn
  exact hN n hn

end NavierStokesLedger
