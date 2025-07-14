/-
  Minimal Continuity Theory
  =========================

  This file provides just the essential continuity facts needed for
  proving J_continuous in CostFunctional.lean, without the full mathlib overhead.

  Key approach: Use elementary composition of continuous functions.

  Author: Recognition Science Institute
-/

namespace RecognitionScience.Core.MiniContinuity

/-!
## Basic Continuity Definitions and Properties
-/

/-- A function f is continuous at a point if small changes in input yield small changes in output -/
def ContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

/-- A function is continuous on a set if it's continuous at every point in the set -/
def ContinuousOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ContinuousAt f x

/-- Continuous functions on subtype domains -/
def Continuous_subtype {P : ℝ → Prop} (f : {x : ℝ // P x} → ℝ) : Prop :=
  ∀ x : {x : ℝ // P x}, ContinuousAt (fun y => if h : P y then f ⟨y, h⟩ else 0) x.val

/-!
## Basic Continuous Functions
-/

/-- The identity function is continuous -/
theorem continuous_id : ContinuousOn (fun x : ℝ => x) Set.univ := by
  intro x _ ε hε
  use ε
  exact ⟨hε, fun y h => h⟩

/-- Constant functions are continuous -/
theorem continuous_const (c : ℝ) : ContinuousOn (fun _ : ℝ => c) Set.univ := by
  intro x _ ε hε
  use 1
  exact ⟨zero_lt_one, fun y h => by simp; exact hε⟩

/-- The reciprocal function 1/x is continuous on (0, ∞) -/
theorem continuous_inv_pos : ContinuousOn (fun x : ℝ => 1/x) {x : ℝ | x > 0} := by
  intro x hx ε hε
  -- For 1/x, we need |1/y - 1/x| < ε when |y - x| < δ
  -- |1/y - 1/x| = |x - y|/(xy) < ε
  -- Since y ≈ x, we can bound xy ≥ x²/2 for y close to x
  let δ := min (x/2) (ε * x^2 / 2)
  use δ
  constructor
  · -- δ > 0
    simp [δ]
    constructor
    · exact div_pos hx (by norm_num)
    · exact div_pos (mul_pos hε (pow_pos hx 2)) (by norm_num)
  · intro y hy
    -- Show |1/y - 1/x| < ε
    have hy_pos : y > 0 := by
      have : |y - x| < x/2 := by
        rw [δ] at hy
        exact lt_of_lt_of_le hy (min_le_left _ _)
      cases' abs_lt.mp this with h1 h2
      linarith [hx]
    have h_bound : |1/y - 1/x| = |x - y| / (x * y) := by
      rw [div_sub_div_eq_sub_div, abs_div]
      congr 1
      exact abs_sub_comm x y
    rw [h_bound]
    have h_xy_bound : x * y ≥ x^2 / 2 := by
      have : y ≥ x/2 := by
        have : |y - x| < x/2 := by
          rw [δ] at hy
          exact lt_of_lt_of_le hy (min_le_left _ _)
        cases' abs_lt.mp this with h1 h2
        linarith
      calc x * y ≥ x * (x/2) := mul_le_mul_of_nonneg_left this (le_of_lt hx)
      _ = x^2 / 2 := by ring
    have : |x - y| / (x * y) ≤ |x - y| / (x^2 / 2) := by
      rw [div_le_div_iff]
      · ring_nf; exact h_xy_bound
      · exact mul_pos hx hy_pos
      · exact div_pos (pow_pos hx 2) (by norm_num)
    calc |x - y| / (x * y) ≤ |x - y| / (x^2 / 2) := this
    _ = 2 * |x - y| / x^2 := by ring
    _ ≤ 2 * (ε * x^2 / 2) / x^2 := by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        have : |x - y| < ε * x^2 / 2 := by
          rw [δ] at hy
          exact lt_of_lt_of_le hy (min_le_right _ _)
        exact le_of_lt this
        norm_num
      · exact pow_pos hx 2
    _ = ε := by ring

/-!
## Continuity of Arithmetic Operations
-/

/-- Sum of continuous functions is continuous -/
theorem continuous_add {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
  ContinuousOn (fun x => f x + g x) s := by
  intro x hx ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf x hx (ε/2) (div_pos hε (by norm_num))
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg x hx (ε/2) (div_pos hε (by norm_num))
  use min δ₁ δ₂
  constructor
  · exact lt_min hδ₁ hδ₂
  · intro y hy
    have h₁' := h₁ y (lt_of_lt_of_le hy (min_le_left _ _))
    have h₂' := h₂ y (lt_of_lt_of_le hy (min_le_right _ _))
    calc |f y + g y - (f x + g x)| = |(f y - f x) + (g y - g x)| := by ring
    _ ≤ |f y - f x| + |g y - g x| := abs_add _ _
    _ < ε/2 + ε/2 := add_lt_add h₁' h₂'
    _ = ε := by ring

/-- Constant multiple of continuous function is continuous -/
theorem continuous_const_mul {f : ℝ → ℝ} {s : Set ℝ} (c : ℝ) (hf : ContinuousOn f s) :
  ContinuousOn (fun x => c * f x) s := by
  intro x hx ε hε
  by_cases h : c = 0
  · simp [h]
    exact continuous_const 0 x (Set.mem_univ x) ε hε
  · have hc_pos : |c| > 0 := abs_pos.mpr h
    obtain ⟨δ, hδ, hf'⟩ := hf x hx (ε / |c|) (div_pos hε hc_pos)
    use δ
    exact ⟨hδ, fun y hy => by
      rw [← mul_div_cancel ε (ne_of_gt hc_pos)]
      rw [abs_mul]
      exact mul_lt_mul_of_pos_left (hf' y hy) hc_pos⟩

/-- Division by nonzero constant is continuous -/
theorem continuous_div_const {f : ℝ → ℝ} {s : Set ℝ} (c : ℝ) (hc : c ≠ 0) (hf : ContinuousOn f s) :
  ContinuousOn (fun x => f x / c) s := by
  rw [show (fun x => f x / c) = (fun x => (1/c) * f x) by ext; ring]
  exact continuous_const_mul (1/c) hf

/-!
## Main Theorem for J(x) = (x + 1/x)/2
-/

/-- The function J(x) = (x + 1/x)/2 is continuous on (0, ∞) -/
theorem continuous_J_on_pos : ContinuousOn (fun x : ℝ => (x + 1/x) / 2) {x : ℝ | x > 0} := by
  -- J(x) = (x + 1/x)/2 = (1/2) * (x + 1/x)
  rw [show (fun x : ℝ => (x + 1/x) / 2) = (fun x => (1/2) * (x + 1/x)) by ext; ring]

  -- Apply continuous_const_mul with c = 1/2
  apply continuous_const_mul (1/2)

  -- Show that x + 1/x is continuous on (0, ∞)
  apply continuous_add
  · -- x is continuous on (0, ∞)
    exact fun x hx => continuous_id x (Set.mem_univ x)
  · -- 1/x is continuous on (0, ∞)
    exact continuous_inv_pos

/-- Bridge theorem: convert to subtype continuity for CostFunctional -/
theorem continuous_J_subtype : Continuous_subtype (fun x : {x : ℝ // x > 0} => (x.val + 1/x.val) / 2) := by
  intro x
  -- We need to show ContinuousAt (fun y => if h : y > 0 then (y + 1/y) / 2 else 0) x.val
  have h_pos : x.val > 0 := x.property
  have h_continuous := continuous_J_on_pos x.val h_pos
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h_continuous ε hε
  use δ
  constructor
  · exact hδ
  · intro y hy
    by_cases hy_pos : y > 0
    · simp [hy_pos]
      exact h y hy
    · -- Case y ≤ 0: this contradicts |y - x.val| < δ when δ is small enough
      simp [hy_pos]
      -- Since x.val > 0 and |y - x.val| < δ, we need δ < x.val to ensure y > 0
      -- But for any ε, we can choose δ small enough
      have : y > 0 := by
        by_contra h_not
        push_neg at h_not
        have : x.val ≤ y + |y - x.val| := by
          cases' le_or_lt y x.val with h1 h2
          · calc x.val ≤ y + (x.val - y) := le_add_of_sub_le (le_refl _)
            _ ≤ y + |y - x.val| := by rw [abs_sub_comm]; exact add_le_add_left (le_abs_self _) _
          · calc x.val = y + (x.val - y) := (add_sub_cancel' x.val y).symm
            _ = y + |x.val - y| := by rw [abs_of_pos (sub_pos.mpr h2)]
            _ = y + |y - x.val| := by rw [abs_sub_comm]
        have : x.val ≤ 0 := by
          calc x.val ≤ y + |y - x.val| := this
          _ < 0 + δ := add_lt_add_of_le_of_lt h_not hy
          _ = δ := zero_add δ
        exact lt_irrefl 0 (lt_of_le_of_lt this (lt_of_lt_of_le hy (le_of_lt hδ)))
      exact absurd this hy_pos

end RecognitionScience.Core.MiniContinuity
