/-
Vector Calculus Basic Utilities
================================

This file contains common vector calculus lemmas and utilities used throughout
the Navier-Stokes proof, particularly for cross products and vector norms.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace NavierStokes.VectorCalc

open Real

/-- Cross product for 3D vectors -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

/-- Cross product norm bound: ‖a × b‖ ≤ ‖a‖ ‖b‖ -/
theorem norm_cross_le (a b : Fin 3 → ℝ) :
    ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  -- This follows from Lagrange's identity and Cauchy-Schwarz
  -- ‖a × b‖² = ‖a‖² ‖b‖² - ⟨a, b⟩²
  -- Since ⟨a, b⟩² ≤ ‖a‖² ‖b‖² by Cauchy-Schwarz
  -- We have ‖a × b‖² ≤ ‖a‖² ‖b‖²

  -- First, use Lagrange's identity
  have h_lagrange := lagrange_identity a b

  -- Apply Cauchy-Schwarz: |⟨a, b⟩| ≤ ‖a‖ ‖b‖
  have h_cs : (⟪a, b⟫_ℝ)^2 ≤ ‖a‖^2 * ‖b‖^2 := by
    have := InnerProductSpace.norm_inner_le_norm a b
    rw [abs_le_iff_sq_le_sq] at this
    exact this.2
    · exact mul_nonneg (norm_nonneg a) (norm_nonneg b)
    · exact abs_nonneg _

  -- Therefore ‖cross a b‖² ≤ ‖a‖² ‖b‖²
  rw [h_lagrange]
  linarith

  -- Taking square roots gives the result
  have h_sq : ‖cross a b‖^2 ≤ (‖a‖ * ‖b‖)^2 := by
    rw [h_lagrange, mul_pow]
    linarith

  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg a) (norm_nonneg b)) h_sq

/-- Cross product is antisymmetric -/
lemma cross_antisymm (a b : Fin 3 → ℝ) :
    cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Cross product with self is zero -/
lemma cross_self (a : Fin 3 → ℝ) :
    cross a a = 0 := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Jacobi identity for cross product -/
lemma cross_jacobi (a b c : Fin 3 → ℝ) :
    cross a (cross b c) + cross b (cross c a) + cross c (cross a b) = 0 := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Cross product is bilinear -/
lemma cross_add_left (a b c : Fin 3 → ℝ) :
    cross (a + b) c = cross a c + cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_smul_left (r : ℝ) (a b : Fin 3 → ℝ) :
    cross (r • a) b = r • cross a b := by
  ext i
  fin_cases i <;> simp [cross, Pi.smul_apply] <;> ring

/-- Dot product of vector with cross product (scalar triple product property) -/
lemma inner_cross_left (a b c : Fin 3 → ℝ) :
    Inner.inner a (cross b c) = Inner.inner b (cross c a) := by
  -- This is the cyclic property of scalar triple product
  simp only [PiLp.inner_apply, cross]
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_three]
  ring

lemma inner_cross_right (a b c : Fin 3 → ℝ) :
    Inner.inner (cross a b) c = Inner.inner a (cross b c) := by
  -- Scalar triple product is symmetric in dot and cross
  simp only [PiLp.inner_apply, cross]
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_three]
  ring

/-- Vector is orthogonal to its cross products -/
lemma inner_cross_self_left (a b : Fin 3 → ℝ) :
    Inner.inner a (cross a b) = 0 := by
  simp only [PiLp.inner_apply, cross]
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_three]
  ring

lemma inner_cross_self_right (a b : Fin 3 → ℝ) :
    Inner.inner b (cross a b) = 0 := by
  simp only [PiLp.inner_apply, cross]
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_three]
  ring

/-- Lagrange's identity (key for cross product norm bound) -/
theorem lagrange_identity (a b : Fin 3 → ℝ) :
    ‖cross a b‖^2 = ‖a‖^2 * ‖b‖^2 - (⟪a, b⟫_ℝ)^2 := by
  -- Direct computation using the definition of cross product and norm
  simp only [sq, PiLp.norm_sq_eq_inner, PiLp.inner_apply, cross]
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_three]
  ring

/-- Helper: For aligned vectors with small angle, the difference is bounded -/
theorem aligned_vectors_close {a b : Fin 3 → ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h_angle : ⟪a, b⟫_ℝ ≥ ‖a‖ * ‖b‖ * Real.cos (π/6)) :
    ‖b - a‖ ≤ 2 * Real.sin (π/12) * max ‖a‖ ‖b‖ := by
  -- This follows from the law of cosines and triangle inequality
  -- When vectors are nearly aligned (angle ≤ π/6), their difference is small

  -- Law of cosines: ‖b - a‖² = ‖a‖² + ‖b‖² - 2⟨a,b⟩
  have h_law : ‖b - a‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * ⟪a, b⟫_ℝ := by
    rw [norm_sub_sq_real]

  -- Since ⟨a,b⟩ ≥ ‖a‖‖b‖cos(π/6), we have
  -- ‖b - a‖² ≤ ‖a‖² + ‖b‖² - 2‖a‖‖b‖cos(π/6)
  have h_bound : ‖b - a‖^2 ≤ ‖a‖^2 + ‖b‖^2 - 2 * ‖a‖ * ‖b‖ * Real.cos (π/6) := by
    rw [h_law]
    gcongr
    exact h_angle

  -- Using cos(π/6) = √3/2 and algebraic manipulation
  -- We can show ‖b - a‖² ≤ 4sin²(π/12) * max(‖a‖², ‖b‖²)
  -- Taking square roots gives the result

  sorry -- TODO: Complete the algebraic manipulation

end NavierStokes.VectorCalc
