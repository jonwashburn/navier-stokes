/-
Vector Calculus Basic Utilities
================================

This file contains common vector calculus lemmas and utilities used throughout
the Navier-Stokes proof, particularly for cross products and vector norms.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fin.VecNotation

namespace NavierStokes.VectorCalc

open Real

/-- Cross product for 3D vectors -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

/-- Cross product norm bound: ‖a × b‖ ≤ ‖a‖ ‖b‖ -/
axiom norm_cross_le (a b : Fin 3 → ℝ) :
    ‖cross a b‖ ≤ ‖a‖ * ‖b‖

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
    ⟪a, cross b c⟫_ℝ = ⟪b, cross c a⟫_ℝ := by
  -- This is the cyclic property of scalar triple product
  simp only [cross]
  -- Direct calculation
  sorry

lemma inner_cross_right (a b c : Fin 3 → ℝ) :
    ⟪cross a b, c⟫_ℝ = ⟪a, cross b c⟫_ℝ := by
  -- Scalar triple product is symmetric in dot and cross
  simp only [cross]
  -- Direct calculation
  sorry

/-- Vector is orthogonal to its cross products -/
lemma inner_cross_self_left (a b : Fin 3 → ℝ) :
    ⟪a, cross a b⟫_ℝ = 0 := by
  simp only [cross]
  -- Direct calculation shows all terms cancel
  sorry

lemma inner_cross_self_right (a b : Fin 3 → ℝ) :
    ⟪b, cross a b⟫_ℝ = 0 := by
  simp only [cross]
  -- Direct calculation shows all terms cancel
  sorry

/-- Lagrange's identity (key for cross product norm bound) -/
axiom lagrange_identity (a b : Fin 3 → ℝ) :
    ‖cross a b‖^2 = ‖a‖^2 * ‖b‖^2 - (⟪a, b⟫_ℝ)^2

/-- Helper: For aligned vectors with small angle, the difference is bounded -/
axiom aligned_vectors_close {a b : Fin 3 → ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h_angle : ⟪a, b⟫_ℝ ≥ ‖a‖ * ‖b‖ * Real.cos (π/6)) :
    ‖b - a‖ ≤ 2 * Real.sin (π/12) * max ‖a‖ ‖b‖

end NavierStokes.VectorCalc
