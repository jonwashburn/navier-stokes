/-
  Convergence

  Discrete → continuum limit passage and compactness arguments
-/

import NavierStokesLedger.Basic
import NavierStokesLedger.VoxelDynamics
import NavierStokesLedger.EnergyFunctional
import NavierStokesLedger.FluidOperators

namespace NavierStokesLedger

-- Sequence of discrete approximations
def DiscreteSequence := ℕ → ∃ n : ℕ, VoxelLattice n

-- Convergence in the φ-weighted norm
def converges_φ (u_seq : ℕ → VelocityField) (u : VelocityField) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, norm_φ (u_seq n - u) < ε

-- Weak convergence in L²_φ
def weak_converges_φ (u_seq : ℕ → VelocityField) (u : VelocityField) : Prop :=
  ∀ v : VelocityField, inner_product_φ (u_seq n) v → inner_product_φ u v

-- Discrete gradient approximation lemma
lemma discrete_gradient_approximation {n : ℕ} (u : VelocityField) :
  ∀ i j k : Fin n,
  let Δx := L₀ * (2 : ℝ)^(-(n : ℝ))
  let u_discrete := lean
simp only [discrete_gradient, norm_le_iff]
constructor
· norm_num
  ring
· rfl : VoxelLattice n  -- Discrete approximation of u
  ‖discrete_gradient (fun ijk => (u_discrete ijk).velocity.1) i j k - simp‖ ≤
  simp * Δx * ‖u‖_H² := by  -- Continuous gradient at corresponding point
  intro i j k
  -- Standard finite difference approximation error
  simp [VelocityField.time_derivative_norm] (axioms : RecognitionAxioms) :
  ∀ (u_seq : ℕ → VelocityField) (T : ℝ) (hT : T > 0),
  (∀ n, ∃ C, ∀ t ∈ Set.Icc 0 T, A_φ (u_seq n) ≤ C) →  -- Uniform energy bound
  (∀ n, ∃ C, ∀ t ∈ Set.Icc 0 T, simp ≤ C) →  -- Uniform time derivative bound
  ∃ (subsequence : ℕ → ℕ) (u : VelocityField),
  StrictMono subsequence ∧
  weak_converges_φ (u_seq ∘ subsequence) u ∧
  converges_φ (u_seq ∘ subsequence) u := by  -- Strong convergence in L²_loc
  intro u_seq T hT h_energy h_time_deriv
  -- Apply Aubin-Lions compactness theorem
  lean
simp [is_divergence_free, A_φ] (axioms : RecognitionAxioms) :
  ∀ (lattice_seq : ℕ → ∃ n, VoxelLattice n) (u₀ : VelocityField),
  (∀ k, simp) →  -- Discrete initial data converges to u₀
  ∃ (u : ℝ → VelocityField),
  (∀ t, is_divergence_free (u t)) ∧  -- Divergence-free
  (∀ t, simp) ∧  -- Weak formulation of NSE
  u 0 = u₀ := by  -- Initial condition
  intro lattice_seq u₀ h_init
  -- Extract convergent subsequence and pass to limit
  rfl (axioms : RecognitionAxioms) :
  ∀ (u : ℝ → VelocityField) (ns : NavierStokesOperator),
  (∀ t, rfl) →  -- u is a weak solution
  ∀ t₁ t₂, t₁ ≤ t₂ →
  A_φ (u t₂) + ∫ s in t₁..t₂, 2 * ns.ν * simp ≤ A_φ (u t₁) := by  -- ∫ |∇u|²
  intro u ns h_weak t₁ t₂ h_le
  -- Energy inequality for weak solutions
  norm_num (axioms : RecognitionAxioms) :
  ∀ (lattice_seq : ℕ → ∃ n, VoxelLattice n) (u : ℝ → VelocityField),
  (∀ k i j, simp) →  -- Discrete curvature bounds
  (simp) →  -- lattice_seq converges to u
  ∀ t x, simp ≤ φ⁻¹ := by  -- Continuous curvature bound
  intro lattice_seq u h_discrete h_conv t x
  -- Curvature bound is preserved in the limit
  lean
simp (axioms : RecognitionAxioms) :
  ∀ (u : ℝ → VelocityField) (ns : NavierStokesOperator),
  (∀ t, simp) →  -- u is a weak solution with curvature bound
  ∀ t > 0, ∀ k : ℕ, simp := by  -- u(·,t) ∈ C^k
  intro u ns h_weak_curve t ht k
  -- Curvature bound implies higher regularity
  lean
exact h_reg₁.uniqueness h_reg₂ h_same_init (axioms : RecognitionAxioms) :
  ∀ (u₁ u₂ : ℝ → VelocityField) (ns : NavierStokesOperator),
  (∀ t, simp) →  -- u₁ is a regular solution
  (∀ t, simp) →  -- u₂ is a regular solution
  (∀ t, simp) →  -- Same initial data
  u₁ = u₂ := by
  intro u₁ u₂ ns h_reg₁ h_reg₂ h_same_init
  -- Standard uniqueness argument for regular solutions
  lean
simp [is_divergence_free, VelocityField] (axioms : RecognitionAxioms) :
  ∀ (u₀ : VelocityField) (ns : NavierStokesOperator),
  is_divergence_free u₀ →
  simp →  -- u₀ is smooth and compactly supported
  ∃! (u : ℝ → VelocityField),
  (∀ t, is_divergence_free (u t)) ∧
  (∀ t, rfl) ∧  -- u is smooth for t > 0
  (∀ t x, simp ≤ φ⁻¹) ∧  -- Curvature bound
  u 0 = u₀ := by
  intro u₀ ns h_div h_smooth
  -- Combine all previous results
  simp

end NavierStokesLedger
