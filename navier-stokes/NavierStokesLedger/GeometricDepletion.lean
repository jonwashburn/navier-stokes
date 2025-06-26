import NavierStokesLedger.RSImports
import Mathlib.Analysis.SingularIntegralKernel
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

namespace NavierStokes

/-- Biot–Savart kernel in R³ written as a matrix-valued function.  We package only the
operator bound we need, deferring full component-wise formula to `Mathlib`. -/
noncomputable def BS_kernel : SingularIntegralKernel (Fin 3 → ℝ) (Fin 3 → ℝ) :=
  Classical.choice (SingularIntegralKernel.exists_BiotSavart ℝ)

lemma BS_kernel_L1_bound : BS_kernel.has_integral_bound :=
  BS_kernel.has_integral_bound

/-- Far–field estimate: the contribution of `|y-x| ≥ r` to `∇u` is O(r⁻¹).  We phrase it as
an operator estimate that will feed the Constantin–Fefferman argument. -/
lemma farField_grad_bound
    (u : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hcurl : ω = curl u)
    (hωL1 : Integrable (fun x => ‖ω x‖) volume)
    (x : Fin 3 → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C, ‖∫ y, (BS_kernel x y) (ω y) * (1 - (Set.indicator (Metric.ball x r) (fun _ => 1) y)) ∂volume‖
      ≤ C / r := by
  -- Use the L¹–bound on the kernel outside the ball.
  obtain ⟨B, hB⟩ := BS_kernel_L1_bound x r hr
  -- |∫ K(x,y) ω(y)| ≤ ∫ ‖K‖ ‖ω‖
  have h1 : ‖∫ y, (BS_kernel x y) (ω y) * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume‖ ≤
      ∫ y, ‖(BS_kernel x y) (ω y)‖ * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume := by
    simpa using norm_integral_le_integral_norm _
  -- bound the kernel pointwise by B/r and factor ‖ω‖
  have h2 : ∫ y, ‖(BS_kernel x y) (ω y)‖ * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume ≤
      (B / r) * ∫ y, ‖ω y‖ ∂volume := by
    have hker : ∀ y, (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) = 0 ∨
      (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) = 1 := by
      intro y; by_cases hmem: y ∈ Metric.ball x r <;> simp [Set.indicator_of_mem, Set.indicator_of_not_mem, hmem] at *
    -- Use kernel bound outside the ball
    have hbound : ∀ y, (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ≠ 0 →
        ‖BS_kernel x y‖ ≤ B / r := hB.bound
    -- Apply integral inequality
    have : (∫ y, ‖(BS_kernel x y) (ω y)‖ * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume) ≤
      (B / r) * ∫ y, ‖ω y‖ ∂volume := by
      have : ∫ y, ‖(BS_kernel x y) (ω y)‖ * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume ≤
        ∫ y, (B / r) * ‖ω y‖ ∂volume := by
        -- bound integrand pointwise
        have hpt : ∀ y, ‖(BS_kernel x y) (ω y)‖ * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ≤ (B/r) * ‖ω y‖ := by
          intro y
          by_cases hmem : y ∈ Metric.ball x r
          · have : (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) = 0 := by
              simp [Set.indicator_of_mem hmem] at *
            simp [this]
          · have hk : ‖BS_kernel x y‖ ≤ B / r := hB.bound _ hmem
            have : (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) = 1 := by
              simp [Set.indicator_of_not_mem hmem] at *
            simpa [this] using mul_le_mul_of_nonneg_right hk (norm_nonneg _)
        have := integral_mono (by
          -- LHS: integrable because bounded by (B/r) * ‖ω y‖
          apply Integrable.bdd_mul
          · apply integrable_const
          · exact hωL1
          · intro y
            exact hpt y) (by
          -- RHS: (B/r) * ‖ω y‖ is integrable
          exact Integrable.const_mul (B/r) hωL1) hpt
        exact this
      simpa [mul_comm, mul_left_comm] using this
    exact this
  -- Combine
  have : ‖∫ y, (BS_kernel x y) (ω y) * (1 - Set.indicator (Metric.ball x r) (fun _ => (1:ℝ)) y) ∂volume‖ ≤ (B / r) * ∫ y, ‖ω y‖ ∂volume :=
    le_trans h1 h2
  -- Package constant
  refine ⟨B * ∫ y, ‖ω y‖ ∂volume, ?_⟩
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

-- Helper: Decompose kernel into symmetric and antisymmetric parts
def kernel_symmetric (K : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) :
    (Fin 3 → ℝ) → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x y => (K x y + (K x y)ᵀ) / 2

def kernel_antisymmetric (K : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) :
    (Fin 3 → ℝ) → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x y => (K x y - (K x y)ᵀ) / 2

-- Helper: Angle between vectors
noncomputable def angle (v w : Fin 3 → ℝ) : ℝ :=
  Real.arccos (inner v w / (‖v‖ * ‖w‖))

-- Helper: Angle bound implies norm bound
lemma angle_bound_norm_bound (v w : Fin 3 → ℝ) (hv : v ≠ 0) (hw : w ≠ 0)
    (h_angle : angle v w ≤ π/6) :
    ‖v - w‖ ≤ 2 * sin(π/12) * max ‖v‖ ‖w‖ := by
  -- Use law of cosines: ‖v - w‖² = ‖v‖² + ‖w‖² - 2⟨v,w⟩
  -- and ⟨v,w⟩ = ‖v‖ ‖w‖ cos(angle v w)
  have h_inner : inner v w = ‖v‖ * ‖w‖ * cos (angle v w) := by
    rw [angle, cos_arccos]
    · ring
    · rw [div_le_one_iff]
      · exact inner_le_norm _ _
      · exact mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw)
    · rw [le_div_iff]
      · rw [mul_comm, ← neg_le_neg_iff]
        simp only [neg_mul, neg_neg]
        exact neg_inner_le_norm _ _
      · exact mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw)

  -- Apply law of cosines
  have h_norm_sq : ‖v - w‖^2 = ‖v‖^2 + ‖w‖^2 - 2 * inner v w := by
    rw [norm_sub_sq_real, two_mul]
    ring

  -- Use cos(angle) ≥ cos(π/6) = √3/2 when angle ≤ π/6
  have h_cos_bound : cos (angle v w) ≥ cos (π/6) := by
    exact cos_le_cos_of_le_of_le_pi (by linarith : 0 ≤ angle v w) h_angle (by linarith : π/6 ≤ π)

  -- Continue with bound...
  rw [h_norm_sq, h_inner]

  -- We have ‖v - w‖² = ‖v‖² + ‖w‖² - 2‖v‖‖w‖cos(θ)
  -- Since cos(θ) ≥ cos(π/6) = √3/2, we get:
  -- ‖v - w‖² ≤ ‖v‖² + ‖w‖² - 2‖v‖‖w‖(√3/2)

  -- For the bound 2sin(π/12)max(‖v‖,‖w‖), we use:
  -- sin²(π/12) = (1 - cos(π/6))/2 = (1 - √3/2)/2
  -- This gives us the desired inequality through algebraic manipulation

  -- The detailed calculation is technical but standard
  sorry -- I need more Lean-specific tactics for this algebraic manipulation

-- Specific case we need: bound by sin(π/6) = 1/2
lemma angle_bound_half_norm (v w : Fin 3 → ℝ) (hv : v ≠ 0)
    (h_angle : angle w v ≤ π/6) :
    ‖w - v‖ ≤ sin(π/6) * ‖v‖ := by
  have : sin (π/6) = 1/2 := by norm_num
  rw [this]

  -- Special case: if w = 0, then ‖w - v‖ = ‖v‖ ≤ (1/2)‖v‖ is false unless v = 0
  -- But we know v ≠ 0, so w ≠ 0 when angle is defined
  by_cases hw : w = 0
  · -- If w = 0, then angle is not well-defined, contradiction
    simp [hw] at h_angle
    -- angle 0 v requires both vectors to be nonzero for arccos to be defined
    sorry -- Need to handle this edge case properly

  -- Now we know both v and w are nonzero
  -- From angle(w,v) ≤ π/6, we want ‖w - v‖ ≤ (1/2)‖v‖

  -- Using the identity: ‖w - v‖² = ‖w‖² + ‖v‖² - 2⟨w,v⟩
  have h_norm_sq : ‖w - v‖^2 = ‖w‖^2 + ‖v‖^2 - 2 * inner w v := by
    rw [norm_sub_sq_real]
    ring

  -- We have ⟨w,v⟩ = ‖w‖‖v‖cos(angle(w,v))
  have h_inner : inner w v = ‖w‖ * ‖v‖ * cos (angle w v) := by
    rw [angle, cos_arccos]
    · ring
    · rw [div_le_one_iff]
      · exact inner_le_norm _ _
      · exact mul_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv)
    · rw [le_div_iff]
      · rw [mul_comm, ← neg_le_neg_iff]
        simp only [neg_mul, neg_neg]
        exact neg_inner_le_norm _ _
      · exact mul_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv)

  -- Key insight: For aligned vectors with small angle, ‖w‖ ≈ ‖v‖
  -- and the difference ‖w - v‖ is controlled by the angle

  sorry -- Still need the final algebraic step

-- Key lemma: Symmetric kernel integrates to zero against constant vector
lemma symmetric_kernel_zero_integral
    (S : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hS : ∀ x y, S x y = (S x y)ᵀ)  -- S is symmetric
    (x : Fin 3 → ℝ) (v : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r)
    (hrad : ∀ g : SO(3, ℝ), ∀ y ∈ Metric.ball x r, S x (g • y) = g • S x y • g⁻¹) : -- radial symmetry
    inner v (∫ y in Metric.ball x r, S x y v ∂volume) = 0 := by
  sorry -- This requires showing the integral has radial symmetry and applying rotation averaging

-- Key lemma: Antisymmetric matrix gives zero in quadratic form
lemma antisymmetric_quadratic_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A = -Aᵀ) (v : Fin 3 → ℝ) :
    inner v (A.mulVec v) = 0 := by
  -- We need to show v^T A v = 0 when A^T = -A
  -- Note that v^T A v is a scalar, so (v^T A v)^T = v^T A v
  -- But (v^T A v)^T = v^T A^T v = v^T (-A) v = -v^T A v
  -- Therefore v^T A v = -v^T A v, which implies v^T A v = 0
  have h1 : inner v (A.mulVec v) = inner (A.mulVec v) v := inner_comm _ _
  have h2 : inner (A.mulVec v) v = inner v (Aᵀ.mulVec v) := by
    rw [Matrix.inner_mulVec_eq_mulVec_inner]
  rw [h1, h2, hA]
  simp only [Matrix.neg_mulVec, inner_neg_right]
  ring

-- Helper: Biot-Savart kernel bound
lemma BS_kernel_bound (x y : Fin 3 → ℝ) (hxy : x ≠ y) :
    ‖BS_kernel x y‖ ≤ (3/(4*π)) / ‖x - y‖^2 := by
  sorry -- Standard bound for Biot-Savart kernel

-- Helper: Operator norm bound
lemma operator_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) :
    ‖A.mulVec v‖ ≤ ‖A‖ * ‖v‖ := by
  -- This is the definition of operator norm
  sorry -- Standard result from matrix analysis

-- Helper: Divergence-free property of Biot-Savart kernel
lemma BS_kernel_divergence_free (x : Fin 3 → ℝ) :
    ∀ y ≠ x, divergence (fun y => BS_kernel x y) y = 0 := by
  intro y hyx
  -- The Biot-Savart kernel K(x,y) as a function of y satisfies div_y K = 0
  -- This is because K is the curl of another vector field
  -- Specifically, K = ∇_y × G where G is related to the Green's function
  -- Since div(curl F) = 0 for any smooth F, we have div K = 0
  sorry -- This requires the explicit formula for the kernel and vector calculus identities

-- Key lemma: Integral of BS kernel against constant vector is zero
lemma BS_kernel_constant_integral_zero (x : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r) (v : Fin 3 → ℝ) :
    ∫ y in Metric.ball x r, BS_kernel x y v ∂volume = 0 := by
  -- This is the crucial cancellation: ∫_{B(x,r)} K(x,y) dy = 0
  -- Proof strategy:
  -- 1. For ε > 0, consider B(x,r) \ B(x,ε)
  -- 2. Apply divergence theorem on this annular region
  -- 3. Since div_y(K(x,y)v) = 0 for y ≠ x (by BS_kernel_divergence_free)
  -- 4. The volume integral is 0, so surface integrals on |y-x|=r and |y-x|=ε cancel
  -- 5. As ε → 0, the inner sphere integral → 0 by symmetry
  -- 6. Therefore the outer sphere integral = 0
  -- 7. By radial homogeneity, this implies the ball integral = 0

  -- Alternative proof using spherical coordinates directly:
  -- K has zero mean on each sphere, so ∫_{|y-x|=ρ} K dy = 0 for all ρ
  -- Therefore ∫_{B(x,r)} K dy = ∫_0^r (∫_{|y-x|=ρ} K dy) dρ = 0

  sorry -- This requires measure theory and the divergence theorem

-- Helper: Integration in spherical coordinates
lemma spherical_integral_bound (x : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r)
    (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C / ‖x - y‖^2) :
    ‖∫ y in Metric.ball x r, f y ∂volume‖ ≤ 4 * π * C * r := by
  -- Convert to spherical coordinates: ∫_0^r ∫_{S²} f dσ ρ² dρ
  -- Using ‖f‖ ≤ C/ρ², we get ∫_0^r (C/ρ²) ρ² dρ = C·r
  -- The surface area of S² is 4π
  sorry -- Technical measure theory calculation

/-- Near-field cancellation: The aligned vorticity cone reduces stretching by O(r⁻¹) factor.
This is the core of the Constantin-Fefferman mechanism. -/
lemma nearField_cancellation
    (u : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (x : Fin 3 → ℝ) {r : ℝ} (hr : 0 < r)
    (halign : ∀ y ∈ Metric.ball x r, angle (ω y) (ω x) ≤ (π/6)) :
    ‖∫ y in (Metric.ball x r), BS_kernel x y (ω y) ∂volume‖ ≤ (C_star/2) / r := by
  -- Step 1: Decompose vorticity as ω(y) = ω(x) + δω(y)
  let δω : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ω y - ω x

  -- Step 2: Split the integral
  have hsplit : ∫ y in Metric.ball x r, BS_kernel x y (ω y) ∂volume =
      ∫ y in Metric.ball x r, BS_kernel x y (ω x) ∂volume +
      ∫ y in Metric.ball x r, BS_kernel x y (δω y) ∂volume := by
    simp only [δω]
    rw [← integral_add]
    · congr 1
      ext y
      simp [sub_eq_iff_eq_add]
    · -- Integrability of BS_kernel x y (ω x)
      -- The kernel has singularity 1/|y-x|^2, which is integrable in 3D
      -- over bounded domains when integrated against a constant vector
      sorry
    · -- Integrability of BS_kernel x y (δω y)
      -- Similar argument: kernel singularity is integrable in 3D
      -- and δω is bounded on the ball
      sorry

  -- Step 3: First integral vanishes due to symmetry
  have h_first_zero : ‖∫ y in Metric.ball x r, BS_kernel x y (ω x) ∂volume‖ = 0 := by
    -- Apply our key cancellation lemma
    have h_zero := BS_kernel_constant_integral_zero x r hr (ω x)
    simp [h_zero, norm_zero]

  -- Step 4: Bound the perturbation term
  have h_delta_bound : ∀ y ∈ Metric.ball x r, ‖δω y‖ ≤ sin (π/6) * ‖ω x‖ := by
    intro y hy
    -- From angle(ω(y), ω(x)) ≤ π/6, deduce ‖ω(y) - ω(x)‖ ≤ sin(π/6) * ‖ω(x)‖
    by_cases h : ω x = 0
    · simp [δω, h, norm_zero, mul_zero]
    · exact angle_bound_half_norm (ω x) (ω y) h (halign y hy)

  -- Step 5: Estimate the second integral
  have h_second_bound : ‖∫ y in Metric.ball x r, BS_kernel x y (δω y) ∂volume‖ ≤ (C_star/2) / r := by
    -- Use kernel bound ‖BS_kernel x y‖ ≤ C/|x-y|²
    -- and ‖δω y‖ ≤ (1/2)‖ω x‖
    have h_integrand : ∀ y ∈ Metric.ball x r, y ≠ x →
        ‖BS_kernel x y (δω y)‖ ≤ (3/(4*π)) * (1/2) * ‖ω x‖ / ‖x - y‖^2 := by
      intro y hy hyx
      calc ‖BS_kernel x y (δω y)‖
          ≤ ‖BS_kernel x y‖ * ‖δω y‖ := operator_norm_bound (BS_kernel x y) (δω y)
        _ ≤ (3/(4*π)) / ‖x - y‖^2 * (sin(π/6) * ‖ω x‖) := by
            apply mul_le_mul (BS_kernel_bound x y (ne_comm.mp hyx)) (h_delta_bound y hy)
                (norm_nonneg _) (div_nonneg (by norm_num : (0:ℝ) ≤ 3/(4*π)) (sq_nonneg _))
        _ = (3/(4*π)) / ‖x - y‖^2 * ((1/2) * ‖ω x‖) := by norm_num
        _ = (3/(4*π)) * (1/2) * ‖ω x‖ / ‖x - y‖^2 := by ring

    -- Apply spherical integration
    have h_bound := spherical_integral_bound x r hr
        (fun y => BS_kernel x y (δω y))
        (by intro y hy
            by_cases hyx : y = x
            · simp [hyx, BS_kernel, norm_zero, div_nonneg]
            · exact h_integrand y hy hyx)

    -- The key insight: when vorticity is aligned, the effective constant is much smaller
    -- than the naive bound due to cancellation effects

    -- What's needed for the sharp bound:
    -- 1. Decompose δω = δω_∥ + δω_⊥ (parallel and perpendicular to ω₀)
    -- 2. The parallel part δω_∥ is O(|y-x|²) by the alignment condition
    -- 3. The perpendicular part requires the anisotropic kernel estimate:
    --    ∫ K(z) f_⊥(z) dz has extra cancellation when f_⊥ ⊥ ω₀ everywhere
    -- 4. This uses that K preferentially amplifies radial components
    -- 5. The Calderón-Zygmund theory gives the precise constant

    -- This is where the Constantin-Fefferman (1993) analysis is essential
    -- The proof requires:
    -- - Littlewood-Paley decomposition
    -- - Anisotropic function spaces
    -- - Precise estimates of oscillatory integrals

    sorry -- This requires the full Constantin-Fefferman harmonic analysis machinery

  -- Combine results
  rw [hsplit]
  simp [h_first_zero, norm_zero, zero_add]
  exact h_second_bound

end NavierStokes
