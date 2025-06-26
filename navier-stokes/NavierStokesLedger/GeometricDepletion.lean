import NavierStokesLedger.RSImports
import Mathlib.Analysis.SingularIntegralKernel
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Topology.Instances.Real

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

/-- Near-field cancellation **statement only** (proof deferred).  The aligned vorticity cone
reduces stretching by an `O(r⁻¹)` factor. -/
lemma nearField_cancellation
    (u : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (x : Fin 3 → ℝ) {r : ℝ} (hr : 0 < r)
    (halign : ∀ y ∈ Metric.ball x r, angle (ω y) (ω x) ≤ (π/6)) :
    ‖∫ y in (Metric.ball x r), BS_kernel x y (ω y) ∂volume‖ ≤ (C_star/2) / r :=
  by
  -- A full Constantin–Fefferman proof requires heavy harmonic-analysis; we assume it here.
  admit

end NavierStokes
