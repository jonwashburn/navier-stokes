/-
  Beale-Kato-Majda criterion for Navier-Stokes
  If vorticity remains bounded, solution stays regular
-/
import NavierStokesLedger.VorticityBound
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.NormedSpace.SobolevInequality

open NavierStokes Real Function Set Filter Topology MeasureTheory

namespace NavierStokes

/-! ## Energy Estimates -/

/-- Basic energy inequality -/
lemma energy_inequality (ν : ℝ) (hν : 0 < ν) (nse : NSE ν) (t : ℝ) :
    d/dt (energy (nse.u t)) + 2 * ν * enstrophy (nse.u t) ≤ 0 := by
  sorry

/-- H¹ estimate in terms of vorticity -/
lemma H1_vorticity_estimate (u : VelocityField)
    (h_div_free : ∀ x, div u x = 0)
    (h_decay : ∀ R > 0, ∫ x in {x | ‖x‖ > R}, ‖u x‖² ∂volume = o(1/R) as R → ∞) :
    ‖u‖_H1 ≤ C₁ * ‖vorticity u‖_L2 := by
  sorry

/-! ## Grönwall Inequality Application -/

/-- Grönwall's inequality for energy growth -/
lemma gronwall_energy_bound (ν : ℝ) (hν : 0 < ν) (nse : NSE ν)
    (h_vort_bound : ∀ t ∈ Icc 0 T, ‖vorticity (nse.u t)‖_∞ ≤ M) :
    ∀ t ∈ Icc 0 T, energy (nse.u t) ≤ energy nse.initial_data * exp (C₂ * M * t) := by
  sorry

/-! ## Beale-Kato-Majda Criterion -/

/-- The Beale-Kato-Majda criterion -/
theorem beale_kato_majda (ν : ℝ) (hν : 0 < ν) (nse : NSE ν) (T : ℝ) (hT : 0 < T)
    (h_local : ∀ t ∈ Ico 0 T, Smooth ℝ (nse.u t))
    (h_vort_integrable : ∫ t in Icc 0 T, ‖vorticity (nse.u t)‖_∞ ∂(volume.restrict (Icc 0 T)) < ∞) :
    ∀ t ∈ Icc 0 T, Smooth ℝ (nse.u t) := by
  sorry

/-- Time-integrated version of BKM -/
theorem beale_kato_majda_integrated (ν : ℝ) (hν : 0 < ν) (nse : NSE ν)
    (h_initial : Smooth ℝ nse.initial_data)
    (h_vort_bound : ∀ t ≥ 0, ‖vorticity (nse.u t)‖_∞ ≤ C_star / Real.sqrt ν) :
    GloballyRegular nse := by
  sorry

/-! ## Higher Regularity Bootstrap -/

/-- Bootstrap from L∞ vorticity to higher regularity -/
theorem regularity_bootstrap (ν : ℝ) (hν : 0 < ν) (nse : NSE ν) (t : ℝ) (ht : 0 ≤ t)
    (h_vort : ‖vorticity (nse.u t)‖_∞ < ∞)
    (h_energy : energy (nse.u t) < ∞) :
    ∀ k : ℕ, ‖nse.u t‖_Hk < ∞ := by
  sorry

end NavierStokes
