import NavierStokesLedger.UnconditionalProof
import Mathlib.Data.Real.Pi.Bounds

namespace NavierStokesLedger

open Real

/-- C₀ = 0.02 is less than φ⁻¹ ≈ 0.618 -/
lemma C₀_lt_phi_inv : C₀ < φ⁻¹ := by
  rw [C₀, phi_inv]
  -- 0.02 < (√5 - 1)/2
  have h1 : (2 : ℝ) < sqrt 5 := by
    have : (4 : ℝ) < 5 := by norm_num
    have : sqrt 4 < sqrt 5 := sqrt_lt_sqrt (by norm_num) this
    simpa
  have h2 : 0.02 < (2 - 1) / 2 := by norm_num
  have h3 : (2 - 1) / 2 < (sqrt 5 - 1) / 2 := by
    apply div_lt_div_of_lt_left
    · norm_num
    · norm_num
    · linarith
  linarith

/-- C* = 0.142 is less than π/4 ≈ 0.785 -/
lemma C_star_lt_pi_div_4 : C_star < π / 4 := by
  -- Need π > 3.14, so π/4 > 0.785 > 0.142
  have : (3 : ℝ) < π := three_lt_pi
  have : π / 4 > 3 / 4 := by
    apply div_lt_div_of_lt_left
    · norm_num
    · norm_num
    · exact this
  have : (3 : ℝ) / 4 = 0.75 := by norm_num
  norm_num -- Need to compute C_star value

/-- K* = 0.090 is less than 1 -/
lemma K_star_lt_one : K_star < 1 := by
  rw [K_star]
  -- K* = 2C*/π < 2 * 0.5 / π < 1
  norm_num -- Need C_star bound

end NavierStokesLedger
