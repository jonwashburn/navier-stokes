import NavierStokesLedger.BasicDefinitions

open Real NavierStokes

namespace NavierStokes

def VelocityField := (Fin 3 → ℝ) → (Fin 3 → ℝ)
def PressureField := (Fin 3 → ℝ) → ℝ

structure NSE (ν : ℝ) where
  u : ℝ → VelocityField
  p : ℝ → PressureField
  initial_data : VelocityField

def GloballyRegular {ν : ℝ} (nse : NSE ν) : Prop := sorry

noncomputable def vorticity (u : VelocityField) : VelocityField := sorry
noncomputable def energy (u : VelocityField) : ℝ := sorry
noncomputable def enstrophy (u : VelocityField) : ℝ := sorry

theorem global_regularity (ν : ℝ) (hν : 0 < ν) (nse : NSE ν) : GloballyRegular nse := by
  sorry

end NavierStokes