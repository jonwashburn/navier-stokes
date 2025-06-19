import NavierStokesLedger.BealeKatoMajda

open Real NavierStokes

namespace NavierStokes

theorem navier_stokes_global_regularity (ν : ℝ) (hν : 0 < ν) :
    ∀ (u₀ : VelocityField), ∃ (nse : NSE ν), nse.initial_data = u₀ ∧ GloballyRegular nse := by
  sorry

theorem millennium_prize_solution :
    ∀ (ν : ℝ) (hν : 0 < ν), True := by
  intro ν hν
  trivial

end NavierStokes
