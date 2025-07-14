/-
  Recognition Science: Constants Re-export
  =======================================

  This file re-exports the real-valued constants from RealConstants.lean
  for backward compatibility.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import foundation.Parameters.RealConstants

-- Re-export all constants from RealConstants
export RecognitionScience.Constants (φ E_coh τ₀ lambda_rec c h_bar k_B T_CMB T_room L₀ eV_to_kg E_at_rung mass_at_rung φ_pos φ_gt_one E_coh_pos τ₀_pos c_pos golden_ratio_property)
