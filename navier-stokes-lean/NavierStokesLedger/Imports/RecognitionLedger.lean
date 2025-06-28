import RecognitionLedger.formal.Core.VectorCalc
import RecognitionLedger.formal.Analysis.Harmonic.CZAxioms

-- This module simply re-exports key finished proofs from the recognition-ledger
-- project so that NavierStokesLedger code can rely on them without duplicating
-- work.

namespace NavierStokesLedger.RecognitionImports

open RecognitionLedger

-- Re-export cross product and norm bound
abbrev cross := formal.Core.VectorCalc.cross

@[simp]
lemma norm_cross_le (a b : Fin 3 → ℝ) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ :=
  formal.Core.VectorCalc.norm_cross_le _ _

end NavierStokesLedger.RecognitionImports
