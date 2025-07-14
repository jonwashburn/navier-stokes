/-
  Recognition Science Foundation
  =============================

  Self-contained mathematical foundation with zero external dependencies.
  Built entirely from first principles.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Lake
open Lake DSL

package RecognitionScience where
  -- Basic settings for clean compilation
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  buildType := BuildType.release

-- Mathlib dependency for advanced proofs
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

@[default_target]
lean_lib RecognitionScience where
  -- Include top-level modules
          roots := #[`RecognitionScience, `MinimalFoundation, `ZeroAxiomFoundation, `Fintype.Basic,
              `Core.Physics.MassGap, `Core.Physics.RungGap]
