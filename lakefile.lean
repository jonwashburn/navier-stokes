import Lake
open Lake DSL

-- Build optimization settings
def leanArgs : Array String := #[
  "-j", "12"       -- Use 12 threads for compilation
]

package «navier-stokes» where
  version := v!"0.1.0"
  keywords := #["mathematics", "pde", "navier-stokes", "recognition-science"]
  description := "Zero-axiom proof of 3D Navier-Stokes global regularity using Recognition Science"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  -- Apply build optimizations
  moreLeanArgs := leanArgs
  -- Enable cache by default
  buildArchive? := none
  -- Prefer cached builds
  preferReleaseBuild := true

-- Add ledger-foundation as a dependency for zero-axiom Recognition Science
require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0-rc3"

@[default_target]
lean_lib «NavierStokesLedger»
