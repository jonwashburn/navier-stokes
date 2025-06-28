import Lake
open Lake DSL

package «navier-stokes» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0-rc3"

@[default_target]
lean_lib «NavierStokesLedger»
