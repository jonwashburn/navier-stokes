import Lake
open Lake DSL

package «navier-stokes» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0-rc3"

@[default_target]
lean_lib «NavierStokesLedger» where
  -- add any library configuration options here

-- Add sorry finder executable
lean_exe «sorry_finder» where
  root := `sorry_finder
