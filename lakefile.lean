import Lake
open Lake DSL

package "navier_stokes_ledger" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «NavierStokesLedger» where
  -- add any library configuration options here

-- Add sorry finder executable
lean_exe «sorry_finder» where
  root := `sorry_finder
