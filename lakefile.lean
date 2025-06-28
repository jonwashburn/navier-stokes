import Lake
open Lake DSL

package NavierStokesLedger where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib NavierStokesLedger

require mathlib from git
  "https://github.com/leanprover-community/m