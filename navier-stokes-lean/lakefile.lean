import Lake
open Lake DSL

package «NavierStokesLedger» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0-rc3"

require RecognitionScience from git
  "https://github.com/jonwashburn/recognition-ledger.git" @ "main"

require «recognition-science» from git
  "https://github.com/jonwashburn/Yang-Mills-Lean.git" @ "main"

@[default_target]
lean_lib «NavierStokesLedger» where
  globs := #[.submodules `NavierStokesLedger]
