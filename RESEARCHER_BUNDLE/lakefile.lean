import Lake
open Lake DSL

package «dual-differentiable» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib HeytingLean where
  roots := #[`HeytingLean]

lean_exe differential_sky_demo where
  root := `HeytingLean.CLI.DifferentialSKYDemoMain
