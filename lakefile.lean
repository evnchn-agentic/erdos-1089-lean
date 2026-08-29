import Lake
open Lake DSL

package «erdos-1089-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Pinned deliberately. This repository exists to be *cited* as a verified proof, so the
-- build must stay reproducible; a floating `@ "master"` would silently stop verifying the
-- day mathlib moves.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "85e6e1b45ac3992b8b08b789e314e2b2adf4d5c5"

@[default_target]
lean_lib «ErdosProofs» where
