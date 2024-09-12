import Lake
open Lake DSL

package «EulerProducts» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩ --,
    -- ⟨`profiler, true⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib «EulerProducts» where
  globs := #[.submodules `EulerProducts]
  -- add any library configuration options here
