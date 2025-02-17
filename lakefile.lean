import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

package «lentil» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Lentil» where
  -- add any library configuration options here

lean_lib Examples where
  globs := #[.submodules `Examples]
