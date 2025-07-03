import Lake
open Lake DSL

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.20.0"

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
