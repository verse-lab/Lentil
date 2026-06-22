import Lake
open Lake DSL

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.31.0"

package «lentil» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Lentil» where
  globs := #[`«Lentil»]

lean_lib «LentilTest» where
  globs := #[Glob.submodules `LentilTest]
