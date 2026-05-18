import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

attribute [tlanormsimp ↓] impl_intro valid_eq_true_implies impl_intro_add_r and_assoc and_true true_and

/--
`tla_normalize` rewrites a raw TLA goal into a shape that proof-mode tactics can
introduce and split more predictably.

For example,
```lean
tla_normalize
```
turns a valid implication goal such as `|-tla- p → q` into the corresponding
sequent shape `p |-tla- q`, and reassociates simple conjunction structure using
the proof-mode normalization simp set.
-/
macro "tla_normalize" : tactic => `(tactic| simp -$(mkIdent `failIfUnchanged) only [tlanormsimp])

end TLA.ProofMode
