module

public import Lentil.ProofMode.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

@[expose] public section

attribute [tlnormsimp ↓] Lentil.impl_intro Lentil.valid_eq_true_implies Lentil.impl_intro_add_r Lentil.and_assoc
  Lentil.and_true Lentil.true_and Lentil.imp_true Lentil.always_true Lentil.eventually_true Lentil.later_true
  Lentil.or_false Lentil.false_or Lentil.forall_unit Lentil.exists_unit

end

public meta section

/--
`tnormalize` rewrites a raw LTL goal into a shape that proof-mode tactics can
introduce and split more predictably.

For example,
```lean
tnormalize
```
turns a valid implication goal such as `|-tl- p → q` into the corresponding
sequent shape `p |-tl- q`, and reassociates simple conjunction structure using
the proof-mode normalization simp set.
-/
macro "tnormalize" : tactic => `(tactic| simp -$(mkIdent `failIfUnchanged) only [tlnormsimp])

end

end Lentil.ProofMode
