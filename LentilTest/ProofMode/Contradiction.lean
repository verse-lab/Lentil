import Lentil

/- Tests for `tla_contradiction`, which closes any proof-mode goal when its
   context contains either `tla_false` or a pair `p`, `¬ p`. -/

namespace TLA.ProofMode.Test.Contradiction

open TLA TLA.ProofMode

variable {σ : Type u} (a p q : pred σ)

-- A `⊥` hypothesis closes any goal.
example (lem : (a) |-tla- (⊥)) : (a) |-tla- (q) := by
  tla_start ha
  tla_have hf : ⊥ by tla_apply lem ; tla_assumption
  tla_contradiction

-- A pair `p`, `¬ p` closes any goal.
example (lem_p : (a) |-tla- (p)) (lem_np : (a) |-tla- (¬ p)) :
    (a) |-tla- (q) := by
  tla_start ha
  tla_have hp : p by tla_apply lem_p ; tla_assumption
  tla_have hnp : ¬ p by tla_apply lem_np ; tla_assumption
  tla_contradiction

-- Order of `p` and `¬ p` in the context doesn't matter.
example (lem_p : (a) |-tla- (p)) (lem_np : (a) |-tla- (¬ p)) :
    (a) |-tla- (q) := by
  tla_start ha
  tla_have hnp : ¬ p by tla_apply lem_np ; tla_assumption
  tla_have hp : p by tla_apply lem_p ; tla_assumption
  tla_contradiction

-- No contradiction → fails with a clear message.
/--
error: tla_contradiction: no contradiction found in proof-mode context
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tla_start ha
  tla_contradiction

-- Not in proof mode → fails.
/--
error: tla_contradiction: goal is not an Entails sequent
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tla_contradiction

end TLA.ProofMode.Test.Contradiction
