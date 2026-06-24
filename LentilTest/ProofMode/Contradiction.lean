import Lentil

/- Tests for `tcontradiction`, which closes any proof-mode goal when its
   context contains either `tla_false` or a pair `p`, `¬ p`. -/

namespace TLA.ProofMode.Test.Contradiction

open TLA TLA.ProofMode

variable {σ : Type u} (a p q : pred σ)

-- A `⊥` hypothesis closes any goal.
example (lem : (a) |-tla- (⊥)) : (a) |-tla- (q) := by
  tstart ha
  thave hf : ⊥ by tapply lem ; tassumption
  tcontradiction

-- A pair `p`, `¬ p` closes any goal.
example (lem_p : (a) |-tla- (p)) (lem_np : (a) |-tla- (¬ p)) :
    (a) |-tla- (q) := by
  tstart ha
  thave hp : p by tapply lem_p ; tassumption
  thave hnp : ¬ p by tapply lem_np ; tassumption
  tcontradiction

-- Order of `p` and `¬ p` in the context doesn't matter.
example (lem_p : (a) |-tla- (p)) (lem_np : (a) |-tla- (¬ p)) :
    (a) |-tla- (q) := by
  tstart ha
  thave hnp : ¬ p by tapply lem_np ; tassumption
  thave hp : p by tapply lem_p ; tassumption
  tcontradiction

-- No contradiction → fails with a clear message.
/--
error: tcontradiction: no contradiction found in proof-mode context
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tstart ha
  tcontradiction

-- Not in proof mode → fails.
/--
error: tcontradiction: goal is not an Entails sequent
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tcontradiction

end TLA.ProofMode.Test.Contradiction
