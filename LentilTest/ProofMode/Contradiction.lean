import Lentil

/- Tests for `tcontradiction`, which closes any proof-mode goal when its
   context contains either `tl_false` or a pair `p`, `¬ p`. -/

namespace Lentil.ProofMode.Test.Contradiction

open Lentil Lentil.ProofMode

variable {σ : Type u} (a p q : pred σ)

-- `texfalso` reduces any proof-mode goal to `⊥` while preserving its context.
example (lem : (a) |-tl- (⊥)) : (a) |-tl- (q) := by
  tstart ha
  texfalso
  guard_target =ₛ Entails [⟨"ha", a⟩] tl_false
  exact lem

-- A `⊥` hypothesis closes any goal.
example (lem : (a) |-tl- (⊥)) : (a) |-tl- (q) := by
  tstart ha
  thave hf : ⊥ by tapply lem ; tassumption
  tcontradiction

-- A pair `p`, `¬ p` closes any goal.
example (lem_p : (a) |-tl- (p)) (lem_np : (a) |-tl- (¬ p)) :
    (a) |-tl- (q) := by
  tstart ha
  thave hp : p by tapply lem_p ; tassumption
  thave hnp : ¬ p by tapply lem_np ; tassumption
  tcontradiction

-- Order of `p` and `¬ p` in the context doesn't matter.
example (lem_p : (a) |-tl- (p)) (lem_np : (a) |-tl- (¬ p)) :
    (a) |-tl- (q) := by
  tstart ha
  thave hnp : ¬ p by tapply lem_np ; tassumption
  thave hp : p by tapply lem_p ; tassumption
  tcontradiction

-- No contradiction → fails with a clear message.
/--
error: tcontradiction: no contradiction found in proof-mode context
-/
#guard_msgs in
example : (a) |-tl- (a) := by
  tstart ha
  tcontradiction

-- Not in proof mode → fails.
/--
error: tcontradiction: goal is not an Entails sequent
-/
#guard_msgs in
example : (a) |-tl- (a) := by
  tcontradiction

end Lentil.ProofMode.Test.Contradiction
