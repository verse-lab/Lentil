import Lentil

/- Tests for `tcheck_goal_form`. -/

namespace TLA.ProofMode.Test.CheckGoalForm

open TLA TLA.ProofMode

variable {σ : Type u} (p : pred σ)

example : (p) |-tla- (p) := by
  tstart hp
  tcheck_goal_form
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n) → (P n)) := by
  tstart
  tintro n hp
  tcheck_goal_form
  guard_target =ₛ Entails [⟨"hp", P n⟩] (P n)
  exact pred_implies_refl _

/--
error: tcheck_goal_form: goal is not in canonical Entails form
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tcheck_goal_form

/--
error: The main goal is

  hp : p
  |-tla- p
but was expected to be

  wrong : p
  |-tla- p
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tstart hp
  guard_target =ₛ Entails [⟨"wrong", p⟩] p

end TLA.ProofMode.Test.CheckGoalForm
