import Lentil

/- Tests for `tcheck_goal_form`. -/

namespace Lentil.ProofMode.Test.CheckGoalForm

open Lentil Lentil.ProofMode

variable {σ : Type u} (p : pred σ)

example : (p) |-tl- (p) := by
  tstart hp
  tcheck_goal_form
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

example (P : Nat → pred σ) :
    (⊤) |-tl- (∀ n : Nat, (P n) → (P n)) := by
  tstart
  tintro n hp
  tcheck_goal_form
  guard_target =ₛ Entails [⟨"hp", P n⟩] (P n)
  exact pred_implies_refl _

/--
error: tcheck_goal_form: goal is not in canonical Entails form
-/
#guard_msgs in
example : (p) |-tl- (p) := by
  tcheck_goal_form

/--
error: The main goal is
  ⏎
  hp : p
  |-tl- p
but was expected to be
  ⏎
  wrong : p
  |-tl- p
-/
#guard_msgs in
example : (p) |-tl- (p) := by
  tstart hp
  guard_target =ₛ Entails [⟨"wrong", p⟩] p

end Lentil.ProofMode.Test.CheckGoalForm
