import Lentil

/- Tests for `tcheck_goal_form`. -/

namespace TLA.ProofMode.Test.CheckGoalForm

open TLA TLA.ProofMode

variable {σ : Type u} (p : pred σ)

example : (p) |-tla- (p) := by
  tstart hp
  tcheck_goal_form
  tcheck_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

/--
error: tcheck_goal_form: goal is not in canonical Entails form
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tcheck_goal_form

/--
error: tcheck_goal: temporal hypothesis 0 is named 'hp', expected 'wrong'
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tstart hp
  tcheck_goal Entails [⟨"wrong", p⟩] p

end TLA.ProofMode.Test.CheckGoalForm
