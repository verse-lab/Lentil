import Lentil

/- Tests for `tla_check_goal_form`. -/

namespace TLA.ProofMode.Test.CheckGoalForm

open TLA TLA.ProofMode

variable {σ : Type u} (p : pred σ)

example : (p) |-tla- (p) := by
  tla_start hp
  tla_check_goal_form
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

/--
error: tla_check_goal_form: goal is not in canonical Entails form
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tla_check_goal_form

/--
error: tla_check_goal: temporal hypothesis 0 is named 'hp', expected 'wrong'
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tla_start hp
  tla_check_goal Entails [⟨"wrong", p⟩] p

end TLA.ProofMode.Test.CheckGoalForm
