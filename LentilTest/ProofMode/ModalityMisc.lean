import Lentil

namespace TLA.Test.ModalityMisc

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

example (h : (□ p ∧ □ r) |-tla- (q)) : (□ p ∧ □ r) |-tla- (□ q) := by
  tla_start hp hr
  tla_toggle_goal_under_always
  tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] q
  exact h

example (h : (□ p ∧ □ r) |-tla- (□ q)) : (□ p ∧ □ r) |-tla- (q) := by
  tla_start hp hr
  tla_toggle_goal_under_always
  tla_toggle_goal_under_always
  tla_toggle_goal_under_always
  tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| □ q]
  exact h

/--
error: tla_toggle_goal_under_always: expected every temporal hypothesis to have an always prefix
-/
#guard_msgs in
example : (□ p ∧ r) |-tla- (q) := by
  tla_start hp hr
  tla_toggle_goal_under_always

end TLA.Test.ModalityMisc
