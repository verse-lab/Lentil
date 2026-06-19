import Lentil

namespace TLA.Test.ModalityMisc

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

def wrappedAlways {α : Type u} (p : pred α) : pred α := [tlafml| □ p]

attribute [tla_modality_unfold] wrappedAlways

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

example (h : (p ⇒ q) |-tla- (r)) : (p ⇒ q) |-tla- (□ r) := by
  tla_start hp
  tla_toggle_goal_under_always
  tla_check_goal Entails [⟨"hp", [tlafml| □ (p → q)]⟩] r
  exact h

example (h : (wrappedAlways p) |-tla- (r)) : (wrappedAlways p) |-tla- (□ r) := by
  tla_start hp
  tla_toggle_goal_under_always
  tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩] r
  exact h

example (h : (p ∧ q) |-tla- (r)) :
    (wrappedAlways p ∧ wrappedAlways q) |-tla- (wrappedAlways r) := by
  tla_start hp hq
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

/--
error: tla_toggle_goal_under_always: expected every temporal hypothesis to have an always prefix
-/
#guard_msgs in
example : (□ p ∧ r) |-tla- (q) := by
  tla_start hp hr
  tla_toggle_goal_under_always

end TLA.Test.ModalityMisc
