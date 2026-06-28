import Lentil

namespace TLA.Test.ModalityMisc

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)
variable (a : action σ)

def wrappedAlways {α : Type u} (p : pred α) : pred α := [tlafml| □ p]

attribute [tla_modality_unfold] wrappedAlways

example (h : (□ p ∧ □ r) |-tla- (q)) : (□ p ∧ □ r) |-tla- (□ q) := by
  tstart hp hr
  ttoggle_goal_under_always
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] q
  exact h

example (h : (□ p ∧ □ r) |-tla- (□ q)) : (□ p ∧ □ r) |-tla- (q) := by
  tstart hp hr
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| □ q]
  exact h

example (h : (p ⇒ q) |-tla- (r)) : (p ⇒ q) |-tla- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  tcheck_goal Entails [⟨"hp", [tlafml| □ (p → q)]⟩] r
  exact h

example (h : (wrappedAlways p) |-tla- (r)) : (wrappedAlways p) |-tla- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩] r
  exact h

/--
trace: σ : Type u
p q r : pred σ
a : action σ
h : (𝒲ℱ a) |-tla- (r)
⊢ 
  hwf : 𝒲ℱ a
  |-tla- r
-/
#guard_msgs in
example (h : (𝒲ℱ a) |-tla- (r)) : (𝒲ℱ a) |-tla- (□ r) := by
  tstart hwf
  ttoggle_goal_under_always
  tcheck_goal Entails [⟨"hwf", [tlafml| 𝒲ℱ a]⟩] r
  trace_state
  exact h

example (h : (p ∧ q) |-tla- (r)) :
    (wrappedAlways p ∧ wrappedAlways q) |-tla- (wrappedAlways r) := by
  tstart hp hq
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example : (□ p ∧ ◇ q ∧ □ r) |-tla- (◇ q) := by
  tstart hp hq hr
  tadvance hq
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| ◇ q]
  tapply TLA.now_weaken_to_eventually
  tassumption

example (h : (𝒲ℱ a ∧ p) |-tla- (◇ q)) :
    (𝒲ℱ a ∧ ◇ p) |-tla- (◇ q) := by
  tstart hwf hp
  tadvance hp
  tcheck_goal Entails [⟨"hwf", [tlafml| 𝒲ℱ a]⟩, ⟨"hp", p⟩] [tlafml| ◇ q]
  exact h

example (h : (□ p ∧ q ∧ □ r) |-tla- (□ ◇ r)) :
    (□ p ∧ ◇ q ∧ □ r) |-tla- (□ ◇ r) := by
  tstart hp hq hr
  tadvance hq
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| □ ◇ r]
  exact h

example {P : Prop} (h : (□ p ∧ q) |-tla- (⌞ P ⌟)) :
    (□ p ∧ ◇ q) |-tla- (⌞ P ⌟) := by
  tstart hp hq
  tadvance hq
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩] [tlafml| ⌞ P ⌟]
  exact h

/--
error: ttoggle_goal_under_always: expected every temporal hypothesis to have an always prefix
-/
#guard_msgs in
example : (□ p ∧ r) |-tla- (q) := by
  tstart hp hr
  ttoggle_goal_under_always

end TLA.Test.ModalityMisc
