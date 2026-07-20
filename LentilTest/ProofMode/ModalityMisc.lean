import Lentil

namespace TLA.Test.ModalityMisc

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)
variable (a : action σ)

def wrappedAlways {α : Type u} (p : pred α) : pred α := [tlafml| □ p]

attribute [tla_modality_unfold] wrappedAlways

def wrappedLater {α : Type u} (p : pred α) : pred α := [tlafml| ◯ p]

attribute [tla_modality_unfold] wrappedLater

example (h : (□ p ∧ □ r) |-tla- (q)) : (□ p ∧ □ r) |-tla- (□ q) := by
  tstart hp hr
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] q
  exact h

example (h : (□ p ∧ □ r) |-tla- (□ q)) : (□ p ∧ □ r) |-tla- (q) := by
  tstart hp hr
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| □ q]
  exact h

example (h : (p ⇒ q) |-tla- (r)) : (p ⇒ q) |-tla- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlafml| p ⇒ q]⟩] r
  exact h

example (h : (wrappedAlways p) |-tla- (r)) : (wrappedAlways p) |-tla- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", wrappedAlways p⟩] r
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
  guard_target =ₛ Entails [⟨"hwf", [tlafml| 𝒲ℱ a]⟩] r
  trace_state
  exact h

example (h : (p ∧ q) |-tla- (r)) :
    (wrappedAlways p ∧ wrappedAlways q) |-tla- (wrappedAlways r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example : (□ p ∧ ◇ q ∧ □ r) |-tla- (◇ q) := by
  tstart hp hq hr
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| ◇ q]
  tapply TLA.now_weaken_to_eventually
  tassumption

example (h : (𝒲ℱ a ∧ p) |-tla- (◇ q)) :
    (𝒲ℱ a ∧ ◇ p) |-tla- (◇ q) := by
  tstart hwf hp
  tadvance hp
  guard_target =ₛ Entails [⟨"hwf", [tlafml| 𝒲ℱ a]⟩, ⟨"hp", p⟩] [tlafml| ◇ q]
  exact h

example (h : (□ p ∧ q ∧ □ r) |-tla- (□ ◇ r)) :
    (□ p ∧ ◇ q ∧ □ r) |-tla- (□ ◇ r) := by
  tstart hp hq hr
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] [tlafml| □ ◇ r]
  exact h

example {P : Prop} (h : (□ p ∧ q) |-tla- (⌞ P ⌟)) :
    (□ p ∧ ◇ q) |-tla- (⌞ P ⌟) := by
  tstart hp hq
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩] [tlafml| ⌞ P ⌟]
  exact h

example (h : (p ∧ q) |-tla- (r)) :
    (◯ p ∧ ◯ q) |-tla- (◯ r) := by
  tstart hp hq
  tstep
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (□ p ∧ □ q) |-tla- (r)) :
    (□ p ∧ □ q) |-tla- (◯ r) := by
  tstart hp hq
  tstep
  tcheck_goal Entails
    [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", [tlafml| □ q]⟩] r
  exact h

example (s : pred σ) (h : (□ q ∧ p ∧ r) |-tla- (s)) :
    (◯ p ∧ □ q ∧ ◯ r) |-tla- (◯ s) := by
  tstart hp hq hr
  tstep
  tcheck_goal Entails
    [⟨"hq", [tlafml| □ q]⟩, ⟨"hp", p⟩, ⟨"hr", r⟩] s
  exact h

example (h : (⊤) |-tla- (p)) : (⊤) |-tla- (◯ p) := by
  tstart
  tstep
  tcheck_goal Entails [] p
  exact h

example (h : (□ p ∧ q) |-tla- (r)) :
    (wrappedAlways p ∧ wrappedLater q) |-tla- (wrappedLater r) := by
  tstart hp hq
  tstep
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩] r
  exact h

/--
error: tstep: expected the proof-mode goal to have a leading next (`◯`) prefix
-/
#guard_msgs in
example : (□ p) |-tla- (q) := by
  tstart hp
  tstep

/--
error: tstep: expected every temporal hypothesis to have a leading always (`□`) or next (`◯`) prefix
-/
#guard_msgs in
example : (□ p ∧ q) |-tla- (◯ r) := by
  tstart hp hq
  tstep

/--
error: ttoggle_goal_under_always: expected every temporal hypothesis to have an always prefix
-/
#guard_msgs in
example : (□ p ∧ r) |-tla- (q) := by
  tstart hp hr
  ttoggle_goal_under_always

end TLA.Test.ModalityMisc
