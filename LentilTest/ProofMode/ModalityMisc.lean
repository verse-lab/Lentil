import Lentil

namespace Lentil.Test.ModalityMisc

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)
variable (a : action σ)

def wrappedAlways {α : Type u} (p : pred α) : pred α := [tlfml| □ p]

attribute [tl_modality_unfold] wrappedAlways

def wrappedLater {α : Type u} (p : pred α) : pred α := [tlfml| ◯ p]

attribute [tl_modality_unfold] wrappedLater

example (h : (□ p ∧ □ r) |-tl- (q)) : (□ p ∧ □ r) |-tl- (□ q) := by
  tstart hp hr
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hr", [tlfml| □ r]⟩] q
  exact h

example (h : (□ p ∧ □ r) |-tl- (□ q)) : (□ p ∧ □ r) |-tl- (q) := by
  tstart hp hr
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hr", [tlfml| □ r]⟩] [tlfml| □ q]
  exact h

example (h : (p ⇒ q) |-tl- (r)) : (p ⇒ q) |-tl- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", [tlfml| p ⇒ q]⟩] r
  exact h

example (h : (wrappedAlways p) |-tl- (r)) : (wrappedAlways p) |-tl- (□ r) := by
  tstart hp
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hp", wrappedAlways p⟩] r
  exact h

/--
trace: σ : Type u
p q r : pred σ
a : action σ
h : (𝒲ℱ a) |-tl- (r)
⊢ ⏎
  hwf : 𝒲ℱ a
  |-tl- r
-/
#guard_msgs in
example (h : (𝒲ℱ a) |-tl- (r)) : (𝒲ℱ a) |-tl- (□ r) := by
  tstart hwf
  ttoggle_goal_under_always
  guard_target =ₛ Entails [⟨"hwf", [tlfml| 𝒲ℱ a]⟩] r
  trace_state
  exact h

example (h : (p ∧ q) |-tl- (r)) :
    (wrappedAlways p ∧ wrappedAlways q) |-tl- (wrappedAlways r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example : (□ p ∧ ◇ q ∧ □ r) |-tl- (◇ q) := by
  tstart hp hq hr
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlfml| □ r]⟩] [tlfml| ◇ q]
  tapply Lentil.now_weaken_to_eventually
  tassumption

example (h : (𝒲ℱ a ∧ p) |-tl- (◇ q)) :
    (𝒲ℱ a ∧ ◇ p) |-tl- (◇ q) := by
  tstart hwf hp
  tadvance hp
  guard_target =ₛ Entails [⟨"hwf", [tlfml| 𝒲ℱ a]⟩, ⟨"hp", p⟩] [tlfml| ◇ q]
  exact h

example (h : (□ p ∧ q ∧ □ r) |-tl- (□ ◇ r)) :
    (□ p ∧ ◇ q ∧ □ r) |-tl- (□ ◇ r) := by
  tstart hp hq hr
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlfml| □ r]⟩] [tlfml| □ ◇ r]
  exact h

example {P : Prop} (h : (□ p ∧ q) |-tl- (⌞ P ⌟)) :
    (□ p ∧ ◇ q) |-tl- (⌞ P ⌟) := by
  tstart hp hq
  tadvance hq
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩] [tlfml| ⌞ P ⌟]
  exact h

example (h : (p ∧ q) |-tl- (r)) :
    (◯ p ∧ ◯ q) |-tl- (◯ r) := by
  tstart hp hq
  tstep
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (□ p ∧ □ q) |-tl- (r)) :
    (□ p ∧ □ q) |-tl- (◯ r) := by
  tstart hp hq
  tstep
  guard_target =ₛ Entails
    [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", [tlfml| □ q]⟩] r
  exact h

example (s : pred σ) (h : (□ q ∧ p ∧ r) |-tl- (s)) :
    (◯ p ∧ □ q ∧ ◯ r) |-tl- (◯ s) := by
  tstart hp hq hr
  tstep
  guard_target =ₛ Entails
    [⟨"hq", [tlfml| □ q]⟩, ⟨"hp", p⟩, ⟨"hr", r⟩] s
  exact h

example (h : (⊤) |-tl- (p)) : (⊤) |-tl- (◯ p) := by
  tstart
  tstep
  guard_target =ₛ Entails [] p
  exact h

example (h : (□ p ∧ q) |-tl- (r)) :
    (wrappedAlways p ∧ wrappedLater q) |-tl- (wrappedLater r) := by
  tstart hp hq
  tstep
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩] r
  exact h

/--
error: tstep: expected the proof-mode goal to have a leading next (`◯`) prefix
-/
#guard_msgs in
example : (□ p) |-tl- (q) := by
  tstart hp
  tstep

/--
error: tstep: expected every temporal hypothesis to have a leading always (`□`) or next (`◯`) prefix
-/
#guard_msgs in
example : (□ p ∧ q) |-tl- (◯ r) := by
  tstart hp hq
  tstep

/--
error: ttoggle_goal_under_always: expected every temporal hypothesis to have an always prefix
-/
#guard_msgs in
example : (□ p ∧ r) |-tl- (q) := by
  tstart hp hr
  ttoggle_goal_under_always

end Lentil.Test.ModalityMisc
