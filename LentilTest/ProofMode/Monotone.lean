import Lentil

namespace Lentil.Test.Modality

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

example (h : (p) |-tl- (q)) : (◯ p) |-tl- (◯ q) := by
  tmonotone
  exact h

example (h : (p ∧ q) |-tl- (r)) : (◯ p ∧ ◯ q) |-tl- (◯ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (p ∧ q) |-tl- (r)) : (□ p ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : ((p → q) ∧ (q → r)) |-tl- (p → r)) :
    ((p ⇒ q) ∧ (q ⇒ r)) |-tl- (p ⇒ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails
    [⟨"hp", [tlfml| p → q]⟩, ⟨"hq", [tlfml| q → r]⟩] [tlfml| p → r]
  exact h

example (h : (p) |-tl- (q)) : (◇ p) |-tl- (◇ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

example (h : (p) |-tl- (q)) : (□ ◇ p) |-tl- (□ ◇ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

example (h : (p ∧ q) |-tl- (r)) : (◇ □ p ∧ ◇ □ q) |-tl- (◇ □ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

end Lentil.Test.Modality
