import Lentil

namespace TLA.Test.Modality

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

example (h : (p) |-tla- (q)) : (◯ p) |-tla- (◯ q) := by
  tmonotone
  exact h

example (h : (p ∧ q) |-tla- (r)) : (◯ p ∧ ◯ q) |-tla- (◯ r) := by
  tstart hp hq
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (p ∧ q) |-tla- (r)) : (□ p ∧ □ q) |-tla- (□ r) := by
  tstart hp hq
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : ((p → q) ∧ (q → r)) |-tla- (p → r)) :
    ((p ⇒ q) ∧ (q ⇒ r)) |-tla- (p ⇒ r) := by
  tstart hp hq
  tmonotone
  tcheck_goal Entails
    [⟨"hp", [tlafml| p → q]⟩, ⟨"hq", [tlafml| q → r]⟩] [tlafml| p → r]
  exact h

example (h : (p) |-tla- (q)) : (◇ p) |-tla- (◇ q) := by
  tstart hp
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩] q
  exact h

example (h : (p) |-tla- (q)) : (□ ◇ p) |-tla- (□ ◇ q) := by
  tstart hp
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩] q
  exact h

example (h : (p ∧ q) |-tla- (r)) : (◇ □ p ∧ ◇ □ q) |-tla- (◇ □ r) := by
  tstart hp hq
  tmonotone
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

end TLA.Test.Modality
