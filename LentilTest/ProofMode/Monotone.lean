import Lentil

namespace TLA.Test.Modality

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

example (h : (p) |-tla- (q)) : (◯ p) |-tla- (◯ q) := by
  tla_monotone
  exact h

example (h : (p ∧ q) |-tla- (r)) : (◯ p ∧ ◯ q) |-tla- (◯ r) := by
  tla_start hp hq
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (p ∧ q) |-tla- (r)) : (□ p ∧ □ q) |-tla- (□ r) := by
  tla_start hp hq
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (p) |-tla- (q)) : (◇ p) |-tla- (◇ q) := by
  tla_start hp
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩] q
  exact h

example (h : (p) |-tla- (q)) : (□ ◇ p) |-tla- (□ ◇ q) := by
  tla_start hp
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩] q
  exact h

example (h : (p ∧ q) |-tla- (r)) : (◇ □ p ∧ ◇ □ q) |-tla- (◇ □ r) := by
  tla_start hp hq
  tla_monotone
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

end TLA.Test.Modality
