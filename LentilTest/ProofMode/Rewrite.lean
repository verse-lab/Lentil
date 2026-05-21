import Lentil

/- Tests for `tla_rewrite`. -/

namespace TLA.ProofMode.Test.Rewrite

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- No location means the goal predicate is rewritten.
example (heq : q = r) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tla_start hp
  tla_rewrite [← heq]
  tla_check_goal Entails [⟨"hp", p⟩] q
  exact h

-- A named proof-mode hypothesis can be rewritten without touching the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_rewrite [heq] at hp
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tla- (q) := by
  tla_start hp hr
  tla_rewrite [heq] at 0
  tla_check_goal Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  intro _ h ; exact h.1

-- Regression: unselected hypotheses must be hidden in the value body of the
-- local continuation, otherwise Lean's `rewrite` traverses and rewrites them.
example (heq : q = p) : (p ∧ p ∧ p) |-tla- (q) := by
  tla_start hp1 hp2 hp3
  tla_rewrite [← heq] at hp1 hp3
  tla_check_goal Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  intro _ h ; exact h.1

-- Rewriting can create ordinary Lean side goals, so `tla_rewrite` is not
-- implemented as a `conv` tactic.
example {P : Prop} (heq : P → p = q) (hP : P) : (p) |-tla- (q) := by
  tla_start hp
  tla_rewrite [heq] at hp
  · tla_check_goal Entails [⟨"hp", q⟩] q
    exact pred_implies_refl _
  · exact hP

-- `at *` exposes all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_rewrite [heq] at *
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `tla_rewrite` follows Lean's location semantics: selected hypotheses are
-- rewritten one by one, not as one combined list of locations.
example : (□□p ∧ q ∧ □□r) |-tla- (q) := by
  tla_start hp hq hr
  tla_rewrite [always_idem] at *
  tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] q
  intro _ h ; exact h.2.1

example : (□□p ∧ q ∧ □□r) |-tla- (q) := by
  tla_start hp hq hr
  tla_rewrite [always_idem] at hp hr
  tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] q
  intro _ h ; exact h.2.1

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tla- (p) := by
  tla_start hp
  tla_rewrite [heq] at hp ⊢
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

end TLA.ProofMode.Test.Rewrite
