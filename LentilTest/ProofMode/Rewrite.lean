import Lentil

/- Tests for `trewrite`. -/

namespace TLA.ProofMode.Test.Rewrite

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- No location means the goal predicate is rewritten.
example (heq : q = r) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tstart hp
  trewrite [← heq]
  tcheck_goal Entails [⟨"hp", p⟩] q
  exact h

-- A named proof-mode hypothesis can be rewritten without touching the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tstart hp
  trewrite [heq] at hp
  tcheck_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tla- (q) := by
  tstart hp hr
  trewrite [heq] at 0
  tcheck_goal Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  intro _ h ; exact h.1

-- Local variables introduced after entering proof mode remain visible to rewrite.
example (P Q : Nat → pred σ) (heq : ∀ n, P n = Q n) :
    (⊤) |-tla- (∀ n : Nat, (P n) → (Q n)) := by
  tstart
  tintro n hp
  trewrite [heq n] at hp
  tcheck_goal Entails [⟨"hp", Q n⟩] (Q n)
  exact pred_implies_refl _

-- Regression: unselected hypotheses must be hidden in the value body of the
-- local continuation, otherwise Lean's `rewrite` traverses and rewrites them.
example (heq : q = p) : (p ∧ p ∧ p) |-tla- (q) := by
  tstart hp1 hp2 hp3
  trewrite [← heq] at hp1 hp3
  tcheck_goal Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  intro _ h ; exact h.1

-- Rewriting can create ordinary Lean side goals, so `trewrite` is not
-- implemented as a `conv` tactic.
example {P : Prop} (heq : P → p = q) (hP : P) : (p) |-tla- (q) := by
  tstart hp
  trewrite [heq] at hp
  · tcheck_goal Entails [⟨"hp", q⟩] q
    exact pred_implies_refl _
  · exact hP

-- `at *` exposes all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tstart hp
  trewrite [heq] at *
  tcheck_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `trewrite` follows Lean's location semantics: selected hypotheses are
-- rewritten one by one, not as one combined list of locations.
example : (□□p ∧ q ∧ □□r) |-tla- (q) := by
  tstart hp hq hr
  trewrite [always_idem] at *
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] q
  intro _ h ; exact h.2.1

example : (□□p ∧ q ∧ □□r) |-tla- (q) := by
  tstart hp hq hr
  trewrite [always_idem] at hp hr
  tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlafml| □ r]⟩] q
  intro _ h ; exact h.2.1

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tla- (p) := by
  tstart hp
  trewrite [heq] at hp ⊢
  tcheck_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

end TLA.ProofMode.Test.Rewrite
