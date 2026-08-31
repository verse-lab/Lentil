import Lentil

/- Tests for `trewrite`. -/

namespace Lentil.ProofMode.Test.Rewrite

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- No location means the goal predicate is rewritten.
example (heq : q = r) (h : (p) |-tl- (q)) : (p) |-tl- (r) := by
  tstart hp
  trewrite [← heq]
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

-- A named proof-mode hypothesis can be rewritten without touching the goal.
example (heq : p = q) : (p) |-tl- (q) := by
  tstart hp
  trewrite [heq] at hp
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tl- (q) := by
  tstart hp hr
  trewrite [heq] at 0
  guard_target =ₛ Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  tassumption

-- Local variables introduced after entering proof mode remain visible to rewrite.
example (P Q : Nat → pred σ) (heq : ∀ n, P n = Q n) :
    (⊤) |-tl- (∀ n : Nat, (P n) → (Q n)) := by
  tstart
  tintro n hp
  trewrite [heq n] at hp
  guard_target =ₛ Entails [⟨"hp", Q n⟩] (Q n)
  exact pred_implies_refl _

-- Regression: unselected hypotheses must be hidden in the value body of the
-- local continuation, otherwise Lean's `rewrite` traverses and rewrites them.
example (heq : q = p) : (p ∧ p ∧ p) |-tl- (q) := by
  tstart hp1 hp2 hp3
  trewrite [← heq] at hp1 hp3
  guard_target =ₛ Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  tassumption

-- Rewriting can create ordinary Lean side goals, so `trewrite` is not
-- implemented as a `conv` tactic.
example {P : Prop} (heq : P → p = q) (hP : P) : (p) |-tl- (q) := by
  tstart hp
  trewrite [heq] at hp
  · guard_target =ₛ Entails [⟨"hp", q⟩] q
    exact pred_implies_refl _
  · exact hP

-- `at *` exposes all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tl- (q) := by
  tstart hp
  trewrite [heq] at *
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `trewrite` follows Lean's location semantics: selected hypotheses are
-- rewritten one by one, not as one combined list of locations.
example : (□□p ∧ q ∧ □□r) |-tl- (q) := by
  tstart hp hq hr
  trewrite [always_idem] at *
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlfml| □ r]⟩] q
  tassumption

example : (□□p ∧ q ∧ □□r) |-tl- (q) := by
  tstart hp hq hr
  trewrite [always_idem] at hp hr
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", q⟩, ⟨"hr", [tlfml| □ r]⟩] q
  tassumption

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tl- (p) := by
  tstart hp
  trewrite [heq] at hp ⊢
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

end Lentil.ProofMode.Test.Rewrite
