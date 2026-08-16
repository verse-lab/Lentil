import Lentil

/- Tests for `tsimp`, `tdsimp`, and `tunfold`. -/

namespace TLA.ProofMode.Test.Simp

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

def wrapPred {σ : Type u} (p : pred σ) : pred σ := p

-- `tsimp` uses Lean-style locations and visits the selected expression by conv.
example (heq : p = q) : (p) |-tla- (q) := by
  tstart hp
  tsimp [heq] at hp
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Goal simplification is the default for `tsimp`.
example (heq : q = r) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tstart hp
  tsimp [← heq]
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tla- (q) := by
  tstart hp hr
  tsimp [heq] at 0
  guard_target =ₛ Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  intro _ h ; exact h.1

-- The direct conv implementation must not simplify unselected hypotheses.
example (heq : p = q) : (p ∧ p ∧ p) |-tla- (q) := by
  tstart hp1 hp2 hp3
  tsimp [heq] at hp1 hp3
  guard_target =ₛ Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  intro _ h ; exact h.1

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tla- (p) := by
  tstart hp
  tsimp [heq] at hp ⊢
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Local variables introduced after entering proof mode remain visible to conv.
example (P Q : Nat → pred σ) (heq : ∀ n, P n = Q n) :
    (⊤) |-tla- (∀ n : Nat, (P n) → (Q n)) := by
  tstart
  tintro n hp
  tsimp [heq n] at hp
  guard_target =ₛ Entails [⟨"hp", Q n⟩] (Q n)
  exact pred_implies_refl _

-- `at *` visits all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tstart hp
  tsimp [heq] at *
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `tdsimp` unfolds selected proof-mode hypotheses.
example : (wrapPred p) |-tla- (p) := by
  tstart hp
  tdsimp [wrapPred] at hp
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tunfold` directly runs Lean's conv-level `unfold` on the goal by default.
example : (p) |-tla- (wrapPred p) := by
  tstart hp
  tunfold wrapPred
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tunfold` can unfold selected proof-mode hypotheses.
example : (wrapPred p) |-tla- (p) := by
  tstart hp
  tunfold wrapPred at hp
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Lean-style locations can include both selected hypotheses and the target.
example : (wrapPred p) |-tla- (wrapPred p) := by
  tstart hp
  tunfold wrapPred at hp ⊢
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `at *` unfolds all temporal hypotheses and the goal.
example : (wrapPred p ∧ wrapPred q) |-tla- (wrapPred p) := by
  tstart hp hq
  tunfold wrapPred at *
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
  intro _ h
  exact h.1

-- The old all-definition unfolding tactic is still available under its new name.
example : |-tla- ([tlafml| ⊤] : pred σ) := by
  tunfold_defs
  intro _
  trivial

end TLA.ProofMode.Test.Simp
