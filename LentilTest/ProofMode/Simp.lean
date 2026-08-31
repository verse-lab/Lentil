import Lentil

/- Tests for `tsimp`, `tdsimp`, and `tunfold`. -/

namespace Lentil.ProofMode.Test.Simp

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

def wrapPred {σ : Type u} (p : pred σ) : pred σ := p

-- `tsimp` uses Lean-style locations and visits the selected expression by conv.
example (heq : p = q) : (p) |-tl- (q) := by
  tstart hp
  tsimp [heq] at hp
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Goal simplification is the default for `tsimp`.
example (heq : q = r) (h : (p) |-tl- (q)) : (p) |-tl- (r) := by
  tstart hp
  tsimp [← heq]
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tl- (q) := by
  tstart hp hr
  tsimp [heq] at 0
  guard_target =ₛ Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  tassumption

-- The direct conv implementation must not simplify unselected hypotheses.
example (heq : p = q) : (p ∧ p ∧ p) |-tl- (q) := by
  tstart hp1 hp2 hp3
  tsimp [heq] at hp1 hp3
  guard_target =ₛ Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  tassumption

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tl- (p) := by
  tstart hp
  tsimp [heq] at hp ⊢
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Local variables introduced after entering proof mode remain visible to conv.
example (P Q : Nat → pred σ) (heq : ∀ n, P n = Q n) :
    (⊤) |-tl- (∀ n : Nat, (P n) → (Q n)) := by
  tstart
  tintro n hp
  tsimp [heq n] at hp
  guard_target =ₛ Entails [⟨"hp", Q n⟩] (Q n)
  exact pred_implies_refl _

-- `at *` visits all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tl- (q) := by
  tstart hp
  tsimp [heq] at *
  guard_target =ₛ Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `tdsimp` unfolds selected proof-mode hypotheses.
example : (wrapPred p) |-tl- (p) := by
  tstart hp
  tdsimp [wrapPred] at hp
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tunfold` directly runs Lean's conv-level `unfold` on the goal by default.
example : (p) |-tl- (wrapPred p) := by
  tstart hp
  tunfold wrapPred
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tunfold` can unfold selected proof-mode hypotheses.
example : (wrapPred p) |-tl- (p) := by
  tstart hp
  tunfold wrapPred at hp
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Lean-style locations can include both selected hypotheses and the target.
example : (wrapPred p) |-tl- (wrapPred p) := by
  tstart hp
  tunfold wrapPred at hp ⊢
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `at *` unfolds all temporal hypotheses and the goal.
example : (wrapPred p ∧ wrapPred q) |-tl- (wrapPred p) := by
  tstart hp hq
  tunfold wrapPred at *
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
  tassumption

-- The old all-definition unfolding tactic is still available under its new name.
example : |-tl- ([tlfml| ⊤] : pred σ) := by
  tunfold_defs
  apply valid_pure True.intro

end Lentil.ProofMode.Test.Simp
