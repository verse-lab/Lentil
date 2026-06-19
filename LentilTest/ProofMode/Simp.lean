import Lentil

/- Tests for `tla_simp`, `tla_dsimp`, and `tla_unfold`. -/

namespace TLA.ProofMode.Test.Simp

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

def wrapPred {σ : Type u} (p : pred σ) : pred σ := p

-- `tla_simp` uses Lean-style locations and visits the selected expression by conv.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_simp [heq] at hp
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Goal simplification is the default for `tla_simp`.
example (heq : q = r) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tla_start hp
  tla_simp [← heq]
  tla_check_goal Entails [⟨"hp", p⟩] q
  exact h

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tla- (q) := by
  tla_start hp hr
  tla_simp [heq] at 0
  tla_check_goal Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  intro _ h ; exact h.1

-- The direct conv implementation must not simplify unselected hypotheses.
example (heq : p = q) : (p ∧ p ∧ p) |-tla- (q) := by
  tla_start hp1 hp2 hp3
  tla_simp [heq] at hp1 hp3
  tla_check_goal Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  intro _ h ; exact h.1

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tla- (p) := by
  tla_start hp
  tla_simp [heq] at hp ⊢
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `at *` visits all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_simp [heq] at *
  tla_check_goal Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `tla_dsimp` unfolds selected proof-mode hypotheses.
example : TLA.pred_implies (wrapPred p) p := by
  tla_start hp
  tla_dsimp [wrapPred] at hp
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tla_unfold` directly runs Lean's conv-level `unfold` on the goal by default.
example : TLA.pred_implies p (wrapPred p) := by
  tla_start hp
  tla_unfold wrapPred
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `tla_unfold` can unfold selected proof-mode hypotheses.
example : TLA.pred_implies (wrapPred p) p := by
  tla_start hp
  tla_unfold wrapPred at hp
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Lean-style locations can include both selected hypotheses and the target.
example : TLA.pred_implies (wrapPred p) (wrapPred p) := by
  tla_start hp
  tla_unfold wrapPred at hp ⊢
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- `at *` unfolds all temporal hypotheses and the goal.
example : (wrapPred p ∧ wrapPred q) |-tla- (wrapPred p) := by
  tla_start hp hq
  tla_unfold wrapPred at *
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
  intro _ h
  exact h.1

-- The old all-definition unfolding tactic is still available under its new name.
example : @TLA.valid σ TLA.tla_true := by
  tla_unfold_defs
  intro _
  trivial

end TLA.ProofMode.Test.Simp
