import Lentil

/- Tests for `tla_simp` and `tla_dsimp`. -/

namespace TLA.ProofMode.Test.Simp

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

def wrapPred {σ : Type u} (p : pred σ) : pred σ := p

-- `tla_simp` uses Lean-style locations and visits the selected expression by conv.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_simp [heq] at hp
  show Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- Goal simplification is the default for `tla_simp`.
example (heq : q = r) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tla_start hp
  tla_simp [← heq]
  show Entails [⟨"hp", p⟩] q
  exact h

-- Numeric locations refer to proof-mode hypothesis indices.
example (heq : p = q) : (p ∧ r) |-tla- (q) := by
  tla_start hp hr
  tla_simp [heq] at 0
  show Entails [⟨"hp", q⟩, ⟨"hr", r⟩] q
  intro _ h ; exact h.1

-- The direct conv implementation must not simplify unselected hypotheses.
example (heq : p = q) : (p ∧ p ∧ p) |-tla- (q) := by
  tla_start hp1 hp2 hp3
  tla_simp [heq] at hp1 hp3
  show Entails [⟨"hp1", q⟩, ⟨"hp2", p⟩, ⟨"hp3", q⟩] q
  intro _ h ; exact h.1

-- Lean-style locations can include both selected hypotheses and the target.
example (heq : p = q) : (p) |-tla- (p) := by
  tla_start hp
  tla_simp [heq] at hp ⊢
  show Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `at *` visits all temporal hypotheses and the goal.
example (heq : p = q) : (p) |-tla- (q) := by
  tla_start hp
  tla_simp [heq] at *
  show Entails [⟨"hp", q⟩] q
  exact pred_implies_refl _

-- `tla_dsimp` unfolds selected proof-mode hypotheses.
example : TLA.pred_implies (wrapPred p) p := by
  tla_start hp
  tla_dsimp [wrapPred] at hp
  show Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

end TLA.ProofMode.Test.Simp
