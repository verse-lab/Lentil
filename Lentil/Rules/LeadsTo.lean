import Lean
import Lentil.Rules.Basic
import Lentil.Gadgets.TheoremDeriving

/-! Theorems about the leads-to operator. -/

open Classical

namespace TLA

section leads_to

variable {σ : Type u}

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tla- ((p x) ↝ q)) ↔ (Γ) |-tla- ((tla_exists p) ↝ q) := by
  tunfold_simp ; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tla- (p ↝ q)) ↔ (Γ) |-tla- (⌞ φ ⌟ ∧ p ↝ q) := by
  tunfold_simp ; aesop

@[tla_derive]
theorem leads_to_conseq {p p' q q' : pred σ} :
  |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) → (p' ↝ q')) := by
  tunfold_simp ; intro e i h1 h2 h k hp'
  specialize h _ (h1 _ hp') ; rcases h with ⟨k1, h⟩
  specialize h2 (k + k1) ; exists k1 ; grind

@[tla_derive]
theorem leads_to_trans {p q r : pred σ} :
  |-tla- ((p ↝ q) → (q ↝ r) → (p ↝ r)) := by
  tunfold_simp ; intro e i h1 h2 k hp
  rcases h1 k hp with ⟨k1, hq⟩
  rcases h2 (k + k1) (by simpa [Nat.add_assoc] using hq) with ⟨k2, hr⟩
  exists k1 + k2
  simpa [Nat.add_assoc] using hr

theorem leads_to_combine {Γ Γ' p1 q1 p2 q2 : pred σ}
  (h1 : (□ Γ ∧ Γ') |-tla- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tla- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tla- □ q1) (h2' : (q2 ∧ □ Γ) |-tla- □ q2) :
  (□ Γ ∧ Γ') |-tla- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tunfold_simp ; intro e i hΓ hΓ' k hp1 hp2
  rcases h1 e i hΓ hΓ' k hp1 with ⟨k1, hq1⟩
  rcases h2 e i hΓ hΓ' k hp2 with ⟨k2, hq2⟩
  exists k1 + k2
  constructor
  · have hq1' := h1' e (i + k + k1) hq1
      (fun l => by simpa [Nat.add_assoc] using hΓ (k + k1 + l)) k2
    simpa [Nat.add_assoc] using hq1'
  · have hq2' := h2' e (i + k + k2) hq2
      (fun l => by simpa [Nat.add_assoc] using hΓ (k + k2 + l)) k1
    have heq : i + k + k2 + k1 = i + k + (k1 + k2) := by omega
    simpa [heq] using hq2'

@[tla_derive]
theorem leads_to_strengthen_lhs {p q inv : pred σ} :
  |-tla- (□ inv → (p ∧ inv ↝ q) → (p ↝ q)) := by
  tunfold_simp ; aesop

end leads_to

end TLA
