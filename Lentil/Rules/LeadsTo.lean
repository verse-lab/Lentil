import Lentil.Rules.Basic

/-! Theorems about the leads-to operator. -/

open Classical

namespace TLA

section leads_to

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tla- ((p x) ↝ q)) ↔ (Γ) |-tla- ((tla_exists p) ↝ q) := by
  tla_unfold_simp ; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tla- (p ↝ q)) ↔ (Γ) |-tla- (⌞ φ ⌟ ∧ p ↝ q) := by
  tla_unfold_simp ; aesop

theorem leads_to_conseq (p p' q q': pred σ) :
  (p') |-tla- (p) → (q) |-tla- (q') → (p ↝ q) |-tla- (p' ↝ q') := by
  intro h1 h2 ; tla_unfold_simp ; intro e h k hh
  specialize h _ (h1 _ hh) ; rcases h with ⟨k1, h⟩ ; aesop

theorem leads_to_trans (Γ p q r : pred σ) :
  (Γ) |-tla- (p ↝ q) → (Γ) |-tla- (q ↝ r) → (Γ) |-tla- (p ↝ r) := by
  intro h1 h2 ; tla_unfold_simp ; intro e h k hh
  specialize h1 _ h k hh ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ h _ h1 ; rcases h2 with ⟨k2, h2⟩
  exists (k1 + k2) ; rw [← Nat.add_assoc] ; assumption

theorem leads_to_combine (Γ Γ' p1 q1 p2 q2 : pred σ)
  (h1 : (□ Γ ∧ Γ') |-tla- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tla- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tla- □ q1) (h2' : (q2 ∧ □ Γ) |-tla- □ q2) :
  (□ Γ ∧ Γ') |-tla- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tla_unfold_simp ; intro e hΓ hΓ' k hp1 hp2
  specialize h1 _ hΓ hΓ' k hp1 ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ hΓ hΓ' k hp2 ; rcases h2 with ⟨k2, h2⟩
  exists k1 + k2
  specialize h1' _ h1 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k2
  specialize h2' _ h2 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k1
  simp [exec.drop_drop] at h1' h2'
  constructor ; rw [← Nat.add_assoc] ; assumption ; rw [Nat.add_comm k1 k2, ← Nat.add_assoc] ; assumption

theorem leads_to_strengthen_lhs (Γ p q inv : pred σ)
  (hinv : (Γ) |-tla- □ inv) :
  (Γ) |-tla- (p ∧ inv ↝ q) → (Γ) |-tla- (p ↝ q) := by
  tla_unfold_simp ; aesop

end leads_to

end TLA
