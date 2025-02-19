import Lentil.Rules.WF

/-! Theorems specialized for state predicates.
    Their premises are typically pure Lean propositions involving
    states before/after an action, instead of being in the form of
    `|-tla-`. -/

open Classical

namespace TLA

section state_pred_specialized

variable {σ : Type u}

theorem state_preds_and (p q : σ → Prop) : (⌜ p ⌝ ∧ ⌜ q ⌝) =tla= ⌜ λ s => p s ∧ q s ⌝ := by
  funext e ; tla_unfold_simp

theorem init_invariant {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hinit : ∀ s, init s → inv s)
    (hnext : ∀ s s', next s s' → inv s → inv s') :
  (⌜ init ⌝ ∧ □ ⟨next⟩) |-tla- (□ ⌜ inv ⌝) := by
  tla_unfold_simp ; unfold exec.drop action_pred ; simp
  intro e hinit hs k
  induction k with
  | zero => aesop
  | succ n ih => rw [Nat.add_comm] ; aesop

set_option maxHeartbeats 800000 in
/-- `wf1` with `p`, `q`, `init` and `inv` being state predicates. -/
theorem wf1' (p q init inv : σ → Prop) (next a : action σ)
  (hpuntilq : ∀ s s', p s → next s s' → p s' ∨ q s')
  (haq : ∀ s s', p s → next s s' → a s s' → q s')
  (henable : ∀ s, inv s → p s → enabled a s ∨ q s)
  (hinit_inv : ∀ s, init s → inv s)
  (hnext_inv : ∀ s s', next s s' → inv s → inv s') :
  (⌜ init ⌝ ∧ □ ⟨next⟩ ∧ 𝒲ℱ a) |-tla- (⌜ p ⌝ ↝ ⌜ q ⌝) := by
  have hinv := init_invariant hinit_inv hnext_inv
  apply wf1 (state_pred p) (state_pred q) (state_pred init) (state_pred inv) <;> tla_unfold_simp <;> aesop

end state_pred_specialized

end TLA
