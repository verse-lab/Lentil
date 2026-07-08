import Lentil.Rules.Basic
import Lentil.Rules.BigOp

/-! Theorems specialized for action predicates. -/

open Classical

namespace TLA

section action_pred_specialized

variable {σ : Type u}

theorem action_pred_true :
    (⟨ fun _ _ : σ => True ⟩) =tla= (⊤) := by
  funext e i ; tunfold_simp

theorem action_pred_false :
    (⟨ fun _ _ : σ => False ⟩) =tla= (⊥) := by
  funext e i ; tunfold_simp

theorem action_pred_not (a : action σ) :
    (⟨ fun s s' => ¬ a s s' ⟩) =tla= (¬ ⟨ a ⟩) := by
  funext e i ; tunfold_simp

theorem action_pred_and (a b : action σ) :
    (⟨ fun s s' => a s s' ∧ b s s' ⟩) =tla= (⟨ a ⟩ ∧ ⟨ b ⟩) := by
  funext e i ; tunfold_simp

theorem action_pred_or (a b : action σ) :
    (⟨ fun s s' => a s s' ∨ b s s' ⟩) =tla= (⟨ a ⟩ ∨ ⟨ b ⟩) := by
  funext e i ; tunfold_simp

theorem action_pred_implies (a b : action σ) :
    (⟨ fun s s' => a s s' → b s s' ⟩) =tla= (⟨ a ⟩ → ⟨ b ⟩) := by
  funext e i ; tunfold_simp

theorem action_pred_forall {α : Sort v} (a : α → action σ) :
    (⟨ fun s s' => ∀ x, a x s s' ⟩) =tla= (∀ x, ⟨ a x ⟩) := by
  funext e i ; tunfold_simp

theorem action_pred_exists {α : Sort v} (a : α → action σ) :
    (⟨ fun s s' => ∃ x, a x s s' ⟩) =tla= (∃ x, ⟨ a x ⟩) := by
  funext e i ; tunfold_simp

theorem action_preds_bigwedge_list {α : Type v} (a : α → action σ) (l : List α) :
    (⋀ x ∈ l, ⟨ a x ⟩) =tla= ⟨ fun s s' => ∀ x, x ∈ l → a x s s' ⟩ := by
  rw [bigwedge_forall_list]
  funext e i ; tnontemporal_simp

theorem action_preds_bigvee_list {α : Type v} (a : α → action σ) (l : List α) :
    (⋁ x ∈ l, ⟨ a x ⟩) =tla= ⟨ fun s s' => ∃ x, x ∈ l ∧ a x s s' ⟩ := by
  rw [bigvee_exists_list]
  funext e i ; tnontemporal_simp

theorem action_pred_valid_iff (a : action σ) :
    (|-tla- ⟨ a ⟩) ↔ ∀ s s', a s s' := by
  constructor
  · intro h s s'
    exact h (fun
      | 0 => s
      | _ + 1 => s') 0
  · intro h e i
    exact h (e i) (e (i + 1))

theorem action_pred_implies_iff (a b : action σ) :
    (⟨ a ⟩ |-tla- ⟨ b ⟩) ↔ ∀ s s', a s s' → b s s' := by
  constructor
  · intro h s s' ha
    exact h (fun
      | 0 => s
      | _ + 1 => s') 0 ha
  · intro h e i ha
    exact h (e i) (e (i + 1)) ha

theorem action_pred_eq_iff (a b : action σ) :
    ((⟨ a ⟩) =tla= (⟨ b ⟩)) ↔ ∀ s s', a s s' ↔ b s s' := by
  constructor
  · intro h s s'
    have h' := congrFun (congrFun h (fun
      | 0 => s
      | _ + 1 => s')) 0
    exact iff_of_eq h'
  · intro h
    funext e i
    exact propext (h (e i) (e (i + 1)))

theorem state_pred_as_action (p : σ → Prop) :
    (⌜ p ⌝) =tla= ⟨ fun s _ => p s ⟩ := by
  funext e i ; tunfold_simp

theorem later_state_pred_as_action (p : σ → Prop) :
    (◯ ⌜ p ⌝) =tla= ⟨ fun _ s' => p s' ⟩ := by
  funext e i ; tunfold_simp

theorem state_pred_and_action (p : σ → Prop) (a : action σ) :
    (⌜ p ⌝ ∧ ⟨ a ⟩) =tla= ⟨ fun s s' => p s ∧ a s s' ⟩ := by
  funext e i ; tunfold_simp

theorem action_and_state_pred (a : action σ) (p : σ → Prop) :
    (⟨ a ⟩ ∧ ⌜ p ⌝) =tla= ⟨ fun s s' => a s s' ∧ p s ⟩ := by
  funext e i ; tunfold_simp

theorem later_state_pred_and_action (p : σ → Prop) (a : action σ) :
    (◯ ⌜ p ⌝ ∧ ⟨ a ⟩) =tla= ⟨ fun s s' => p s' ∧ a s s' ⟩ := by
  funext e i ; tunfold_simp

theorem action_and_later_state_pred (a : action σ) (p : σ → Prop) :
    (⟨ a ⟩ ∧ ◯ ⌜ p ⌝) =tla= ⟨ fun s s' => a s s' ∧ p s' ⟩ := by
  funext e i ; tunfold_simp

theorem state_pred_and_later_state_pred (p q : σ → Prop) :
    (⌜ p ⌝ ∧ ◯ ⌜ q ⌝) =tla= ⟨ fun s s' => p s ∧ q s' ⟩ := by
  funext e i ; tunfold_simp

theorem action_preds_and (a b : action σ) :
    (⟨ a ⟩ ∧ ⟨ b ⟩) =tla= ⟨ fun s s' => a s s' ∧ b s s' ⟩ := by
  funext e i ; tunfold_simp

theorem enabled_state_pred_and_action (p : σ → Prop) (a : action σ) :
    (Enabled (fun s s' => p s ∧ a s s')) =tla= ⌜ fun s => p s ∧ enabled a s ⌝ := by
  funext e i ; simp [tla_enabled, state_pred, enabled]

theorem enabled_action_and_later_state_pred (a : action σ) (p : σ → Prop) :
    (Enabled (fun s s' => a s s' ∧ p s')) =tla= ⌜ fun s => ∃ s', a s s' ∧ p s' ⌝ := by
  funext e i ; simp [tla_enabled, state_pred, enabled]

end action_pred_specialized

end TLA
