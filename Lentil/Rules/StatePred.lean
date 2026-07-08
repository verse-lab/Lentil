import Lentil.Rules.WF
import Lentil.Rules.BigOp
import Lentil.Tactics.FiniteWindow

/-! Theorems specialized for state predicates.
    Their premises are typically pure Lean propositions involving
    states before/after an action, instead of being in the form of
    `|-tla-`. -/

open Classical

namespace TLA

section state_pred_specialized

variable {σ : Type u}

theorem state_preds_and (p q : σ → Prop) : (⌜ p ⌝ ∧ ⌜ q ⌝) =tla= ⌜ fun s => p s ∧ q s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_preds_not (p : σ → Prop) : (¬ ⌜ p ⌝) =tla= ⌜ fun s => ¬ p s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_preds_or (p q : σ → Prop) : (⌜ p ⌝ ∨ ⌜ q ⌝) =tla= ⌜ fun s => p s ∨ q s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_preds_implies (p q : σ → Prop) : (⌜ p ⌝ → ⌜ q ⌝) =tla= ⌜ fun s => p s → q s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_preds_forall {α : Sort v} (p : α → σ → Prop) : (∀ x, ⌜ p x ⌝) =tla= ⌜ fun s => ∀ x, p x s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_preds_exists {α : Sort v} (p : α → σ → Prop) : (∃ x, ⌜ p x ⌝) =tla= ⌜ fun s => ∃ x, p x s ⌝ := by
  funext e i ; tnontemporal_simp

theorem state_pred_valid_iff (p : σ → Prop) : (|-tla- ⌜ p ⌝) ↔ ∀ s, p s := by
  constructor
  · intro h s
    exact h (fun _ => s) 0
  · intro h e i
    exact h (e i)

theorem state_pred_implies_iff (p q : σ → Prop) : (⌜ p ⌝ |-tla- ⌜ q ⌝) ↔ ∀ s, p s → q s := by
  constructor
  · intro h s hp
    exact h (fun _ => s) 0 hp
  · intro h e i hp
    exact h (e i) hp

theorem state_pred_eq_iff (p q : σ → Prop) : ((⌜ p ⌝) =tla= (⌜ q ⌝)) ↔ ∀ s, p s ↔ q s := by
  constructor
  · intro h s
    have h' := congrFun (congrFun h (fun _ => s)) 0
    exact iff_of_eq h'
  · intro h
    funext e i
    exact propext (h (e i))

theorem state_pred_as_action (p : σ → Prop) : (⌜ p ⌝) =tla= ⟨ fun s _ => p s ⟩ := by
  funext e i ; tunfold_simp

theorem later_state_pred_as_action (p : σ → Prop) : (◯ ⌜ p ⌝) =tla= ⟨ fun _ s' => p s' ⟩ := by
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

theorem state_preds_bigwedge_list {α : Type v} (p : α → σ → Prop) (l : List α) :
    (⋀ x ∈ l, ⌜ p x ⌝) =tla= ⌜ fun s => ∀ x, x ∈ l → p x s ⌝ := by
  rw [bigwedge_forall_list]
  funext e i ; tnontemporal_simp

theorem state_preds_bigvee_list {α : Type v} (p : α → σ → Prop) (l : List α) :
    (⋁ x ∈ l, ⌜ p x ⌝) =tla= ⌜ fun s => ∃ x, x ∈ l ∧ p x s ⌝ := by
  rw [bigvee_exists_list]
  funext e i ; tnontemporal_simp

theorem init_invariant {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hinit : ∀ s, init s → inv s)
    (hnext : ∀ s s', next s s' → inv s → inv s') :
  (⌜ init ⌝ ∧ □ ⟨next⟩) |-tla- (□ ⌜ inv ⌝) := by
  have hstep : (⌜ inv ⌝ ∧ ⟨next⟩) |-tla- (◯ ⌜ inv ⌝) := by
    tfinite_window
    aesop
  rw (occs := .pos [2]) [always_induction]
  rw [and_pred_implies_split] ; apply And.intro
  · intro e i ⟨hinit', _⟩
    exact hinit _ hinit'
  · intro e i ⟨_, hnext'⟩ k hinv
    exact hstep e (i + k) ⟨hinv, hnext' k⟩

end state_pred_specialized

end TLA
