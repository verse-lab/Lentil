import Lentil.Rules.Basic

/-! Theorems about big operators (e.g., `⋀`, `⋁`). -/

open Classical LentilLib

namespace TLA

section bigop

variable {α : Type u} {β : Type v} (f g : β → pred α) (l : List β)

-- FIXME: currently we only have the definition of `fold`, but we do not specify
-- its result, so for each `Foldable` instance, we need to repeat the following proofs!
-- maybe we should revise the definitions of `bigwedge` and `bigvee` (see `Lentil/Basic.lean`)
-- also, can we get rid of the repetition?

section bigwedge

@[tlasimp]
theorem bigwedge_list_nil : (⋀ x ∈ [], (f x)) =tla= (⊤) := rfl

@[tlasimp]
theorem bigwedge_list_cons (b : β) : (⋀ x ∈ (b :: l), (f x)) =tla= ((f b) ∧ ⋀ x ∈ l, (f x)) := rfl

theorem bigwedge_forall_list : (⋀ x ∈ l, (f x)) =tla= (∀ x, (⌞ x ∈ l ⌟ → (f x))) := by
  induction l with
  | nil => funext e ; tla_unfold_simp
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e ; tla_unfold_simp

theorem bigwedge_forall_fintype_list : (⋀ x ∈ l, (f x)) =tla= (∀ x : Fin l.length, (f l[x])) := by
  rw [bigwedge_forall_list]
  funext e ; tla_unfold_simp ; apply List.mem_forall_iff_fin_index

theorem bigwedge_inner_and_split : (⋀ x ∈ l, (f x) ∧ (g x)) =tla= ((⋀ x ∈ l, (f x)) ∧ (⋀ x ∈ l, (g x))) := by
  (repeat rw [bigwedge_forall_list]) ; funext e ; tla_unfold_simp ; aesop

theorem always_bigwedge : (□ ⋀ x ∈ l, (f x)) =tla= (⋀ x ∈ l, □ (f x)) := by
  (repeat rw [bigwedge_forall_list]) ; funext e ; tla_unfold_simp ; aesop

theorem eventually_always_bigwedge_distrib : (◇ □ ⋀ x ∈ l, (f x)) =tla= (⋀ x ∈ l, ◇ □ (f x)) := by
  induction l with
  | nil => funext e ; tla_unfold_simp
  | cons x l ih => simp [tlasimp, eventually_always_and_distrib, ih]

end bigwedge

section bigvee

@[tlasimp]
theorem bigvee_list_nil : (⋁ x ∈ [], (f x)) =tla= (⊥) := rfl

@[tlasimp]
theorem bigvee_list_cons (b : β) : (⋁ x ∈ (b :: l), (f x)) =tla= ((f b) ∨ ⋁ x ∈ l, (f x)) := rfl

theorem bigvee_exists_list : (⋁ x ∈ l, (f x)) =tla= (∃ x, (⌞ x ∈ l ⌟ ∧ (f x))) := by
  induction l with
  | nil => funext e ; tla_unfold_simp
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e ; tla_unfold_simp

theorem bigvee_exists_fintype_list : (⋁ x ∈ l, (f x)) =tla= (∃ x : Fin l.length, (f l[x])) := by
  rw [bigvee_exists_list]
  funext e ; tla_unfold_simp ; apply List.mem_exists_iff_fin_index

theorem bigvee_and_distrib (p : pred α) : (p ∧ ⋁ x ∈ l, (f x)) =tla= (⋁ x ∈ l, p ∧ (f x)) := by
  repeat rw [bigvee_exists_list]
  funext e ; tla_unfold_simp ; aesop

end bigvee

theorem bigwedge_bigvee_match : ((⋀ x ∈ l, (f x)) ∧ (⋁ x ∈ l, (g x))) |-tla- (⋁ x ∈ l, (f x) ∧ (g x)) := by
  rw [bigwedge_forall_list, bigvee_exists_list, bigvee_exists_list] ; tla_unfold_simp ; aesop

end bigop

end TLA
