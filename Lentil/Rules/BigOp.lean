module

public import Lentil.Rules.Basic

@[expose] public section

/-! Theorems about big operators (e.g., `⋀`, `⋁`). -/

open Classical LentilLib

namespace Lentil

section bigop

variable {α : Type u} {β : Type v} (f g : β → pred α) (l : List β)

-- FIXME: currently we only have the definition of `fold`, but we do not specify
-- its result, so for each `Foldable` instance, we need to repeat the following proofs!
-- maybe we should revise the definitions of `bigwedge` and `bigvee` (see `Lentil/Basic.lean`)
-- also, can we get rid of the repetition?

section bigwedge

@[tlsimp]
theorem bigwedge_list_nil : (⋀ x ∈ [], (f x)) =tl= (⊤) := rfl

@[tlsimp]
theorem bigwedge_list_cons (b : β) : (⋀ x ∈ (b :: l), (f x)) =tl= ((f b) ∧ ⋀ x ∈ l, (f x)) := rfl

@[tlsimp]
theorem bigwedge_list_append (l1 l2 : List β) : (⋀ x ∈ (l1 ++ l2), (f x)) =tl= ((⋀ x ∈ l1, (f x)) ∧ ⋀ x ∈ l2, (f x)) := by
  simp only [tl_bigwedge, Foldable.fold, List.foldr_append]
  simp only [← List.foldr_map]
  generalize (l1.map f) = l1' ; clear l1
  generalize (List.foldr tl_and [tlfml|⊤] (List.map f l2)) = p ; clear l2
  -- CHECK Why so hard? No existing lemma?
  induction l1' with
  | nil => simp [true_and]
  | cons b l1' ih => simp [and_assoc, ih]

theorem bigwedge_forall_list : (⋀ x ∈ l, (f x)) =tl= (∀ x, (⌞ x ∈ l ⌟ → (f x))) := by
  induction l with
  | nil => funext e i ; apply propext ; tunfold_simp
  | cons b l ih =>
    simp [tlsimp, ih]
    funext e i ; tunfold_simp

theorem bigwedge_forall_fintype_list : (⋀ x ∈ l, (f x)) =tl= (∀ x : Fin l.length, (f l[x])) := by
  rw [bigwedge_forall_list]
  funext e i ; tunfold_simp ; apply List.mem_forall_iff_fin_index

omit f in
theorem bigwedge_forall_swap {γ : Type w} (f : β → γ → pred α) : (∀ c : γ, (⋀ x ∈ l, (f x c))) =tl= (⋀ x ∈ l, ∀ c : γ, ((f x c))) := by
  simp only [bigwedge_forall_fintype_list] ; apply Lentil.forall_comm

theorem bigwedge_inner_and_split : (⋀ x ∈ l, (f x) ∧ (g x)) =tl= ((⋀ x ∈ l, (f x)) ∧ (⋀ x ∈ l, (g x))) := by
  (repeat rw [bigwedge_forall_list]) ; funext e i ; tunfold_simp ; aesop

theorem always_bigwedge : (□ ⋀ x ∈ l, (f x)) =tl= (⋀ x ∈ l, □ (f x)) := by
  (repeat rw [bigwedge_forall_list]) ; funext e i ; tunfold_simp ; aesop

theorem later_bigwedge : (◯ ⋀ x ∈ l, (f x)) =tl= (⋀ x ∈ l, ◯ (f x)) := by
  (repeat rw [bigwedge_forall_list]) ; funext e i ; tunfold_simp

theorem eventually_always_bigwedge_distrib : (◇ □ ⋀ x ∈ l, (f x)) =tl= (⋀ x ∈ l, ◇ □ (f x)) := by
  induction l with
  | nil => funext e i ; tunfold_simp
  | cons x l ih => simp [tlsimp, eventually_always_and_distrib, ih]

end bigwedge

section bigvee

@[tlsimp]
theorem bigvee_list_nil : (⋁ x ∈ [], (f x)) =tl= (⊥) := rfl

@[tlsimp]
theorem bigvee_list_cons (b : β) : (⋁ x ∈ (b :: l), (f x)) =tl= ((f b) ∨ ⋁ x ∈ l, (f x)) := rfl

theorem bigvee_exists_list : (⋁ x ∈ l, (f x)) =tl= (∃ x, (⌞ x ∈ l ⌟ ∧ (f x))) := by
  induction l with
  | nil => funext e i ; tunfold_simp
  | cons b l ih =>
    simp [tlsimp, ih]
    funext e i ; tunfold_simp

theorem bigvee_exists_fintype_list : (⋁ x ∈ l, (f x)) =tl= (∃ x : Fin l.length, (f l[x])) := by
  rw [bigvee_exists_list]
  funext e i ; tunfold_simp ; rw [List.mem_exists_iff_fin_index] ; rfl

theorem bigvee_and_distrib (p : pred α) : (p ∧ ⋁ x ∈ l, (f x)) =tl= (⋁ x ∈ l, p ∧ (f x)) := by
  repeat rw [bigvee_exists_list]
  funext e i ; tunfold_simp ; aesop

theorem later_bigvee : (◯ ⋁ x ∈ l, (f x)) =tl= (⋁ x ∈ l, ◯ (f x)) := by
  (repeat rw [bigvee_exists_list]) ; funext e i ; tunfold_simp

end bigvee

end bigop

section bigop_rule

variable {α : Type u} {β : Type v}

theorem bigwedge_bigvee_match {f g : β → pred α} (l : List β) :
    ((⋀ x ∈ l, (f x)) ∧ (⋁ x ∈ l, (g x))) |-tl- (⋁ x ∈ l, (f x) ∧ (g x)) := by
  rw [bigwedge_forall_list, bigvee_exists_list, bigvee_exists_list] ; tunfold_simp ; aesop

end bigop_rule

end Lentil
