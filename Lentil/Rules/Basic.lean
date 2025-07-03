import Lentil.Basic
import Lentil.Tactics.Basic
import Lentil.Gadgets.TheoremLifting

/-! Basic theorems about TLA. -/

open Classical LentilLib

-- lift a bunch of proplemmas first

-- `And`
#tla_lift and_self_iff and_not_self_iff not_and_self_iff and_comm and_assoc
#tla_lift And.left => TLA.and_left
#tla_lift And.right => TLA.and_right
#tla_lift And.imp_left => TLA.and_imp_left
#tla_lift And.imp_right => TLA.and_imp_right
#tla_lift And.imp => TLA.and_imp_both
#tla_lift not_and_of_not_left not_and_of_not_right and_left_comm and_right_comm
  and_rotate and_and_and_comm and_and_left and_and_right

-- `Or`
#tla_lift or_self_iff or_left_comm or_right_comm or_or_or_comm or_or_distrib_left
  or_or_distrib_right or_rotate or_comm or_assoc
#tla_lift Or.inl => TLA.or_inl
#tla_lift Or.inr => TLA.or_inr

-- distributive laws
#tla_lift and_or_left or_and_right or_and_left and_or_right

-- `Not`
#tla_lift not_and' not_or imp_false not_true
#tla_lift not_false_iff => TLA.not_false

-- `∀`, `∃`
#tla_lift not_exists forall_and exists_or exists_and_left exists_and_right
  forall_comm exists_comm
#tla_lift Bool.forall_bool Bool.exists_bool'

-- `Decidable`, but we are in the classical setting
#tla_lift Decidable.not_not Decidable.by_contra Decidable.not_imp_comm
  Decidable.not_imp_self Decidable.or_iff_not_imp_left
  Decidable.imp_iff_or_not Decidable.not_and_not_right
  Decidable.or_iff_not_not_and_not Decidable.and_iff_not_not_or_not
#tla_lift Decidable.not_and_iff_not_or_not => TLA.not_and
#tla_lift Decidable.imp_iff_not_or => TLA.implies_to_or
#tla_lift Decidable.not_imp_iff_and_not => TLA.not_implies_to_and
#tla_lift Decidable.not_imp_not => TLA.contraposition_for_tla_implies

namespace TLA

section playground

variable {σ : Type u}

theorem dual_lemma (p q : pred σ) : ¬ p =tla= ¬ q → (p) =tla= (q) := by
  unfold tla_not ; intro h ; funext e ; have := congrFun h e ; aesop

theorem pred_eq_iff_iff (p q : pred σ) : (p) =tla= (q) ↔ (p) |-tla- (q) ∧ (q) |-tla- (p) := by
  tla_unfold_simp ; constructor
  · aesop
  · intro h ; funext e ; aesop

section structural

theorem impl_intro (p q : pred σ) : |-tla- (p → q) = (p) |-tla- (q) := rfl

theorem impl_decouple (p q : pred σ) : |-tla- (p → q) → |-tla- (p) → |-tla- (q) := by
  tla_unfold_simp ; aesop

theorem and_pred_implies_split (Γ p q : pred σ) : (Γ) |-tla- (p ∧ q) = ((Γ) |-tla- (p) ∧ (Γ) |-tla- (q)) := by
  tla_unfold_simp ; aesop

theorem and_valid_split (p q : pred σ) : |-tla- (p ∧ q) = (|-tla- (p) ∧ |-tla- (q)) := by
  tla_unfold_simp ; aesop

theorem impl_intro_add_r (p q r : pred σ) : (r) |-tla- (p → q) = (r ∧ p) |-tla- (q) := by
  tla_unfold_simp

theorem impl_drop_hyp (p q : pred σ) : |-tla- (q) → (p) |-tla- (q) := by
  tla_unfold_simp ; aesop

theorem impl_drop_hyp_one_r (p q r : pred σ) : (p) |-tla- (q) → (p ∧ r) |-tla- (q) := by
  tla_unfold_simp ; aesop

end structural

section one

variable (p : pred σ)

theorem always_intro : (|-tla- (p)) = (|-tla- (□ p)) := by
  tla_unfold_simp ; constructor
  · aesop
  · intro h ; exact (fun e => h e 0)

theorem later_always_comm : (◯ □ p) =tla= (□ ◯ p) := by
  funext e ; tla_unfold_simp
  constructor <;> intro h k <;> rw [Nat.add_comm] <;> apply h

theorem always_unroll : □ p =tla= (p ∧ ◯ □ p) := by
  rw [later_always_comm]
  funext e ; tla_unfold_simp
  constructor
  · intro h ; apply And.intro (h 0) (by aesop)
  · intro ⟨h0, hs⟩ k ; cases k with
    | zero => exact h0
    | succ k => apply hs

theorem always_induction : □ p =tla= (p ∧ □ (p → ◯ p)) := by
  funext e ; tla_unfold_simp
  constructor
  · intro h ; apply And.intro (h 0) (by aesop)
  · intro ⟨h0, hs⟩ k ; induction k <;> aesop

theorem always_weaken : □ p |-tla- (p) := by
  tla_unfold_simp ; intro e h ; apply h 0

theorem always_weaken_to_eventually : □ p |-tla- ◇ p := by
  tla_unfold_simp ; intro e h ; exists 0 ; apply h

theorem later_weaken_to_eventually : ◯ p |-tla- ◇ p := by
  tla_unfold_simp ; intro e h ; exists 1

theorem now_weaken_to_eventually : (p) |-tla- ◇ p := by
  tla_unfold_simp ; intro e h ; exists 0

theorem not_always : (¬ □ p) =tla= (◇ ¬ p) := by
  funext e ; tla_unfold_simp

@[tladual]
theorem not_eventually : (¬ ◇ p) =tla= □ ¬ p := by
  funext e ; tla_unfold_simp

theorem eventually_to_always : ◇ p =tla= ¬ □ ¬ p := by
  funext e ; tla_unfold_simp

@[tladual]
theorem always_to_eventually : □ p =tla= ¬ ◇ ¬ p := by
  funext e ; tla_unfold_simp

theorem always_idem : (□ □ p) =tla= □ p := by
  funext e ; tla_unfold_simp
  constructor <;> intro h
  · intro k ; apply h _ 0
  · intros ; apply h

@[tladual]
theorem eventually_idem : (◇ ◇ p) =tla= ◇ p := by
  apply dual_lemma ; simp [not_eventually, always_idem]

theorem always_eventually_always : (□ ◇ □ p) =tla= ◇ □ p := by
  funext e ; ext ; constructor
  on_goal 1=> apply always_weaken
  tla_unfold_simp ; intro kk h k ; exists kk ; intros k2
  have hq : k + kk + k2 = kk + (k + k2) := by omega
  rw [hq] ; apply h

@[tladual]
theorem eventually_always_eventually : (◇ □ ◇ p) =tla= □ ◇ p := by
  apply dual_lemma ; simp [not_eventually, not_always, always_eventually_always]

theorem always_eventually_idem : (□ ◇ □ ◇ p) =tla= □ ◇ p := by
  simp [eventually_always_eventually, always_idem]

@[tladual]
theorem eventually_always_idem : (◇ □ ◇ □ p) =tla= ◇ □ p := by
  simp [always_eventually_always, eventually_idem]

end one

attribute [tlasimp] not_not not_always not_eventually always_idem eventually_idem
  always_eventually_always eventually_always_eventually
  always_eventually_idem eventually_always_idem

section two

variable (p q : pred σ)

theorem contraposition_for_pred_implies : (p) |-tla- (q) = ((¬ q) |-tla- ¬ p) := by
  repeat rw [← impl_intro, ← contraposition_for_tla_implies]

theorem proof_by_contra : (p) |-tla- (q) = (¬ q ∧ p) |-tla- (⊥) := by
  rw [contraposition_for_pred_implies] ; tla_unfold_simp

theorem modus_ponens : (p ∧ (p → q)) |-tla- (q) := by
  tla_unfold_simp ; aesop

theorem modus_ponens_with_premise : (p ∧ (p → q)) |-tla- (p ∧ q) := by
  tla_unfold_simp ; aesop

-- the following: about modal operators

theorem always_and_eventually : (◇ p ∧ □ q) |-tla- (◇ (p ∧ q)) := by
  tla_unfold_simp ; aesop

theorem always_and_eventually' : (◇ p ∧ □ q) |-tla- (◇ (p ∧ □ q)) := by
  tla_unfold_simp ; aesop

theorem later_monotone : (p) |-tla- (q) → ◯ p |-tla- ◯ q := by
  tla_unfold_simp ; aesop

theorem always_monotone : (p) |-tla- (q) → □ p |-tla- □ q := by
  tla_unfold_simp ; aesop

theorem eventually_monotone : (p) |-tla- (q) → ◇ p |-tla- ◇ q := by
  tla_unfold_simp ; aesop

theorem always_eventually_monotone : (p) |-tla- (q) → (□ ◇ p) |-tla- (□ ◇ q) := by
  intro h ; apply always_monotone ; apply eventually_monotone ; assumption

theorem eventually_always_monotone : (p) |-tla- (q) → (◇ □ p) |-tla- (◇ □ q) := by
  intro h ; apply eventually_monotone ; apply always_monotone ; assumption

theorem until_induction : (p ∧ □ (p ∧ ¬ q → ◯ p)) |-tla- ((□ (p ∧ ¬ q)) ∨ (p 𝑈 (p ∧ q))) := by
  tla_unfold_simp ; intro e hp h
  by_cases h' : (∃ n, q <| e.drop n)
  · rcases h' with ⟨n', h'⟩
    have ⟨n', _, hq, hmin⟩ := Nat.find_min (p := fun n_ => q (exec.drop n_ e)) _ h'
    right ; exists n'
    suffices hthis : q (exec.drop n' e) ∧ ∀ (j : Nat), j ≤ n' → p (exec.drop j e) by
      rcases hthis with ⟨h1, h2⟩
      apply And.intro (And.intro (by apply h2 n' (by simp)) h1) (fun j hlt => h2 _ (by omega))
    apply And.intro hq ; intro j hlt
    induction j with
    | zero => exact hp
    | succ j ih => apply h ; apply ih ; omega ; apply hmin ; omega
  · simp at h'
    left ; intro j ; apply And.intro _ (h' _)
    induction j <;> solve_by_elim

end two

section two_with_quantifiers

variable {α : Sort v} (p : α → pred σ)

theorem later_forall : (◯ ∀ x, (p x)) =tla= (∀ x, ◯ (p x)) := by
  funext e ; tla_unfold_simp

theorem later_exists : (◯ ∃ x, (p x)) =tla= (∃ x, ◯ (p x)) := by
  funext e ; tla_unfold_simp

theorem always_forall : (□ ∀ x, (p x)) =tla= (∀ x, □ (p x)) := by
  funext e ; tla_unfold_simp ; aesop

theorem eventually_exists : (◇ ∃ x, (p x)) =tla= (∃ x, ◇ (p x)) := by
  funext e ; tla_unfold_simp ; aesop

/-- uni-direction, moving `∃` into `□` -/
theorem exists_into_always : (∃ x, □ (p x)) |-tla- □ (∃ x, (p x)) := by
  tla_unfold_simp ; aesop

/-- uni-direction, moving `◇` into `∀` -/
@[tladual]
theorem eventually_into_forall : (◇ ∀ x, (p x)) |-tla- (∀ x, ◇ (p x)) := by
  tla_unfold_simp ; aesop

end two_with_quantifiers

section two'

variable (p q : pred σ)

/- NOTE: in principle we can derive the following via metaprogramming,
   but these proofs are so short, so why bother ... -/
theorem later_and : (◯ (p ∧ q)) =tla= (◯ p ∧ ◯ q) := by
  funext e ; tla_unfold_simp

theorem later_or : (◯ (p ∨ q)) =tla= (◯ p ∨ ◯ q) := by
  funext e ; tla_unfold_simp

theorem always_and : (□ (p ∧ q)) =tla= (□ p ∧ □ q) := by
  funext e ; tla_unfold_simp ; aesop

@[tladual]
theorem eventually_or : (◇ (p ∨ q)) =tla= (◇ p ∨ ◇ q) := by
  funext e ; tla_unfold_simp ; aesop

/-- uni-direction, merging the `∨` outside `◇` in -/
theorem always_or_merge : (□ p ∨ □ q) |-tla- □ (p ∨ q) := by
  tla_unfold_simp ; aesop

/-- uni-direction, splitting the `∧` inside `◇` -/
@[tladual]
theorem eventually_and_split : (◇ (p ∧ q)) |-tla- (◇ p ∧ ◇ q) := by
  tla_unfold_simp ; aesop

-- NOTE: this __DOES NOT__ apply if we change `∧` into `∀`, unless, e.g. `α` is finite!
theorem eventually_always_and_distrib : (◇ □ (p ∧ q)) =tla= (◇ □ p ∧ ◇ □ q) := by
  rw [pred_eq_iff_iff] ; constructor
  on_goal 1=> rw [always_and] ; apply eventually_and_split
  tla_unfold_simp ; intro e n1 h1 n2 h2 ; exists (n1 + n2)
  intro k
  specialize h1 (n2 + k) ; specialize h2 (n1 + k)
  have hq1 : n1 + (n2 + k) = n1 + n2 + k := by omega
  have hq2 : n2 + (n1 + k) = n1 + n2 + k := by omega
  rw [hq1] at h1 ; rw [hq2] at h2 ; aesop

@[tladual]
theorem always_eventually_or_distrib : (□ ◇ (p ∨ q)) =tla= (□ ◇ p ∨ □ ◇ q) := by
  apply dual_lemma ; simp [tlasimp, not_or, eventually_always_and_distrib]

end two'

end playground

end TLA
