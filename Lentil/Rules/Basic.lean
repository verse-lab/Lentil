import Lentil.Basic
import Lentil.Tactics.Basic

/-! Basic theorems about TLA. -/

open Classical LentilLib

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

theorem not_not : (¬ ¬ p) =tla= (p) := by
  funext e ; tla_unfold_simp

theorem not_as_implies_false : (¬ p) =tla= (p → ⊥) := by
  funext e ; tla_unfold_simp

-- the following: about modal operators

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

theorem and_comm : (p ∧ q) =tla= (q ∧ p) := by
  funext e ; tla_unfold_simp ; aesop

theorem and_left : (p ∧ q) |-tla- (p) := by
  tla_unfold_simp ; try (intros ; assumption)

theorem and_right : (p ∧ q) |-tla- (q) := by
  tla_unfold_simp

theorem and_assoc : ((p ∧ q) ∧ r) =tla= (p ∧ (q ∧ r)) := by
  funext e ; tla_unfold_simp ; aesop

theorem implies_to_or : (p → q) =tla= (¬ p ∨ q) := by
  funext e ; tla_unfold_simp ; apply Decidable.imp_iff_not_or

theorem not_implies_to_and : (¬ (p → q)) =tla= (p ∧ ¬ q) := by
  funext e ; tla_unfold_simp

theorem not_or : (¬ (p ∨ q)) =tla= (¬ p ∧ ¬ q) := by
  funext e ; tla_unfold_simp

theorem not_and : (¬ (p ∧ q)) =tla= (¬ p ∨ ¬ q) := by
  funext e ; tla_unfold_simp ; apply Decidable.imp_iff_not_or

theorem contraposition_for_tla_implies : (p → q) =tla= (¬ q → ¬ p) := by
  funext e ; tla_unfold_simp ; aesop

theorem contraposition_for_pred_implies : (p) |-tla- (q) = ((¬ q) |-tla- ¬ p) := by
  repeat rw [← impl_intro, contraposition_for_tla_implies]

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

end playground

end TLA
