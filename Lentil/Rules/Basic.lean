module

public import Lentil.Basic
public import Lentil.Tactics.Basic
public import Lentil.Gadgets.TheoremLifting

@[expose] public section

/-! Basic theorems about Lentil. -/

open Classical LentilLib

-- lift a bunch of proplemmas first

-- `And`
#tl_lift and_self_iff and_not_self_iff not_and_self_iff and_comm and_assoc
#tl_lift And.intro => Lentil.and_intro
#tl_lift And.left => Lentil.and_left
#tl_lift And.right => Lentil.and_right
#tl_lift And.imp_left => Lentil.and_imp_left
#tl_lift And.imp_right => Lentil.and_imp_right
#tl_lift And.imp => Lentil.and_imp_both
#tl_lift not_and_of_not_left not_and_of_not_right and_left_comm and_right_comm
  and_rotate and_and_and_comm and_and_left and_and_right
  and_imp

-- `Or`
#tl_lift or_self_iff or_left_comm or_right_comm or_or_or_comm or_or_distrib_left
  or_or_distrib_right or_rotate or_comm or_assoc
#tl_lift Or.inl => Lentil.or_inl
#tl_lift Or.inr => Lentil.or_inr
#tl_lift Or.elim => Lentil.or_elim
#tl_lift Or.imp => Lentil.or_imp
#tl_lift Or.imp_left => Lentil.or_imp_left
#tl_lift Or.imp_right => Lentil.or_imp_right

-- distributive laws
#tl_lift and_or_left or_and_right or_and_left and_or_right

-- `Not`
#tl_lift not_and' not_or imp_false not_true
#tl_lift not_and => Lentil.not_and_to_imp
#tl_lift not_false_iff => Lentil.not_false

-- `∀`, `∃`
#tl_lift not_exists forall_and exists_or exists_and_left exists_and_right
  forall_comm exists_comm
#tl_lift Bool.forall_bool Bool.exists_bool'
#tl_lift LentilLib.forall_unit LentilLib.exists_unit

-- `Decidable`, but we are in the classical setting
#tl_lift Decidable.not_not Decidable.by_contra Decidable.not_imp_comm
  Decidable.not_imp_self Decidable.or_iff_not_imp_left
  Decidable.imp_iff_or_not Decidable.not_and_not_right
  Decidable.or_iff_not_not_and_not Decidable.and_iff_not_not_or_not
#tl_lift Decidable.em => Lentil.excluded_middle
#tl_lift Decidable.not_and_iff_not_or_not => Lentil.not_and
#tl_lift Decidable.imp_iff_not_or => Lentil.implies_to_or
#tl_lift Decidable.not_imp_iff_and_not => Lentil.not_implies_to_and
#tl_lift Decidable.not_imp_not => Lentil.contraposition_for_tl_implies

#tl_lift LentilLib.Nat.find_min => Lentil.find_min by {
  intro σ p n e i
  apply LentilLib.Nat.find_min (p := fun n => p n e i)
}

namespace Lentil

section playground

variable {σ : Type u}

theorem dual_lemma (p q : pred σ) : ¬ p =tl= ¬ q → (p) =tl= (q) := by
  unfold tl_not ; intro h ; funext e i ; have := congrFun (congrFun h e) i ; aesop

theorem pred_eq_iff_iff (p q : pred σ) : (p) =tl= (q) ↔ (p) |-tl- (q) ∧ (q) |-tl- (p) := by
  tunfold_simp ; constructor
  · aesop
  · intro h ; funext e i ; aesop

section structural

theorem impl_intro (p q : pred σ) : |-tl- (p → q) = (p) |-tl- (q) := rfl

theorem impl_decouple {p q : pred σ} : |-tl- (p → q) → |-tl- (p) → |-tl- (q) := by
  tunfold_simp ; aesop

theorem and_pred_implies_split (Γ p q : pred σ) : (Γ) |-tl- (p ∧ q) = ((Γ) |-tl- (p) ∧ (Γ) |-tl- (q)) := by
  tunfold_simp ; aesop

theorem valid_eq_true_implies (p : pred σ) : |-tl- (p) = ((⊤) |-tl- (p)) := by
  tunfold_simp

theorem and_valid_split (p q : pred σ) : |-tl- (p ∧ q) = (|-tl- (p) ∧ |-tl- (q)) := by
  tunfold_simp ; aesop

theorem impl_intro_add_r (p q r : pred σ) : (r) |-tl- (p → q) = (r ∧ p) |-tl- (q) := by
  tunfold_simp

theorem impl_drop_hyp (p : pred σ) {q : pred σ} : |-tl- (q) → (p) |-tl- (q) := by
  tunfold_simp ; aesop

theorem impl_drop_hyp_one_r {p q : pred σ} (r : pred σ) : (p) |-tl- (q) → (p ∧ r) |-tl- (q) := by
  tunfold_simp ; aesop

end structural

section one

section one_explicit

variable (p : pred σ)

-- FIXME: These should be automatically generated
theorem and_true (p : pred σ) : (p ∧ ⊤) =tl= (p) := by funext e i ; tunfold_simp'

theorem true_and (p : pred σ) : (⊤ ∧ p) =tl= (p) := by funext e i ; tunfold_simp'

theorem or_false (p : pred σ) : (p ∨ ⊥) =tl= (p) := by funext e i ; tunfold_simp'

theorem false_or (p : pred σ) : (⊥ ∨ p) =tl= (p) := by funext e i ; tunfold_simp'

theorem imp_true (p : pred σ) : (p → ⊤) =tl= (⊤) := by funext e i ; tunfold_simp'

theorem always_true :
  letI lhs : pred σ := [tlfml| □ ⊤]
  ((lhs)) =tl= (⊤) := by funext e i ; tunfold_simp'

theorem eventually_true :
  letI lhs : pred σ := [tlfml| ◇ ⊤]
  ((lhs)) =tl= (⊤) := by funext e i ; tunfold_simp'

theorem later_true :
  letI lhs : pred σ := [tlfml| ◯ ⊤]
  ((lhs)) =tl= (⊤) := by funext e i ; tunfold_simp'

theorem later_false :
  letI lhs : pred σ := [tlfml| ◯ ⊥]
  ((lhs)) =tl= (⊥) := by funext e i ; tunfold_simp'

theorem always_intro : (|-tl- (p)) = (|-tl- (□ p)) := by
  tunfold_simp ; constructor
  · aesop
  · intro h e i ; exact h e i 0

theorem later_not : (◯ ¬ p) =tl= (¬ ◯ p) := by
  funext e i ; tunfold_simp

theorem later_always_comm : (◯ □ p) =tl= (□ ◯ p) := by
  funext e i ; tunfold_simp ; grind

theorem later_eventually_comm : (◯ ◇ p) =tl= (◇ ◯ p) := by
  funext e i ; tunfold_simp ; grind

theorem always_induction : □ p =tl= (p ∧ □ (p → ◯ p)) := by
  funext e i ; tunfold_simp
  constructor
  · intro h ; apply And.intro (by simpa using h 0)
      (by intro k _ ; simpa [Nat.add_assoc] using h (k + 1))
  · intro ⟨h0, hs⟩ k
    induction k with
    | zero => simpa using h0
    | succ k ih => simpa [Nat.add_assoc] using hs k ih

end one_explicit

theorem always_weaken {p : pred σ} : □ p |-tl- (p) := by
  tunfold_simp ; intro e i h ; simpa using h 0

theorem always_weaken_to_eventually {p : pred σ} : □ p |-tl- ◇ p := by
  tunfold_simp ; intro e i h ; exists 0 ; apply h

theorem later_weaken_to_eventually {p : pred σ} : ◯ p |-tl- ◇ p := by
  tunfold_simp ; intro e i h ; exists 1

theorem now_weaken_to_eventually {p : pred σ} : (p) |-tl- ◇ p := by
  tunfold_simp ; intro e i h ; exists 0

section one_modal_rewrites

variable (p : pred σ)

theorem eventually_as_until : (◇ p) =tl= (⊤ 𝑈 p) := by
  funext e i ; tunfold_simp

theorem not_always : (¬ □ p) =tl= (◇ ¬ p) := by
  funext e i ; tunfold_simp

@[tldual]
theorem not_eventually : (¬ ◇ p) =tl= □ ¬ p := by
  funext e i ; tunfold_simp

theorem eventually_to_always : ◇ p =tl= ¬ □ ¬ p := by
  funext e i ; tunfold_simp

@[tldual]
theorem always_to_eventually : □ p =tl= ¬ ◇ ¬ p := by
  funext e i ; tunfold_simp

theorem always_as_until : (□ p) =tl= (¬ (⊤ 𝑈 ¬ p)) := by
  rw [always_to_eventually, eventually_as_until]

theorem always_idem : (□ □ p) =tl= □ p := by
  funext e i ; tunfold_simp
  constructor <;> intro h
  · intro k ; exact h k 0
  · intro k l ; simpa [Nat.add_assoc] using h (k + l)

@[tldual]
theorem eventually_idem : (◇ ◇ p) =tl= ◇ p := by
  apply dual_lemma ; simp [not_eventually, always_idem]

theorem always_eventually_always : (□ ◇ □ p) =tl= ◇ □ p := by
  funext e i ; tunfold_simp
  constructor
  · intro h ; exact h 0
  · intro ⟨kk, h⟩ k
    exists kk
    intro k2
    have hq : i + k + kk + k2 = i + kk + (k + k2) := by omega
    rw [hq] ; apply h

@[tldual]
theorem eventually_always_eventually : (◇ □ ◇ p) =tl= □ ◇ p := by
  apply dual_lemma ; simp [not_eventually, not_always, always_eventually_always]

theorem always_eventually_idem : (□ ◇ □ ◇ p) =tl= □ ◇ p := by
  simp [eventually_always_eventually, always_idem]

@[tldual]
theorem eventually_always_idem : (◇ □ ◇ □ p) =tl= ◇ □ p := by
  simp [always_eventually_always, eventually_idem]

theorem always_unroll : □ p =tl= (p ∧ ◯ □ p) := by
  rw [later_always_comm]
  funext e i ; tunfold_simp
  constructor
  · intro h ; apply And.intro (h 0)
      (by intro k ; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (k + 1))
  · intro ⟨h0, hs⟩ k
    cases k with
    | zero => simpa using h0
    | succ k => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs k

@[tldual]
theorem eventually_unroll : ◇ p =tl= (p ∨ ◇ ◯ p) := by
  apply dual_lemma ; simp [not_eventually, not_or, ← later_not, ← later_always_comm]
  apply always_unroll

end one_modal_rewrites

/-- The finite prefix of `p` of depth `n`.  Depth zero observes `p` now;
depth `n + 1` additionally observes one more shifted copy of `p`. -/
def alwaysPrefix (p : pred σ) : Nat → pred σ
  | 0 => p
  | n + 1 => tl_and p (later (alwaysPrefix p n))

theorem alwaysPrefix_succ (p : pred σ) (n : Nat) :
    alwaysPrefix p (n + 1) = tl_and p (later (alwaysPrefix p n)) := rfl

/-- An `always` assumption can be weakened to any finite prefix. -/
theorem always_weaken_n {p : pred σ} (n : Nat) :
    (□ p) |-tl- (alwaysPrefix p n) := by
  induction n with
  | zero => apply always_weaken
  | succ n ih =>
    rw [alwaysPrefix, always_unroll]
    generalize alwaysPrefix p n = x at *
    generalize always p = y at *
    tunfold_simp
    grind

end one

attribute [tlsimp] not_not not_always not_eventually always_idem eventually_idem
  always_eventually_always eventually_always_eventually
  always_eventually_idem eventually_always_idem

section two

section two_structural

variable (p q : pred σ)

theorem contraposition_for_pred_implies : (p) |-tl- (q) = ((¬ q) |-tl- ¬ p) := by
  repeat rw [← impl_intro, ← contraposition_for_tl_implies]

theorem proof_by_contra : (p) |-tl- (q) = (¬ q ∧ p) |-tl- (⊥) := by
  rw [contraposition_for_pred_implies] ; tunfold_simp

end two_structural

theorem modus_ponens {p q : pred σ} : (p ∧ (p → q)) |-tl- (q) := by
  tunfold_simp ; aesop

theorem modus_ponens_with_premise {p q : pred σ} : (p ∧ (p → q)) |-tl- (p ∧ q) := by
  tunfold_simp ; aesop

-- the following: about modal operators

section two_modal_rewrites

variable (p q : pred σ)

theorem always_pred_implies : ((□ p) |-tl- (q)) = ((□ p) |-tl- (□ q)) := by
  tunfold_simp ; constructor
  · intro h e i hp k
    apply h
    intro l
    simpa [Nat.add_assoc] using hp (k + l)
  · intro h e i hp
    simpa using h e i hp 0

end two_modal_rewrites

theorem always_and_eventually {p q : pred σ} : (◇ p ∧ □ q) |-tl- (◇ (p ∧ q)) := by
  tunfold_simp ; aesop

theorem always_and_eventually' {p q : pred σ} : (◇ p ∧ □ q) |-tl- (◇ (p ∧ □ q)) := by
  tunfold_simp
  intro e i k hp hq
  exists k
  apply And.intro hp
  intro l
  simpa [Nat.add_assoc] using hq (k + l)

theorem later_monotone {p q : pred σ} : (p) |-tl- (q) → ◯ p |-tl- ◯ q := by
  tunfold_simp ; aesop

theorem later_monotone' {p q : pred σ} : |-tl- ((p ⇒ q) → (◯ p → ◯ q)) := by
  tunfold_simp ; aesop

theorem always_monotone {p q : pred σ} : (p) |-tl- (q) → □ p |-tl- □ q := by
  tunfold_simp ; aesop

theorem always_monotone' {p q : pred σ} : |-tl- ((p ⇒ q) → (□ p → □ q)) := by
  tunfold_simp ; aesop

theorem eventually_monotone {p q : pred σ} : (p) |-tl- (q) → ◇ p |-tl- ◇ q := by
  tunfold_simp ; aesop

theorem eventually_monotone' {p q : pred σ} : |-tl- ((p ⇒ q) → (◇ p → ◇ q)) := by
  tunfold_simp ; aesop

theorem always_eventually_monotone {p q : pred σ} : (p) |-tl- (q) → (□ ◇ p) |-tl- (□ ◇ q) := by
  intro h ; apply always_monotone ; apply eventually_monotone ; assumption

theorem eventually_always_monotone {p q : pred σ} : (p) |-tl- (q) → (◇ □ p) |-tl- (◇ □ q) := by
  intro h ; apply eventually_monotone ; apply always_monotone ; assumption

theorem until_induction {p q : pred σ} : (p ∧ □ (p ∧ ¬ q → ◯ p)) |-tl- ((□ (p ∧ ¬ q)) ∨ (p 𝑈 (p ∧ q))) := by
  tunfold_simp ; intro e i hp h
  by_cases h' : ∃ n, q e (i + n)
  · rcases h' with ⟨n', h'⟩
    have ⟨n', _, hq, hmin⟩ := Nat.find_min (p := fun n_ => q e (i + n_)) _ h'
    right ; exists n'
    suffices hthis : q e (i + n') ∧ ∀ (j : Nat), j ≤ n' → p e (i + j) by
      rcases hthis with ⟨h1, h2⟩
      apply And.intro
      · apply And.intro
        · apply h2 ; simp
        · exact h1
      · intro j hlt ; apply h2 ; omega
    apply And.intro hq ; intro j hlt
    induction j with
    | zero => simpa using hp
    | succ j ih =>
      simpa [Nat.add_assoc] using h j (ih (by omega)) (hmin j (by omega))
  · simp at h'
    left ; intro j ; apply And.intro _ (h' _)
    induction j with
    | zero => simpa using hp
    | succ j ih => simpa [Nat.add_assoc] using h j ih (h' j)

theorem eventually_and_eq
    {p q : pred σ} :
    (◇ p ∧ ◇ q) =tl= (◇ (p ∧ ◇ q) ∨ ◇ (q ∧ ◇ p)) := by
  rw [pred_eq_iff_iff] ; constructor
  · tunfold_simp
    intro e i k1 hp k2 hq
    by_cases h : k1 ≤ k2
    · left ; exists k1 ; constructor ; assumption ; exists (k2 - k1) ; grind
    · right ; exists k2 ; constructor ; assumption ; exists (k1 - k2) ; grind
  · tunfold_simp
    rintro e i (⟨k, hp, k', hq⟩ | ⟨k, hq, k', hp⟩)
    · constructor
      · exists k
      · exists (k + k') ; grind
    · constructor
      · exists (k + k') ; grind
      · exists k

end two

section two_with_quantifiers

variable {α : Sort v}

section quantifier_rewrites

variable (p : α → pred σ)

theorem later_forall : (◯ ∀ x, (p x)) =tl= (∀ x, ◯ (p x)) := by
  funext e i ; tunfold_simp

theorem later_exists : (◯ ∃ x, (p x)) =tl= (∃ x, ◯ (p x)) := by
  funext e i ; tunfold_simp

theorem always_forall : (□ ∀ x, (p x)) =tl= (∀ x, □ (p x)) := by
  funext e i ; tunfold_simp ; aesop

theorem eventually_exists : (◇ ∃ x, (p x)) =tl= (∃ x, ◇ (p x)) := by
  funext e i ; tunfold_simp ; aesop

end quantifier_rewrites

/-- uni-direction, moving `∃` into `□` -/
theorem exists_into_always {p : α → pred σ} : (∃ x, □ (p x)) |-tl- □ (∃ x, (p x)) := by
  tunfold_simp ; aesop

/-- uni-direction, moving `◇` into `∀` -/
@[tldual]
theorem eventually_into_forall {p : α → pred σ} : (◇ ∀ x, (p x)) |-tl- (∀ x, ◇ (p x)) := by
  tunfold_simp ; aesop

end two_with_quantifiers

section two'

section binary_rewrites

variable (p q : pred σ)

/- NOTE: in principle we can derive the following via metaprogramming,
   but these proofs are so short, so why bother ... -/
theorem later_and : (◯ (p ∧ q)) =tl= (◯ p ∧ ◯ q) := by
  funext e i ; tunfold_simp

theorem later_or : (◯ (p ∨ q)) =tl= (◯ p ∨ ◯ q) := by
  funext e i ; tunfold_simp

theorem later_implies : (◯ (p → q)) =tl= (◯ p → ◯ q) := by
  funext e i ; tunfold_simp

theorem always_and : (□ (p ∧ q)) =tl= (□ p ∧ □ q) := by
  funext e i ; tunfold_simp ; aesop

@[tldual]
theorem eventually_or : (◇ (p ∨ q)) =tl= (◇ p ∨ ◇ q) := by
  funext e i ; tunfold_simp ; aesop

end binary_rewrites

/-- uni-direction, merging the `∨` outside `◇` in -/
theorem always_or_merge {p q : pred σ} : (□ p ∨ □ q) |-tl- □ (p ∨ q) := by
  tunfold_simp ; aesop

/-- uni-direction, splitting the `∧` inside `◇` -/
@[tldual]
theorem eventually_and_split {p q : pred σ} : (◇ (p ∧ q)) |-tl- (◇ p ∧ ◇ q) := by
  tunfold_simp ; aesop

section binary_distrib_rewrites

variable (p q : pred σ)

-- NOTE: this __DOES NOT__ apply if we change `∧` into `∀`, unless, e.g. `α` is finite!
theorem eventually_always_and_distrib : (◇ □ (p ∧ q)) =tl= (◇ □ p ∧ ◇ □ q) := by
  rw [pred_eq_iff_iff] ; constructor
  on_goal 1=> rw [always_and] ; apply eventually_and_split
  tunfold_simp ; intro e i n1 h1 n2 h2 ; exists (n1 + n2)
  intro k
  specialize h1 (n2 + k) ; specialize h2 (n1 + k)
  have hq1 : i + n1 + (n2 + k) = i + (n1 + n2) + k := by omega
  have hq2 : i + n2 + (n1 + k) = i + (n1 + n2) + k := by omega
  rw [hq1] at h1 ; rw [hq2] at h2 ; aesop

@[tldual]
theorem always_eventually_or_distrib : (□ ◇ (p ∨ q)) =tl= (□ ◇ p ∨ □ ◇ q) := by
  apply dual_lemma ; simp [tlsimp, not_or, eventually_always_and_distrib]

end binary_distrib_rewrites

end two'

end playground

-- FIXME: Better name
section more

theorem forall_elim {α : Type u} {β : Sort v} {p : β → pred α} {Γ : pred α} :
  (∀ x, (Γ) |-tl- ((p x))) = ((Γ) |-tl- (∀ x, (p x))) := by tunfold_simp ; grind

theorem exists_elim {α : Type u} {β : Sort v} {p : β → pred α} {Γ : pred α} (x : β) :
  ((Γ) |-tl- ((p x))) → ((Γ) |-tl- (∃ x, (p x))) := by tunfold_simp ; grind

end more

section pure

theorem valid_pure {p : Prop} : p → @valid α (pure_pred p) := by tunfold_simp ; grind

theorem pred_implies_pure {p : Prop} : p → @pred_implies α q (pure_pred p) := by tunfold_simp ; grind

theorem pure_fact_intro {α : Type u} {Γ p : pred α} {q : Prop} :
  (q → ((Γ) |-tl- (p))) = ((Γ) |-tl- (⌞ q ⌟ → p)) := by tunfold_simp ; grind

theorem pure_implies_to_forall {p : Prop} : (⌞ p ⌟ → q) =tl= (∀ _x : p, q) := by funext e i ; tunfold_simp

theorem pure_and_to_exists {p : Prop} : (⌞ p ⌟ ∧ q) =tl= (∃ _x : p, q) := by funext e i ; tunfold_simp

end pure

end Lentil
