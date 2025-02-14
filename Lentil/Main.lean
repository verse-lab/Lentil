import Aesop
import Batteries.Tactic.Basic
import Lentil.Basic

open Classical

namespace TLA

section main

syntax "try_unfold_at_all" ident+ : tactic
macro_rules
  | `(tactic| try_unfold_at_all $idt ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt $idts:ident* ) => `(tactic| (try unfold $idt at *) ; try_unfold_at_all $idts* )

macro "tla_unfold" : tactic =>
  `(tactic| (try_unfold_at_all leads_to weak_fairness tla_and tla_or tla_not tla_implies tla_forall tla_exists tla_true tla_false always eventually later state_pred pure_pred valid pred_implies exec.satisfies tla_bigwedge tla_bigvee)
     <;> (try (dsimp only [Foldable.fold] at *)))

attribute [tlasimp_def] leads_to weak_fairness tla_and tla_or tla_not tla_implies tla_forall tla_exists tla_true tla_false
  always eventually later state_pred pure_pred
  valid pred_implies exec.satisfies exec.drop_drop
  tla_bigwedge tla_bigvee Foldable.fold

macro "tla_unfold_simp" : tactic => `(tactic| (simp [tlasimp_def] at *))

variable {σ : Type u}

theorem dual_lemma (p q : pred σ) : ¬ p =tla= ¬ q → (p) =tla= (q) := by
  unfold tla_not ; intro h ; funext e ; have := congrFun h e ; aesop

theorem pred_eq_iff_iff (p q : pred σ) : (p) =tla= (q) ↔ (p) |-tla- (q) ∧ (q) |-tla- (p) := by
  tla_unfold_simp ; constructor
  · aesop
  · intro h ; funext e ; aesop

section structural

theorem impl_intro (p q : pred σ) : |-tla- (p → q) = (p) |-tla- (q) := rfl

theorem impl_intro_add_r (p q r : pred σ) : (r) |-tla- (p → q) = (r ∧ p) |-tla- (q) := by
  tla_unfold_simp

theorem impl_drop_hyp (p q : pred σ) : |-tla- (q) → (p) |-tla- (q) := by
  tla_unfold_simp ; aesop

theorem impl_drop_hyp_one_r (p q r : pred σ) : (p) |-tla- (q) → (p ∧ r) |-tla- (q) := by
  tla_unfold_simp ; aesop

end structural

macro "tla_intros" : tactic =>
  `(tactic| try (rw [TLA.impl_intro]) ; repeat rw [TLA.impl_intro_add_r])

section one

variable (p : pred σ)

theorem not_not : (¬ ¬ p) =tla= (p) := by
  funext e ; tla_unfold_simp

-- the following: about modal operators

theorem always_weaken : □ p |-tla- (p) := by
  tla_unfold_simp ; intro e h ; apply h 0

theorem always_weaken_eventually : □ p |-tla- ◇ p := by
  tla_unfold_simp ; intro e h ; exists 0 ; apply h

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

theorem proof_by_contra (p q : pred σ) : (p) |-tla- (q) = (¬ q ∧ p) |-tla- (⊥) := by
  rw [contraposition_for_pred_implies] ; tla_unfold_simp

-- the following: about modal operators

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
  tla_unfold ; intro e ⟨⟨n1, h1⟩, ⟨n2, h2⟩⟩ ; exists (n1 + n2)
  intro k ; simp [exec.drop_drop] at *
  specialize h1 (n2 + k) ; specialize h2 (n1 + k)
  have hq1 : n1 + (n2 + k) = n1 + n2 + k := by omega
  have hq2 : n2 + (n1 + k) = n1 + n2 + k := by omega
  rw [hq1] at h1 ; rw [hq2] at h2 ; aesop

@[tladual]
theorem always_eventually_or_distrib : (□ ◇ (p ∨ q)) =tla= (□ ◇ p ∨ □ ◇ q) := by
  apply dual_lemma ; simp [tlasimp, not_or, eventually_always_and_distrib]

end two

theorem state_preds_and (p q : σ → Prop) : (⌜ p ⌝ ∧ ⌜ q ⌝) =tla= ⌜ λ s => p s ∧ q s ⌝ := by
  funext e ; tla_unfold_simp

-- sometimes, adding too many things may not work well
-- attribute [tlasimp] always_and eventually_or eventually_always_and_distrib always_eventually_or_distrib

section wf

variable {a : action σ}

theorem wf_as_leads_to : (𝒲ℱ a) =tla= (□ Enabled a ↝ ⟨a⟩) := rfl

theorem wf_alt1 : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ □ ◇ ⟨a⟩) := by
  funext e ; unfold weak_fairness ; rw [implies_to_or] ; simp [tlasimp]
  rw [← eventually_or] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

theorem wf_alt1' : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ ⟨a⟩) := by
  rw [wf_alt1] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

end wf

section leads_to

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

theorem init_invariant {init : σ → Prop} {next : action σ} {inv : σ → Prop} :
  (∀ s, init s → inv s) →
  (∀ s s', next s s' → inv s → inv s') →
  (⌜ init ⌝ ∧ □ ⟨next⟩) |-tla- (□ ⌜ inv ⌝) := by
  tla_unfold_simp ; unfold exec.drop action_pred ; simp
  intro hb hn e hinit hs k
  induction k with
  | zero => aesop
  | succ n ih => rw [Nat.add_comm] ; aesop

/--
A useful rule for proving `↝`. Compared with its original presentation in
the paper "The Temporal Logic of Actions", the following version contains
some changes to make it hopefully more practical.
-/
theorem wf1 (p q init inv : pred σ) (next a : action σ)
  (hpuntilq : |-tla- (p ∧ ⟨next⟩ → ◯ p ∨ ◯ q))
  (haq : |-tla- (p ∧ ⟨next⟩ ∧ ⟨a⟩ → ◯ q))
  (henable : (inv) |-tla- (p → Enabled a ∨ q))
  (hinv : (init ∧ □ ⟨next⟩) |-tla- □ inv) :
  (init ∧ □ ⟨next⟩ ∧ 𝒲ℱ a) |-tla- (p ↝ q) := by
  rw [wf_alt1']
  tla_unfold_simp
  intro e hinit hnext hwf_alt k hp
  specialize hwf_alt k ; rcases hwf_alt with ⟨k1, hwf_alt⟩
  -- know that: either `q` holds between `k` and `k + k1`, or `p` holds at `k1`
  -- use `henable` to know that if it is the latter case, then `q` must hold in the next step
  have htmp : (∃ k' ≤ k1, q <| e.drop (k + k')) ∨ (p <| e.drop (k + k1)) := by
    clear hwf_alt
    induction k1 with
    | zero => right ; assumption
    | succ n ih => {
      rcases ih with ⟨k', hle, ih⟩ | ih
      · left ; exists k' ; constructor ; omega ; apply ih
      · specialize hpuntilq _ ih (hnext _)
        simp [exec.drop_drop] at hpuntilq ; rcases hpuntilq with hq | hq
        · right ; apply hq
        · left ; exists (n + 1) ; aesop
    }
  rcases htmp with ⟨k', _, hq⟩ | hq
  · aesop
  · rcases hwf_alt with hq2 | hq2
    · specialize henable _ _ hq <;> aesop
    · exists (k1 + 1)
      specialize haq (e.drop (k + k1)) ; simp [exec.drop_drop] at haq ; apply haq <;> aesop

/-- A (relatively) original presentation of the `wf1` rule. -/
theorem wf1_original (p q : pred σ) (next a : action σ)
  (hpuntilq : |-tla- (p ∧ ⟨next⟩ → ◯ (p ∨ q)))
  (haq : |-tla- (p ∧ ⟨next⟩ ∧ ⟨a⟩ → ◯ q))
  (henable : |-tla- (p → Enabled a)) :
  |-tla- (□ ⟨next⟩ ∧ 𝒲ℱ a → p ↝ q) := by
  tla_intros
  apply pred_implies_trans
  on_goal 2=> apply wf1 p q tla_true tla_true next a
  all_goals (tla_unfold_simp ; try aesop)

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

end main

end TLA
