import Lentil.Rules.Basic
import Lentil.Tactics.Structural

/-! Theorems about weak-fairness. -/

open Classical

namespace TLA

section wf

variable {σ : Type u}

section wf_def

variable {a : action σ}

theorem wf_as_leads_to : (𝒲ℱ a) =tla= (□ Enabled a ↝ ⟨a⟩) := rfl

theorem wf_alt1 : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ □ ◇ ⟨a⟩) := by
  funext e ; unfold weak_fairness ; rw [implies_to_or] ; simp [tlasimp]
  rw [← eventually_or] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

theorem wf_alt1' : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ ⟨a⟩) := by
  rw [wf_alt1] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

end wf_def

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

end wf

end TLA
