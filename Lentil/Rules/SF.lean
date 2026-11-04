module

public import Lentil.Rules.WF

@[expose] public section

/-! Theorems about strong-fairness. -/

open Classical

namespace Lentil

section sf

variable {σ : Type u}

section sf_def

variable {a : action σ}

theorem sf_as_leads_to : (𝒮ℱ a) =tl= (□ ◇ Enabled a ↝ ⟨a⟩) := rfl

theorem sf_alt1 : (𝒮ℱ a) =tl= □ ◇ ((□ ¬ Enabled a) ∨ □ ◇ ⟨a⟩) := by
  funext e ; unfold strong_fairness ; rw [implies_to_or] ; simp [tlsimp]
  rw [← eventually_or] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlsimp, always_eventually_always]

theorem sf_alt1' : (𝒮ℱ a) =tl= □ ◇ ((□ ¬ Enabled a) ∨ ⟨a⟩) := by
  rw [sf_alt1] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlsimp]

/-- The usual presentation of strong fairness: if `a` is enabled infinitely often,
then it is taken infinitely often. -/
theorem sf_as_implies : (𝒮ℱ a) =tl= ((□ ◇ Enabled a) → □ ◇ ⟨a⟩) := by
  rw [sf_alt1, implies_to_or] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlsimp, always_eventually_always]

theorem sf_implies_wf : (𝒮ℱ a) |-tl- (𝒲ℱ a) := by
  intro e i hsf k hen
  apply hsf k
  intro n ; exists 0 ; simpa using hen n

end sf_def

/--
The strong-fairness counterpart of `wf1`: compared with `wf1`, `a` only needs
to be enabled again and again (rather than continuously) while `p` holds.
-/
@[tl_derive]
theorem sf1 {p q : pred σ} (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ p ∨ ◯ q) ∧
   (p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q) ∧
   (□ p ⇒ ◇ (Enabled a ∨ q)) ∧
   (□ ⟨next⟩ ∧ 𝒮ℱ a)) |-tl- (p ↝ q) := by
  intro e i ⟨hpuntilq, haq, henable, hnext, hsf⟩ k hp
  apply byContradiction ; intro hnq
  have hnq' : ∀ n, ¬ q e (i + k + n) := fun n hq => hnq ⟨n, hq⟩
  -- without `q`, `p` holds forever
  have hpalways : ∀ n, p e (i + k + n) := by
    intro n
    induction n with
    | zero => simpa using hp
    | succ n ih =>
      rcases hpuntilq (k + n) ⟨by simpa [Nat.add_assoc] using ih, hnext (k + n)⟩ with hp' | hq'
      · simpa [later, Nat.add_assoc] using hp'
      · exact False.elim (hnq' (n + 1) (by simpa [later, Nat.add_assoc] using hq'))
  -- so `a` is enabled infinitely often
  have henabled : ∀ n, ∃ m, Lentil.enabled a (e (i + k + n + m)) := by
    intro n
    rcases henable (k + n) (fun m => by simpa [Nat.add_assoc] using hpalways (n + m)) with ⟨m, hm | hm⟩
    · exact ⟨m, by simpa [tl_enabled, state_pred, Nat.add_assoc] using hm⟩
    · exact False.elim (hnq' (n + m) (by simpa [Nat.add_assoc] using hm))
  -- so `a` is eventually taken, which gives `q`
  rcases hsf k (fun n => by simpa [eventually, tl_enabled, state_pred, Nat.add_assoc] using henabled n)
    with ⟨m, hm⟩
  apply hnq' (m + 1)
  have := haq (k + m) ⟨by simpa [Nat.add_assoc] using hpalways m, hnext (k + m), by simpa [Nat.add_assoc] using hm⟩
  simpa [later, Nat.add_assoc] using this

/-- A (relatively) original presentation of the `sf1` rule. -/
theorem sf1_original {p q : pred σ} (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ (p ∨ q)) ∧
   ((p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q)) ∧
   ((□ p ⇒ ◇ Enabled a))) |-tl- (□ ⟨next⟩ ∧ 𝒮ℱ a → p ↝ q) := by
  tstart hpuntilq haq henable
  trintro ⟨hnext, hfair⟩
  tapply sf1 (next := next) (a := a)
  tsplit_ands
  · rw [later_or] ; tapply hpuntilq
  · tapply haq
  · intro e i ⟨_, _, henable, _⟩ k hp
    rcases henable k hp with ⟨m, hm⟩
    exact ⟨m, Or.inl hm⟩
  · tapply hnext
  · tapply hfair

end sf

end Lentil
