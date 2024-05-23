import Lentil.Basic

/-
  A nice thing is that in Lean, pred ext can be used by default,
  so there is no need to use `==` to represent pred-level eq.
-/

-- challenge: to what extent can you automate the following proofs?

/-
  different levels of unfolding
  0: basic connectives
  1: modalities
-/
macro "tla_unfold_0" : tactic =>
  `(tactic|
      (simp [tla_and, tla_or, tla_not, tla_implies, tla_forall, tla_exist] at *))

macro "tla_unfold_1" : tactic =>
  `(tactic|
      (simp [always, eventually, next] at *))

-- HMM this should be different from repeating calling unfold_0, unfold_1, ...?
macro "tla_unfold" : tactic =>
  `(tactic|
      (simp [tla_and, tla_or, tla_not, tla_implies, tla_forall, tla_exist,
        always, eventually, later,
        leads_to,
        valid, pred_implies, satisfies,
        drop_drop] at *))

section test_simple

variable {α : Type}
variable (p q r : predicate α)

local add_aesop_rules norm tactic (by tla_unfold)
-- local add_aesop_rules unsafe 20% tactic (by push_neg)
local add_aesop_rules safe [tactic (by funext), apply Iff.intro]

lemma eventually_to_always :
  ◇ p = ¬ □ ¬ p := by aesop

lemma always_to_eventually :
  □ p = ¬ ◇ ¬ p := by aesop

-- this seems not very easy to automate
lemma always_idem :
  □ □ p = □ p := by
  funext e ; tla_unfold
  apply Iff.intro <;> intro h
  · intro k ; apply h _ 0
  · intros ; apply h

lemma eventually_idem :
  ◇ ◇ p = ◇ p := by
  repeat rw [eventually_to_always]
  rewrite (config := {occs := .neg [0,1,2]}) [<- always_idem]
  aesop -- TODO why worked?

-- lemma always_intro :
--   (⊢ p) ↔ ⊢ □ p := by sorry
  -- aesop
  --   (add norm tactic (by tla_unfold), safe apply Iff.intro)

lemma always_and :
  □ (p ∧ q) = □ p ∧ □ q := by aesop

lemma eventually_or :
  ◇ (p ∨ q) = ◇ p ∨ ◇ q := by
  repeat rw [eventually_to_always]
  sorry

lemma later_and :
  ◯ (p ∧ q) = ◯ p ∧ ◯ q := by aesop

lemma later_or :
  ◯ (p ∨ q) = ◯ p ∨ ◯ q := by aesop

end test_simple

-- direct translation without leanssr: tedious!

example {α} {Γ p q r : predicate α} :
  Γ ⊢ p ↝ q → Γ ⊢ q ↝ r → Γ ⊢ p ↝ r :=
  by
    intro h1 h2
    tla_unfold
    intro σ h k hh
    specialize h1 _ h k hh
    cases h1 with
    | intro k1 h1 =>
      specialize h2 _ h _ h1
      cases h2 with
      | intro k2 h2 =>
        exists (k1 + k2)
        rw [<- add_assoc]
        assumption

lemma leads_to_trans {α} {Γ p q r : predicate α} :
  Γ ⊢ p ↝ q → Γ ⊢ q ↝ r → Γ ⊢ p ↝ r :=
  by
    intros h1 h2
    tla_unfold ; intros
    sorry
    -- aesop
    --   (add norm tactic (by tla_unfold), forward )
