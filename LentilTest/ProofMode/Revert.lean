import Lentil

/- Tests for the `tla_revert` tactic.

   `tla_revert h₁ … hₙ` is the inverse of `tla_intro`. For each name (processed
   right-to-left, so the left-most ends up outermost in the rebuilt goal):
     * If the name is a Lean-local non-Prop variable → `Entails_revert_forall`
       (= `forall_elim.mpr`), preceded by Lean's `revert`.
     * If the name is a Lean-local Prop hypothesis  → `Entails_revert_pure`
       (= `pure_fact_intro.mpr`), preceded by Lean's `revert`.
     * Otherwise (the name lives in the temporal context) → `Entails_revert`,
       which filters the named hypothesis out and re-introduces it as a `→`
       antecedent of the goal pred.
-/

namespace TLA.ProofMode.Test.Revert

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

/-! ## Temporal revert -/

-- Revert a single temporal hypothesis: `hp : p` goes from the temporal
-- context to a `p → ..` antecedent of the goal pred.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_revert hp
  tla_check_goal_form
  show Entails [⟨"hq", q⟩] [tlafml| p → q]
  intro e hq _ ; exact hq

-- Reverting then re-introducing should round-trip back to the same shape.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_revert hp
  tla_check_goal_form
  tla_intro hp
  show Entails [⟨"hq", q⟩, ⟨"hp", p⟩] q
  intro e ⟨hq, _⟩ ; exact hq

-- Revert multiple temporal hypotheses; the leftmost name ends up as the
-- outermost antecedent of the resulting `→`-chain.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_revert hp hq
  tla_check_goal_form
  show Entails [] [tlafml| p → q → q]
  intro e _ _ hq ; exact hq

-- Reverting a temporal hyp from the *middle* of the list filters it cleanly
-- without disturbing the order of the rest.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tla_start hp hq hr
  tla_revert hq
  tla_check_goal_form
  show Entails [⟨"hp", p⟩, ⟨"hr", r⟩] [tlafml| q → r]
  intro e ⟨_, hr⟩ _ ; exact hr

/-! ## ∀-revert (Lean-local non-Prop var) -/

-- Revert a `∀`-introduced binder.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) → (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tla_start
  tla_intro n
  tla_revert n
  show Entails [] (TLA.tla_forall P)
  exact h

-- Round-trip: intro then revert should be a no-op (up to displayed shape).
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) → (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tla_start
  tla_intro n
  tla_revert n
  exact h

/-! ## Pure-revert (Lean-local Prop hypothesis) -/

-- Revert a pure-fact assumption.
example (Q : Prop) :
    (⊤) |-tla- (⌞ Q ⌟ → (p)) → (⊤) |-tla- (⌞ Q ⌟ → (p)) := by
  intro h
  tla_start
  tla_intro hQ
  tla_revert hQ
  show Entails [] [tlafml| ⌞ Q ⌟ → p]
  exact h

/-! ## Mixed sequence -/

-- A `tla_revert hp n hQ` undoes a matching `tla_intro hp n hQ` in shape:
-- internally we revert right-to-left so that the user-written order matches
-- the order of antecedents in the resulting goal.
example (P : Nat → pred σ) (Q : Prop) :
    (⊤) |-tla- (∀ n : Nat, (p → ⌞ Q ⌟ → (P n))) →
    (⊤) |-tla- (p → (∀ n : Nat, (⌞ Q ⌟ → (P n)))) := by
  intro h
  tla_start
  tla_intro hp n hQ
  tla_revert n hp hQ
  exact h

end TLA.ProofMode.Test.Revert
