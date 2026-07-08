import Lentil

/- Tests for the `trevert` tactic.

   `trevert h₁ … hₙ` is the inverse of `tintro`. For each name (processed
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
  tstart hp hq
  trevert hp
  guard_target =ₛ Entails [⟨"hq", q⟩] [tlafml| p → q]
  tintro hp
  tassumption

-- Reverting then re-introducing should round-trip back to the same shape.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tstart hp hq
  trevert hp
  guard_target =ₛ Entails [⟨"hq", q⟩] [tlafml| p → q]
  tintro hp
  guard_target =ₛ Entails [⟨"hq", q⟩, ⟨"hp", p⟩] q
  tassumption

-- Revert multiple temporal hypotheses; the leftmost name ends up as the
-- outermost antecedent of the resulting `→`-chain.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tstart hp hq
  trevert hp hq
  guard_target =ₛ Entails [] [tlafml| p → q → q]
  tintro hp hq
  tassumption

-- Reverting a temporal hyp from the *middle* of the list filters it cleanly
-- without disturbing the order of the rest.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tstart hp hq hr
  trevert hq
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hr", r⟩] [tlafml| q → r]
  tintro hq
  tassumption

/-! ## Revert all temporal hypotheses -/

-- Revert every temporal hypothesis at once. The temporal context becomes empty
-- and the hypotheses are rebuilt as a left-to-right implication chain.
example : (p ∧ q) |-tla- (p) := by
  tstart hp hq
  trevert_all
  guard_target =ₛ Entails [] [tlafml| p → q → p]
  tintro hp hq
  tassumption

-- On an empty temporal context, `trevert_all` is a no-op on the goal shape.
example : (q) |-tla- (⊤) := by
  tstart hq
  tclear hq
  trevert_all
  guard_target =ₛ @Entails σ [] (@TLA.tla_true σ)
  tprove_pure
  trivial

/-! ## ∀-revert (Lean-local non-Prop var) -/

-- Revert a `∀`-introduced binder.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) → (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tstart
  tintro n
  trevert n
  guard_target =ₛ Entails [] [tlafml| ∀ n : Nat, (P n)]
  exact h

-- Round-trip: intro then revert should be a no-op (up to displayed shape).
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) → (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tstart
  tintro n
  trevert n
  exact h

/-! ## Pure-revert (Lean-local Prop hypothesis) -/

-- Revert a pure-fact assumption.
example (Q : Prop) :
    (⊤) |-tla- (⌞ Q ⌟ → (p)) → (⊤) |-tla- (⌞ Q ⌟ → (p)) := by
  intro h
  tstart
  tintro hQ
  trevert hQ
  guard_target =ₛ Entails [] [tlafml| ⌞ Q ⌟ → p]
  exact h

/-! ## Mixed sequence -/

-- A `trevert hp n hQ` undoes a matching `tintro hp n hQ` in shape:
-- internally we revert right-to-left so that the user-written order matches
-- the order of antecedents in the resulting goal.
example (P : Nat → pred σ) (Q : Prop) :
    (⊤) |-tla- (∀ n : Nat, (p → ⌞ Q ⌟ → (P n))) →
    (⊤) |-tla- (p → (∀ n : Nat, (⌞ Q ⌟ → (P n)))) := by
  intro h
  tstart
  tintro hp n hQ
  trevert n hp hQ
  exact h

end TLA.ProofMode.Test.Revert
