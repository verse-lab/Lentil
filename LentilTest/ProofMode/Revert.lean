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

namespace Lentil.ProofMode.Test.Revert

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

/-! ## Temporal revert -/

-- Revert a single temporal hypothesis: `hp : p` goes from the temporal
-- context to a `p → ..` antecedent of the goal pred.
example : (p ∧ q) |-tl- (q) → (p ∧ q) |-tl- (q) := by
  intro h
  tstart hp hq
  trevert hp
  guard_target =ₛ Entails [⟨"hq", q⟩] [tlfml| p → q]
  tintro hp
  tassumption

-- Reverting then re-introducing should round-trip back to the same shape.
example : (p ∧ q) |-tl- (q) → (p ∧ q) |-tl- (q) := by
  intro h
  tstart hp hq
  trevert hp
  guard_target =ₛ Entails [⟨"hq", q⟩] [tlfml| p → q]
  tintro hp
  guard_target =ₛ Entails [⟨"hq", q⟩, ⟨"hp", p⟩] q
  tassumption

-- Revert multiple temporal hypotheses; the leftmost name ends up as the
-- outermost antecedent of the resulting `→`-chain.
example : (p ∧ q) |-tl- (q) → (p ∧ q) |-tl- (q) := by
  intro h
  tstart hp hq
  trevert hp hq
  guard_target =ₛ Entails [] [tlfml| p → q → q]
  tintro hp hq
  tassumption

-- Reverting a temporal hyp from the *middle* of the list filters it cleanly
-- without disturbing the order of the rest.
example : (p ∧ q ∧ r) |-tl- (r) → (p ∧ q ∧ r) |-tl- (r) := by
  intro h
  tstart hp hq hr
  trevert hq
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hr", r⟩] [tlfml| q → r]
  tintro hq
  tassumption

/-! ## Revert all temporal hypotheses -/

-- Revert every temporal hypothesis at once. The temporal context becomes empty
-- and the hypotheses are rebuilt as a left-to-right implication chain.
example : (p ∧ q) |-tl- (p) := by
  tstart hp hq
  trevert_all
  guard_target =ₛ Entails [] [tlfml| p → q → p]
  tintro hp hq
  tassumption

-- On an empty temporal context, `trevert_all` is a no-op on the goal shape.
example : (q) |-tl- (⊤) := by
  tstart hq
  tclear hq
  trevert_all
  guard_target =ₛ @Entails σ [] (@Lentil.tl_true σ)
  tprove_pure
  trivial

/-! ## ∀-revert (Lean-local non-Prop var) -/

-- Revert a `∀`-introduced binder.
example (P : Nat → pred σ) :
    (⊤) |-tl- (∀ n : Nat, (P n)) → (⊤) |-tl- (∀ n : Nat, (P n)) := by
  intro h
  tstart
  tintro n
  trevert n
  guard_target =ₛ Entails [] [tlfml| ∀ n : Nat, (P n)]
  exact h

-- Round-trip: intro then revert should be a no-op (up to displayed shape).
example (P : Nat → pred σ) :
    (⊤) |-tl- (∀ n : Nat, (P n)) → (⊤) |-tl- (∀ n : Nat, (P n)) := by
  intro h
  tstart
  tintro n
  trevert n
  exact h

/-! ## Pure-revert (Lean-local Prop hypothesis) -/

-- Revert a pure-fact assumption.
example (Q : Prop) :
    (⊤) |-tl- (⌞ Q ⌟ → (p)) → (⊤) |-tl- (⌞ Q ⌟ → (p)) := by
  intro h
  tstart
  tintro hQ
  trevert hQ
  guard_target =ₛ Entails [] [tlfml| ⌞ Q ⌟ → p]
  exact h

/-! ## Mixed sequence -/

-- A `trevert hp n hQ` undoes a matching `tintro hp n hQ` in shape:
-- internally we revert right-to-left so that the user-written order matches
-- the order of antecedents in the resulting goal.
example (P : Nat → pred σ) (Q : Prop) :
    (⊤) |-tl- (∀ n : Nat, (p → ⌞ Q ⌟ → (P n))) →
    (⊤) |-tl- (p → (∀ n : Nat, (⌞ Q ⌟ → (P n)))) := by
  intro h
  tstart
  tintro hp n hQ
  trevert n hp hQ
  exact h

end Lentil.ProofMode.Test.Revert
