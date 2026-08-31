import Lentil

/- Tests for the `tintro` tactic.

   `tintro x₁ … xₙ` repeatedly peels things off the goal side of the
   current `Entails` sequent, one item per iteration:
     * `∀`-binder           → `Entails_intro_forall` (= `forall_elim.mp`),
                              then Lean `intro` of the binder name;
     * `⌞..⌟ → ..`          → `Entails_intro_pure` (= `pure_fact_intro.mp`),
                              then Lean `intro` of the Prop hypothesis;
     * `p → q` (non-pure)   → `Entails_intro_temporal`, which appends the
                              new hypothesis to the temporal context with
                              the user-supplied label.
-/

namespace Lentil.ProofMode.Test.Intro

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q : pred σ)

-- Intro a ∀ binder.
set_option linter.unusedVariables false in
example : (p) |-tl- (∀ n : Nat, (p)) := by
  tstart hp
  tintro n
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Universal binders may range over proof values.
example (Q : Prop) (P : Q → pred σ) :
    (⊤) |-tl- (∀ hQ : Q, (P hQ)) →
    (⊤) |-tl- (∀ hQ : Q, (P hQ)) := by
  intro h
  tstart
  tintro hQ
  guard_target =ₛ Entails [] (P hQ)
  thave htop : ⊤ by
    tprove_pure
    trivial
  thave := h htop hQ
  tassumption

-- Intro a pure-predicate antecedent (`⌞q⌟ → …`).
example (Q : Prop) : (p) |-tl- (⌞ Q ⌟ → (p)) := by
  tstart hp
  tintro hQ
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- The introduced pure fact lands as a Lean hypothesis usable in subsequent
-- reasoning.
example (Q : Prop) (h : Q → (p) |-tl- (q)) : (p) |-tl- (⌞ Q ⌟ → (q)) := by
  tstart hp
  tintro hQ
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h hQ

-- Mixed sequence: ∀, then ⌞..⌟→, then ∀ again. Starting from `⊤` on the
-- premise side gives an empty hypothesis list after `tstart`.
example (P : Nat → Nat → pred σ) :
    (⊤) |-tl- (∀ x : Nat, ⌞ x = x ⌟ → ∀ y : Nat, P x y) →
    (⊤) |-tl- (∀ x : Nat, ⌞ x = x ⌟ → ∀ y : Nat, P x y) := by
  intro h
  tstart
  tintro x hxx y
  guard_target =ₛ Entails [] (P x y)
  thave htop : ⊤ by
    tprove_pure
    trivial
  thave := h htop x hxx y
  tassumption

-- Multiple ∀ introductions in one call.
example (P : Nat → Nat → pred σ) :
    (⊤) |-tl- (∀ x : Nat, (∀ y : Nat, (P x y))) →
    (⊤) |-tl- (∀ x : Nat, (∀ y : Nat, (P x y))) := by
  intro h
  tstart
  tintro x y
  guard_target =ₛ Entails [] (P x y)
  thave htop : ⊤ by
    tprove_pure
    trivial
  thave := h htop x y
  tassumption

-- Error: goal is not an `Entails` (we never called `tstart`).
/--
error: tintro: goal is not an Entails sequent, but (p) |-tl- (∀ n, p)
-/
#guard_msgs in
example : (p) |-tl- (∀ n : Nat, (p)) := by
  tintro n

-- Error: goal predicate head is neither ∀ nor `⌞..⌟ →`.
/--
error: tintro: goal predicate is not a ∀ or a ⌞..⌟ →; got p
-/
#guard_msgs in
example : (p) |-tl- (p) := by
  tstart hp
  tintro x

-- Intro a temporal implication antecedent into the temporal context.
example : (p) |-tl- (p → q) → (p) |-tl- (p → q) := by
  intro h
  tstart hp
  tintro hp'
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hp'", p⟩] q
  thave hpq := h hp'
  tapply hpq hp'

-- Multiple temporal intros stack the new hypotheses at the end of the list,
-- in the order they were introduced.
example : (⊤) |-tl- (p → q → p) := by
  tstart
  tintro hp hq
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
  tassumption

-- Mixed: temporal intro followed by ∀-intro and pure-intro.
example (P : Nat → pred σ) :
    (⊤) |-tl- (p → (∀ n : Nat, (⌞ n = n ⌟ → (P n)))) →
    (⊤) |-tl- (p → (∀ n : Nat, (⌞ n = n ⌟ → (P n)))) := by
  intro h
  tstart
  tintro hp n heq
  guard_target =ₛ Entails [⟨"hp", p⟩] (P n)
  thave htop : ⊤ by
    tprove_pure
    trivial
  thave := h htop hp n heq
  tassumption

end Lentil.ProofMode.Test.Intro
