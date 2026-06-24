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

namespace TLA.ProofMode.Test.Intro

open TLA TLA.ProofMode

variable {σ : Type u} (p q : pred σ)

-- Intro a ∀ binder.
set_option linter.unusedVariables false in
example : (p) |-tla- (∀ n : Nat, (p)) := by
  tstart hp
  tintro n
  tcheck_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Universal binders may range over proof values.
example (Q : Prop) (P : Q → pred σ) :
    (⊤) |-tla- (∀ hQ : Q, (P hQ)) →
    (⊤) |-tla- (∀ hQ : Q, (P hQ)) := by
  intro h
  tstart
  tintro hQ
  tcheck_goal Entails [] (P hQ)
  intro e _
  exact h e True.intro hQ

-- Intro a pure-predicate antecedent (`⌞q⌟ → …`).
example (Q : Prop) : (p) |-tla- (⌞ Q ⌟ → (p)) := by
  tstart hp
  tintro hQ
  tcheck_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- The introduced pure fact lands as a Lean hypothesis usable in subsequent
-- reasoning.
example (Q : Prop) (h : Q → (p) |-tla- (q)) : (p) |-tla- (⌞ Q ⌟ → (q)) := by
  tstart hp
  tintro hQ
  tcheck_goal Entails [⟨"hp", p⟩] q
  exact h hQ

-- Mixed sequence: ∀, then ⌞..⌟→, then ∀ again. Starting from `⊤` on the
-- premise side gives an empty hypothesis list after `tstart`.
example (P : Nat → Nat → pred σ) :
    (⊤) |-tla- (∀ x : Nat, ⌞ x = x ⌟ → ∀ y : Nat, P x y) →
    (⊤) |-tla- (∀ x : Nat, ⌞ x = x ⌟ → ∀ y : Nat, P x y) := by
  intro h
  tstart
  tintro x hxx y
  tcheck_goal Entails [] (P x y)
  intro e _
  exact h e True.intro x hxx y

-- Multiple ∀ introductions in one call.
example (P : Nat → Nat → pred σ) :
    (⊤) |-tla- (∀ x : Nat, (∀ y : Nat, (P x y))) →
    (⊤) |-tla- (∀ x : Nat, (∀ y : Nat, (P x y))) := by
  intro h
  tstart
  tintro x y
  tcheck_goal Entails [] (P x y)
  intro e _
  exact h e True.intro x y

-- Error: goal is not an `Entails` (we never called `tstart`).
/--
error: tintro: goal is not an Entails sequent, but (p) |-tla- (∀ n, p)
-/
#guard_msgs in
example : (p) |-tla- (∀ n : Nat, (p)) := by
  tintro n

-- Error: goal predicate head is neither ∀ nor `⌞..⌟ →`.
/--
error: tintro: goal predicate is not a ∀ or a ⌞..⌟ →; got p
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tstart hp
  tintro x

-- Intro a temporal implication antecedent into the temporal context.
example : (p) |-tla- (p → q) → (p) |-tla- (p → q) := by
  intro h
  tstart hp
  tintro hp'
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hp'", p⟩] q
  intro e ⟨_, hp'⟩
  exact h e hp' hp'

-- Multiple temporal intros stack the new hypotheses at the end of the list,
-- in the order they were introduced.
example : (⊤) |-tla- (p → q → p) := by
  tstart
  tintro hp hq
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
  intro _ ⟨hp, _⟩ ; exact hp

-- Mixed: temporal intro followed by ∀-intro and pure-intro.
example (P : Nat → pred σ) :
    (⊤) |-tla- (p → (∀ n : Nat, (⌞ n = n ⌟ → (P n)))) →
    (⊤) |-tla- (p → (∀ n : Nat, (⌞ n = n ⌟ → (P n)))) := by
  intro h
  tstart
  tintro hp n heq
  tcheck_goal Entails [⟨"hp", p⟩] (P n)
  intro e hp
  exact h e True.intro hp n heq

end TLA.ProofMode.Test.Intro
