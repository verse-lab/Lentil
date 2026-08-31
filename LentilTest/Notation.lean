import Lentil

/- Tests pinning down the LTL formula parser precedences. -/

namespace Lentil.Test.Notation

open Lentil

variable {σ : Type u} (p q r : pred σ) (P : Nat → pred σ) (A : Nat → action σ)

-- Lean applications can be used directly as atomic LTL formulas.
example (n : Nat) : [tlfml| P n] = P n := rfl
example (n : Nat) : [tlfml| P (n + 1)] = P (n + 1) := rfl
example (n : Nat) : [tlfml| P n ∧ q] = [tlfml| (P n) ∧ q] := rfl
example (n : Nat) : [tlfml| Enabled A n ∧ p] = [tlfml| (Enabled (A n)) ∧ p] := rfl
example (n : Nat) : [tlfml| 𝒲ℱ A n ∧ p] = [tlfml| (𝒲ℱ (A n)) ∧ p] := rfl

-- Quantifiers scope over the whole following formula, matching Lean's binders.
example : [tlfml| ∀ n : Nat, P n ∧ q] = [tlfml| ∀ n : Nat, ((P n) ∧ q)] := rfl
example : [tlfml| ∃ n : Nat, P n ∨ q] = [tlfml| ∃ n : Nat, ((P n) ∨ q)] := rfl
example : [tlfml| ∀ n : Nat, ⌞ n = n ⌟ → P n] = [tlfml| ∀ n : Nat, (⌞ n = n ⌟ → (P n))] := rfl

-- Until binds more tightly than conjunction and disjunction, but less tightly than unary temporal operators.
example : [tlfml| p ∧ q 𝑈 r] = [tlfml| p ∧ (q 𝑈 r)] := rfl
example : [tlfml| p 𝑈 q ∧ r] = [tlfml| (p 𝑈 q) ∧ r] := rfl
example : [tlfml| p ∨ q 𝑈 r] = [tlfml| p ∨ (q 𝑈 r)] := rfl
example : [tlfml| p 𝑈 q ∨ r] = [tlfml| (p 𝑈 q) ∨ r] := rfl
example : [tlfml| □ p 𝑈 q] = [tlfml| (□ p) 𝑈 q] := rfl
example : [tlfml| p 𝑈 □ q] = [tlfml| p 𝑈 (□ q)] := rfl

-- The LTL implication follows Lean's arrow precedence and right associativity.
example : [tlfml| p → q → r] = [tlfml| p → (q → r)] := rfl
example : [tlfml| p ∨ q → r] = [tlfml| (p ∨ q) → r] := rfl
example : [tlfml| p → q ∨ r] = [tlfml| p → (q ∨ r)] := rfl

-- The derived implication-like operators still bind more tightly than plain implication.
example : [tlfml| p ⇒ q → r] = [tlfml| (p ⇒ q) → r] := rfl
example : [tlfml| p → q ⇒ r] = [tlfml| p → (q ⇒ r)] := rfl
example : [tlfml| p ↝ q → r] = [tlfml| (p ↝ q) → r] := rfl
example : [tlfml| p → q ↝ r] = [tlfml| p → (q ↝ r)] := rfl

-- Weakening the term fallback should not make a following sequent prefix become a Lean argument.
example : (□ p |-tl- (q)) = ((□ p) |-tl- (q)) := rfl
example : (|-tl- (p → q)) = Lentil.valid [tlfml| p → q] := rfl

end Lentil.Test.Notation
