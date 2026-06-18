import Lentil

/- Tests pinning down the TLA formula parser precedences. -/

namespace TLA.Test.Notation

open TLA

variable {σ : Type u} (p q r : pred σ) (P : Nat → pred σ) (A : Nat → action σ)

-- Lean applications can be used directly as atomic TLA formulas.
example (n : Nat) : [tlafml| P n] = P n := rfl
example (n : Nat) : [tlafml| P (n + 1)] = P (n + 1) := rfl
example (n : Nat) : [tlafml| P n ∧ q] = [tlafml| (P n) ∧ q] := rfl
example (n : Nat) : [tlafml| Enabled A n ∧ p] = [tlafml| (Enabled (A n)) ∧ p] := rfl
example (n : Nat) : [tlafml| 𝒲ℱ A n ∧ p] = [tlafml| (𝒲ℱ (A n)) ∧ p] := rfl

-- Quantifiers scope over the whole following formula, matching Lean's binders.
example : [tlafml| ∀ n : Nat, P n ∧ q] = [tlafml| ∀ n : Nat, ((P n) ∧ q)] := rfl
example : [tlafml| ∃ n : Nat, P n ∨ q] = [tlafml| ∃ n : Nat, ((P n) ∨ q)] := rfl
example : [tlafml| ∀ n : Nat, ⌞ n = n ⌟ → P n] = [tlafml| ∀ n : Nat, (⌞ n = n ⌟ → (P n))] := rfl

-- Until binds more tightly than conjunction and disjunction, but less tightly than unary temporal operators.
example : [tlafml| p ∧ q 𝑈 r] = [tlafml| p ∧ (q 𝑈 r)] := rfl
example : [tlafml| p 𝑈 q ∧ r] = [tlafml| (p 𝑈 q) ∧ r] := rfl
example : [tlafml| p ∨ q 𝑈 r] = [tlafml| p ∨ (q 𝑈 r)] := rfl
example : [tlafml| p 𝑈 q ∨ r] = [tlafml| (p 𝑈 q) ∨ r] := rfl
example : [tlafml| □ p 𝑈 q] = [tlafml| (□ p) 𝑈 q] := rfl
example : [tlafml| p 𝑈 □ q] = [tlafml| p 𝑈 (□ q)] := rfl

-- The TLA implication follows Lean's arrow precedence and right associativity.
example : [tlafml| p → q → r] = [tlafml| p → (q → r)] := rfl
example : [tlafml| p ∨ q → r] = [tlafml| (p ∨ q) → r] := rfl
example : [tlafml| p → q ∨ r] = [tlafml| p → (q ∨ r)] := rfl

-- The derived implication-like operators still bind more tightly than plain implication.
example : [tlafml| p ⇒ q → r] = [tlafml| (p ⇒ q) → r] := rfl
example : [tlafml| p → q ⇒ r] = [tlafml| p → (q ⇒ r)] := rfl
example : [tlafml| p ↝ q → r] = [tlafml| (p ↝ q) → r] := rfl
example : [tlafml| p → q ↝ r] = [tlafml| p → (q ↝ r)] := rfl

-- Weakening the term fallback should not make a following sequent prefix become a Lean argument.
example : (□ p |-tla- (q)) = ((□ p) |-tla- (q)) := rfl
example : (|-tla- (p → q)) = TLA.valid [tlafml| p → q] := rfl

end TLA.Test.Notation
