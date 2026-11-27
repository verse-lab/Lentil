import Lentil

/- Tests pinning down the LTL formula parser precedences. -/

-- Importing Lentil leaves these names available in ordinary Lean code.
example (𝒞 : Nat) : 𝒞 = 𝒞 := rfl
example (unfolding forward_instance : Nat) : unfolding = forward_instance →
    forward_instance = unfolding := Eq.symm
example (𝒲ℱ 𝒮ℱ : Nat → Nat) : 𝒲ℱ (𝒮ℱ 0) = 𝒲ℱ (𝒮ℱ 0) := rfl
-- Lean's own quantifiers keep their binder forms.
example : forall a b : Nat, a + b = b + a := Nat.add_comm
example : exists (a b : Nat), a + b = 1 := ⟨0, 1, rfl⟩
example : ∀ n > 0, n ≠ 0 := fun _ h => Nat.ne_of_gt h

open scoped Lentil in
example (p : Lentil.pred Bool) : [tlfml| 𝒞 p] = Lentil.safetyClosure p := rfl

namespace Lentil.Test.Notation

open Lentil

variable {σ : Type u} (p q r : pred σ) (P : Nat → pred σ) (A : Nat → action σ)

-- Lean applications can be used directly as atomic LTL formulas.
example (n : Nat) : [tlfml| P n] = P n := rfl
example (n : Nat) : [tlfml| P (n + 1)] = P (n + 1) := rfl
example (n : Nat) : [tlfml| P n ∧ q] = [tlfml| (P n) ∧ q] := rfl
example (n : Nat) : [tlfml| Enabled A n ∧ p] = [tlfml| (Enabled (A n)) ∧ p] := rfl
example (n : Nat) : [tlfml| 𝒲ℱ A n ∧ p] = [tlfml| (𝒲ℱ (A n)) ∧ p] := rfl
example (n : Nat) : [tlfml| 𝒮ℱ A n ∧ p] = [tlfml| (𝒮ℱ (A n)) ∧ p] := rfl
example (n : Nat) : [tlfml| 𝒮ℱ A n] = Lentil.strong_fairness (A n) := rfl

-- `Enabled` is also available as an ordinary Lean identifier.
example (Enabled : Nat → Nat) : Enabled 0 = Enabled 0 := rfl

-- Quantifiers scope over the whole following formula, matching Lean's binders.
example : [tlfml| ∀ n : Nat, P n ∧ q] = [tlfml| ∀ n : Nat, ((P n) ∧ q)] := rfl
example : [tlfml| ∃ n : Nat, P n ∨ q] = [tlfml| ∃ n : Nat, ((P n) ∨ q)] := rfl
example : [tlfml| ∀ n : Nat, ⌞ n = n ⌟ → P n] = [tlfml| ∀ n : Nat, (⌞ n = n ⌟ → (P n))] := rfl

-- Quantifiers accept the same binders as Lean's `∃`, and expand one binder at a time.
example (R : Nat → Nat → pred σ) : [tlfml| ∀ a b, R a b] = [tlfml| ∀ a, ∀ b, R a b] := rfl
example (R : Nat → Nat → pred σ) : [tlfml| ∀ a b : Nat, R a b ∧ q] =
    [tlfml| ∀ a : Nat, ∀ b : Nat, ((R a b) ∧ q)] := rfl
example (R : Nat → Bool → pred σ) : [tlfml| ∀ (a : Nat) (b : Bool), R a b] =
    tl_forall fun (a : Nat) => tl_forall fun (b : Bool) => R a b := rfl
example (R : Nat → Nat → pred σ) : [tlfml| ∃ a b, R a b] = [tlfml| ∃ a, ∃ b, R a b] := rfl
example (R : Nat → Nat → pred σ) : [tlfml| ∃ (a b : Nat), R a b] =
    [tlfml| ∃ a : Nat, ∃ b : Nat, R a b] := rfl
example : [tlfml| ∀ _ : Nat, q] = tl_forall fun (_ : Nat) => q := rfl
example : [tlfml| ∃ _ : Nat, q] = tl_exists fun (_ : Nat) => q := rfl
example (R : Nat → Nat → pred σ) : [tlfml| forall a b, R a b] = [tlfml| ∀ a b, R a b] := rfl
example (R : Nat → Nat → pred σ) : [tlfml| exists a b, R a b] = [tlfml| ∃ a b, R a b] := rfl

-- Binder predicates follow Lean: `∀` guards with `→` and `∃` with `∧`.
example : [tlfml| ∀ n > 0, P n ∧ q] = [tlfml| ∀ n, ⌞ n > 0 ⌟ → ((P n) ∧ q)] := rfl
example : [tlfml| ∃ n < 3, P n ∨ q] = [tlfml| ∃ n, ⌞ n < 3 ⌟ ∧ ((P n) ∨ q)] := rfl
example (a : Nat) : [tlfml| ∀ _ > a, P a] = [tlfml| ∀ m, ⌞ m > a ⌟ → P a] := rfl
example (a : Nat) : [tlfml| ∃ _ < a, P a] = [tlfml| ∃ m, ⌞ m < a ⌟ ∧ P a] := rfl

-- Directly nested quantifiers of the same kind print as one binder list.
section
variable (R : Nat → Nat → pred σ)

/-- info: [tlfml|∀ a b, R a b] : pred σ -/
#guard_msgs in #check [tlfml| ∀ a, ∀ b, R a b]

/-- info: [tlfml|∃ a b, R a b] : pred σ -/
#guard_msgs in #check [tlfml| ∃ (a : Nat) (b : Nat), R a b]

/-- info: [tlfml|∀ a, ∃ b, R a b] : pred σ -/
#guard_msgs in #check [tlfml| ∀ a, ∃ b, R a b]

/-- info: [tlfml|∀ a, (∀ b, R a b) ∧ p] : pred σ -/
#guard_msgs in #check [tlfml| ∀ a, (∀ b, R a b) ∧ p]

-- Binder types follow `pp.funBinderTypes`; adjacent binders of the same type are grouped.
variable (D : (n : Nat) → Fin n → pred σ)

/-- info: [tlfml|∀ (a b : Nat), R a b] : pred σ -/
#guard_msgs in set_option pp.funBinderTypes true in #check [tlfml| ∀ a b, R a b]

/-- info: [tlfml|∃ (n : Nat) (u v : Fin n), D n u ∧ D n v] : pred σ -/
#guard_msgs in set_option pp.funBinderTypes true in
#check [tlfml| ∃ (n : Nat) (u : Fin n) (v : Fin n), D n u ∧ D n v]

/-- info: [tlfml|∀ (x : Nat), P x] : pred σ -/
#guard_msgs in set_option pp.funBinderTypes true in #check tl_forall P
end

-- Eta-expanding a function argument keeps the outer `x` distinct from the new binder.
section
variable (x : Nat → pred σ) (xs : List Nat)

/-- info: [tlfml|∀ x_1, x x_1] : pred σ -/
#guard_msgs in #check tl_forall x

/-- info: [tlfml|∃ (x_1 : Nat), x x_1] : pred σ -/
#guard_msgs in set_option pp.funBinderTypes true in #check tl_exists x

/-- info: [tlfml|⋀ x_1 ∈ xs, x x_1] : pred σ -/
#guard_msgs in #check tl_bigwedge x xs

/-- info: [tlfml|⋁ x_1 ∈ xs, x x_1] : pred σ -/
#guard_msgs in #check tl_bigvee x xs

example : [tlfml| ∀ x_1, x x_1] = tl_forall x := rfl
example : [tlfml| ∃ (x_1 : Nat), x x_1] = tl_exists x := rfl
end

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

-- The LTL biconditional follows Lean's `↔`: it binds more loosely than all other binary operators.
example : [tlfml| p → q ↔ r] = [tlfml| (p → q) ↔ r] := rfl
example : [tlfml| p ↔ q → r] = [tlfml| p ↔ (q → r)] := rfl
example : [tlfml| p ∧ q ↔ q ∨ p] = [tlfml| (p ∧ q) ↔ (q ∨ p)] := rfl
example : [tlfml| p ⇒ q ↔ r] = [tlfml| (p ⇒ q) ↔ r] := rfl
example : [tlfml| ¬ p ↔ q] = [tlfml| (¬ p) ↔ q] := rfl
example : [tlfml| ∀ n : Nat, P n ↔ q] = [tlfml| ∀ n : Nat, ((P n) ↔ q)] := rfl
example : [tlfml| p ↔ q] = Lentil.tl_iff p q := rfl

-- Weakening the term fallback should not make a following sequent prefix become a Lean argument.
example : (□ p |-tl- (q)) = ((□ p) |-tl- (q)) := rfl
example : (|-tl- (p → q)) = Lentil.valid [tlfml| p → q] := rfl

-- Brackets delimit the temporal connectives from the surrounding Lean proposition.
example : (IsSafety[□ (p ∧ q)] ∧ IsLiveness[◇ p]) =
    (IsSafety (always (tl_and p q)) ∧ IsLiveness (eventually p)) := rfl

-- Quantifier commas can appear in either argument of MachineClosed.
example : MachineClosed[∀ n, □ (P n), ∃ n, ◇ ⟨A n⟩] =
    MachineClosed (tl_forall fun n => always (P n))
      (tl_exists fun n => eventually (action_pred (A n))) := rfl

end Lentil.Test.Notation
