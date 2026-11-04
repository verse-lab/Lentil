import Lentil

/- Tests for the `tconstructor` tactic.

   `tconstructor` splits a `tl_and`, `tl_iff` or `tl_exists` goal by its
   introduction rule, the converse of `trcases` with a tuple pattern.
-/

namespace Lentil.ProofMode.Test.Constructor

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ) (P : Nat → pred σ)

/-! ## Conjunction -/

example : (p ∧ q) |-tl- (q ∧ p) := by
  tstart hp hq
  tconstructor
  · guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] q
    tassumption
  · guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] p
    tassumption

-- Only the outermost conjunction is split, unlike `tsplit_ands`.
example : (p ∧ q ∧ r) |-tl- (p ∧ q ∧ r) := by
  tstart hp hq hr
  tconstructor
  · tassumption
  · guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] [tlfml| q ∧ r]
    tsplit_ands <;> tassumption

-- The goals are tagged after the fields of `And`, as with `constructor`.
example : (p ∧ q) |-tl- (q ∧ p) := by
  tstart hp hq
  tconstructor
  case right => tassumption
  case left => tassumption

/-! ## Biconditional -/

example : (p ∧ q) |-tl- (p ↔ q) := by
  tstart hp hq
  tconstructor
  · guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] [tlfml| p → q]
    tintro h
    tassumption
  · guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] [tlfml| q → p]
    tintro h
    tassumption

-- Destructuring a biconditional with `trcases` and rebuilding it with
-- `tconstructor` are converse steps; the goals are tagged `mp` and `mpr`.
example : (p ↔ q) |-tl- (q ↔ p) := by
  tstart h
  trcases h with ⟨hpq, hqp⟩
  tconstructor
  case mpr => tassumption
  case mp => tassumption

/-! ## Existential -/

-- The witness is left to unification.
example : (P 0) |-tl- (∃ n : Nat, (P n)) := by
  tstart hp
  tconstructor
  tassumption

-- The witness can also be supplied through its own goal, tagged `w`.
example (lem : (p) |-tl- (P 1)) : (p) |-tl- (∃ n : Nat, (P n)) := by
  tstart hp
  tconstructor
  case w => exact 1
  guard_target =ₛ Entails [⟨"hp", p⟩] (P 1)
  exact lem

-- A witness shared by later goals is fixed by whichever goal assigns it first.
example : (P 0 ∧ q) |-tl- (∃ n : Nat, ((P n) ∧ q)) := by
  tstart hp hq
  tconstructor
  tconstructor <;> tassumption

/-! ## Errors -/

/--
error: tconstructor: goal predicate is not a ∧, ↔ or ∃; got [tlfml|p ∨ q]
-/
#guard_msgs in
example : (p) |-tl- (p ∨ q) := by
  tstart hp
  tconstructor

end Lentil.ProofMode.Test.Constructor
