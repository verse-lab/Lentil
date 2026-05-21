import Lentil

/- Tests for the `tla_exists` tactic.

   `tla_exists t` provides a witness `t` for a `tla_exists`-headed goal,
   reducing `Entails hyps (∃ x, p x)` to `Entails hyps (p t)`. The soundness
   theorem is a thin wrapper around `exists_elim`.
-/

namespace TLA.ProofMode.Test.Exists

open TLA TLA.ProofMode

variable {σ : Type u} (a : pred σ) (P : Nat → pred σ)

-- Basic: provide a witness.
example (lem : (a) |-tla- ((P 0))) : (a) |-tla- (∃ n : Nat, (P n)) := by
  tla_start ha
  tla_exists 0
  tla_check_goal Entails [⟨"ha", a⟩] (P 0)
  exact lem

-- Chained existentials: invoke `tla_exists` twice.
example (Q : Nat → Nat → pred σ) (lem : (a) |-tla- ((Q 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, ((Q x y)))) := by
  tla_start ha
  tla_exists 1
  tla_exists 2
  tla_check_goal Entails [⟨"ha", a⟩] (Q 1 2)
  exact lem

-- Multiple witnesses in one invocation, comma-separated (mirrors Lean's `exists`).
example (Q : Nat → Nat → pred σ) (lem : (a) |-tla- ((Q 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, ((Q x y)))) := by
  tla_start ha
  tla_exists 1, 2
  tla_check_goal Entails [⟨"ha", a⟩] (Q 1 2)
  exact lem

-- Three witnesses at once.
example (R : Nat → Nat → Nat → pred σ) (lem : (a) |-tla- ((R 0 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, (∃ z : Nat, ((R x y z))))) := by
  tla_start ha
  tla_exists 0, 1, 2
  tla_check_goal Entails [⟨"ha", a⟩] (R 0 1 2)
  exact lem

-- Witness depending on a Lean-context variable.
example (P : Nat → pred σ) (k : Nat) (lem : (a) |-tla- ((P k))) :
    (a) |-tla- (∃ n : Nat, (P n)) := by
  tla_start ha
  tla_exists k
  tla_check_goal Entails [⟨"ha", a⟩] (P k)
  exact lem

-- After `tla_exists`, the remaining proof works in the proof-mode view.
example (lem : (a) |-tla- ((P 0))) : (a) |-tla- (∃ n : Nat, (P n)) := by
  tla_start ha
  tla_exists 0
  -- We can still use `tla_apply` etc. since the goal is still an `Entails`.
  tla_apply lem
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end TLA.ProofMode.Test.Exists
