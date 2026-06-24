import Lentil

/- Tests for the `texists` tactic.

   `texists t` provides a witness `t` for a `texists`-headed goal,
   reducing `Entails hyps (∃ x, p x)` to `Entails hyps (p t)`. The soundness
   theorem is a thin wrapper around `exists_elim`.
-/

namespace TLA.ProofMode.Test.Exists

open TLA TLA.ProofMode

variable {σ : Type u} (a : pred σ) (P : Nat → pred σ)

-- Basic: provide a witness.
example (lem : (a) |-tla- ((P 0))) : (a) |-tla- (∃ n : Nat, (P n)) := by
  tstart ha
  texists 0
  tcheck_goal Entails [⟨"ha", a⟩] (P 0)
  exact lem

-- Chained existentials: invoke `texists` twice.
example (Q : Nat → Nat → pred σ) (lem : (a) |-tla- ((Q 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, ((Q x y)))) := by
  tstart ha
  texists 1
  texists 2
  tcheck_goal Entails [⟨"ha", a⟩] (Q 1 2)
  exact lem

-- Multiple witnesses in one invocation, comma-separated (mirrors Lean's `exists`).
example (Q : Nat → Nat → pred σ) (lem : (a) |-tla- ((Q 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, ((Q x y)))) := by
  tstart ha
  texists 1, 2
  tcheck_goal Entails [⟨"ha", a⟩] (Q 1 2)
  exact lem

-- Three witnesses at once.
example (R : Nat → Nat → Nat → pred σ) (lem : (a) |-tla- ((R 0 1 2))) :
    (a) |-tla- (∃ x : Nat, (∃ y : Nat, (∃ z : Nat, ((R x y z))))) := by
  tstart ha
  texists 0, 1, 2
  tcheck_goal Entails [⟨"ha", a⟩] (R 0 1 2)
  exact lem

-- Witness depending on a Lean-context variable.
example (P : Nat → pred σ) (k : Nat) (lem : (a) |-tla- ((P k))) :
    (a) |-tla- (∃ n : Nat, (P n)) := by
  tstart ha
  texists k
  tcheck_goal Entails [⟨"ha", a⟩] (P k)
  exact lem

-- Existential witnesses may be proof values.
example (Q : Prop) (hQ : Q) (P : Q → pred σ) (lem : (a) |-tla- ((P hQ))) :
    (a) |-tla- (∃ h : Q, (P h)) := by
  tstart ha
  texists hQ
  tcheck_goal Entails [⟨"ha", a⟩] (P hQ)
  exact lem

-- After `texists`, the remaining proof works in the proof-mode view.
example (lem : (a) |-tla- ((P 0))) : (a) |-tla- (∃ n : Nat, (P n)) := by
  tstart ha
  texists 0
  -- We can still use `tapply` etc. since the goal is still an `Entails`.
  tapply lem
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end TLA.ProofMode.Test.Exists
