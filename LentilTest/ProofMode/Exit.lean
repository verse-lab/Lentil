import Lentil

/- Tests for the `tla_exit` tactic, which leaves proof mode by converting an
   `Entails` goal back into a raw `|-tla-` sequent. -/

namespace TLA.ProofMode.Test.Exit

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Round-trip: `tla_start` then `tla_exit` brings the goal back to its raw
-- shape, and a non-proof-mode tactic finishes it.
example : (p ∧ q) |-tla- (p) := by
  tla_start hp hq
  tla_exit
  intro _ ⟨h, _⟩ ; exact h

-- Singleton proof-mode context becomes a single-premise raw sequent.
example : (p) |-tla- (p) := by
  tla_start h
  tla_exit
  exact pred_implies_refl _

-- Empty proof-mode context exits to `valid rhs` rather than `(⊤) |-tla- rhs`.
-- (We construct an empty context via `tla_clear` since `tla_start` from a
-- `valid` goal isn't supported.)
example : (q) |-tla- (⊤) := by
  tla_start hq
  tla_clear hq
  tla_exit
  -- Goal is now `valid (tla_true : pred σ) = ∀ σ', σ'.satisfies tla_true`.
  intro _ ; exact True.intro

-- After some proof-mode tactics we can drop back to the raw view to finish.
example : (p) |-tla- (p ∨ q) := by
  tla_start hp
  tla_left
  tla_exit
  exact pred_implies_refl _

-- `tla_exit` fails on a goal that is not in `Entails` form.
/--
error: tla_exit: goal is not an Entails sequent, but (p) |-tla- (p)
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  tla_exit

end TLA.ProofMode.Test.Exit
