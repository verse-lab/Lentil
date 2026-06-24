import Lentil

/- Tests for the `texit` tactic, which leaves proof mode by converting an
   `Entails` goal back into a raw `|-tla-` sequent. -/

namespace TLA.ProofMode.Test.Exit

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Round-trip: `tstart` then `texit` brings the goal back to its raw
-- shape, and a non-proof-mode tactic finishes it.
example : (p ∧ q) |-tla- (p) := by
  tstart hp hq
  texit
  intro _ ⟨h, _⟩ ; exact h

-- Singleton proof-mode context becomes a single-premise raw sequent.
example : (p) |-tla- (p) := by
  tstart h
  texit
  exact pred_implies_refl _

-- Empty proof-mode context exits to `valid rhs` rather than `(⊤) |-tla- rhs`.
-- (We construct an empty context via `tclear` since `tstart` from a
-- `valid` goal isn't supported.)
example : (q) |-tla- (⊤) := by
  tstart hq
  tclear hq
  texit
  -- Goal is now `valid (tla_true : pred σ) = ∀ σ', σ'.satisfies tla_true`.
  intro _ ; exact True.intro

-- After some proof-mode tactics we can drop back to the raw view to finish.
example : (p) |-tla- (p ∨ q) := by
  tstart hp
  tleft
  texit
  exact pred_implies_refl _

-- `texit` fails on a goal that is not in `Entails` form.
/--
error: texit: goal is not an Entails sequent, but (p) |-tla- (p)
-/
#guard_msgs in
example : (p) |-tla- (p) := by
  texit

end TLA.ProofMode.Test.Exit
