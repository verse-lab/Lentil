import Lentil

/- Tests for the `texit` tactic, which leaves proof mode by converting an
   `Entails` goal back into a raw `|-tl-` sequent. -/

namespace Lentil.ProofMode.Test.Exit

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Round-trip: `tstart` then `texit` brings the goal back to its raw
-- shape, and a non-proof-mode tactic finishes it.
example : (p ∧ q) |-tl- (p) := by
  tstart hp hq
  texit
  exact Lentil.and_left

-- Singleton proof-mode context becomes a single-premise raw sequent.
example : (p) |-tl- (p) := by
  tstart h
  texit
  exact pred_implies_refl _

-- Empty proof-mode context exits to `valid rhs` rather than `(⊤) |-tl- rhs`.
-- (We construct an empty context via `tclear` since `tstart` from a
-- `valid` goal isn't supported.)
example : (q) |-tl- (⊤) := by
  tstart hq
  tclear hq
  texit
  -- Goal is now `valid (tl_true : pred σ) = ∀ σ', σ'.satisfies tl_true`.
  exact valid_pure True.intro

-- After some proof-mode tactics we can drop back to the raw view to finish.
example : (p) |-tl- (p ∨ q) := by
  tstart hp
  tleft
  texit
  exact pred_implies_refl _

-- `texit` fails on a goal that is not in `Entails` form.
/--
error: texit: goal is not an Entails sequent, but (p) |-tl- (p)
-/
#guard_msgs in
example : (p) |-tl- (p) := by
  texit

end Lentil.ProofMode.Test.Exit
