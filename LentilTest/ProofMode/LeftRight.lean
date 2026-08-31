import Lentil

/- Tests for the `tleft` and `tright` tactics.

   These reduce a disjunctive proof-mode goal `p ∨ q` to one of its disjuncts.
-/

namespace Lentil.ProofMode.Test.LeftRight

open Lentil Lentil.ProofMode

variable {σ : Type u} (a b c : pred σ)

-- `tleft` picks the left disjunct.
example (lem : (a) |-tl- (a)) : (a) |-tl- (a ∨ b) := by
  tstart ha
  tleft
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem

-- `tright` picks the right disjunct.
example (lem : (a) |-tl- (a)) : (a) |-tl- (b ∨ a) := by
  tstart ha
  tright
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem

-- N-ary right-associative disjunction: `tleft` on `a ∨ b ∨ c` picks `a`.
example (lem : (a) |-tl- (a)) : (a) |-tl- (a ∨ b ∨ c) := by
  tstart ha
  tleft
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem

-- Two `tright`s in sequence peel down to the rightmost disjunct.
example (lem : (a) |-tl- (a)) : (a) |-tl- (b ∨ c ∨ a) := by
  tstart ha
  tright
  tright
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem

-- After `tleft`/`tright` the goal is still in proof-mode form and other
-- proof-mode tactics continue to work.
example (lem : (a) |-tl- (a)) : (a) |-tl- (a ∨ b) := by
  tstart ha
  tleft
  tapply lem
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end Lentil.ProofMode.Test.LeftRight
