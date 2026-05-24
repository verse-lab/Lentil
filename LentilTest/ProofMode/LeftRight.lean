import Lentil

/- Tests for the `tla_left` and `tla_right` tactics.

   These reduce a disjunctive proof-mode goal `p ∨ q` to one of its disjuncts.
-/

namespace TLA.ProofMode.Test.LeftRight

open TLA TLA.ProofMode

variable {σ : Type u} (a b c : pred σ)

-- `tla_left` picks the left disjunct.
example (lem : (a) |-tla- (a)) : (a) |-tla- (a ∨ b) := by
  tla_start ha
  tla_left
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact lem

-- `tla_right` picks the right disjunct.
example (lem : (a) |-tla- (a)) : (a) |-tla- (b ∨ a) := by
  tla_start ha
  tla_right
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact lem

-- N-ary right-associative disjunction: `tla_left` on `a ∨ b ∨ c` picks `a`.
example (lem : (a) |-tla- (a)) : (a) |-tla- (a ∨ b ∨ c) := by
  tla_start ha
  tla_left
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact lem

-- Two `tla_right`s in sequence peel down to the rightmost disjunct.
example (lem : (a) |-tla- (a)) : (a) |-tla- (b ∨ c ∨ a) := by
  tla_start ha
  tla_right
  tla_right
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact lem

-- After `tla_left`/`tla_right` the goal is still in proof-mode form and other
-- proof-mode tactics continue to work.
example (lem : (a) |-tla- (a)) : (a) |-tla- (a ∨ b) := by
  tla_start ha
  tla_left
  tla_apply lem
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end TLA.ProofMode.Test.LeftRight
