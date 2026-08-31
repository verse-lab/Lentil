import Lentil

/- Tests for `tassumption`. -/

namespace Lentil.ProofMode.Test.Assumption

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

example : (p) |-tl- (p) := by
  tstart hp
  tassumption

example : (p ∧ q ∧ r) |-tl- (q) := by
  tstart hp hq hr
  tassumption

example : (p) |-tl- ((fun e => p e)) := by
  tstart hp
  tassumption

example (h : (p) |-tl- (q)) : (p) |-tl- (q) := by
  tassumption

/--
error: tassumption: no matching temporal hypothesis for
  q
-/
#guard_msgs in
example : (p) |-tl- (q) := by
  tstart hp
  tassumption

end Lentil.ProofMode.Test.Assumption
