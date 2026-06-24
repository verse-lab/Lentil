import Lentil

/- Tests for `tassumption`. -/

namespace TLA.ProofMode.Test.Assumption

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

example : (p) |-tla- (p) := by
  tstart hp
  tassumption

example : (p ∧ q ∧ r) |-tla- (q) := by
  tstart hp hq hr
  tassumption

example : (p) |-tla- ((fun e => p e)) := by
  tstart hp
  tassumption

example (h : (p) |-tla- (q)) : (p) |-tla- (q) := by
  tassumption

/--
error: tassumption: no matching temporal hypothesis for
  q
-/
#guard_msgs in
example : (p) |-tla- (q) := by
  tstart hp
  tassumption

end TLA.ProofMode.Test.Assumption
