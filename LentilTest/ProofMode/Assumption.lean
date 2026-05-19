import Lentil

/- Tests for `tla_assumption`. -/

namespace TLA.ProofMode.Test.Assumption

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

example : (p) |-tla- (p) := by
  tla_start hp
  tla_assumption

example : (p ∧ q ∧ r) |-tla- (q) := by
  tla_start hp hq hr
  tla_assumption

example : (p) |-tla- ((fun e => p e)) := by
  tla_start hp
  tla_assumption

example (h : (p) |-tla- (q)) : (p) |-tla- (q) := by
  tla_assumption

/--
error: tla_assumption: no matching temporal hypothesis for
  q
-/
#guard_msgs in
example : (p) |-tla- (q) := by
  tla_start hp
  tla_assumption

end TLA.ProofMode.Test.Assumption
