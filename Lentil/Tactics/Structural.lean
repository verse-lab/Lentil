import Lentil.Rules.Basic

/-! Tactics manipulating the structure of premises/goals. -/

open Lean

namespace TLA

/-- `tla_intros` repeatedly moves the premise on the right-hand side
    of `|-tla-` to the left-hand side. -/
macro "tla_intros" : tactic =>
  `(tactic| (try rw [TLA.impl_intro]) <;> (repeat rw [TLA.impl_intro_add_r]))

end TLA
