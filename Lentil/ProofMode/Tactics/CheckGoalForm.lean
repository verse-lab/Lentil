import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Elab Tactic

/--
`tla_check_goal_form` checks that the current proof-mode goal is in the
canonical literal `Entails [...] goal` form used by the proof-mode tactics.

It does not change the goal. This is useful in tests after a tactic that
reflects over the hypothesis list: if the goal still contains unreduced list
computations, then the check fails.
-/
elab "tla_check_goal_form" : tactic => do
  unless (← recognizeEntailsHypsFromGoal).isSome do
    throwError "tla_check_goal_form: goal is not in canonical Entails form"

end TLA.ProofMode
