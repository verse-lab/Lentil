import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

/--
`texit` is the inverse of `tstart`: it leaves the proof mode by
converting an `Entails`-shaped goal back into a raw `|-tla-` sequent whose
left-hand side is the conjunction of the proof-mode hypotheses.

For example, in a proof-mode context with `hp : p`, `hq : q`, and goal `r`,
```lean
texit
```
changes the proof state back to `(p ∧ q) |-tla- r`. A single hypothesis
`hp : p` becomes `p |-tla- r`. An empty proof-mode context becomes the
canonical `|-tla- r` (i.e. `valid r`), rather than the equivalent
`(⊤) |-tla- r`.
-/
syntax (name := tlaExitTac) "texit" : tactic

elab_rules : tactic
  | `(tactic| texit) => withMainContext do
    let mainGoal ← getMainGoal
    let ty ← cleanupAnnotAndMore (← mainGoal.getType)
    let (σ, _, _, hyps, rhs) ←
      parseCanonicalEntails ty m!"texit: goal is not an Entails sequent, but {ty}"
    let preds := hyps.map (·.2)
    if preds.isEmpty then
      let thm ← mkAppM ``valid_eq_true_implies #[rhs]
      let thm ← mkAppM ``Eq.mp #[thm]
      let gs ← mainGoal.apply thm
      replaceMainGoal gs
    else
      let lhs ← mkRepeatedAndExpr σ preds
      let newGoal ← mkAppM ``TLA.pred_implies #[lhs, rhs]
      let g' ← mainGoal.change newGoal
      replaceMainGoal [g']

end TLA.ProofMode
