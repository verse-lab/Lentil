import Lentil.ProofMode.Tactics.Monotone

namespace TLA.ProofMode

open Lean Meta Elab Tactic

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

theorem Entails_toggle_goal_under_always :
    Entails (mapHypPreds TLA.always hyps) goal =
      Entails (mapHypPreds TLA.always hyps) (TLA.always goal) := by
  unfold Entails
  rw [mapHypPreds_preds, repeatedAnd_map_always]
  apply TLA.always_pred_implies

end

-- FIXME: The following logic is very similar in `Lentil.ProofMode.Tactics.Monotone`,
-- consider unifying them
private def peelAlwaysDirect? (p : Expr) : Option Expr :=
  if p.getAppFn'.isConstOf ``TLA.always then
    if h : p.isApp = true then some (p.appArg h) else none
  else
    none

private def peelAlways? (p : Expr) : MetaM (Option Expr) :=
  recognizeWithTlaModalityHeadUnfold? peelAlwaysDirect? p

private def peelAlwaysHyps? (hyps : List (String × Expr)) : MetaM (Option (List (String × Expr))) := do
  let mut peeledHyps := []
  for (name, pred) in hyps do
    let some pred ← peelAlways? pred
      | return none
    peeledHyps := (name, pred) :: peeledHyps
  return some peeledHyps.reverse

private def proofModeToggleGoalUnderAlways : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target
    | throwError "ttoggle_goal_under_always: expected a proof-mode Entails goal"
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "ttoggle_goal_under_always: failed to read the hypotheses from the goal"
  let some peeledHypsList ← peelAlwaysHyps? hyps
    | throwError "ttoggle_goal_under_always: expected every temporal hypothesis to have an always prefix"
  let peeledHypsExpr ← toHypsList hypTy peeledHypsList
  let peeledGoal? ← peelAlways? goal
  let (leftToRight?, toggledGoal) :=
    match peeledGoal? with
    | some goal => (true, goal)
    | none => (false, goal)
  let thm ← mkAppOptM ``Entails_toggle_goal_under_always #[none, some peeledHypsExpr, some toggledGoal]
  let thm ← mkAppM (if leftToRight? then ``Eq.mp else ``Eq.mpr) #[thm]
  let [g'] ← g.apply thm
    | throwError "ttoggle_goal_under_always: unexpected number of goals after applying the reflection theorem"
  let newGoal ← if leftToRight? then pure toggledGoal else mkAppM ``TLA.always #[toggledGoal]
  let newTarget ← mkAppM ``Entails #[hypsExpr, newGoal]
  replaceMainGoal [← g'.change newTarget]

/--
`ttoggle_goal_under_always` toggles one leading `□` on the current
proof-mode goal when every temporal hypothesis has a leading `□`.

When the leading `□` is hidden behind a definition tagged with
`[tla_modality_unfold]`, this tactic unfolds only that expression head while
checking for the prefix. This includes the built-in wrappers
`TLA.always_implies` (`⇒`), `TLA.leads_to` (`↝`), and `TLA.weak_fairness`
(`𝒲ℱ`).

For example, with `hp : □ p`, it changes a proof-mode goal `□ q` to `q`:
```lean
tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
ttoggle_goal_under_always
tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩] q
```
If the current goal has no leading `□`, the same tactic changes `q` to `□ q`:
```lean
tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩] q
ttoggle_goal_under_always
tcheck_goal Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
```
-/
syntax (name := tlaToggleGoalUnderAlwaysTac) "ttoggle_goal_under_always" : tactic

elab_rules : tactic
  | `(tactic| ttoggle_goal_under_always) => proofModeToggleGoalUnderAlways

end TLA.ProofMode
