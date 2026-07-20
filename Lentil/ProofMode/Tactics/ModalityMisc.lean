import Lentil.ProofMode.Location
import Lentil.ProofMode.Tactics.Monotone
import Lentil.ProofMode.Tactics.Apply
import Lentil.ProofMode.Tactics.Revert

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

section

variable {σ : Type u}

/-- Carrying a proof of `◇p |-tla- p`. -/
class PrefixClosed (p : pred σ) : Prop where
  prefix_closed : ◇p |-tla- (p)

instance prefixClosedEventually (p : pred σ) : PrefixClosed (TLA.eventually p) where
  prefix_closed := by rw [eventually_idem]

instance prefixClosedAlwaysEventually (p : pred σ) :
    PrefixClosed (TLA.always (TLA.eventually p)) where
  prefix_closed := by rw [eventually_always_eventually]

instance prefixClosedPure (p : Prop) : @PrefixClosed σ (TLA.pure_pred p) where
  prefix_closed := by tunfold_simp

-- These are good, but let's have them later ...
/-
instance prefixClosedAnd (p q : pred σ) [PrefixClosed p] [PrefixClosed q] :
    PrefixClosed (TLA.tla_and p q) where
  prefix_closed := by
    intro e k h
    exact ⟨PrefixClosed.prefix_closed (p := p) e k h.1,
      PrefixClosed.prefix_closed (p := q) e k h.2⟩

instance prefixClosedOr (p q : pred σ) [PrefixClosed p] [PrefixClosed q] :
    PrefixClosed (TLA.tla_or p q) where
  prefix_closed := by
    intro e k h
    rcases h with h | h
    · exact Or.inl (PrefixClosed.prefix_closed (p := p) e k h)
    · exact Or.inr (PrefixClosed.prefix_closed (p := q) e k h)

instance prefixClosedForall {α : Sort v} (p : α → pred σ)
    [∀ x, PrefixClosed (p x)] :
    PrefixClosed (TLA.tla_forall p) where
  prefix_closed := by
    intro e k h x
    exact PrefixClosed.prefix_closed (p := p x) e k (h x)

instance prefixClosedExists {α : Sort v} (p : α → pred σ)
    [∀ x, PrefixClosed (p x)] :
    PrefixClosed (TLA.tla_exists p) where
  prefix_closed := by
    intro e k h
    rcases h with ⟨x, hx⟩
    exact ⟨x, PrefixClosed.prefix_closed (p := p x) e k hx⟩
-/

-- NOTE: This prefix & suffix representation does not look very nice, but what
-- else can we do?
theorem Entails_advance_eventually_under_always
    (pre post : List (NamedPred σ)) {name : String} {p goal : pred σ}
    [inst : PrefixClosed goal] :
    Entails (mapHypPreds TLA.always pre ++ ⟨name, p⟩ :: mapHypPreds TLA.always post) goal →
    Entails (mapHypPreds TLA.always pre ++ ⟨name, TLA.eventually p⟩ :: mapHypPreds TLA.always post) goal := by
  intro h
  apply Entails_trans ; apply inst.prefix_closed
  refine Entails_revert_by_idx (mapHypPreds TLA.always pre).length ?_
  simp
  rw [List.eraseIdx_append_of_length_le]
  on_goal 2=> simp
  simp
  unfold Entails
  rw [← mapHypPreds_append, mapHypPreds_preds, repeatedAnd_map_always,
    impl_intro_add_r, TLA.and_comm]
  apply pred_implies_trans ; apply always_and_eventually'
  apply eventually_monotone
  apply pred_implies_trans
  on_goal 2 => apply h
  simp [← repeatedAnd_map_always, mapHypPreds_preds]
  rw [← repeatedAnd_cons]
  apply repeatedAnd_subset_implies ; grind

end

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

private theorem Entails_step_aux
    (stable stepped : List (NamedPred σ))
    (h : Entails (mapHypPreds TLA.always stable ++ stepped) goal) :
    Entails
      (mapHypPreds TLA.always stable ++ mapHypPreds TLA.later stepped)
      (TLA.later goal) := by
  unfold Entails at h ⊢
  simp only [List.map_append, mapHypPreds_preds,
    repeatedAnd_append, repeatedAnd_map_always] at h ⊢
  rw [repeatedAnd_map_later]
  rw [← impl_intro_add_r] at h ⊢
  rw [← later_implies]
  rw [always_pred_implies] at h
  apply pred_implies_trans ; refine h ; apply later_monotone'

theorem Entails_step
    (stable stepped : List (NamedPred σ))
    (stableIdxs steppedIdxs : List Nat)
    (heqStable :
      stableIdxs.filterMap (hyps[·]?) = mapHypPreds TLA.always stable)
    (heqStepped :
      steppedIdxs.filterMap (hyps[·]?) = mapHypPreds TLA.later stepped)
    (h : Entails (mapHypPreds TLA.always stable ++ stepped) goal) :
    Entails hyps (TLA.later goal) := by
  refine Entails_drop_hyps
    (mapHypPreds TLA.always stable ++ mapHypPreds TLA.later stepped) ?_ ?_
  · grind
  · exact Entails_step_aux stable stepped h

end

-- FIXME: The following logic is very similar in `Lentil.ProofMode.Tactics.Monotone`,
-- consider unifying them
private def peelModalDirect? (modal : Name) (p : Expr) : Option Expr :=
  if p.getAppFn'.isConstOf modal then
    if h : p.isApp = true then some (p.appArg h) else none
  else
    none

private def peelModal? (modal : Name) (p : Expr) : MetaM (Option Expr) :=
  recognizeWithTlaModalityHeadUnfold? (peelModalDirect? modal) p

private def peelAlways? (p : Expr) : MetaM (Option Expr) :=
  peelModal? ``TLA.always p

private def peelEventually? (p : Expr) : MetaM (Option Expr) :=
  peelModal? ``TLA.eventually p

private def peelLater? (p : Expr) : MetaM (Option Expr) :=
  peelModal? ``TLA.later p

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

private def proofModeAdvanceEventually (loc : TemporalHypLoc) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target
    | throwError "tadvance: expected a proof-mode Entails goal"
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tadvance: failed to read the hypotheses from the goal"
  let (idx, chosenName, chosenPred) ← findIdxByTemporalHypLoc hyps loc "tadvance" "the goal's Entails list"
  let (preHyps, postHyps) := hyps.splitAt idx
  let postHyps := postHyps.tail
  let some chosenP ← peelEventually? chosenPred
    | throwError "tadvance: selected hypothesis must have a leading eventually (`◇`) prefix"
  let some peeledPreHyps ← peelAlwaysHyps? preHyps
    | throwError "tadvance: every hypothesis before the selected one must have a leading always (`□`) prefix"
  let some peeledPostHyps ← peelAlwaysHyps? postHyps
    | throwError "tadvance: every hypothesis after the selected one must have a leading always (`□`) prefix"
  let preExpr ← toHypsList hypTy peeledPreHyps
  let postExpr ← toHypsList hypTy peeledPostHyps
  let hgoal ← do
    let expected ← mkAppM ``PrefixClosed #[goal]
    try
      synthInstance expected
    catch _ =>
      throwError "tadvance: failed to synthesize a PrefixClosed instance for the goal"
  let thm ← mkAppOptM ``Entails_advance_eventually_under_always
    #[none, some preExpr, some postExpr, some (toExpr chosenName),
      some chosenP, some goal, some hgoal]
  let [g'] ← g.apply thm
    | throwError "tadvance: unexpected number of goals after applying the reflection theorem"
  let newHypsExpr ← toHypsList hypTy (preHyps ++ (chosenName, chosenP) :: postHyps)
  let newTarget ← mkAppM ``Entails #[newHypsExpr, goal]
  replaceMainGoal [← g'.change newTarget]

-- FIXME: This pattern repetitively appears in several places, like `tshift_nom`
private def proofModeStep : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let some (σExpr, hypsExpr, hypTy, hyps, goal) ← recognizeCanonicalEntails target
    | throwError "tstep: expected a proof-mode Entails goal"
  let some goalBody ← peelLater? goal
    | throwError "tstep: expected the proof-mode goal to have a leading next (`◯`) prefix"

  let (stableIdxs, steppedIdxs, stableHyps, steppedHyps) ← splitHyps hyps
  let stableHypsExpr ← toHypsList hypTy stableHyps
  let steppedHypsExpr ← toHypsList hypTy steppedHyps
  let natTy := mkConst ``Nat
  let stableIdxsExpr ← mkListLit natTy (stableIdxs.map toExpr)
  let steppedIdxsExpr ← mkListLit natTy (steppedIdxs.map toExpr)
  let thm ← mkAppOptM ``Entails_step
    #[some σExpr, some hypsExpr, some goalBody,
      some stableHypsExpr, some steppedHypsExpr,
      some stableIdxsExpr, some steppedIdxsExpr]
  let goals ← g.apply thm
  let goals ← goals.filterM fun subgoal =>
    (do
      let _ ← subgoal.applyRfl
      pure false)
    <|> pure true
  let [temporalGoal] := goals
    | throwError "tstep: expected exactly one temporal subgoal after applying the soundness theorem"

  let displayedStableHyps ← stableHyps.mapM fun (name, pred) => do
    let pred ← mkAppM ``TLA.always #[pred]
    pure (name, pred)
  let advancedHypsExpr ← toHypsList hypTy (displayedStableHyps ++ steppedHyps)
  let advancedTarget ← mkAppM ``Entails #[advancedHypsExpr, goalBody]
  replaceMainGoal [← temporalGoal.change advancedTarget]
where
  splitHyps (hyps : List (String × Expr)) :
      MetaM (List Nat × List Nat × List (String × Expr) × List (String × Expr)) := do
    let mut stableIdxs : List Nat := []
    let mut steppedIdxs : List Nat := []
    let mut stableHyps : List (String × Expr) := []
    let mut steppedHyps : List (String × Expr) := []
    for ((name, pred), idx) in hyps.zipIdx do
      if let some body ← peelAlways? pred then
        stableIdxs := idx :: stableIdxs
        stableHyps := (name, body) :: stableHyps
      else if let some body ← peelLater? pred then
        steppedIdxs := idx :: steppedIdxs
        steppedHyps := (name, body) :: steppedHyps
      else
        throwError
          "tstep: expected every temporal hypothesis to have a leading always (`□`) or next (`◯`) prefix"

    stableIdxs := stableIdxs.reverse
    steppedIdxs := steppedIdxs.reverse
    stableHyps := stableHyps.reverse
    steppedHyps := steppedHyps.reverse
    return (stableIdxs, steppedIdxs, stableHyps, steppedHyps)

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
guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
ttoggle_goal_under_always
guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩] q
```
If the current goal has no leading `□`, the same tactic changes `q` to `□ q`:
```lean
guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩] q
ttoggle_goal_under_always
guard_target =ₛ Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
```
-/
syntax (name := tlaToggleGoalUnderAlwaysTac) "ttoggle_goal_under_always" : tactic

/--
`tadvance h` advances the current proof point to a selected eventuality.

If `h : ◇ p`, the tactic replaces `h` by `p`, provided every other proof-mode
hypothesis has a leading `□` (possibly hidden behind a definition tagged with
`[tla_modality_unfold]`) and typeclass search can synthesize
`PrefixClosed goal`. Built-in instances cover `◇ q`, `□◇ q`, and pure facts.
For other prefix-closed goals, add a `PrefixClosed` instance.
-/
syntax (name := tlaAdvanceTac) "tadvance" (ppSpace colGt temporalHypLoc) : tactic

/--
`tstep` advances a proof-mode sequent by one deterministic temporal step.

The goal must have a leading `◯`. Each temporal hypothesis must have either a
leading `□` or `◯`; `□ p` remains `□ p`, while `◯ q` becomes `q`. The resulting
context groups the always hypotheses before the peeled next hypotheses.
-/
syntax (name := tlaStepTac) "tstep" : tactic

elab_rules : tactic
  | `(tactic| ttoggle_goal_under_always) => proofModeToggleGoalUnderAlways
  | `(tactic| tadvance $hyp:temporalHypLoc) => do
    let loc ← parseTemporalHypLoc hyp "tadvance: invalid syntax for hypothesis position"
    proofModeAdvanceEventually loc
  | `(tactic| tstep) => proofModeStep

end TLA.ProofMode
