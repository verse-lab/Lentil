import Lentil.ProofMode.Location

namespace TLA.ProofMode

open Lean Meta Elab Tactic LentilLib
open Lean.Parser.Tactic

/-
Design notes.

`tla_rewrite` operates on selected pieces of a proof-mode sequent

  `Entails [⟨h₀, p₀⟩, ..., ⟨hₙ, pₙ⟩] goal`.

The first implementation tried to change the goal to a wrapper whose selected
locations were explicit arguments and whose unselected locations were implicit
arguments. That does not isolate the unselected predicates: Lean's `rewrite`
still traverses implicit arguments, so a rewrite intended for `hp₁ hp₃` could
also rewrite `hp₂`.

The current implementation instead follows the shape of the manual script

  `let cont := fun preds => EntailsWithSomePredsExtractedOut hyps idxs preds goal`
  `change cont [selected predicates]`
  `rewrite ...`
  `revert cont`
  `change Entails [updated hypotheses] updatedGoal`

If the goal itself is selected, `cont` takes a second explicit argument for it.
The body of the local `let` is opaque to `rewrite`, while the explicit arguments
remain normal Lean expressions. After rewriting, reverting and unfolding `cont`
restores a literal `Entails` target with the original hypothesis order and names.
The final target is computed here at the meta level; we do not rely on `dsimp`
to clean up `replacePredsAtIndices`.

`tla_simp` and `tla_dsimp` deliberately do not use this helper. They are
implemented as direct `conv` visits to the selected expressions because
simplification does not need `rewrite`'s theorem-premise side-goal behavior.
-/

def replacePredsAtIndices {σ : Type u} (hyps : List (NamedPred σ))
    (idxs : List Nat) (preds : List (pred σ)) : List (NamedPred σ) :=
  (idxs.zip preds).foldl (fun hyps ⟨idx, pred⟩ => hyps.modify idx fun h => { h with pred := pred }) hyps

def EntailsWithSomePredsExtractedOut {σ : Type u} (hyps : List (NamedPred σ))
    (idxs : List Nat) (preds : List (pred σ)) (goal : pred σ) : Prop :=
  Entails (replacePredsAtIndices hyps idxs preds) goal

/-- Compute the restored `Entails` target by inspecting the partially exposed
target itself. This is the meta-level counterpart of
`change Entails [updated hypotheses] updatedGoal`: it reads the rewritten
predicate list, patches the original hypothesis list, and builds a fresh literal
`Entails` expression. -/
private def unfoldPartialHiddenTarget (target : Expr) : MetaM (Option Expr) := target.withApp' fun f args => do
  -- Recognize
  unless f.isConstOf ``EntailsWithSomePredsExtractedOut do
    return none
  let [σ, hypsExpr, idxsExpr, predsExpr, goal] := args.toList | return none
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr | return none
  let some (_, idxExprs) := idxsExpr.listLit? | return none
  let idxs := idxExprs.filterMap Expr.nat?
  unless idxs.length == idxExprs.length do
    return none
  let some (_, preds) := predsExpr.listLit? | return none
  unless idxs.length == preds.length do
    throwError "tla_rewrite: internal error: length of indices and predicates do not match in partial hidden target"
  -- Build `Entails`
  let hyps := idxs.zip preds |>.foldl (init := hyps) fun hyps' (idx, pred) =>
    hyps'.modify idx fun (name, _) => (name, pred)
  let hypsExpr ← toHypsList hypTy hyps
  return some <| ← mkAppOptM ``Entails #[some σ, some hypsExpr, some goal]

private def restorePartiallyHiddenGoals (contFVar : FVarId) : TacticM Unit := do
  let gs ← getGoals
  let gs' ← gs.mapM fun g => g.withContext do
    unless (← getLCtx).contains contFVar do
      return g
    let target ← cleanupAnnotAndMore (← g.getType)
    -- NOTE: `zetaDeltaFVars` seems good to use, so instead of `revert`,
    -- first do `zetaDeltaFVars` and then `clear`
    let target ← zetaDeltaFVars target #[contFVar]
    let g' ← g.change target
    let g' ← g'.clear contFVar
    if let some newTarget ← unfoldPartialHiddenTarget target then
      let g'' ← g'.change newTarget
      pure g''
    else
      pure g'
  setGoals gs'

private def exposeSelectedLocations (hypsExpr goal : Expr)
    (hyps : List (String × Expr)) (loc : RewriteLocation) (mainGoal : MVarId) :
    TacticM (FVarId × MVarId) := do
  let predTy ← inferType goal
  let idxs := loc.idxs.toList
  let preds := idxs.filterMap fun idx => hyps[idx]?.map Prod.snd   -- Should not fail since `parseRewriteLocation` checks the indices
  let predsExpr ← mkListLit predTy preds
  let idxsExpr := toExpr idxs
  let predsTy ← mkAppM ``List #[predTy]
  let contVal ← withLocalDeclD `preds predsTy fun predsVar => do
    if loc.includeGoal then
      withLocalDeclD `goal predTy fun goalVar => do
        let body ← mkAppOptM ``EntailsWithSomePredsExtractedOut
          #[none, some hypsExpr, some idxsExpr, some predsVar, some goalVar]
        mkLambdaFVars #[predsVar, goalVar] body
    else
      let body ← mkAppOptM ``EntailsWithSomePredsExtractedOut
        #[none, some hypsExpr, some idxsExpr, some predsVar, some goal]
      mkLambdaFVars #[predsVar] body
  let contName ← mainGoal.withContext do mkFreshUserName `cont
  let (contFVar, g') ← «let» mainGoal contName contVal
  let g'' ← g'.withContext do
    let cont := mkFVar contFVar
    let newTarget := if loc.includeGoal then mkApp2 cont predsExpr goal else mkApp cont predsExpr
    g'.change newTarget
  return (contFVar, g'')

/-- Expose the proof-mode locations selected by Lean's location syntax, run `k`,
then restore all generated goals back from the local-`let` view to `Entails`.
The continuation receives the parsed locations for rewrite-specific bookkeeping;
this helper is intentionally private to `tla_rewrite`. -/
private def withExposedLocations (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (k : RewriteLocation → TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target
    | throwError "tla_rewrite: goal is not an Entails sequent, but {target}"
  let some (_, hyps) ← recognizeEntailsHyps target
    | throwError "tla_rewrite: failed to read the hypotheses from the goal"
  let loc ← parseRewriteLocation hyps loc? "tla_rewrite"
  let (contFVar, g') ← exposeSelectedLocations hypsExpr goal hyps loc g
  replaceMainGoal [g']
  g'.withContext <| k loc
  restorePartiallyHiddenGoals contFVar

syntax (name := tlaRewrite) "tla_rewrite" optConfig rwRuleSeq (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| tla_rewrite $cfg:optConfig $rules:rwRuleSeq $[$loc]?) => do
    withExposedLocations loc fun _ => do
      evalTactic <| ← `(tactic| rewrite $cfg:optConfig $rules:rwRuleSeq)

end TLA.ProofMode
