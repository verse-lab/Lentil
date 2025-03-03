import Lean
import Lentil.Tactics.Basic

open Lean

namespace TLA

open Elab Tactic Meta

-- FIXME: is there any better way? something like `findAll?`?
partial def generalizeExecStatesAuxFinder (e typ : Expr) (visited : List Expr) : List Expr :=
  match typ.find? (fun e' => match e' with
    | .app e1 e2 => e1 == e && !e2.hasLooseBVars && !(visited.contains e2)
    | _ => false) with
  | some res => generalizeExecStatesAuxFinder e typ (res.appArg! :: visited)  -- `visited` only keeps `e2`
  | none => visited.map (mkApp e)

partial def generalizeExecStatesAux (e typ : Expr) (mv : MVarId) : MetaM MVarId := do
  let targets := generalizeExecStatesAuxFinder e typ []
  if targets.isEmpty then return mv
  mv.withContext do
    -- use the underlying meta program for `generalize` tactic
    -- some code are taken from `evalGeneralize`
    let ss ← Array.range targets.length |>.mapM fun x => do mkFreshUserName <| Name.mkSimple <| "s" ++ ⟨List.replicate x '\''⟩
    let args : Array GeneralizeArg := ss.zip targets.toArray |>.map fun (s, expr) => { expr, xName? := s }
    let hyps := ((← getLocalHyps).map (·.fvarId!))
    let (_, _, mv') ← mv.generalizeHyp args hyps
    pure mv'

/-- Find all occurrences like `e k` where `k` is "closed" (e.g., does not contain
    bounded variables), and generalize them. -/
partial def generalizeExecStates (e : Expr) : TacticM Unit := withMainContext do
  -- do for the goal
  let g ← getMainTarget >>= instantiateMVars
  let mv' ← generalizeExecStatesAux e g (← getMainGoal)
  replaceMainGoal [mv']
  -- do for the hypotheses
  withMainContext do
  let hyps ← getLCtx
  for hyp in hyps do
    if !hyp.isImplementationDetail then
      let mv' ← generalizeExecStatesAux e hyp.type (← getMainGoal)
      replaceMainGoal [mv']

/-- This tactic attempts to simplify the goal `e |=tla= q` when the goal only
    depends on a finite (and hopefully length-fixed) part of `e`.
    For example, when `q` is `□ ⌜ a ⌝`, then after unfolding the definitions,
    the goal reduces to `∀ k, a (e k)`, which only depends on `e k` (a single state).

    This tactic makes the following assumptions, for which the user is responsible
    to ensure before applying this tactic:
    - After reducing the goal, the timestamps that `e` applies to are at the
      leading position. For example, `e |=tla= □ ⌜ a ⌝` reduces to `∀ k, a (e k)`,
      where `k` is at the leading position.
    - Similar condition applies to the premises in the form of `e |=tla= p`.

    Currently, this tactic only handles simple cases, so it additionally assumes
    that the goal and the premises have at most one timestamp variable universally
    quantified at the leading position. -/
partial def elabSimpFiniteExecTLAGoal : TacticM Unit := do
  withMainContext do
    evalTactic $ ← `(tactic| try simp [exec.satisfies] at * )
  withMainContext do
  let g ← getMainTarget >>= instantiateMVars
  let g := g.cleanupAnnotations
  if !g.isApp then throwError "the goal should be an application"
  let e := g.appArg!
  let k ← mkIdent <$> mkFreshUserName `k
  -- (1) do some initial simplification
  -- `simp at *` is for simplifying the arithmetic things like `0 + k = k`
  evalTactic $ ← `(tactic| tla_unfold_simp' ; (try simp at *) ; intro $k:ident )
  -- (2) find all premises that accept a timestamp variable and `specialize` them
  -- TODO it sometimes requires having multiple instantiations, like `k`, `k + 1`, etc.
  withMainContext do
  let hyps ← getLCtx
  for hyp in hyps do
    if !hyp.isImplementationDetail then forallTelescope hyp.type fun xs body => do
      -- only consider that there is 1 universally quantified timestamp variable
      if xs.size >= 1 then
        let x := xs[0]! |>.fvarId!
        if (← isDefEq (mkConst ``Nat) (← inferType xs[0]!)) then
          -- check if `e` is applied to that timestamp variable
          if body.find? (fun e' => match e' with
            | .app e1 e2 => e1 == e && e2.containsFVar x
            | _ => false) |>.isSome then
            evalTactic $ ← `(tactic| specialize $(mkIdent hyp.userName) $k:ident )
  -- (3) normalize the arithmetic expressions in the form of `n + k` to `k + n`
  -- after doing various `simp`, we should be able to assume that there won't be
  -- expressions like `(1 + (1 + k))` or `(0 + k)`
  withMainContext do
    evalTactic $ ← `(tactic| (repeat rw [← $(mkIdent ``Nat.add_comm) $k] at *) )
  -- (4) generalize states like `e k` and `e (k + 1)` to `s` and `s'`, etc.
  generalizeExecStates e
  -- (5) clear the hypotheses which contain `e`
  -- since at this stage, if the goal is truly "finite", then `e` should be nowhere
  -- or maybe the goal becomes "finite" after clearing
  withMainContext do
    if Expr.occurs (← getMainTarget) e then
      throwTacticEx `simp_finite_exec_goal (← getMainGoal)
  -- the following code is taken from `Mathlib/Tactic/ClearExcept.lean`
  liftMetaTactic1 fun mv => do
    let mut toClear : Array FVarId := #[]
    for decl in ← getLCtx do
      if Expr.occurs decl.type e then
        toClear := toClear.push decl.fvarId
    mv.tryClearMany toClear

end TLA

@[inherit_doc TLA.elabSimpFiniteExecTLAGoal]
syntax "simp_finite_exec_goal" : tactic

elab_rules : tactic
  | `(tactic| simp_finite_exec_goal ) => TLA.elabSimpFiniteExecTLAGoal
