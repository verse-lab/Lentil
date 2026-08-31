import Lean.Meta.Tactic.Generalize
import Lean.Meta.CollectFVars
import Lean.Elab.Tactic.Config
import Lentil.ProofMode.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

/-- How `tcoalesce_to_ptl` treats binders while collecting PTL atoms. -/
inductive CoalesceBinderMode where
  /-- Abstract quantifiers and big operators as single coalescing atoms. -/
  | block
  /-- Keep binders in the PTL skeleton and collect atoms inside their bodies. -/
  | ignore
deriving BEq, Inhabited

/-- How much temporal structure `tcoalesce_to_ptl` preserves. -/
inductive CoalesceAbstractLevel where
  /-- Abstract only first-order leaves such as state, action, pure, and enabled predicates. -/
  | leaves
  /-- Abstract the immediate arguments of modal operators. -/
  | modal
  /-- Abstract each whole formula position as one atom. -/
  | formula
deriving BEq, Inhabited

structure CoalesceConfig where
  /-- Whether quantifiers and big operators are abstracted as atoms or traversed. -/
  binders : CoalesceBinderMode := .block
  /-- How much temporal structure to keep before abstracting subformulas. -/
  level : CoalesceAbstractLevel := .leaves
  /-- Also abstract opaque `pred σ` terms that are not recognized first-order leaves. -/
  abstractOpaque : Bool := false
  -- FIXME: Allow customizing the list; before having that we disable this
  -- /-- Unfold derived temporal operators before collecting coalescing blocks. -/
  -- unfoldDerived : Bool := true

declare_config_elab elabCoalesceConfig CoalesceConfig

-- FIXME: In principle the following two should also be customizable
private def coalesceLeafHeads : List Name := [
  ``Lentil.state_pred,
  ``Lentil.action_pred,
  ``Lentil.pure_pred,
  ``Lentil.tl_enabled
]

private def coalesceBinderHeads : List Name := [
  ``Lentil.tl_forall,
  ``Lentil.tl_exists,
  ``Lentil.tl_bigwedge,
  ``Lentil.tl_bigvee
]

private def hasAnyHead (heads : List Name) (p : Expr) : Bool :=
  heads.any p.getAppFn'.isConstOf

private def isCoalesceLeafHead (p : Expr) : Bool :=
  hasAnyHead coalesceLeafHeads p

private def isCoalesceBinderHead (p : Expr) : Bool :=
  hasAnyHead coalesceBinderHeads p

private def shouldAbstractBlock (cfg : CoalesceConfig) (p : Expr) : Bool :=
  isCoalesceLeafHead p || (isCoalesceBinderHead p && cfg.binders == .block)

private structure CollectResult where
  blocks : Array Expr
  expr : Expr

-- CHECK I guess caching would be useful somewhere below

private def usedBoundFVars (bound : Array Expr) (e : Expr) : MetaM (Array Expr) := do
  let (_, used) ← e.collectFVars.run ({} : CollectFVars.State)
  let used ← used.addDependencies
  return bound.filter fun fvar => fvar.isFVar && used.fvarSet.contains fvar.fvarId!

private def exposeBlock (bound : Array Expr) (p : Expr) : MetaM (Expr × Expr) := do
  let used ← usedBoundFVars bound p
  let block ← mkLambdaFVars used p
  return (block, mkAppN block used)

/--
Collect maximal non-PTL formula blocks below a propositional temporal skeleton.

The PTL atoms stay at type `pred σ` in Lentil's shallow embedding. The config
controls where the walker stops: at concrete first-order leaves, at modal
arguments, or at whole formula positions.
-/
private partial def collectPTLBlocks (cfg : CoalesceConfig) (bound : Array Expr) (p : Expr) :
    MetaM CollectResult := do
  if cfg.level == .formula || shouldAbstractBlock cfg p then
    let res ← collectTerminalPosition p
    return res
  -- FIXME: The following is too specific for LTL
  match_expr p with
  | Lentil.tl_not _ p =>
    collectUnary ``Lentil.tl_not p
  | Lentil.tl_and _ p q => collectBinary ``Lentil.tl_and p q
  | Lentil.tl_or _ p q => collectBinary ``Lentil.tl_or p q
  | Lentil.tl_implies _ p q => collectBinary ``Lentil.tl_implies p q
  | Lentil.tl_forall _ _ p => collectBinder ``Lentil.tl_forall p
  | Lentil.tl_exists _ _ p => collectBinder ``Lentil.tl_exists p
  -- NOTE: Design choice: big op should be first turned into `forall`/`exists`
  /-
  | Lentil.tl_bigwedge _ _ _ _ p s => collectBigOp ``Lentil.tl_bigwedge p s
  | Lentil.tl_bigvee _ _ _ _ p s => collectBigOp ``Lentil.tl_bigvee p s
  -/
  | Lentil.always _ p => collectModal ``Lentil.always p
  | Lentil.eventually _ p => collectModal ``Lentil.eventually p
  | Lentil.later _ p => collectModal ``Lentil.later p
  | Lentil.tl_until _ p q => collectBinary ``Lentil.tl_until p q
  | _ =>
    -- Opaque `pred σ` terms already behave like propositional temporal atoms
    -- unless the user asks to refresh them into fresh coalescing atoms.
    if cfg.abstractOpaque then
      let res ← collectTerminalPosition p
      return res
    else
      return ⟨#[], p⟩
where
  -- FIXME: The following usages of `mkAppM` should be optimized away?
  collectUnary (op : Name) (p : Expr) : MetaM CollectResult := do
    let r ← collectPTLBlocks cfg bound p
    return ⟨r.blocks, ← mkAppM op #[r.expr]⟩
  collectBinary (op : Name) (p q : Expr) : MetaM CollectResult := do
    let rp ← collectPTLBlocks cfg bound p
    let rq ← collectPTLBlocks cfg bound q
    return ⟨rp.blocks ++ rq.blocks, ← mkAppM op #[rp.expr, rq.expr]⟩
  collectModal (op : Name) (p : Expr) : MetaM CollectResult := do
    if cfg.level == .modal then
      let (block, expr) ← exposeBlock bound p
      return ⟨#[block], ← mkAppM op #[expr]⟩
    else
      collectUnary op p
  collectBinder (op : Name) (p : Expr) : MetaM CollectResult := do
    lambdaTelescope p fun xs body => do
      if xs.isEmpty then
        return ⟨#[], ← mkAppM op #[p]⟩
      let r ← collectPTLBlocks cfg (bound ++ xs) body
      let p' ← mkLambdaFVars xs r.expr
      return ⟨r.blocks, ← mkAppM op #[p']⟩
  /-
  collectBigOp (op : Name) (p s : Expr) : MetaM CollectResult := do
    lambdaTelescope p fun xs body => do
      if xs.isEmpty then
        return ⟨#[], ← mkAppM op #[p, s]⟩
      let r ← collectPTLBlocks cfg (bound ++ xs) body
      let p' ← mkLambdaFVars xs r.expr
      return ⟨r.blocks, ← mkAppM op #[p', s]⟩
  -/
  collectTerminalPosition (p : Expr) : MetaM CollectResult := do
    let (block, expr) ← exposeBlock bound p
    return ⟨#[block], expr⟩

private def collectGoalBlocks (cfg : CoalesceConfig) (target : Expr) : MetaM CollectResult := do
  match_expr target with
  | Lentil.valid _ p =>
    let r ← collectPTLBlocks cfg #[] p
    return ⟨r.blocks, ← mkAppM ``Lentil.valid #[r.expr]⟩
  | Lentil.pred_implies _ p q =>
    let rp ← collectPTLBlocks cfg #[] p
    let rq ← collectPTLBlocks cfg #[] q
    return ⟨rp.blocks ++ rq.blocks, ← mkAppM ``Lentil.pred_implies #[rp.expr, rq.expr]⟩
  | Entails _ hyps goal => collectEntailsBlocks cfg hyps goal
  | _ => throwError "tcoalesce_to_ptl: expected a LTL validity goal, raw LTL sequent, or proof-mode Entails goal"
where collectEntailsBlocks (cfg : CoalesceConfig) (hypsExpr goal : Expr) : MetaM CollectResult := do
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tcoalesce_to_ptl: proof-mode hypotheses are not in canonical literal-list form"
  let (hypBlocks, hyps') ←
    hyps.foldlM (init := ((#[] : Array Expr), (#[] : Array (String × Expr))))
      fun (blocks, hyps') (name, pred) => do
        let r ← collectPTLBlocks cfg #[] pred
        return (blocks ++ r.blocks, hyps'.push (name, r.expr))
  let rGoal ← collectPTLBlocks cfg #[] goal
  let hypsExpr' ← toHypsList hypTy hyps'.toList
  return ⟨hypBlocks ++ rGoal.blocks, ← mkAppM ``Entails #[hypsExpr', rGoal.expr]⟩

private def ensureSupportedGoalShape (target : Expr) : MetaM Unit := do
  match_expr target with
  | Lentil.valid _ _ => pure ()
  | Lentil.pred_implies _ _ _ => pure ()
  | Entails _ _ _ => pure ()
  | _ => throwError "tcoalesce_to_ptl: expected a LTL validity goal, raw LTL sequent, or proof-mode Entails goal"

private def dedupBlocks (blocks : Array Expr) : MetaM (Array Expr) :=
  blocks.foldlM (init := #[]) fun seen block => do
    if ← seen.anyM fun old => isDefEq old block then
      return seen
    else
      return seen.push block

/-
private def unfoldDerivedTemporalHeads : TacticM Unit := do
  evalTactic <| ← `(tactic|
    try dsimp only [Lentil.leads_to, Lentil.always_implies, Lentil.weak_fairness])
-/

private def coalesceToPTL (cfg : CoalesceConfig) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← g.getType
  let target ← cleanupAnnotAndMore target
  ensureSupportedGoalShape target
  /-
  if cfg.unfoldDerived then
    unfoldDerivedTemporalHeads
  -/
  let collected ← collectGoalBlocks cfg target
  let blocks ← dedupBlocks collected.blocks
  if blocks.isEmpty then
    throwError "tcoalesce_to_ptl: found no non-PTL predicate blocks to abstract"
  let g ← g.change collected.expr
  let args := blocks.map fun block =>
    { expr := block, xName? := some `ptlAtom : GeneralizeArg }
  -- `generalize` leaves a stronger obligation over arbitrary fresh atoms.
  -- Specializing those atoms back to the original blocks recovers the goal.
  let (_, g') ← g.generalize args
  replaceMainGoal [g']

/--
`tcoalesce_to_ptl` abstracts formula blocks from a LTL goal and keeps the
requested amount of propositional temporal skeleton.

It supports raw validity goals, raw LTL sequents, and proof-mode `Entails`
goals. The resulting fresh atoms are arbitrary `pred σ` values, so subsequent
steps can reason propositionally about the remaining temporal structure.

Granularity options:
* `level := .leaves` abstracts concrete first-order leaves. This is the default.
* `level := .modal` abstracts immediate arguments of temporal operators.
* `level := .formula` abstracts each whole hypothesis/goal formula.
* `binders := .block` abstracts quantifiers and big operators as blocks. This is
  the default.
* `binders := .ignore` keeps quantifiers and big operators while coalescing
  blocks inside their bodies.
* `abstractOpaque := true` also abstracts opaque `pred σ` leaves.
* `unfoldDerived := false` leaves derived temporal definitions opaque.
-/
syntax (name := tlCoalesceToPTLTac) "tcoalesce_to_ptl" optConfig : tactic

elab_rules : tactic
  | `(tactic| tcoalesce_to_ptl $cfg:optConfig) => do
    coalesceToPTL (← elabCoalesceConfig cfg)

end Lentil.ProofMode
