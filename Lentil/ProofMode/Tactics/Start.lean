import Lentil.ProofMode.Basic
import Lentil.Expr

namespace TLA.ProofMode

open Lean Meta Elab Tactic

private def sequent? (e : Expr) : Option (Expr × Expr × Expr) :=
  match_expr e with
  | TLA.pred_implies σ lhs rhs => some (σ, lhs, rhs)
  | _ => none

private def getPremiseList (lhs : Expr) : MetaM (List Expr) := do
  if lhs.isAppOfArity' ``TLA.tla_true 1 then pure [] else TLA.Expr.splitAndIntoParts lhs

private def mkNamedPredListExpr (σ : Expr) (hyps : List (String × Expr)) : MetaM Expr := do
  let elemTy ← mkAppM ``TLA.ProofMode.NamedPred #[σ]
  toHypsList elemTy hyps

syntax (name := tlaStartTac) "tla_start" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| tla_start $[$names:ident]*) => do
    -- Get input labels
    let lbls := names.toList.map fun name => toString name.getId
    if LentilLib.List.containsDuplicateElemHashable lbls then
      throwError "tla_start hypothesis names must be distinct"
    -- Build the new goal view
    let mainGoal ← getMainGoal
    let ty ← mainGoal.getType
    let ty ← cleanupAnnotAndMore ty
    let some (σ, lhs, rhs) := sequent? ty |
      throwError "tla_start only supports goals reduced to a single |-tla- sequent, but got {ty}"
    let hyps ← getPremiseList lhs
    unless hyps.length == lbls.length do
      throwError "tla_start expected {hyps.length} names, but got {lbls.length}"
    let namedHyps ← mkNamedPredListExpr σ <| lbls.zip hyps
    let pmTarget ← mkAppM ``TLA.ProofMode.Entails #[namedHyps, rhs]
    -- Build the proof for the new goal
    -- ... well, the proof is refl!
    let g' ← mainGoal.change pmTarget
    replaceMainGoal [g']

end TLA.ProofMode
