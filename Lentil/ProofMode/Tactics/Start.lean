module

public import Lentil.ProofMode.Basic
public import Lentil.Expr

public meta section

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

private def sequent? (e : Expr) : Option (Expr × Expr × Expr) :=
  match_expr e with
  | Lentil.pred_implies σ lhs rhs => some (σ, lhs, rhs)
  | _ => none

private def getPremiseList (lhs : Expr) : MetaM (List Expr) := do
  if lhs.isAppOfArity' ``Lentil.tl_true 1 then pure [] else Lentil.Expr.splitAndIntoParts lhs

private def mkNamedPredListExpr (σ : Expr) (hyps : List (String × Expr)) : MetaM Expr := do
  let elemTy ← mkAppM ``Lentil.ProofMode.NamedPred #[σ]
  toHypsList elemTy hyps

/--
`tstart h₁ h₂ ...` enters proof mode for a raw LTL sequent. It splits the
left-hand side conjunction into named temporal hypotheses and keeps the right
hand side as the proof-mode goal.

For example, from a raw goal `(p ∧ q) |-tl- r`,
```lean
tstart hp hq
```
changes the proof state to a proof-mode context with `hp : p`, `hq : q`, and
goal `r`.
-/
syntax (name := tlStartTac) "tstart" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| tstart $[$names:ident]*) => withMainContext do
    -- Get input labels
    let lbls := names.toList.map fun name => toString name.getId
    if LentilLib.List.containsDuplicateElemHashable lbls then
      throwError "tstart hypothesis names must be distinct"
    -- Build the new goal view
    let mainGoal ← getMainGoal
    let ty ← mainGoal.getType
    let ty ← cleanupAnnotAndMore ty
    let some (σ, lhs, rhs) := sequent? ty |
      throwError "tstart only supports goals reduced to a single |-tl- sequent, but got {ty}"
    let hyps ← getPremiseList lhs
    unless hyps.length == lbls.length do
      throwError "tstart expected {hyps.length} names, but got {lbls.length}"
    let namedHyps ← mkNamedPredListExpr σ <| lbls.zip hyps
    let pmTarget ← mkAppM ``Lentil.ProofMode.Entails #[namedHyps, rhs]
    -- Build the proof for the new goal
    -- ... well, the proof is refl!
    let g' ← mainGoal.change pmTarget
    replaceMainGoal [g']

end Lentil.ProofMode
