import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_drop_hyps {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (subHyps : List (NamedPred σ)) (hinc : subHyps.map NamedPred.pred ⊆ hyps.map NamedPred.pred) :
  Entails subHyps goal → Entails hyps goal := by
  intro h
  refine pred_implies_trans ?_ (by apply h) ; clear h
  apply repeatedAnd_subset_implies ; exact hinc

theorem Entails_clear {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toClear : List String) :
  letI hyps' := hyps.filter fun h => !toClear.contains h.name
  Entails hyps' goal → Entails hyps goal := Entails_drop_hyps _ (by grind)

syntax (name := tlaClearTac) "tla_clear" (ppSpace colGt ident)+ : tactic

private def clearTacDSimps := #[``List.filter, ``List.contains, ``List.elem, ``or, ``and, ``not,
  ``String.reduceBEq, ``String.reduceBNe, ``Bool.false_or, ``Bool.or_false]

elab_rules : tactic
  | `(tactic| tla_clear $[$names:ident]*) => do
    let toClear := names.toList.map fun name => toString name.getId
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_clear) ($(quote toClear)) ?_)
    postDSimpAfterApplyingReflectionTheorem clearTacDSimps

end TLA.ProofMode
