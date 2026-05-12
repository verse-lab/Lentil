import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

def renameHyp {σ : Type u} (hyps : List (NamedPred σ)) (oldName newName : String) :=
  modifyHypByName hyps oldName fun ⟨_, pred⟩ => ⟨newName, pred⟩

theorem renameHyp_pred_same {σ : Type u} (hyps : List (NamedPred σ)) (oldName newName : String) :
  (renameHyp hyps oldName newName).map NamedPred.pred = hyps.map NamedPred.pred := by
  unfold renameHyp modifyHypByName
  cases hidx : hyps.findIdx? (fun h => h.name == oldName) with
  | none => rfl
  | some idx =>
    have hidx' := hidx ; rw [List.findIdx?_eq_some_iff_findIdx_eq] at hidx'
    replace hidx' := hidx'.left
    dsimp only [Option.elim] ; rw [List.modify_eq_take_cons_drop hidx']
    conv => enter [2, 2] ; rw [← LentilLib.List.take_getElem_drop hidx']
    simp only [List.map_append, List.map_take, List.map_cons, List.map_drop]

theorem Entails_rename {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (oldName newName : String) :
  Entails (renameHyp hyps oldName newName) goal = Entails hyps goal := by
  unfold Entails ; congr 1 ; rw [renameHyp_pred_same]

private def renameTacDSimps := #[``renameHyp, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go, ``String.reduceBEq, ``String.reduceBNe,
    ``dreduceIte, ``Option.elim, ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx,
    ``List.modifyTailIdx.go, ``List.modifyHead]

syntax (name := tlaRenameTac) "tla_rename" (ppSpace colGt ident) " => " ident : tactic

elab_rules : tactic
  | `(tactic| tla_rename $old:ident => $new:ident) => do
    let oldStr := toString old.getId
    let newStr := toString new.getId
    evalTactic <| ← `(tactic|
      refine ($(mkIdent ``Entails_rename) ($(quote oldStr)) ($(quote newStr))).$(mkIdent `mp) ?_)
    postDSimpAfterApplyingReflectionTheorem renameTacDSimps

end TLA.ProofMode
