import Lentil.ProofMode.Basic
import Lentil.ProofMode.Tactics.Clear

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_trans {σ : Type u} {hyps : List (NamedPred σ)} {mid goal : pred σ} :
  (mid) |-tla- (goal) → Entails hyps mid → Entails hyps goal := by
  intro h1 h2 ; revert h1 ; revert h2 ; apply pred_implies_trans

/-- The general thing used in `apply`, `have` and `suffices`. -/
theorem Entails_add_new {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (subHyps : List (pred σ)) (hinc : subHyps ⊆ hyps.map NamedPred.pred)
  (newHypName : String) (newHyp : pred σ) :
  ((repeatedAnd subHyps)) |-tla- (newHyp) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by
  intro h1 h2
  refine pred_implies_trans ?_ (by apply h2) ; clear h2
  simp [repeatedAnd_append, and_pred_implies_split] ; constructor
  · rfl
  · refine pred_implies_trans ?_ (by apply h1) ; clear h1
    apply repeatedAnd_subset_implies ; grind

-- CHECK Maybe working on `chosen.map Prod.fst` would be better?
def chooseHyps (hyps : List (NamedPred σ)) (chosen : List (String × Bool)) : List (pred σ) :=
  chosen.filterMap fun (name, _) => Option.map NamedPred.pred <| hyps.find? fun h => h.name == name

theorem chosenHyps_subset (hyps : List (NamedPred σ)) (chosen : List (String × Bool)) :
  chooseHyps hyps chosen ⊆ hyps.map NamedPred.pred := by
  unfold chooseHyps ; rw [List.subset_def]
  simp only [List.mem_filterMap, Option.map_eq_some_iff, List.mem_map]
  grind

theorem Entails_apply_forward_noclear {σ : Type u} {hyps : List (NamedPred σ)} {newHyp goal : pred σ}
  (newHypName : String) (chosen : List (String × Bool)) :
  ((repeatedAnd <| chooseHyps hyps chosen)) |-tla- (newHyp) →
  -- NOTE: If we add the new hypothesis at the beginning then the diff in the
  -- info view will look very weird, so we add it at the end instead.
  -- This of course is going to have worse time complexity, but since
  -- the computation of `hyps'` is already linear, so anyway ...
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_add_new _ (chosenHyps_subset _ _) newHypName newHyp

theorem Entails_apply_forward {σ : Type u} {hyps : List (NamedPred σ)} {newHyp goal : pred σ}
  (newHypName : String) (chosen : List (String × Bool)) :
  letI hyps' := hyps.filter fun h => chosen.all fun (name, toClear) => h.name != name || !toClear
  ((repeatedAnd <| chooseHyps hyps chosen)) |-tla- (newHyp) →
  Entails (hyps' ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by
  intro h1 h2 ; apply Entails_apply_forward_noclear (newHypName := newHypName) ; apply h1
  revert h2 ; apply Entails_drop_hyps ; grind

private def applyTacDSimps := #[``List.filter, ``List.all, ``or, ``and, ``not, ``chooseHyps, ``List.filterMap,
  ``Option.map, ``List.find?, ``repeatedAnd, ``LentilLib.List.foldrD,
  ``String.reduceBEq, ``String.reduceBNe, ``List.cons_append, ``List.nil_append]

syntax (name := tlaApplyBackwardTac) "tla_apply " term : tactic
syntax tlaApplyForwardPremise := ppSpace colGt ("-")? ident
syntax (name := tlaApplyForwardTac) "tla_apply " term " at " tlaApplyForwardPremise+ " as " ident : tactic

elab_rules : tactic
  | `(tactic| tla_apply $tm:term) => withMainContext do
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_trans) (by apply $tm) ?_)
  | `(tactic| tla_apply $tm:term at $locs:tlaApplyForwardPremise* as $out:ident) => do
    -- FIXME: should prohibit `out` taking existing name
    let chosen ← locs.mapM fun l =>
      match l with
      | `(tlaApplyForwardPremise| -$name:ident) => pure (toString name.getId, true)
      | `(tlaApplyForwardPremise| $name:ident) => pure (toString name.getId, false)
      | _ => throwUnsupportedSyntax
    let newHypName := toString out.getId
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_apply_forward) ($(quote newHypName)) ($(quote chosen.toList)) (by apply $tm) ?_)
    postDSimpAfterApplyingReflectionTheorem applyTacDSimps

end TLA.ProofMode
