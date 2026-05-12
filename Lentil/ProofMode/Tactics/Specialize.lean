import Lentil.ProofMode.Basic
import Lentil.ProofMode.Tactics.Intro
import Lentil.ProofMode.Tactics.Apply

namespace TLA.ProofMode

open Lean Meta Elab Tactic

def replaceChosenPred {σ : Type u} (hyps : List (NamedPred σ)) (chosen : String) (newPred : pred σ) :=
  modifyHypByName hyps chosen fun ⟨name, _⟩ => ⟨name, newPred⟩

theorem Entails_specializeHyp {σ : Type u} {hyps : List (NamedPred σ)}
  (subHyps : List (pred σ)) (hinc : subHyps ⊆ hyps.map NamedPred.pred)
  {goal newHyp : pred σ} (chosen : String) :
  ((repeatedAnd subHyps)) |-tla- (newHyp) →
  Entails (replaceChosenPred hyps chosen newHyp) goal →
  Entails hyps goal := by
  intro h1 h2
  unfold replaceChosenPred modifyHypByName at h2
  cases hidx : hyps.findIdx? (fun h => h.name == chosen) with
  | none => rw [hidx] at h2 ; exact h2
  | some idx =>
    rw [hidx] at h2 ; dsimp only [Option.elim] at h2
    apply Entails_add_new (newHypName := chosen)
    on_goal 2=> apply h1
    on_goal 1=> exact hinc
    unfold Entails
    have hidx' := hidx ; rw [List.findIdx?_eq_some_iff_getElem] at hidx'
    rcases hidx' with ⟨hidx', hname, -⟩ ; simp at hname
    have htmp2 := repeatedAnd_modifyHyp_reorder hyps _ hidx' (fun ⟨name, _⟩ => NamedPred.mk name newHyp)
    dsimp only at htmp2
    simp only [List.map_append, repeatedAnd_append, List.map_singleton, repeatedAnd_singleton, htmp2]
    apply impl_drop_hyp_one_r ; exact h2

theorem Entails_specialize_forall {σ : Type u} {hyps : List (NamedPred σ)}
    {goal : pred σ} (chosen : String)
    {α : Type v} {p : α → pred σ} (witness : α)
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, TLA.tla_forall p⟩) :
    Entails (replaceChosenPred hyps chosen (p witness)) goal → Entails hyps goal := by
  apply Entails_specializeHyp (subHyps := [TLA.tla_forall p])
  · grind
  · simp [repeatedAnd_singleton] ; tla_unfold_simp ; grind

theorem Entails_specialize_temporal {σ : Type u} {hyps : List (NamedPred σ)}
    {goal lhs rhs : pred σ} (chosen premise : String)
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, [tlafml| lhs → rhs]⟩)
    (hprem : hyps.find? (fun h => h.name == premise) = some ⟨premise, lhs⟩) :
    Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal := by
  apply Entails_specializeHyp (subHyps := [lhs, [tlafml| lhs → rhs]])
  · grind
  · simp [repeatedAnd, LentilLib.List.foldrD] ; tla_unfold_simp ; grind

theorem Entails_specialize_pure {σ : Type u} {hyps : List (NamedPred σ)}
    {goal rhs : pred σ} {q : Prop} (chosen : String) (hq : q)
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, [tlafml| ⌞ q ⌟ → rhs]⟩) :
    Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal := by
  apply Entails_specializeHyp (subHyps := [[tlafml| ⌞ q ⌟ → rhs]])
  · grind
  · simp [repeatedAnd_singleton] ; tla_unfold_simp ; grind

private def specializeTacDSimps := #[``replaceChosenPred, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go,
  ``String.reduceBEq, ``String.reduceBNe, ``dreduceIte, ``Option.elim,
  ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx, ``List.modifyTailIdx.go,
  ``List.modifyHead]

private def termIdent? (stx : TSyntax `term) : TacticM (Option (TSyntax `ident)) := do
  match stx with
  | `(term| $id:ident) => pure (some id)
  | _ => pure none

private def tlaSpecializeStep (chosen : String) (arg : TSyntax `term) : TacticM Unit := withMainContext do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | throwError "tla_specialize: failed to read the hypotheses from the goal"
  let some (_, pred) := hyps.find? (fun ⟨n, _⟩ => n == chosen) | throwError "tla_specialize: hypothesis '{chosen}' not found in the goal's Entails list"
  match_expr pred with
  | TLA.tla_forall _ _ _ =>
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_specialize_forall) ($(quote chosen)) $arg (by rfl) ?_)
  | TLA.tla_implies _ lhs _ =>
    match ← termIdent? arg with
    | some id =>
      match (← getLCtx).findFromUserName? id.getId with
      | some decl =>
        unless ← Meta.isProp decl.type do
          throwError "tla_specialize: Lean-local argument '{id.getId}' is not a proof"
        unless lhs.isAppOfArity' ``TLA.pure_pred 2 do
          throwError "tla_specialize: Lean-local argument '{id.getId}' can only specialize a pure antecedent; got {lhs}"
        evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_specialize_pure) ($(quote chosen)) (by exact $arg) (by rfl) ?_)
      | none =>
        let argName := toString id.getId
        let some (_, argPred) := hyps.find? (fun ⟨n, _⟩ => n == argName) |
          throwError "tla_specialize: temporal hypothesis '{argName}' not found in the goal's Entails list"
        unless ← Meta.isDefEq lhs argPred do
          throwError "tla_specialize: temporal hypothesis '{argName}' has predicate {argPred}, but expected {lhs}"
        evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_specialize_temporal)
            ($(quote chosen)) ($(quote argName)) (by rfl) (by rfl) ?_)
    | none => throwError "tla_specialize: implication arguments must be a Lean-local proof or a proof-mode hypothesis name"
  | _ => throwError "tla_specialize: hypothesis '{chosen}' is not a ∀ or implication; got {pred}"
  postDSimpAfterApplyingReflectionTheorem specializeTacDSimps

syntax (name := tlaSpecializeTac) "tla_specialize" (ppSpace colGt ident) (ppSpace colGt term:arg)+ : tactic

elab_rules : tactic
  | `(tactic| tla_specialize $h:ident $[$args:term]*) => do
    let chosen := toString h.getId
    for arg in args do
      tlaSpecializeStep chosen arg

end TLA.ProofMode
