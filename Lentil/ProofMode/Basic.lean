import Lentil.Rules.BigOp

namespace TLA.ProofMode

open TLA LentilLib

structure NamedPred (σ : Type u) where
  name : String
  pred : pred σ

-- FIXME: How to unify this with `tla_bigwedge`?
def repeatedAnd (ps : List (pred σ)) : pred σ := (List.foldrD tla_and tla_true ps)

-- FIXME: This is not satisfactory ...
theorem repeatedAnd_eq_bigwedge (ps : List (pred σ)) :
  ((repeatedAnd ps)) =tla= (⋀ x ∈ ps, x) := by
  dsimp [tla_bigwedge, Foldable.fold]
  rw [← List.foldrD_eq_foldr]
  · rfl
  · apply and_true

theorem repeatedAnd_eq_in_iff (ps1 ps2 : List (pred σ)) (h : ∀ p, p ∈ ps1 ↔ p ∈ ps2) :
  ((repeatedAnd ps1)) =tla= ((repeatedAnd ps2)) := by
  simp [repeatedAnd_eq_bigwedge, bigwedge_forall_list, h]

theorem repeatedAnd_singleton (p : pred σ) : repeatedAnd [p] = p := rfl

theorem repeatedAnd_append (ps1 ps2 : List (pred σ)) :
  ((repeatedAnd (ps1 ++ ps2))) =tla= ((repeatedAnd ps1) ∧ (repeatedAnd ps2)) := by
  simp [repeatedAnd_eq_bigwedge, bigwedge_list_append]

/-
theorem repeatedAnd_reorder (ps1 ps2 : List (pred σ)) (p : pred σ) :
  ((repeatedAnd (ps1 ++ p :: ps2))) =tla= ((repeatedAnd (ps1 ++ ps2)) ∧ p) := by
  rw [repeatedAnd_eq_in_iff (ps2 := (ps1 ++ ps2) ++ [p]), repeatedAnd_append] ; rfl ; grind

theorem repeatedAnd_add_duplicate (ps : List (pred σ)) (p : pred σ)
  (h : p ∈ ps) :
  ((repeatedAnd ps)) =tla= ((repeatedAnd ps) ∧ p) := by
  simp [repeatedAnd_eq_bigwedge, bigwedge_forall_list]
  funext e ; tla_unfold_simp ; grind
-/

theorem repeatedAnd_subset_implies (ps1 ps2 : List (pred σ)) :
  ps1 ⊆ ps2 → ((repeatedAnd ps2)) |-tla- ((repeatedAnd ps1)) := by
  intro h ; rw [List.subset_def] at h
  simp only [repeatedAnd_eq_bigwedge, bigwedge_forall_list]
  tla_nontemporal_simp ; aesop

def Entails (hyps : List (NamedPred σ)) (goal : pred σ) : Prop :=
  TLA.pred_implies (repeatedAnd (hyps.map NamedPred.pred)) goal

def EntailsWithHidden (hyps : List (NamedPred σ)) {hyps' : List (NamedPred σ)} {goal : pred σ} : Prop :=
  Entails (hyps ++ hyps') goal

def modifyHypByName {σ : Type u} (hyps : List (NamedPred σ)) (name : String)
  (f : NamedPred σ → NamedPred σ) : List (NamedPred σ) :=
  letI idx? := hyps.findIdx? fun h => h.name == name
  idx?.elim hyps fun idx => hyps.modify idx f

theorem repeatedAnd_modifyHyp_reorder {σ : Type u} (hyps : List (NamedPred σ))
  (idx : Nat) (h : idx < hyps.length) (f : NamedPred σ → NamedPred σ) :
  ((repeatedAnd <| hyps.map NamedPred.pred) ∧ (f (hyps[idx]'h) |>.pred)) =tla=
  ((repeatedAnd <| (hyps.modify idx f).map NamedPred.pred) ∧ (hyps[idx]'h |>.pred)) := by
  rw [← repeatedAnd_singleton hyps[idx].pred, ← repeatedAnd_singleton (f (hyps[idx]'h)).pred,
    ← repeatedAnd_append, ← repeatedAnd_append]
  apply repeatedAnd_eq_in_iff
  have htmp := List.Perm.map NamedPred.pred <| LentilLib.List.modify_perm h f
  simp at htmp ; intro p ; apply List.Perm.mem_iff ; exact htmp

open Lean Meta Elab Tactic

/-- Like `Expr.isStringLit`, but returns the string. -/
def parseStringLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- Obtain a cleaned-up version of `e`. -/
def cleanupAnnotAndMore (e : Expr) : MetaM Expr := do
  pure (← instantiateMVars e).headBeta.cleanupAnnotations

def postDSimpAfterApplyingReflectionTheorem (l : Array Name) : TacticM Unit := do
  let gs ← getGoals
  let gs' ← gs.mapM fun g => do
    let ty ← cleanupAnnotAndMore (← g.getType)
    if ty.isAppOfArity' ``Entails 3 then
      let simps := l.map Lean.mkIdent
      let [g'] ← evalTacticAt (← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$[$simps:ident],*])) g
        | throwError "Unexpected number of goals after dsimp"
      pure g'
    else pure g
  setGoals gs'

def recognizeEntailsHyps (e : Expr) : MetaM (Option (Expr × List (String × Expr))) := do
  let_expr TLA.ProofMode.Entails _ hyps _ := e | return none
  let some (ty, hyps) := hyps.listLit? | return none
  let hyps ← hyps.foldrM (init := some []) fun hyp acc => do
    match acc with
    | none => pure none
    | some l =>
      let_expr TLA.ProofMode.NamedPred.mk _ nm pred := hyp
        | return none
      let some nameStr := parseStringLit? nm | return none
      pure <| some ((nameStr, pred) :: l)
  let some hyps := hyps | return none
  return some (ty, hyps)

def recognizeEntailsHypsFromGoal : TacticM (Option (Expr × List (String × Expr))) := do
  let g ← getMainTarget
  let g := g.headBeta.cleanupAnnotations
  recognizeEntailsHyps g

end TLA.ProofMode
