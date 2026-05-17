import Lentil.ProofMode.Tactics.Specialize

namespace TLA.ProofMode

open Lean Meta Elab Tactic LentilLib
open Lean.Parser.Tactic

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ} (newHypName : String) (newHyp : pred σ)

theorem Entails_have_or_suffices :
  Entails hyps newHyp →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_add_new _ (List.Subset.refl _) newHypName newHyp

omit newHyp in
theorem Entails_have_valid {newHyp : pred σ} :
  (|-tla- (newHyp)) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by rw [valid_eq_true_implies] ; exact Entails_add_new [] (List.nil_subset _) newHypName newHyp

-- NOTE: In theory we don't need this, but applying `Entails_have_valid` on a `pred_implies`
-- can break its form, so still have this more specific version to preserve the `pred_implies` shape
omit newHyp in
theorem Entails_have_pred_implies {newHypLHS newHypRHS : pred σ} :
  ((newHypLHS) |-tla- (newHypRHS)) →
  Entails (hyps ++ [⟨newHypName, [tlafml| newHypLHS → newHypRHS ]⟩]) goal →
  Entails hyps goal := Entails_have_valid newHypName

theorem Entails_duplicate_one_hyp :
  newHyp ∈ hyps.map NamedPred.pred →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := fun h1 => Entails_add_new [newHyp] (by grind) newHypName newHyp (pred_implies_refl _)

omit newHyp in
theorem Entails_duplicate_one_hyp_by_name {newHyp : pred σ} (oldHypName : String)
  (hpred : hyps.find? (fun h => h.name == oldHypName) = some ⟨oldHypName, newHyp⟩) :
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_duplicate_one_hyp newHypName newHyp (by grind)

end

/-
-/

/-
Target design for `tla_have h := t`:

1. First try elaborating the whole term directly. If its type is already a TLA
   theorem, either `|-tla- p` or `p |-tla- q`, add the corresponding temporal
   hypothesis with `Entails_have_valid`.
2. If direct elaboration does not produce a TLA theorem, analyze the term as an
   application. Move this fallback application-analysis logic here from
   `Apply.lean`.
3. In the fallback path, if the head is a Lean term, elaborate/infer the head and
   consume just enough ordinary Lean arguments for the expression to become a
   TLA theorem. This handles examples such as `lem n hp`, where
   `lem : forall n, p |-tla- q` and `n` is not a temporal hypothesis.
4. If the head is a proof-mode hypothesis, duplicate it as the newest temporal
   hypothesis with `Entails_duplicate_one_hyp`.
5. After the theorem head has been added as the newest temporal hypothesis,
   specialize that newest hypothesis by index using the remaining arguments.
   Temporal reasoning over arguments belongs to `tla_specialize`, not to this
   analysis step.
6. The anonymous form `tla_have := t` follows the same pipeline, but uses only
   the newest-hypothesis index instead of a user-facing name.

The implementation below follows this shape: the only argument-level analysis
outside `tla_specialize` is finding the first prefix that elaborates as a TLA
theorem.
-/

private def haveTacDSimps : Array Name := #[``List.cons_append, ``List.nil_append]

private def addValidTermHyp (newHypName : String) (tm : Term) : TacticM Unit := do
  let e ← Term.elabTermAndSynthesize tm none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← inferType e >>= instantiateMVars
  -- To be safe, instantiate the theorem better
  let g ← getMainGoal
  let target ← g.getType
  let target ← cleanupAnnotAndMore target
  let_expr Entails σ hypsExpr goal := target
    | throwError "tla_have: goal is not an Entails sequent, but {target}"
  let newHypNameExpr := mkStrLit newHypName
  -- NOTE: The following restricts that `e` must be directly a TLA theorem,
  -- not a theorem whose conclusion is a TLA theorem. This is just for convenience.
  let thm ←
    if ty.isAppOfArity' ``TLA.pred_implies 3 then
      mkAppOptM ``Entails_have_pred_implies #[some σ, some hypsExpr, some goal, some newHypNameExpr, none, none, some e]
    else if ty.isAppOfArity' ``TLA.valid 2 then
      mkAppOptM ``Entails_have_valid #[some σ, some hypsExpr, some goal, some newHypNameExpr, none, some e]
    else throwError "tla_have: term is not a TLA theorem, got type {ty}"
  let goals ← g.apply thm
  replaceMainGoal goals
  postDSimpAfterApplyingReflectionTheorem haveTacDSimps

private def addTheoremPrefix (newHypName : String) (head : Term) (usedArgs : Array Term) (restArgs : List Term) : TacticM (List Term) := do
  let candidate := Syntax.mkApp head usedArgs
  (do
    addValidTermHyp newHypName candidate
    return restArgs)
  <|>
  (do
    let arg :: args := restArgs | throwError "tla_have: failed to elaborate a TLA theorem head from {head}"
    addTheoremPrefix newHypName head (usedArgs.push arg) args)

def tlaHaveTerm (newHypName : String) (tm : Term) : TacticM Nat := withMainContext do
  (do
    let some hypsLen ← goalHypsLength | throwError "tla_have: goal is not an Entails sequent"
    addValidTermHyp newHypName tm
    return hypsLen)
  <|>
  (do
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "tla_have: failed to read the hypotheses from the goal"
    let idx := hyps.length
    let (head, args) ← match tm with
      | `(term| $f:term $args:term* ) => pure (f, args)
      | _ => pure (tm, #[])
    if let some oldHypName ← temporalHypName? hyps head then
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_duplicate_one_hyp_by_name) ($(quote newHypName)) ($(quote oldHypName)) (by rfl) ?_)
      postDSimpAfterApplyingReflectionTheorem haveTacDSimps
      specializeByIdx idx args
      return idx
    else
      let rest ← addTheoremPrefix newHypName head #[] args.toList
      specializeByIdx idx rest.toArray
      return idx)
where
  temporalHypName? (hyps : List (String × Expr)) (tm : Term) : TacticM (Option String) := withMainContext do
    let some id ← termIdent? tm | return none
    let name := toString id.getId
    return if hyps.any (fun ⟨n, _⟩ => n == name) then some name else none
  specializeByIdx (idx : Nat) (args : Array (Term)) : TacticM Unit := do
    for arg in args do
      tlaSpecializeStep (Sum.inr idx) arg

declare_syntax_cat tlaHaveClause
syntax " : " tlafml " by " tacticSeq : tlaHaveClause
syntax " := " term : tlaHaveClause
syntax (name := tlaHaveTac) "tla_have" (ppSpace colGt ident) tlaHaveClause : tactic
syntax (name := tlaHaveAnonTac) "tla_have" " := " term : tactic
syntax (name := tlaSufficesTac) "tla_suffices" (ppSpace colGt ident) " : " tlafml " by " tacticSeq : tactic

private def haveOrSufficesCommon (h : Ident) (fml : TSyntax `tlafml) : TacticM Unit := do
  let nameStr := toString h.getId
  let fmlTerm ← TLA.syntax_tlafml_to_term fml
  evalTactic <| ← `(tactic|
    refine $(mkIdent ``Entails_have_or_suffices)
      ($(quote nameStr)) $fmlTerm ?_ ?_)

-- FIXME: Will there be some incrementality issue here?
elab_rules : tactic
  | `(tactic| tla_have $h:ident : $fml:tlafml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Close the premise goal `Entails hyps fml` with the user's tac.
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails (hyps ++ [⟨h, fml⟩]) goal` — collapse the `++`.
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
  | `(tactic| tla_suffices $h:ident : $fml:tlafml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Swap so the `Entails (hyps ++ …) goal` goal is focused, clean up the `++`,
    -- then close it with the user's tac.
    evalTactic <| ← `(tactic| swap)
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails hyps fml` (no `++` to clean).

  | `(tactic| tla_have $h:ident := $t:term) => do
    let nameStr := toString h.getId
    discard <| tlaHaveTerm nameStr t
  | `(tactic| tla_have := $t:term) => do
    discard <| tlaHaveTerm "this" t

end TLA.ProofMode
