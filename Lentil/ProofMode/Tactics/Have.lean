import Lentil.ProofMode.Tactics.Clear
import Lentil.ProofMode.Tactics.Specialize
import Lentil.Expr

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
theorem Entails_have_true_pred_implies {newHyp : pred σ} :
  ((⊤) |-tla- (newHyp)) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_add_new [] (List.nil_subset _) newHypName newHyp

omit newHyp in
theorem Entails_have_valid {newHyp : pred σ} :
  (|-tla- (newHyp)) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by rw [valid_eq_true_implies] ; apply Entails_have_true_pred_implies

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
Target design for `thave h := t`:

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
   Temporal reasoning over arguments belongs to `tspecialize`, not to this
   analysis step.
6. The anonymous form `thave := t` follows the same pipeline, but uses only
   the newest-hypothesis index instead of a user-facing name.

The implementation below follows this shape: the only argument-level analysis
outside `tspecialize` is finding the first prefix that elaborates as a TLA
theorem.
-/

private def haveTacDSimps : Array Name := #[``List.cons_append, ``List.nil_append]

private def addValidTermHyp (newHypName : String) (tm : Term) : TacticM Unit := do
  let e ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize tm none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← inferType e >>= instantiateMVars
  -- To be safe, instantiate the theorem better
  let g ← getMainGoal
  let target ← g.getType
  let target ← cleanupAnnotAndMore target
  let_expr Entails σ hypsExpr goal := target
    | throwError "thave: goal is not an Entails sequent, but {target}"
  let newHypNameExpr := toExpr newHypName
  -- NOTE: The following restricts that `e` must be directly a TLA theorem,
  -- not a theorem whose conclusion is a TLA theorem. This is just for convenience.
  let thm ←
    -- Manual unification, as `e` might have uninstantiated metavariables that
    -- might make `mkAppOptM` fail. It seems that at minimum we need to unify
    -- the state type `σ` here
    match_expr ty with
    -- FIXME: Slightly repetitive
    | TLA.pred_implies σ' lhs rhs =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      mkAppOptM ``Entails_have_pred_implies
        #[some σ, some hypsExpr, some goal, some newHypNameExpr, some lhs, some rhs, some e]
    | TLA.ProofMode.Entails σ' hyps rhs =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      let some (_, hypsExprList) ← recognizeHypsList hyps
        | throwError "thave: failed to read the hypotheses from the theorem type"
      if hypsExprList.isEmpty then
        mkAppOptM ``Entails_have_true_pred_implies
          #[some σ, some hypsExpr, some goal, some newHypNameExpr, some rhs, some e]
      else
        let op ← mkAppOptM ``tla_and #[σ]
        let lhs := List.foldrD (mkApp2 op) default <| hypsExprList.map Prod.snd
        mkAppOptM ``Entails_have_pred_implies
          #[some σ, some hypsExpr, some goal, some newHypNameExpr, some lhs, some rhs, some e]
    | TLA.valid σ' p =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      mkAppOptM ``Entails_have_valid
        #[some σ, some hypsExpr, some goal, some newHypNameExpr, some p, some e]
    | _ => throwError "thave: term is not a TLA theorem, got type {ty}"
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
    let arg :: args := restArgs | throwError "thave: failed to elaborate a TLA theorem head from {head}"
    addTheoremPrefix newHypName head (usedArgs.push arg) args)

private def theoremArgCount (allBinders : Bool) (head : Ident) : TacticM Nat := do
  -- `head` is restricted to an identifier, so inspect its type directly.
  -- This avoids asking the term elaborator to instantiate implicit arguments
  -- just to count how many explicit theorem arguments the prime tactic needs.
  let ty ← theoremHeadType head
  countBindersUntilTLATheorem ty
where
  theoremHeadType (head : Ident) : TacticM Expr := do
    if let some ldecl := (← getLCtx).findFromUserName? head.getId then
      return ldecl.type
    let decl ← resolveGlobalConstNoOverload head
    return (← getConstInfo decl).type
  countBindersUntilTLATheorem (ty : Expr) : MetaM Nat := do
    forallTelescope (← instantiateMVars ty) fun args body => do
      let nm := body.getAppFn'.constName
      unless [``TLA.pred_implies, ``TLA.ProofMode.Entails, ``TLA.valid].contains nm do
        throwError "thave': failed to find a TLA theorem shape after omitted arguments, got type {body}"
      let lctx ← getLCtx
      return args.countP fun arg =>
        lctx.findFVar? arg |>.elim false fun decl => allBinders || decl.binderInfo.isExplicit

def tlaHaveTerm (newHypName : String) (tm : Term) : TacticM Nat := withMainContext do
  (do
    let some hypsLen ← goalHypsLength | throwError "thave: goal is not an Entails sequent"
    addValidTermHyp newHypName tm
    return hypsLen)
  <|>
  (do
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "thave: failed to read the hypotheses from the goal"
    let idx := hyps.length
    let (head, args) ← match tm with
      | `(term| $f:term $args:term* ) => pure (f, args)
      | _ => pure (tm, #[])
    if let some oldHypName ← temporalHypNameOfBareTerm? hyps head then
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
  specializeByIdx (idx : Nat) (args : Array (Term)) : TacticM Unit := do
    for arg in args do
      tlaSpecializeStep (.byIdx idx) arg

declare_syntax_cat tlaHaveClause
syntax " : " tlafml " by " tacticSeq : tlaHaveClause
syntax " := " term : tlaHaveClause

declare_syntax_cat tlaMixedArg
syntax:max tlafml:max : tlaMixedArg
syntax:max term:max : tlaMixedArg

private def mixedArgToTerm [Monad m] [MonadError m] [MonadQuotation m] (arg : TSyntax `tlaMixedArg) : m Term := do
  let candidates : List (m (Option Term)) := [
    parseTla? arg,
    parseChoice? arg parseTla?,
    parseTerm? arg,
    parseChoice? arg parseTerm?]
  match ← candidates.findSomeM? id with
  | some t => return t
  | none => throwError "thave': failed to parse mixed argument {arg}"
where
  parseTla? (arg : TSyntax `tlaMixedArg) : m (Option Term) := do
    match arg with
    | `(tlaMixedArg| $f:tlafml) => return some (← TLA.syntax_tlafml_to_term f)
    | _ => return none
  parseTerm? (arg : TSyntax `tlaMixedArg) : m (Option Term) := do
    match arg with
    | `(tlaMixedArg| $t:term) => return some t
    | _ => return none
  parseChoice? (arg : TSyntax `tlaMixedArg) (parse? : TSyntax `tlaMixedArg → m (Option Term)) :
      m (Option Term) := do
    -- NOTE: `tlaMixedArg` has both `tlafml` and `term` productions. For ambiguous
    -- inputs such as `(a ∧ b)`, Lean's parser keeps both parses under a
    -- `choice` node, so inspect the alternatives and let `parse?` select one.
    if !arg.raw.isOfKind choiceKind then
      return none
    arg.raw.getArgs.findSomeM? fun alt => parse? ⟨alt⟩

def tlaHavePrimeTerm (newHypName : String) (head : Ident) (allBinders : Bool)
    (args : Array (TSyntax `tlaMixedArg)) : TacticM Nat := withMainContext do
  let some hypsLen ← goalHypsLength | throwError "thave': goal is not an Entails sequent"
  let termArgs ← args.toList.mapM mixedArgToTerm
  let argCount ← theoremArgCount allBinders head
  let (theoremArgs, rest) := termArgs.splitAt argCount
  let holes := List.replicate (argCount - theoremArgs.length) <| ← `(_)
  let headTerm : Term ← if allBinders then `(term| @$head:ident) else pure head
  addValidTermHyp newHypName (Syntax.mkApp headTerm (theoremArgs ++ holes).toArray)
  for arg in rest do
    tlaSpecializeStep (.byIdx hypsLen) arg
  return hypsLen

/--
`thave h : p by tac` adds a new temporal hypothesis `h : p` to the
proof-mode context, after `tac` proves `p` from the current context.

For example, if the current context can prove `p`, then
```lean
thave hp : p by
  exact pred_implies_refl _
```
adds `hp : p` to the proof-mode context and returns to the original goal.

`thave h := t` adds the temporal fact obtained from `t`. For example,
```lean
thave hq := lemma hp
```
adds the result of applying `lemma` to the temporal hypothesis `hp`.
-/
syntax (name := tlaHaveTac) "thave" (ppSpace colGt ident) tlaHaveClause : tactic
/--
`thave' h := thm arg₁ ... argₙ` adds the temporal fact obtained by applying
the theorem or local hypothesis `thm` to the given arguments.

Compared with `thave h := t`, the prime form is more restricted: the theorem
head must be an identifier, not an arbitrary Lean term. In exchange, its
arguments may be written as TLA formulas, without explicit `[tlafml| ... ]`
wrappers.

Writing `@thm` instead of `thm` exposes implicit theorem arguments, just like
Lean's ordinary `@` notation.

For example, if `lem : ∀ p : pred σ, |-tla- (p → p)`, then
```lean
thave' h := lem (a ∧ b)
```
adds `h : (a ∧ b) → (a ∧ b)` to the proof-mode context.
-/
syntax (name := tlaHavePrimeTac) "thave' " (ppSpace colGt ident) " := " ("@")? ident (ppSpace colGt tlaMixedArg)* : tactic
/--
`thave := t` adds the temporal fact obtained from `t` under the default
proof-mode name `"this"`.

For example,
```lean
thave := lemma hp
```
adds a new hypothesis named `this` containing the result of `lemma hp`.
-/
syntax (name := tlaHaveAnonTac) "thave" " := " term : tactic
/--
`treplace h := t` replaces the named proof-mode hypothesis `h` by the
temporal fact obtained from `t`.

For example, if `hp : p` and `lem : (p) |-tla- (q)`, then
```lean
treplace hp := lem hp
```
removes `hp : p` and adds `hp : q`. The replacement is appended at the end of
the proof-mode context, as if `thave`, `tclear`, and `trename` had
been used in sequence.
-/
syntax (name := tlaReplaceTac) "treplace" (ppSpace colGt ident) " := " term : tactic
/--
`tsuffices h : p by tac` changes the main goal to proving `p`. The block
`tac` must show that the original goal follows after adding `h : p` to the
proof-mode context.

For example,
```lean
tsuffices h : p ∧ q by
  trcases h with ⟨hp, hq⟩
```
leaves the new main goal `p ∧ q`; inside the `by` block, the original goal is
available with an extra temporal hypothesis `h : p ∧ q`.
-/
syntax (name := tlaSufficesTac) "tsuffices" (ppSpace colGt ident) " : " tlafml " by " tacticSeq : tactic

private def haveOrSufficesCommon (h : Ident) (fml : TSyntax `tlafml) : TacticM Unit := do
  let nameStr := toString h.getId
  let fmlTerm ← TLA.syntax_tlafml_to_term fml
  evalTactic <| ← `(tactic|
    refine $(mkIdent ``Entails_have_or_suffices)
      ($(quote nameStr)) $fmlTerm ?_ ?_)

-- FIXME: Will there be some incrementality issue here?
elab_rules : tactic
  | `(tactic| thave $h:ident : $fml:tlafml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Close the premise goal `Entails hyps fml` with the user's tac.
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails (hyps ++ [⟨h, fml⟩]) goal` — collapse the `++`.
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
  | `(tactic| tsuffices $h:ident : $fml:tlafml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Swap so the `Entails (hyps ++ …) goal` goal is focused, clean up the `++`,
    -- then close it with the user's tac.
    evalTactic <| ← `(tactic| swap)
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails hyps fml` (no `++` to clean).

  | `(tactic| thave $h:ident := $t:term) => do
    let nameStr := toString h.getId
    discard <| tlaHaveTerm nameStr t
  | `(tactic| thave' $h:ident := $[@%$explicit?]? $head:ident $[$args:tlaMixedArg]*) => withMainContext do
    let nameStr := toString h.getId
    discard <| tlaHavePrimeTerm nameStr head explicit?.isSome args
  | `(tactic| thave := $t:term) => do
    discard <| tlaHaveTerm "this" t
  | `(tactic| treplace $h:ident := $t:term) => withMainContext do
    let nameStr := toString h.getId
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "treplace: failed to read the hypotheses from the goal"
    unless hyps.any (fun ⟨name, _⟩ => name == nameStr) do
      throwError "treplace: hypothesis '{nameStr}' not found in the goal's Entails list"
    let idx ← tlaHaveTerm "" t
    evalTactic <| ← `(tactic| tclear $h:ident)
    tlaRename (.byIdx <| idx - 1) nameStr

end TLA.ProofMode
