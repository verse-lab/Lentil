module

public import Lentil.ProofMode.Tactics.Clear
public import Lentil.ProofMode.Tactics.Specialize
public import Lentil.Expr

namespace Lentil.ProofMode

open Lean Meta Elab Tactic LentilLib
open Lean.Parser.Tactic

@[expose] public section

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ} (newHypName : String) (newHyp : pred σ)

theorem Entails_have_or_suffices :
  Entails hyps newHyp →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_add_new _ (List.Subset.refl _) newHypName newHyp

omit newHyp in
theorem Entails_have_true_pred_implies {newHyp : pred σ} :
  ((⊤) |-tl- (newHyp)) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := Entails_add_new [] (List.nil_subset _) newHypName newHyp

omit newHyp in
theorem Entails_have_valid {newHyp : pred σ} :
  (|-tl- (newHyp)) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by rw [valid_eq_true_implies] ; apply Entails_have_true_pred_implies

-- NOTE: In theory we don't need this, but applying `Entails_have_valid` on a `pred_implies`
-- can break its form, so still have this more specific version to preserve the `pred_implies` shape
omit newHyp in
theorem Entails_have_pred_implies {newHypLHS newHypRHS : pred σ} :
  ((newHypLHS) |-tl- (newHypRHS)) →
  Entails (hyps ++ [⟨newHypName, [tlfml| newHypLHS → newHypRHS ]⟩]) goal →
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

end

public meta section

/-
-/

/-
Target design for `thave h := t`:

1. First try elaborating the whole term directly. If its type is already a LTL
   theorem, either `|-tl- p` or `p |-tl- q`, add the corresponding temporal
   hypothesis with `Entails_have_valid`.
2. Otherwise, split the application into its head and arguments. If the head is
   a proof-mode hypothesis, duplicate it as the newest temporal hypothesis with
   `Entails_duplicate_one_hyp`.
3. For a Lean head, try successively longer argument prefixes as part of the
   theorem term. For example, one split of `rule 0 ⟨hx, hp⟩` has theorem
   candidate `rule 0` and remaining argument `⟨hx, hp⟩`. The remaining
   arguments form a *reflected temporal suffix* when every one is a proof-mode
   hypothesis name or a tuple of such names.
4. To elaborate a candidate with such a suffix, resolve the names to the
   predicates stored in the current `Entails` context and create a new
   assignable metavariable `?result : pred σ`. Each suffix argument contributes
   one premise; a tuple contributes the conjunction of its named predicates.
   Elaborate the candidate against `|-tl- premise₁ → ... → ?result`. Here
   `?result` is the "fresh conclusion"; it is not the current proof-mode goal.
   The premises can determine implicit theorem parameters now, while a later
   `tapply` can still assign `?result`.
5. If the remaining arguments are not all reflected hypotheses, try the
   candidate as an ordinary theorem. If it is not one yet, consume another
   ordinary Lean argument into the prefix and retry. This handles `lem n hp`,
   where `lem : forall n, p |-tl- q` and `n` is not a temporal hypothesis.
6. After the theorem candidate has been added as the newest temporal
   hypothesis, specialize it by index using the remaining arguments.
   Temporal reasoning over arguments belongs to `tspecialize`, not to this
   analysis step.
7. The anonymous form `thave := t` follows the same pipeline, but uses only
   the newest-hypothesis index instead of a user-facing name.

The implementation below only inspects arguments to distinguish an ordinary
Lean prefix from a reflected temporal suffix. `tspecialize` remains responsible
for changing the introduced temporal hypothesis.
-/

private def haveTacDSimps : Array Name := #[``List.cons_append, ``List.nil_append]

abbrev TheoremExprTransform := Expr → TacticM Expr

def elabTheoremTerm (tm : Term) (expectedType? : Option Expr := none) : TacticM Expr := do
  let e ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize tm expectedType?
  if expectedType?.isNone then
    Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def addValidExprHyp (newHypName : String) (e : Expr) : TacticM Unit := do
  let ty ← inferType e >>= instantiateMVars
  -- To be safe, instantiate the theorem better
  let g ← getMainGoal
  let target ← g.getType
  let target ← cleanupAnnotAndMore target
  let_expr Entails σ hypsExpr goal := target
    | throwError "thave: goal is not an Entails sequent, but {target}"
  let newHypNameExpr := toExpr newHypName
  -- NOTE: The following restricts that `e` must be directly a LTL theorem,
  -- not a theorem whose conclusion is a LTL theorem. This is just for convenience.
  let thm ←
    -- Manual unification, as `e` might have uninstantiated metavariables that
    -- might make `mkAppOptM` fail. It seems that at minimum we need to unify
    -- the state type `σ` here
    match_expr ty with
    -- FIXME: Slightly repetitive
    | Lentil.pred_implies σ' lhs rhs =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      mkAppOptM ``Entails_have_pred_implies
        #[some σ, some hypsExpr, some goal, some newHypNameExpr, some lhs, some rhs, some e]
    | Lentil.ProofMode.Entails σ' hyps rhs =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      let some (_, hypsExprList) ← recognizeHypsList hyps
        | throwError "thave: failed to read the hypotheses from the theorem type"
      if hypsExprList.isEmpty then
        mkAppOptM ``Entails_have_true_pred_implies
          #[some σ, some hypsExpr, some goal, some newHypNameExpr, some rhs, some e]
      else
        let lhs ← mkRepeatedAndExpr σ <| hypsExprList.map Prod.snd
        mkAppOptM ``Entails_have_pred_implies
          #[some σ, some hypsExpr, some goal, some newHypNameExpr, some lhs, some rhs, some e]
    | Lentil.valid σ' p =>
      unless ← isDefEq σ' σ do
        throwError "thave: theorem state type{indentExpr σ'}\ndoes not match proof-mode state type{indentExpr σ}"
      mkAppOptM ``Entails_have_valid
        #[some σ, some hypsExpr, some goal, some newHypNameExpr, some p, some e]
    | _ => throwError "thave: term is not a LTL theorem, got type {ty}"
  let goals ← g.apply thm
  replaceMainGoal goals
  postDSimpAfterApplyingReflectionTheorem haveTacDSimps

private def addValidTermHyp (newHypName : String) (tm : Term) : TacticM Unit := do
  addValidExprHyp newHypName (← elabTheoremTerm tm)

private def addValidTermHypWithTransform (newHypName : String) (tm : Term)
    (transform? : Option TheoremExprTransform) (expectedType? : Option Expr := none) : TacticM Unit := do
  let e ← elabTheoremTerm tm expectedType?
  let e ← transform?.elim (pure e) (· e)
  addValidExprHyp newHypName e

/-- Elaborate a theorem candidate against an already resolved, nonempty suffix
of temporal premises. Their implication chain ends in a new assignable
`?result : pred σ`. -/
private def addValidTermHypWithTemporalPremises (newHypName : String) (tm : Term) (predType : Expr)
    (premises : List Expr) (transform? : Option TheoremExprTransform := none) : TacticM Unit := do
  if premises.isEmpty then
    throwError "thave: expected at least one temporal argument"
  let conclusion ← mkFreshExprMVar (some predType)
  let expectedPred ← premises.foldrM (fun premise rest =>
    mkAppM ``Lentil.tl_implies #[premise, rest]) conclusion
  let expectedType ← mkAppM ``Lentil.valid #[expectedPred]
  addValidTermHypWithTransform newHypName tm transform? (some expectedType)

/-- Find a theorem prefix of an application. Resolve the longest reflected
temporal suffix once, then reuse its predicates while successively moving
arguments into the ordinary Lean prefix. -/
private def addTheoremPrefix (newHypName : String) (head : Term) (args : Array Term)
    (stateType predType : Expr) (hyps : List (String × Expr))
    (transform? : Option TheoremExprTransform := none) : TacticM (List Term) := do
  let (_, temporalPremises) ← args.toList.foldrM
      (init := (true, ([] : List Expr))) fun arg (suffixIsTemporal, premises) => do
    if !suffixIsTemporal then
      return (false, premises)
    (do
      let preds := (← resolveTemporalHypArg hyps arg "thave").map Prod.snd
      -- Keep conjunction heads visible so unification does not unfold premise predicates
      -- while reducing an object-level `repeatedAnd` application.
      let premise ← mkRepeatedAndExpr stateType preds
      return (true, premise :: premises))
    <|> pure (false, premises)
  let temporalStart := args.size - temporalPremises.length
  let rec loop (usedArgs : Array Term) (restArgs : List Term) : TacticM (List Term) := do
    let candidate := Syntax.mkApp head usedArgs
    (do
      unless temporalStart ≤ usedArgs.size do
        throwError "thave: theorem candidate still has ordinary Lean arguments"
      let premises := temporalPremises.drop (usedArgs.size - temporalStart)
      addValidTermHypWithTemporalPremises newHypName candidate predType premises transform?
      return restArgs)
    <|>
    (do
      addValidTermHypWithTransform newHypName candidate transform?
      return restArgs)
    <|>
    (do
      let arg :: args := restArgs | throwError "thave: failed to elaborate a LTL theorem head from {head}"
      loop (usedArgs.push arg) args)
  loop #[] args.toList

private def theoremArgCount (allBinders : Bool) (head : Ident) : TacticM Nat := do
  -- `head` is restricted to an identifier, so inspect its type directly.
  -- This avoids asking the term elaborator to instantiate implicit arguments
  -- just to count how many explicit theorem arguments the prime tactic needs.
  let ty ← theoremHeadType head
  countBindersUntilTLTheorem ty
where
  theoremHeadType (head : Ident) : TacticM Expr := do
    if let some ldecl := (← getLCtx).findFromUserName? head.getId then
      return ldecl.type
    let decl ← resolveGlobalConstNoOverload head
    return (← getConstInfo decl).type
  countBindersUntilTLTheorem (ty : Expr) : MetaM Nat := do
    forallTelescope (← instantiateMVars ty) fun args body => do
      let nm := body.getAppFn'.constName
      unless [``Lentil.pred_implies, ``Lentil.ProofMode.Entails, ``Lentil.valid].contains nm do
        throwError "thave': failed to find a LTL theorem shape after omitted arguments, got type {body}"
      let lctx ← getLCtx
      return args.countP fun arg =>
        lctx.findFVar? arg |>.elim false fun decl => allBinders || decl.binderInfo.isExplicit

private def tlHaveTermCore (newHypName : String) (tm : Term)
    (transform? : Option TheoremExprTransform := none) : TacticM Nat := withMainContext do
  let (stateType, _, _, hyps, _) ← parseCanonicalEntails (← getMainTarget)
    "thave: goal is not a canonical Entails sequent"
  let idx := hyps.length
  (do
    addValidTermHypWithTransform newHypName tm transform?
    return idx)
  <|>
  (do
    let (head, args) ← match tm with
      | `(term| $f:term $args:term* ) => pure (f, args)
      | _ => pure (tm, #[])
    if let some oldHypName ← temporalHypNameOfBareTerm? hyps head then
      if transform?.isSome then
        throwError "thave: theorem transform cannot be used when the head is a proof-mode hypothesis"
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_duplicate_one_hyp_by_name) ($(quote newHypName)) ($(quote oldHypName)) (by rfl) ?_)
      postDSimpAfterApplyingReflectionTheorem haveTacDSimps
      specializeByIdx idx args
      return idx
    else
      let predType ← mkAppM ``Lentil.pred #[stateType]
      let rest ← addTheoremPrefix newHypName head args stateType predType hyps transform?
      specializeByIdx idx rest.toArray
      return idx)
where
  specializeByIdx (idx : Nat) (args : Array (Term)) : TacticM Unit := do
    for arg in args do
      tlSpecializeStep (.byIdx idx) arg

def tlHaveTerm (newHypName : String) (tm : Term) : TacticM Nat :=
  tlHaveTermCore newHypName tm

def tlHaveTermWithTransform (newHypName : String) (tm : Term)
    (transform : TheoremExprTransform) : TacticM Nat :=
  tlHaveTermCore newHypName tm (some transform)

/-- Replace a temporal hypothesis by appending a new hypothesis under a fresh
internal name, clearing the selected entry, and renaming the appended entry.
The callback returns the index at which it appended the replacement. -/
def replaceTemporalHypByAppending (tacticName : String) (targetLoc : TemporalHypLoc)
    (appendReplacement : String → TacticM Nat) : TacticM Unit := withMainContext do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal
    | throwError "{tacticName}: failed to read the hypotheses from the goal"
  let (targetIdx, targetName, _) ← findIdxByTemporalHypLoc hyps targetLoc
    tacticName "the goal's Entails list"
  let internalName ← mkFreshInternalTemporalHypName
  let replacementIdx ← appendReplacement internalName
  unless targetIdx < replacementIdx do
    throwError "{tacticName}: internal replacement was not appended after the selected hypothesis"
  tlClearByIdx targetIdx
  tlRename (.byIdx <| replacementIdx - 1) targetName

def tlReplaceTermCore (h : Ident) (tm : Term)
    (transform? : Option TheoremExprTransform := none) : TacticM Unit := do
  let nameStr := toString h.getId
  replaceTemporalHypByAppending "treplace" (.byName nameStr) fun internalName =>
    tlHaveTermCore internalName tm transform?

def tlReplaceTerm (h : Ident) (tm : Term) : TacticM Unit :=
  tlReplaceTermCore h tm

def tlReplaceTermWithTransform (h : Ident) (tm : Term)
    (transform : TheoremExprTransform) : TacticM Unit :=
  tlReplaceTermCore h tm (some transform)

declare_syntax_cat tlHaveClause
syntax " : " tlfml " by " tacticSeq : tlHaveClause
syntax " := " term : tlHaveClause

declare_syntax_cat tlMixedArg
syntax:max tlfml:max : tlMixedArg
syntax:max term:max : tlMixedArg

private def mixedArgToTerm [Monad m] [MonadError m] [MonadQuotation m] (arg : TSyntax `tlMixedArg) : m Term := do
  let candidates : List (m (Option Term)) := [
    parseTl? arg,
    parseChoice? arg parseTl?,
    parseTerm? arg,
    parseChoice? arg parseTerm?]
  match ← candidates.findSomeM? id with
  | some t => return t
  | none => throwError "thave': failed to parse mixed argument {arg}"
where
  parseTl? (arg : TSyntax `tlMixedArg) : m (Option Term) := do
    match arg with
    | `(tlMixedArg| $f:tlfml) => return some (← Lentil.syntax_tlfml_to_term f)
    | _ => return none
  parseTerm? (arg : TSyntax `tlMixedArg) : m (Option Term) := do
    match arg with
    | `(tlMixedArg| $t:term) => return some t
    | _ => return none
  parseChoice? (arg : TSyntax `tlMixedArg) (parse? : TSyntax `tlMixedArg → m (Option Term)) :
      m (Option Term) := do
    -- NOTE: `tlMixedArg` has both `tlfml` and `term` productions. For ambiguous
    -- inputs such as `(a ∧ b)`, Lean's parser keeps both parses under a
    -- `choice` node, so inspect the alternatives and let `parse?` select one.
    if !arg.raw.isOfKind choiceKind then
      return none
    arg.raw.getArgs.findSomeM? fun alt => parse? ⟨alt⟩

private def tlHavePrimeTermCore (newHypName : String) (head : Ident) (allBinders : Bool)
    (args : Array (TSyntax `tlMixedArg)) (transform? : Option TheoremExprTransform := none) :
    TacticM Nat := withMainContext do
  let some hypsLen ← goalHypsLength | throwError "thave': goal is not an Entails sequent"
  let termArgs ← args.toList.mapM mixedArgToTerm
  let argCount ← theoremArgCount allBinders head
  let (theoremArgs, rest) := termArgs.splitAt argCount
  let holes := List.replicate (argCount - theoremArgs.length) <| ← `(_)
  let headTerm : Term ← if allBinders then `(term| @$head:ident) else pure head
  addValidTermHypWithTransform newHypName (Syntax.mkApp headTerm (theoremArgs ++ holes).toArray) transform?
  for arg in rest do
    tlSpecializeStep (.byIdx hypsLen) arg
  return hypsLen

def tlHavePrimeTerm (newHypName : String) (head : Ident) (allBinders : Bool)
    (args : Array (TSyntax `tlMixedArg)) : TacticM Nat :=
  tlHavePrimeTermCore newHypName head allBinders args

def tlHavePrimeTermWithTransform (newHypName : String) (head : Ident) (allBinders : Bool)
    (args : Array (TSyntax `tlMixedArg)) (transform : TheoremExprTransform) : TacticM Nat :=
  tlHavePrimeTermCore newHypName head allBinders args (some transform)

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
syntax (name := tlHaveTac) "thave" (ppSpace colGt ident) tlHaveClause : tactic
/--
`thave' h := thm arg₁ ... argₙ` adds the temporal fact obtained by applying
the theorem or local hypothesis `thm` to the given arguments.

Compared with `thave h := t`, the prime form is more restricted: the theorem
head must be an identifier, not an arbitrary Lean term. In exchange, its
arguments may be written as LTL formulas, without explicit `[tlfml| ... ]`
wrappers.

Writing `@thm` instead of `thm` exposes implicit theorem arguments, just like
Lean's ordinary `@` notation.

For example, if `lem : ∀ p : pred σ, |-tl- (p → p)`, then
```lean
thave' h := lem (a ∧ b)
```
adds `h : (a ∧ b) → (a ∧ b)` to the proof-mode context.
-/
syntax (name := tlHavePrimeTac) "thave' " (ppSpace colGt ident) " := " ("@")? ident (ppSpace colGt tlMixedArg)* : tactic
/--
`thave := t` adds the temporal fact obtained from `t` under the default
proof-mode name `"this"`.

For example,
```lean
thave := lemma hp
```
adds a new hypothesis named `this` containing the result of `lemma hp`.
-/
syntax (name := tlHaveAnonTac) "thave" " := " term : tactic
/--
`treplace h := t` replaces the named proof-mode hypothesis `h` by the
temporal fact obtained from `t`.

For example, if `hp : p` and `lem : (p) |-tl- (q)`, then
```lean
treplace hp := lem hp
```
removes `hp : p` and adds `hp : q`. The replacement is appended at the end of
the proof-mode context, as if `thave`, `tclear`, and `trename` had
been used in sequence.
-/
syntax (name := tlReplaceTac) "treplace" (ppSpace colGt ident) " := " term : tactic
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
syntax (name := tlSufficesTac) "tsuffices" (ppSpace colGt ident) " : " tlfml " by " tacticSeq : tactic

private def haveOrSufficesCommon (h : Ident) (fml : TSyntax `tlfml) : TacticM Unit := do
  let nameStr := toString h.getId
  let fmlTerm ← Lentil.syntax_tlfml_to_term fml
  evalTactic <| ← `(tactic|
    refine $(mkIdent ``Entails_have_or_suffices)
      ($(quote nameStr)) $fmlTerm ?_ ?_)

-- FIXME: Will there be some incrementality issue here?
elab_rules : tactic
  | `(tactic| thave $h:ident : $fml:tlfml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Close the premise goal `Entails hyps fml` with the user's tac.
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails (hyps ++ [⟨h, fml⟩]) goal` — collapse the `++`.
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
  | `(tactic| tsuffices $h:ident : $fml:tlfml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Swap so the `Entails (hyps ++ …) goal` goal is focused, clean up the `++`,
    -- then close it with the user's tac.
    evalTactic <| ← `(tactic| swap)
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
    Tactic.focusAndDone <| evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails hyps fml` (no `++` to clean).

  | `(tactic| thave $h:ident := $t:term) => do
    let nameStr := toString h.getId
    discard <| tlHaveTerm nameStr t
  | `(tactic| thave' $h:ident := $[@%$explicit?]? $head:ident $[$args:tlMixedArg]*) => withMainContext do
    let nameStr := toString h.getId
    discard <| tlHavePrimeTerm nameStr head explicit?.isSome args
  | `(tactic| thave := $t:term) => do
    discard <| tlHaveTerm "this" t
  | `(tactic| treplace $h:ident := $t:term) => tlReplaceTerm h t

end

end Lentil.ProofMode
