import Lentil.ProofMode.Attrs
import Lentil.ProofMode.Tactics.Have

/-!
`tmap` adds the result of applying an implication underneath any nesting of
modalities. There are two proof paths:

* A Lean theorem is normalized to a raw implication `p |-tla- q`, then lifted
  one operator at a time with its registered monotonicity theorem.
* A proof-mode hypothesis `p ⇒ q` is not a Lean proof of `p |-tla- q`. It stays
  as a temporal premise while the implication is transported through each
  modality, and is applied to the source hypothesis only at the end.

Keeping these paths separate makes the dependency of the resulting hypothesis
explicit: a global rule depends only on the source, while a temporal rule
depends on both the rule hypothesis and the source.
-/

namespace TLA.ProofMode

/-- Transport an `always_implies` consequence through one monotone step while
keeping the original stable implication as the premise. -/
private theorem always_implies_map {p q r s r' s' : pred σ}
    (hmono : |-tla- ((r ⇒ s) → (r' → s')))
    (h : (p ⇒ q) |-tla- (r ⇒ s)) :
    (p ⇒ q) |-tla- (r' ⇒ s') := by
  unfold always_implies at h ⊢
  rw [← always_pred_implies]
  refine pred_implies_trans (q := always (tla_implies r s)) h ?_
  rwa [← impl_intro]

/-- Apply an `always_implies` conclusion obtained under another predicate. -/
private theorem always_implies_apply {Γ p q : pred σ}
    (h : (Γ) |-tla- (p ⇒ q)) :
    (Γ ∧ p) |-tla- (q) := by
  rw [← impl_intro_add_r]
  exact pred_implies_trans h always_weaken

private theorem always_impl_intro (p q : pred σ) :
    (|-tla- (p ⇒ q)) = ((p) |-tla- (q)) := by
  unfold always_implies
  rw [← always_intro, impl_intro]

open Lean Meta Elab Tactic

attribute [tmap_mono]
  TLA.later_monotone' TLA.always_monotone' TLA.eventually_monotone'

/-- The common internal form for both Lean-term and proof-mode rules. The
meaning of `proof` is determined by the lifting step used with the rule. -/
private structure MapRule where
  lhs : Expr
  rhs : Expr
  /-- The base proof returned when the source reaches `lhs`: either
  `lhs |-tla- rhs` for a global rule, or
  `(lhs ⇒ rhs) |-tla- (lhs ⇒ rhs)` for a proof-mode rule. -/
  proof : Expr

/-- Elaborate the user rule and normalize every global form to `lhs |-tla- rhs`.

Leading theorem parameters are instantiated together so that matching the
rule lhs against the source predicate can infer them. `forallMetaTelescope`
stops at the unexpanded TLA proposition constructors; pointwise state
theorems are intentionally not adapted at this layer. -/
private def normalizeGlobalRule (stateType : Expr) (tm : Term) : TacticM MapRule := do
  let proof ← elabTheoremTerm tm
  let ty ← inferType proof >>= instantiateMVars
  let (args, _, body) ← forallMetaTelescope ty
  let proof := mkAppN proof args
  match_expr body with
  | TLA.pred_implies stateType' lhs rhs =>
      unless ← isDefEq stateType' stateType do
        throwError "tmap: rule state type{indentExpr stateType'}\ndoes not match proof-mode state type{indentExpr stateType}"
      return ⟨lhs, rhs, proof⟩
  | TLA.valid stateType' formula =>
      unless ← isDefEq stateType' stateType do
        throwError "tmap: rule state type{indentExpr stateType'}\ndoes not match proof-mode state type{indentExpr stateType}"
      let some (lhs, rhs) ← recognizeAlwaysImplies? formula
        | throwError "tmap: valid rule must have the form `|-tla- (p ⇒ q)`; got {body}"
      let introEq ← mkAppM ``always_impl_intro #[lhs, rhs]
      let normalized ← mkAppM ``Eq.mp #[introEq, proof]
      return ⟨lhs, rhs, normalized⟩
  | _ => throwError "tmap: expected a rule whose body is `p |-tla- q` or `|-tla- (p ⇒ q)`; got {ty}"

/-- Peel one registered monotone operator, returning the partially applied
operator, its registered theorem, and the inner predicate. Keeping the partial
application allows registered operators to have parameters before the predicate. -/
private def recognizeMonotoneStep? (e : Expr) :
    MetaM (Option (Expr × Name × Expr)) := do
  let env ← getEnv
  recognizeWithTlaModalityHeadUnfold? (recognizeDirect env) e
where
  recognizeDirect (env : Environment) (e : Expr) : Option (Expr × Name × Expr) := do
    let .app op inner := e | none
    let operatorHead ← op.getAppFn'.constName?
    let monotonicityTheorem ← findTmapMonotonicity? env operatorHead
    return (op, monotonicityTheorem, inner)

/-- Instantiate a registered theorem for the particular operator application
and predicates encountered during recursive lifting. Applying against an
expected type also infers any parameters captured by the partial application. -/
private def instantiateMonotonicity
    (theoremName : Name) (op p q : Expr) : MetaM Expr := do
  let stableImplication ← mkAppM ``TLA.always_implies #[p, q]
  let mappedImplication ← mkAppM ``TLA.tla_implies #[mkApp op p, mkApp op q]
  let expectedFormula ← mkAppM ``TLA.tla_implies #[stableImplication, mappedImplication]
  -- CHECK This might be problematic if the theorem is not a `valid` but a `pred_implies`
  let expectedType ← mkAppM ``TLA.valid #[expectedFormula]
  let goal ← mkFreshExprMVar (some expectedType)
  let theoremExpr ← mkConstWithFreshMVarLevels theoremName
  let subgoals ← goal.mvarId!.apply theoremExpr
  unless subgoals.isEmpty do
    throwError "@[tmap_mono] theorem '{theoremName}' has parameters that cannot be inferred from the mapped operator"
  instantiateMVars goal

/-- Transport the current proof through one registered operator. Global rules
and proof-mode rules share the same recursive traversal but maintain different
proof invariants while that traversal unwinds. -/
private abbrev LiftStep := (inner target monotonicity proof : Expr) → MetaM Expr

/-- Lift one step when `proof` is the global raw implication `inner |-tla- target`. -/
private def liftGlobalStep (inner target monotonicity proof : Expr) : MetaM Expr := do
  let introEq ← mkAppM ``always_impl_intro #[inner, target]
  let stableProof ← mkAppM ``Eq.mpr #[introEq, proof]
  mkAppM ``TLA.impl_decouple #[monotonicity, stableProof]

/-- Lift one step when `proof` keeps a proof-mode rule as its explicit premise. -/
private def liftTemporalStep
    (_inner _target monotonicity proof : Expr) : MetaM Expr :=
  mkAppM ``always_implies_map #[monotonicity, proof]

/-- Recursively lift a rule through the registered operators around `source`.

The recursion peels one registered operator from `source` until it reaches
`rule.lhs`. Its base case returns `rule.rhs` and `rule.proof`. As the recursion
unwinds, `liftStep` maintains the proof invariant for either a global raw
implication or a proof-mode rule premise. -/
private partial def liftRule
    (source : Expr) (rule : MapRule) (liftStep : LiftStep) : MetaM (Expr × Expr) := do
  if ← isDefEq source rule.lhs then
    return (rule.rhs, rule.proof)
  let some (op, monotonicityTheorem, inner) ← recognizeMonotoneStep? source
    | throwError "tmap: source predicate{indentExpr source}\nis not the rule lhs{indentExpr rule.lhs}\nunder a supported modality context"
  let (innerTarget, proof) ← liftRule inner rule liftStep
  let monotonicity ← instantiateMonotonicity monotonicityTheorem op inner innerTarget
  let proof ← liftStep inner innerTarget monotonicity proof
  let target := mkApp op innerTarget
  return (target, proof)

-- CHECK These soundness theorems seem kind of tedious, but what would be a better way?
/-- Add a mapped global-rule result using the reflected source position. -/
private theorem Entails_add_global_map {σ : Type u}
    {hyps : List (NamedPred σ)} {goal source : pred σ}
    (sourceIdx : Nat)
    (hsource : (hyps.map NamedPred.pred)[sourceIdx]? = some source)
    (newHypName : String) (newHyp : pred σ) :
    (source) |-tla- (newHyp) →
    Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
    Entails hyps goal := by
  refine Entails_add_new [source] ?_ newHypName newHyp ; grind

/-- Add a mapped proof-mode-rule result using the reflected rule and source
positions. -/
private theorem Entails_add_temporal_map {σ : Type u}
    {hyps : List (NamedPred σ)} {goal relation source : pred σ}
    (ruleIdx sourceIdx : Nat)
    (hrule : (hyps.map NamedPred.pred)[ruleIdx]? = some relation)
    (hsource : (hyps.map NamedPred.pred)[sourceIdx]? = some source)
    (newHypName : String) (newHyp : pred σ) :
    (relation ∧ source) |-tla- (newHyp) →
    Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
    Entails hyps goal := by
  refine Entails_add_new [relation, source] ?_ newHypName newHyp ; grind

/-- Apply a fully instantiated reflection theorem and assign its mapped-proof
premise directly. -/
private def applyMappedHypTheorem (thm proof : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let [hmapGoal, continuation] ← g.apply thm
    | throwError "tmap: unexpected subgoals while adding the mapped hypothesis"
  hmapGoal.withContext do
    unless ← isDefEq (mkMVar hmapGoal) proof do
      let expected ← hmapGoal.getType
      let actual ← inferType proof
      throwError "tmap: internal lifted proof has type{indentExpr actual}\nbut expected{indentExpr expected}"
  replaceMainGoal [continuation]
  postDSimpAfterApplyingReflectionTheorem #[``List.cons_append, ``List.nil_append]

/-- Resolve the source and distinguish a bare proof-mode rule name from an
ordinary Lean theorem term. Lean local variables intentionally take precedence;
that convention is implemented by `temporalHypLocOfBareTerm?`. -/
private def proofModeMap (newName : String) (sourceLoc : TemporalHypLoc)
    (ruleTerm : Term) : TacticM Unit := withMainContext do
  let (stateType, hypsExpr, _, hyps, goal) ← parseCanonicalEntails (← getMainTarget)
    "tmap: goal is not a canonical Entails sequent"
  let (sourceIdx, _, source) ← findIdxByTemporalHypLoc hyps sourceLoc
    "tmap" "the goal's Entails list"
  if let some ruleLoc ← temporalHypLocOfBareTerm? hyps ruleTerm then
    let (ruleIdx, _, relation) ← findIdxByTemporalHypLoc hyps ruleLoc
      "tmap" "the goal's Entails list"
    let some (lhs, rhs) ← recognizeAlwaysImplies? relation
      | throwError "tmap: temporal rule must have the form `p ⇒ q` or `□ (p → q)`; got {relation}"
    -- Reflexivity makes the selected temporal rule an explicit premise. Each
    -- lifting step preserves that same premise via `always_implies_map`.
    let relationProof ← mkAppM ``TLA.pred_implies_refl #[relation]
    let rule : MapRule := ⟨lhs, rhs, relationProof⟩
    let (dst, liftedProof) ← liftRule source rule liftTemporalStep
    -- Only now combine the lifted implication with the selected source.
    let appliedProof ← mkAppM ``always_implies_apply #[liftedProof]
    addTemporalMappedHyp stateType hypsExpr goal relation source dst appliedProof
      ruleIdx sourceIdx newName
  else
    let rule ← normalizeGlobalRule stateType ruleTerm
    let (dst, liftedProof) ← liftRule source rule liftGlobalStep
    addGlobalMappedHyp stateType hypsExpr goal source dst liftedProof sourceIdx newName
where
  /-- Append the result of a global rule. -/
  addGlobalMappedHyp (stateType hypsExpr goal source dst proof : Expr)
    (sourceIdx : Nat) (newName : String) : TacticM Unit := do
  let hsource ← mkAppM ``Option.some #[source] >>= (mkEqRefl ·)
  let thm ← mkAppOptM ``Entails_add_global_map
    #[some stateType, some hypsExpr, some goal, some source, some (toExpr sourceIdx),
      some hsource, some (toExpr newName), some dst]
  applyMappedHypTheorem thm proof
  /-- Append the result of a proof-mode rule. -/
  addTemporalMappedHyp
    (stateType hypsExpr goal relation source dst proof : Expr)
    (ruleIdx sourceIdx : Nat) (newName : String) : TacticM Unit := do
  let hrule ← mkAppM ``Option.some #[relation] >>= (mkEqRefl ·)
  let hsource ← mkAppM ``Option.some #[source] >>= (mkEqRefl ·)
  let thm ← mkAppOptM ``Entails_add_temporal_map
    #[some stateType, some hypsExpr, some goal, some relation, some source,
      some (toExpr ruleIdx), some (toExpr sourceIdx), some hrule, some hsource,
      some (toExpr newName), some dst]
  applyMappedHypTheorem thm proof

/--
`tmap hnew := hsrc using rule` applies an implication `rule` underneath
nesting of modalities that have registered monotonicity.

The rule may prove `p |-tla- q`, `|-tla- (p ⇒ q)`, or `|-tla- □ (p → q)`.
A proof-mode hypothesis `hrule : p ⇒ q` or `hrule : □ (p → q)` is also accepted.

Additional unary predicate operators can be registered with:
```lean
@[tmap_mono]
theorem op_monotone {p q : pred σ} :
    |-tla- ((p ⇒ q) → (op p → op q)) := by
  ...
```
Operators may have parameters before their predicate argument.

For example, from `hp : □ ◇ p` and `hpq : p |-tla- q`,
```lean
tmap hq := hp using hpq
```
adds `hq : □ ◇ q` while preserving the rest of the context.
-/
syntax (name := tlaMapTac) "tmap " ident " := " temporalHypLoc " using " term : tactic

elab_rules : tactic
  | `(tactic| tmap $newName:ident := $source:temporalHypLoc using $rule:term) => do
    let sourceLoc ← parseTemporalHypLoc source "tmap: invalid source hypothesis"
    proofModeMap (toString newName.getId) sourceLoc rule

end TLA.ProofMode
