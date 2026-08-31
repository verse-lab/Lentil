import Lentil.ProofMode.Tactics.Have
import Lentil.Expr

namespace Lentil.ProofMode

open Lean Meta Elab Tactic LentilLib

theorem Entails_trans {σ : Type u} {hyps : List (NamedPred σ)} {mid goal : pred σ} :
  (mid) |-tl- (goal) → Entails hyps mid → Entails hyps goal := by
  intro h1 h2 ; revert h1 ; revert h2 ; apply pred_implies_trans

/-
`tapply t` first tries Lean's ordinary `apply`. If that cannot consume reflected
proof-mode hypotheses, `tlHaveTerm` introduces the theorem as the newest
temporal hypothesis and delegates its temporal arguments to `tspecialize`.
`tlHaveTerm` keeps the theorem conclusion assignable, so the current target can
still constrain it here. Then this file inspects the introduced hypothesis,
splits its remaining implication chain with
`Lentil.Expr.splitImplicationsIntoParts`, and applies `Entails_apply_hyp` with an
explicit list of premise metavariables of the same length.
-/

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

-- Well, this "last" thing might be too specific?

theorem Entails_apply_hyp (hs : List (pred σ)) (h : hyps.getLast?.map NamedPred.pred = some (repeatedImplies hs goal)) :
  Entails hyps.dropLast (repeatedAnd hs) → Entails hyps goal := by
  unfold Entails
  simp [List.getLast?_eq_some_iff] at h ; rcases h with ⟨a, ⟨hyps, rfl⟩, heq⟩
  simp [heq, repeatedAnd_append, repeatedAnd_singleton, ← impl_intro_add_r]
  intro h ; refine pred_implies_trans h ?_ ; simp [impl_intro_add_r]
  apply repeatedImplies_apply

-- FIXME: Generalize this to allow `tassumption`
theorem Entails_apply_hyp_closing_goal (h : hyps.getLast?.map NamedPred.pred = some goal) :
  Entails hyps goal := Entails_apply_hyp [] h (by intro _ _ _ ; exact True.intro)

end

private def applyTacDSimps := #[``repeatedAnd, ``LentilLib.List.foldrD, ``List.dropLast,
  ``List.foldr]

private def goalDirectedPremisesCut (remainingPremises : List Expr) (goal conclusion : Expr) : MetaM (List Expr) := do
  if ← isDefEq goal conclusion then
    return remainingPremises
  else
    match remainingPremises with
    | [] => throwError "tapply: failed to find a way to unify the goal and the hypothesis conclusion"
    | prem :: rest =>
      let newConclusion ← mkAppM ``tl_implies #[prem, conclusion]
      goalDirectedPremisesCut rest goal newConclusion

def applyIntroducedHypByIdx (idx : Nat) : TacticM Unit := withMainContext do
  let g ← getMainTarget
  let g := g.headBeta.cleanupAnnotations    -- Since `getMainTarget` does `instantiateMVars`
  let_expr Lentil.ProofMode.Entails _ hyps goal := g
    | throwError "tapply: goal is not an Entails sequent, but {g}"
  let some (_, hyps) ← recognizeHypsList hyps
    | throwError "tapply: failed to read the hypotheses from the goal"
  let some (_, pred) := hyps[idx]?
    | throwError "tapply: failed to find the introduced theorem hypothesis"
  -- NOTE: For convenience, do not cut inner `∧`s
  let (premises, conclusion) ← Lentil.Expr.splitImplicationsIntoParts pred (cutAnd? := false)
  -- The goal might be an implication, so need to find where to cut `premises`
  let premisesToProve ← goalDirectedPremisesCut premises goal conclusion
  if premisesToProve.isEmpty then
    evalTactic <| ← `(tactic| exact $(mkIdent ``Entails_apply_hyp_closing_goal) (by rfl))
  else
    let holesListStx ← do
      let holes := Array.replicate premisesToProve.length (← `(_))
      `([$holes,*])
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_apply_hyp) $holesListStx (by rfl) ?_)
    postDSimpAfterApplyingReflectionTheorem applyTacDSimps

/--
`tapply t` proves the current proof-mode goal using a LTL theorem or a
temporal hypothesis. If the theorem concludes the current goal but still has
unsupplied temporal premises, those premises become new proof-mode goals.

For example, if the context contains `hp : p` and the goal is `q`, then
`tapply h hp` closes the goal when `h` proves `p |-tl- q`:
```lean
tapply lemma hp
```

If the goal is `r` and `lemma hp` has type `q |-tl- r`, then
```lean
tapply lemma hp
```
changes the goal to `q`.
-/
syntax (name := tlApplyBackwardTac) "tapply " term : tactic
/--
`tapply' thm arg₁ ... argₙ` proves the current proof-mode goal by applying
the theorem or local hypothesis `thm` to the given arguments.

Compared with `tapply t`, the prime form is more restricted: the theorem
head must be an identifier, not an arbitrary Lean term. In exchange, its
arguments may be written as LTL formulas, without explicit `[tlfml| ... ]`
wrappers.

Writing `@thm` instead of `thm` exposes implicit theorem arguments, just like
Lean's ordinary `@` notation.

For example, if `lem : ∀ p : pred σ, (p) |-tl- r`, then
```lean
tapply' lem (p ∧ q)
```
reduces the current goal `r` to proving `p ∧ q`.
-/
syntax (name := tlApplyPrimeBackwardTac) "tapply' " ("@")? ident (ppSpace colGt tlMixedArg)* : tactic

elab_rules : tactic
  | `(tactic| tapply $tm:term) => withMainContext do
    (do
      let g ← getMainGoal
      let gs ← evalTacticAt (← `(tactic| refine @$(mkIdent ``Entails_trans) _ _ ?_ _ ?_ ?_)) g
      -- NOTE: This is kind of ad-hoc, relying on the exact shape of `Entails_trans`
      let [midGoal, theoremGoal, entailsGoal] := gs
        | throwError "tapply: failed to generate the expected number of subgoals"
      replaceMainGoal [theoremGoal, entailsGoal, midGoal]
      -- NOTE: `mid` is an auxiliary predicate to be inferred by applying the theorem;
      -- make it assignable by unification instead of leaving it synthetic opaque.
      midGoal.setKind .natural
      Tactic.focusAndDone <| evalTactic <| ← `(tactic| apply $tm)
      pruneSolvedGoals)
    <|>
    (do
      let internalName ← mkFreshInternalTemporalHypName
      let idx ← tlHaveTerm internalName tm
      applyIntroducedHypByIdx idx)
  | `(tactic| tapply' $[@%$explicit?]? $head:ident $[$args:tlMixedArg]*) => withMainContext do
    let internalName ← mkFreshInternalTemporalHypName
    let idx ← tlHavePrimeTerm internalName head explicit?.isSome args
    applyIntroducedHypByIdx idx

end Lentil.ProofMode
