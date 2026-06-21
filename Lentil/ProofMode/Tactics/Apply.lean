import Lentil.ProofMode.Tactics.Have
import Lentil.Expr

namespace TLA.ProofMode

open Lean Meta Elab Tactic LentilLib

theorem Entails_trans {σ : Type u} {hyps : List (NamedPred σ)} {mid goal : pred σ} :
  (mid) |-tla- (goal) → Entails hyps mid → Entails hyps goal := by
  intro h1 h2 ; revert h1 ; revert h2 ; apply pred_implies_trans

/-
`tla_apply t` is implemented through `tla_have := t`.

First, `tlaHaveTerm` introduces the theorem to apply as the newest temporal
hypothesis and delegates all supplied arguments to `tla_specialize`. Then this
file inspects that newest hypothesis, splits its remaining implication chain
with `TLA.Expr.splitImplicationsIntoParts`, and applies `Entails_apply_hyp` with
an explicit list of premise metavariables of the same length. This avoids the
old residual-premise guessing loop.
-/

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

-- Well, this "last" thing might be too specific?

theorem Entails_apply_hyp (hs : List (pred σ)) (h : hyps.getLast?.map NamedPred.pred = some (repeatedImplies hs goal)) :
  Entails hyps.dropLast (repeatedAnd hs) → Entails hyps goal := by
  unfold Entails
  simp [List.getLast?_eq_some_iff] at h ; rcases h with ⟨a, ⟨hyps, rfl⟩, heq⟩
  simp [heq, repeatedAnd_append, repeatedAnd_singleton, ← impl_intro_add_r]
  intro h ; apply pred_implies_trans h ; simp [impl_intro_add_r]
  apply repeatedImplies_apply

-- FIXME: Generalize this to allow `tla_assumption`
theorem Entails_apply_hyp_closing_goal (h : hyps.getLast?.map NamedPred.pred = some goal) :
  Entails hyps goal := Entails_apply_hyp [] h (by intro _ _ ; exact True.intro)

end

private def applyTacDSimps := #[``repeatedAnd, ``LentilLib.List.foldrD, ``List.dropLast,
  ``List.foldr]

private def goalDirectedPremisesCut (remainingPremises : List Expr) (goal conclusion : Expr) : MetaM (List Expr) := do
  if ← isDefEq goal conclusion then
    return remainingPremises
  else
    match remainingPremises with
    | [] => throwError "tla_apply: failed to find a way to unify the goal and the hypothesis conclusion"
    | prem :: rest =>
      let newConclusion ← mkAppM ``tla_implies #[prem, conclusion]
      goalDirectedPremisesCut rest goal newConclusion

private def applyIntroducedHypByIdx (idx : Nat) : TacticM Unit := withMainContext do
  let g ← getMainTarget
  let g := g.headBeta.cleanupAnnotations    -- Since `getMainTarget` does `instantiateMVars`
  let_expr TLA.ProofMode.Entails _ hyps goal := g
    | throwError "tla_apply: goal is not an Entails sequent, but {g}"
  let some (_, hyps) ← recognizeHypsList hyps
    | throwError "tla_apply: failed to read the hypotheses from the goal"
  let some (_, pred) := hyps[idx]?
    | throwError "tla_apply: failed to find the introduced theorem hypothesis"
  -- NOTE: For convenience, do not cut inner `∧`s
  let (premises, conclusion) ← TLA.Expr.splitImplicationsIntoParts pred (cutAnd? := false)
  -- The goal might be an implication, so need to find where to cut `premises`
  let premisesToProve ← goalDirectedPremisesCut premises goal conclusion
  if premisesToProve.isEmpty then
    evalTactic <| ← `(tactic| apply $(mkIdent ``Entails_apply_hyp_closing_goal) (by rfl))
  else
    let holesListStx ← do
      let holes := Array.replicate premisesToProve.length (← `(_))
      `([$holes,*])
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_apply_hyp) $holesListStx (by rfl) ?_)
    postDSimpAfterApplyingReflectionTheorem applyTacDSimps

/--
`tla_apply t` proves the current proof-mode goal using a TLA theorem or a
temporal hypothesis. If the theorem concludes the current goal but still has
unsupplied temporal premises, those premises become new proof-mode goals.

For example, if the context contains `hp : p` and the goal is `q`, then
`tla_apply h hp` closes the goal when `h` proves `p |-tla- q`:
```lean
tla_apply lemma hp
```

If the goal is `r` and `lemma hp` has type `q |-tla- r`, then
```lean
tla_apply lemma hp
```
changes the goal to `q`.
-/
syntax (name := tlaApplyBackwardTac) "tla_apply " term : tactic
/--
`tla_apply' thm arg₁ ... argₙ` proves the current proof-mode goal by applying
the theorem or local hypothesis `thm` to the given arguments.

Compared with `tla_apply t`, the prime form is more restricted: the theorem
head must be an identifier, not an arbitrary Lean term. In exchange, its
arguments may be written as TLA formulas, without explicit `[tlafml| ... ]`
wrappers.

Writing `@thm` instead of `thm` exposes implicit theorem arguments, just like
Lean's ordinary `@` notation.

For example, if `lem : ∀ p : pred σ, (p) |-tla- r`, then
```lean
tla_apply' lem (p ∧ q)
```
reduces the current goal `r` to proving `p ∧ q`.
-/
syntax (name := tlaApplyPrimeBackwardTac) "tla_apply' " ("@")? ident (ppSpace colGt tlaMixedArg)* : tactic

elab_rules : tactic
  | `(tactic| tla_apply $tm:term) => withMainContext do
    (do
      let g ← getMainGoal
      let gs ← evalTacticAt (← `(tactic| refine @$(mkIdent ``Entails_trans) _ _ ?_ _ ?_ ?_)) g
      -- NOTE: This is kind of ad-hoc, relying on the exact shape of `Entails_trans`
      let [midGoal, theoremGoal, entailsGoal] := gs
        | throwError "tla_apply: failed to generate the expected number of subgoals"
      replaceMainGoal [theoremGoal, entailsGoal, midGoal]
      -- NOTE: `mid` is an auxiliary predicate to be inferred by applying the theorem;
      -- make it assignable by unification instead of leaving it synthetic opaque.
      midGoal.setKind .natural
      Tactic.focusAndDone <| evalTactic <| ← `(tactic| apply $tm)
      pruneSolvedGoals)
    <|>
    (do
      let idx ← tlaHaveTerm default /- the name does not matter here -/ tm
      applyIntroducedHypByIdx idx)
  | `(tactic| tla_apply' $[@%$explicit?]? $head:ident $[$args:tlaMixedArg]*) => withMainContext do
    let idx ← tlaHavePrimeTerm default /- the name does not matter here -/ head explicit?.isSome args
    applyIntroducedHypByIdx idx

end TLA.ProofMode
