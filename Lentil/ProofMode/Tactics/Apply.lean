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

private def applyTacDSimps := #[``repeatedAnd, ``LentilLib.List.foldrD, ``List.dropLast]

private def getHypByIdx (idx : Nat) : TacticM Expr := do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal
    | throwError "tla_apply: failed to read the hypotheses from the goal"
  let some (_, pred) := hyps[idx]?
    | throwError "tla_apply: failed to find the introduced theorem hypothesis"
  return pred

syntax (name := tlaApplyBackwardTac) "tla_apply " term : tactic

elab_rules : tactic
  | `(tactic| tla_apply $tm:term) => withMainContext do
    (do evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_trans) (by apply $tm) ?_))
    <|>
    (do
      let idx ← tlaHaveTerm default /- the name does not matter here -/ tm
      withMainContext do
      let pred ← getHypByIdx idx
      -- NOTE: For convenience, do not cut inner `∧`s
      let (premises, _) ← TLA.Expr.splitImplicationsIntoParts pred (cutAnd? := false)
      if premises.isEmpty then
        evalTactic <| ← `(tactic| apply $(mkIdent ``Entails_apply_hyp_closing_goal) (by rfl))
      else
        let holesListStx ← do
          let holes := Array.replicate premises.length (← `(_))
          `([$holes,*])
        evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_apply_hyp) $holesListStx (by rfl) ?_)
        postDSimpAfterApplyingReflectionTheorem applyTacDSimps)

end TLA.ProofMode
