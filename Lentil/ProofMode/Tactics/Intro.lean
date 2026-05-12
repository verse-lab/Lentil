import Lentil.Rules.Basic
import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_intro_forall {σ : Type u} {hyps : List (NamedPred σ)}
  {α : Type v} {p : α → pred σ} :
  (∀ x, Entails hyps (p x)) → Entails hyps (TLA.tla_forall p) := forall_elim.mp

theorem Entails_pure_fact_intro {σ : Type u} {hyps : List (NamedPred σ)}
  {q : Prop} {p : pred σ} :
  (q → Entails hyps p) = Entails hyps [tlafml| ⌞ q ⌟ → p ] := pure_fact_intro

theorem Entails_intro_temporal {σ : Type u} {hyps : List (NamedPred σ)}
  {goal newHyp : pred σ} (newHypName : String) :
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal =
  Entails hyps [tlafml| newHyp → goal ] := by
  unfold Entails ; simp [impl_intro_add_r, repeatedAnd_append] ; rfl

private def introTacDSimps := #[``List.cons_append, ``List.nil_append]

syntax (name := tlaIntroTac) "tla_intro" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| tla_intro%$tk $[$names:ident]*) => do
    -- Following the built-in `intro` tactic: wrap each iteration in its own
    -- `withTacticInfoContext` so the proof state in the infoview steps through
    -- the identifiers one-by-one as the cursor advances past each name.
    for name in names, i in 0...* do
      let ctxRef := if i == 0 then Lean.mkNullNode #[tk, name] else name
      withTacticInfoContext ctxRef <| withRef name <| withMainContext do
        let ty ← getMainTarget
        let ty := ty.headBeta.cleanupAnnotations
        let_expr TLA.ProofMode.Entails _ _ goalPred := ty
          | throwError "tla_intro: goal is not an Entails sequent, but {ty}"
        match_expr goalPred with
        | TLA.tla_forall _ _ _ =>
          evalTactic <| ← `(tactic|
            refine $(mkIdent ``Entails_intro_forall) ?_ ; intro $name:ident)
        | TLA.tla_implies _ lhs _ =>
          if lhs.isAppOf' ``TLA.pure_pred then
            evalTactic <| ← `(tactic|
              refine $(mkIdent ``Entails_pure_fact_intro).$(mkIdent `mp) ?_ ; intro $name:ident)
          else
            let nameStr := toString name.getId
            evalTactic <| ← `(tactic|
              refine ($(mkIdent ``Entails_intro_temporal) ($(quote nameStr))).$(mkIdent `mp) ?_)
            postDSimpAfterApplyingReflectionTheorem introTacDSimps
        | _ =>
          throwError "tla_intro: goal predicate is not a ∀ or a ⌞..⌟ →; got {goalPred}"

end TLA.ProofMode
