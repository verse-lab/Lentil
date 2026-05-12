import Lentil.ProofMode.Tactics.Apply

namespace TLA.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

theorem Entails_have_or_suffices {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
    (newHypName : String) (newHyp : pred σ) :
    Entails hyps newHyp →
    Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
    Entails hyps goal := Entails_add_new _ (List.Subset.refl _) newHypName newHyp

theorem Entails_have_valid {σ : Type u} {hyps : List (NamedPred σ)} {goal newHyp : pred σ}
    (newHypName : String) :
    (|-tla- (newHyp)) →
    Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
    Entails hyps goal := by rw [valid_eq_true_implies] ; exact Entails_add_new [] (List.nil_subset _) newHypName newHyp

private def haveTacDSimps : Array Name := #[``List.cons_append, ``List.nil_append]

declare_syntax_cat tlaHaveClause
syntax " : " tlafml " by " tacticSeq : tlaHaveClause
syntax " := " term : tlaHaveClause
syntax (name := tlaHaveTac) "tla_have" (ppSpace colGt ident) tlaHaveClause : tactic
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
    evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails (hyps ++ [⟨h, fml⟩]) goal` — collapse the `++`.
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps

  | `(tactic| tla_have $h:ident := $t:term) => do
    let nameStr := toString h.getId
    evalTactic <| ← `(tactic|
      refine $(mkIdent ``Entails_have_valid) ($(quote nameStr)) (by apply $t) ?_)
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps

  | `(tactic| tla_suffices $h:ident : $fml:tlafml by $tac:tacticSeq) => do
    haveOrSufficesCommon h fml
    -- Swap so the `Entails (hyps ++ …) goal` goal is focused, clean up the `++`,
    -- then close it with the user's tac.
    evalTactic <| ← `(tactic| swap)
    postDSimpAfterApplyingReflectionTheorem haveTacDSimps
    evalTactic <| ← `(tactic| ($tac))
    -- Remaining main goal: `Entails hyps fml` (no `++` to clean).

end TLA.ProofMode
