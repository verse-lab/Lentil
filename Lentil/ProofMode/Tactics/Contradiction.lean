import Lentil.ProofMode.Tactics.Revert
import Lentil.ProofMode.Tactics.Specialize

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

/-- If the proof-mode context contains `tl_false`, every goal follows
    vacuously. -/
theorem Entails_of_false_in_hyps (idx : Nat) (h : hyps[idx]?.map NamedPred.pred = some tl_false) :
  Entails hyps goal := by
  simp [← List.get?Internal_eq_getElem?] at h ; rcases h with ⟨a, h1, h2⟩
  refine Entails_revert_by_idx idx ?_
  simp only [h1, Option.elim, h2]
  intro _ _ _ hfalse ; exact hfalse.elim

/-- If the proof-mode context contains both `p` and `¬ p`, every goal follows. -/
theorem Entails_of_contradicting_hyps {p : pred σ}
  (idx1 idx2 : Nat)
  (h1 : hyps[idx1]?.map NamedPred.pred = some p)
  (h2 : hyps[idx2]?.map NamedPred.pred = some (tl_not p)) :
  Entails hyps goal := by
  refine Entails_add_new [p, tl_not p] (by grind) "_" tl_false ?_ ?_
  · dsimp only [repeatedAnd, LentilLib.List.foldrD] ; rw [Lentil.and_not_self_iff]
  · exact Entails_of_false_in_hyps hyps.length (by simp)

/-- A proof of `⊥` in the current proof-mode context proves any goal. -/
theorem Entails_false_elim (h : Entails hyps tl_false) : Entails hyps goal :=
  fun e i hhyps => (h e i hhyps).elim

end

/-- `texfalso` changes the current proof-mode goal to `⊥`. -/
macro "texfalso" : tactic =>
  `(tactic| refine $(mkIdent ``Entails_false_elim) ?_)

/--
`tcontradiction` closes any proof-mode goal whose context contains an
explicit contradiction:

* a temporal hypothesis with predicate `⊥` (i.e. `tl_false`), or
* a pair of temporal hypotheses with predicates `p` and `¬ p`.

It fails if neither pattern is found.
-/
syntax (name := tlContradictionTac) "tcontradiction" : tactic

elab_rules : tactic
  | `(tactic| tcontradiction) => withMainContext do
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "tcontradiction: goal is not an Entails sequent"
    -- Step 1: a `tl_false` hypothesis closes the goal directly.
    if let some idx := hyps.findIdx? fun x => x.2.isAppOf' ``Lentil.tl_false then
      evalTactic <| ← `(tactic| exact $(mkIdent ``Entails_of_false_in_hyps) ($(quote idx)) (by rfl))
      return
    -- Step 2: a `(p, ¬ p)` pair, with `p` matched by `isDefEq`.
    let hyps := hyps.zipIdx
    for (x, idx2) in hyps do
      let_expr Lentil.tl_not _ p := x.2 | continue
      if let some (_, idx1) ← hyps.findM? fun y => isDefEq y.1.2 p then
        evalTactic <| ← `(tactic|
          exact $(mkIdent ``Entails_of_contradicting_hyps) ($(quote idx1)) ($(quote idx2)) (by rfl) (by rfl))
        return
    throwError "tcontradiction: no contradiction found in proof-mode context"

end Lentil.ProofMode
