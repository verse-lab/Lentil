import Lentil.ProofMode.Basic
import Lentil.ProofMode.Tactics.Intro
import Lentil.ProofMode.Tactics.Revert

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

/-- Pull a pure-fact hypothesis `⟨h, ⌞q⌟⟩` from the temporal context into Lean's
    local context.

    The dedicated soundness theorem is built by composing the soundness of
    `trevert` (which moves the temporal hyp into a `⌞q⌟ → goal` antecedent)
    and `tintro`'s `Entails_pure_fact_intro` (which converts a
    `Entails Γ (⌞q⌟ → goal)` to a Lean-level `q → Entails Γ goal`). Inlining
    the composition here keeps the proof term short. -/
theorem Entails_pull_pure {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toPull : String) {q : Prop} :
  letI idx := hyps.findIdx fun h => h.name == toPull
  letI hyps' := hyps.eraseIdx idx
  hyps[idx]?.map NamedPred.pred = some [tlfml| ⌞ q ⌟] →
  (q → Entails hyps' goal) → Entails hyps goal := by
  intro heq hh
  refine Entails_revert_by_name (toRevert := toPull) ?_
  simp at heq ; rcases heq with ⟨r, heq1, heq2⟩
  rw [List.get?Internal_eq_getElem?, heq1] ; simp only [Option.elim, heq2]
  rw [← Entails_pure_fact_intro]
  exact hh

/--
`tpull_pure h₁ h₂ ...` moves pure temporal hypotheses into Lean's local
context.

For example, if the proof-mode context contains `hP : ⌞P⌟`, then
```lean
tpull_pure hP
```
removes `hP` from the temporal context and introduces a Lean local
`hP : P`.
-/
syntax (name := tlPullPureTac) "tpull_pure" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| tpull_pure $[$hs:ident]*) => do
    for h in hs do withMainContext do
      let g ← getMainGoal
      let target ← cleanupAnnotAndMore (← g.getType)
      let (σ, hypsExpr, hypTy, hyps, goal) ←
        parseCanonicalEntails target "tpull_pure: expected a proof-mode Entails goal"
      let nameStr := toString h.getId
      let some idx := hyps.findIdx? fun hyp => hyp.1 == nameStr
        | throwError "tpull_pure: hypothesis '{nameStr}' not found in the goal's Entails list"
      let (_, pred) := hyps[idx]!
      let_expr Lentil.pure_pred _ q := pred
        | throwError "tpull_pure: hypothesis '{nameStr}' is not a pure predicate; got {pred}"
      -- Pass the original `q` explicitly: inferring it from the lookup equality can
      -- unfold reducible typeclass projections such as `LE.le` to `Nat.le`.
      let somePred ← mkAppM ``Option.some #[pred]
      let heq ← mkEqRefl somePred
      let thm ← mkAppOptM ``Entails_pull_pure
        #[some σ, some hypsExpr, some goal, some (toExpr nameStr), some q, some heq]
      let [g'] ← g.apply thm
        | throwError "tpull_pure: unexpected number of goals after applying the reflection theorem"
      let hypsExpr' ← toHypsList hypTy (hyps.eraseIdx idx)
      let entails' ← mkAppM ``Entails #[hypsExpr', goal]
      -- Restore a canonical target before `intro`, so the new local keeps the
      -- original expression for `q` as well as the intended temporal context.
      let newTarget ← mkArrow q entails'
      replaceMainGoal [← g'.change newTarget]
      evalTactic <| ← `(tactic| intro $h:ident)

/--
`tprove_pure` proves a pure LTL entailment by reducing it to an ordinary Lean
proposition.

For example, on a goal whose temporal conclusion is `⌞P⌟`,
```lean
tprove_pure
```
changes the remaining obligation to the Lean proposition `P`.
-/
macro "tprove_pure" : tactic => `(tactic| refine $(mkIdent ``pred_implies_pure) ?_)

end Lentil.ProofMode
