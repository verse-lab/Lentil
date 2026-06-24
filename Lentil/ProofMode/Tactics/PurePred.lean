import Lentil.ProofMode.Basic
import Lentil.ProofMode.Tactics.Intro
import Lentil.ProofMode.Tactics.Revert

namespace TLA.ProofMode

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
  hyps[idx]?.map NamedPred.pred = some [tlafml| ⌞ q ⌟] →
  (q → Entails hyps' goal) → Entails hyps goal := by
  intro heq hh
  apply Entails_revert_by_name (toRevert := toPull)
  simp at heq ; rcases heq with ⟨r, heq1, heq2⟩
  rw [List.get?Internal_eq_getElem?, heq1] ; simp only [Option.elim, heq2]
  rw [← Entails_pure_fact_intro]
  exact hh

private def pullPureTacDSimps := #[``List.findIdx, ``List.findIdx.go, ``List.eraseIdx, ``String.reduceBEq,
  ``String.reduceBNe, ``cond_false, ``cond_true, ``Option.elim]

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
syntax (name := tlaPullPureTac) "tpull_pure" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| tpull_pure $[$hs:ident]*) => do
    for h in hs do
      let nameStr := toString h.getId
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_pull_pure) ($(quote nameStr)) (by rfl) ?_ ; intro $h:ident)
      postDSimpAfterApplyingReflectionTheorem pullPureTacDSimps

/--
`tprove_pure` proves a pure TLA entailment by reducing it to an ordinary Lean
proposition.

For example, on a goal whose temporal conclusion is `⌞P⌟`,
```lean
tprove_pure
```
changes the remaining obligation to the Lean proposition `P`.
-/
macro "tprove_pure" : tactic => `(tactic| refine $(mkIdent ``pred_implies_pure) ?_)

end TLA.ProofMode
