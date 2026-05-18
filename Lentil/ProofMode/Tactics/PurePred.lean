import Lentil.ProofMode.Basic
import Lentil.ProofMode.Tactics.Intro
import Lentil.ProofMode.Tactics.Revert

namespace TLA.ProofMode

open Lean Meta Elab Tactic

/-- Pull a pure-fact hypothesis `⟨h, ⌞q⌟⟩` from the temporal context into Lean's
    local context.

    The dedicated soundness theorem is built by composing the soundness of
    `tla_revert` (which moves the temporal hyp into a `⌞q⌟ → goal` antecedent)
    and `tla_intro`'s `Entails_pure_fact_intro` (which converts a
    `Entails Γ (⌞q⌟ → goal)` to a Lean-level `q → Entails Γ goal`). Inlining
    the composition here keeps the proof term short. -/
theorem Entails_pull_pure {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
    (toPull : String) {q : Prop}
    (hfound : hyps.find? (fun h => h.name == toPull) = some ⟨toPull, [tlafml| ⌞ q ⌟]⟩) :
    letI hyps' := hyps.eraseP fun h => h.name == toPull
    (q → Entails hyps' goal) → Entails hyps goal := by
  intro hh
  apply Entails_revert (toRevert := toPull)
  rw [hfound] ; dsimp only [Option.elim]
  rw [← Entails_pure_fact_intro]
  exact hh

private def pullPureTacDSimps := #[``List.find?, ``List.eraseP, ``String.reduceBEq,
  ``String.reduceBNe, ``cond_false, ``cond_true, ``Option.elim]

/--
`tla_pull_pure h₁ h₂ ...` moves pure temporal hypotheses into Lean's local
context.

For example, if the proof-mode context contains `hP : ⌞P⌟`, then
```lean
tla_pull_pure hP
```
removes `hP` from the temporal context and introduces a Lean local
`hP : P`.
-/
syntax (name := tlaPullPureTac) "tla_pull_pure" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| tla_pull_pure $[$hs:ident]*) => do
    for h in hs do
      let nameStr := toString h.getId
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_pull_pure) ($(quote nameStr)) (by rfl) ?_ ; intro $h:ident)
      postDSimpAfterApplyingReflectionTheorem pullPureTacDSimps

/--
`tla_prove_pure` proves a pure TLA entailment by reducing it to an ordinary Lean
proposition.

For example, on a goal whose temporal conclusion is `⌞P⌟`,
```lean
tla_prove_pure
```
changes the remaining obligation to the Lean proposition `P`.
-/
macro "tla_prove_pure" : tactic => `(tactic| refine $(mkIdent ``pred_implies_pure) ?_)

end TLA.ProofMode
