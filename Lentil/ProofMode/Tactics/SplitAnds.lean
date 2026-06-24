import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_and_split {σ : Type u} {hyps : List (NamedPred σ)} {g1 g2 : pred σ} :
  Entails hyps (tla_and g1 g2) = (Entails hyps g1 ∧ Entails hyps g2) := and_pred_implies_split ..

/--
`tsplit_ands` splits a conjunctive proof-mode goal into separate goals.

For example, if the proof-mode goal is `p ∧ q`, then
```lean
tsplit_ands
```
creates one goal for `p` and one goal for `q`.
-/
macro "tsplit_ands" : tactic => `(tactic| (simp only [$(mkIdent ``Entails_and_split):ident] ; split_ands ))

end TLA.ProofMode
