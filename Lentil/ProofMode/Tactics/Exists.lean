module

public import Lentil.ProofMode.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

@[expose] public section

theorem Entails_exists {σ : Type u} {hyps : List (NamedPred σ)}
    {α : Sort v} {p : α → pred σ} (witness : α) :
    Entails hyps (p witness) → Entails hyps (Lentil.tl_exists p) := exists_elim witness

end

public meta section

/--
`texists w₁, w₂, ...` supplies witnesses for existential quantifiers in the
proof-mode goal.

For example, if the goal is `∃ n : Nat, P n`, then
```lean
texists 0
```
changes the goal to `P 0`. Multiple witnesses are applied from left to right,
so `texists n, m` handles a goal such as `∃ n, ∃ m, P n m`.
-/
syntax (name := tlExistsTac) "texists" (ppSpace colGt term),+ : tactic

elab_rules : tactic
  | `(tactic| texists $[$ts],*) => do
    for t in ts do
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_exists) $t ?_)

end

end Lentil.ProofMode
