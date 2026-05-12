import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_exists {σ : Type u} {hyps : List (NamedPred σ)}
    {α : Type v} {p : α → pred σ} (witness : α) :
    Entails hyps (p witness) → Entails hyps (TLA.tla_exists p) := exists_elim witness

syntax (name := tlaExistsTac) "tla_exists" (ppSpace colGt term),+ : tactic

elab_rules : tactic
  | `(tactic| tla_exists $[$ts],*) => do
    for t in ts do
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_exists) $t ?_)

end TLA.ProofMode
