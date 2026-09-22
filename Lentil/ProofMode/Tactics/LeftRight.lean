module

public import Lentil.ProofMode.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

@[expose] public section

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {a b : pred σ}

-- NOTE: Implemented in a way that is probably more boring than you'd have expected
theorem Entails_or_left : Entails hyps a → Entails hyps (tl_or a b) :=
  fun h => pred_implies_trans h Lentil.or_inl

theorem Entails_or_right : Entails hyps b → Entails hyps (tl_or a b) :=
  fun h => pred_implies_trans h Lentil.or_inr

end

end

public meta section

/--
`tleft` reduces a disjunctive proof-mode goal `p ∨ q` to its left disjunct
`p`.
-/
macro "tleft" : tactic => `(tactic| refine $(mkIdent ``Entails_or_left) ?_)

/--
`tright` reduces a disjunctive proof-mode goal `p ∨ q` to its right
disjunct `q`.
-/
macro "tright" : tactic => `(tactic| refine $(mkIdent ``Entails_or_right) ?_)

end

end Lentil.ProofMode
