import Lentil

/- Tests for the `tla_clear` tactic.

   `tla_clear h₁ … hₙ` drops the named hypotheses from the current `Entails`
   sequent via the `Entails_clear` soundness theorem (which filters by name)
   and then `dsimp`s the resulting `List.filter` down to a concrete list.
-/

namespace TLA.ProofMode.Test.Clear

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Clear a single hypothesis.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_clear hp
  show Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- Clear multiple hypotheses in one call.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tla_start hp hq hr
  tla_clear hp hq
  show Entails [⟨"hr", r⟩] r
  exact pred_implies_refl _

-- Clear all hypotheses leaves an empty hypothesis list. (The resulting
-- `Entails [] ⊤` is trivially closable; we only verify the shape via `show`.)
example : (p ∧ q) |-tla- (⊤) := by
  tla_start hp hq
  tla_clear hp hq
  show Entails [] [tlafml| ⊤]
  intro _ _ ; trivial

-- Order of `tla_clear` arguments doesn't matter (filter is by membership);
-- the remaining list keeps the original positional order.
example : (p ∧ q ∧ r) |-tla- (q) → (p ∧ q ∧ r) |-tla- (q) := by
  intro h
  tla_start hp hq hr
  tla_clear hr hp
  show Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- Clearing a name that isn't in the context is a no-op.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_clear nonexistent
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩] q
  exact h

-- Mid-proof use: combine with `tla_apply` forward form, then drop the
-- newly-derived hypothesis.
example (lem : (p) |-tla- (q)) : (p) |-tla- (p) := by
  tla_start hp
  tla_apply lem at hp as hq
  tla_clear hq
  show Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

end TLA.ProofMode.Test.Clear
