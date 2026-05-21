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
  tla_check_goal Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- Clear multiple hypotheses in one call.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tla_start hp hq hr
  tla_clear hp hq
  tla_check_goal Entails [⟨"hr", r⟩] r
  exact pred_implies_refl _

-- Clear all hypotheses leaves an empty hypothesis list. (The resulting
-- `Entails [] ⊤` is trivially closable; we only verify the named goal shape.)
example : (p ∧ q) |-tla- (⊤) := by
  tla_start hp hq
  tla_clear hp hq
  tla_check_goal Entails [] [tlafml| ⊤]
  intro _ _ ; trivial

-- Order of `tla_clear` arguments doesn't matter (filter is by membership);
-- the remaining list keeps the original positional order.
example : (p ∧ q ∧ r) |-tla- (q) → (p ∧ q ∧ r) |-tla- (q) := by
  intro h
  tla_start hp hq hr
  tla_clear hr hp
  tla_check_goal Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- `tla_clear * - ...` clears every hypothesis except the listed ones.
example : (p ∧ q ∧ r) |-tla- (q) → (p ∧ q ∧ r) |-tla- (q) := by
  intro h
  tla_start hp hq hr
  tla_clear * - hq
  tla_check_goal Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- The clear-except form preserves the original order of the kept hypotheses.
example : (p ∧ q ∧ r) |-tla- ([tlafml| p ∧ r]) → (p ∧ q ∧ r) |-tla- ([tlafml| p ∧ r]) := by
  intro h
  tla_start hp hq hr
  tla_clear *- hp hr
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hr", r⟩] [tlafml| p ∧ r]
  exact pred_implies_refl _

-- With no names after the minus, the clear-except form clears all hypotheses.
example : (p ∧ q) |-tla- (⊤) := by
  tla_start hp hq
  tla_clear * -
  tla_check_goal Entails [] [tlafml| ⊤]
  intro _ _ ; trivial

-- Clearing a name that isn't in the context is a no-op.
example : (p ∧ q) |-tla- (q) → (p ∧ q) |-tla- (q) := by
  intro h
  tla_start hp hq
  tla_clear nonexistent
  tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] q
  exact h

-- Mid-proof use: derive a hypothesis with `tla_have`, then drop it.
example (lem : (p) |-tla- (q)) : (p) |-tla- (p) := by
  tla_start hp
  tla_have hq := lem hp
  tla_clear hq
  tla_check_goal Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

end TLA.ProofMode.Test.Clear
