import Lentil

/- Tests for the `tclear` tactic.

   `tclear h₁ … hₙ` drops the named hypotheses from the current `Entails`
   sequent via the `Entails_clear` soundness theorem (which filters by name)
   and then `dsimp`s the resulting `List.filter` down to a concrete list.
-/

namespace Lentil.ProofMode.Test.Clear

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Clear a single hypothesis.
example : (p ∧ q) |-tl- (q) → (p ∧ q) |-tl- (q) := by
  intro h
  tstart hp hq
  tclear hp
  guard_target =ₛ Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- Clear multiple hypotheses in one call.
example : (p ∧ q ∧ r) |-tl- (r) → (p ∧ q ∧ r) |-tl- (r) := by
  intro h
  tstart hp hq hr
  tclear hp hq
  guard_target =ₛ Entails [⟨"hr", r⟩] r
  exact pred_implies_refl _

-- Clear all hypotheses leaves an empty hypothesis list. (The resulting
-- `Entails [] ⊤` is trivially closable; we only verify the named goal shape.)
example : (p ∧ q) |-tl- (⊤) := by
  tstart hp hq
  tclear hp hq
  guard_target =ₛ @Entails σ [] (@Lentil.tl_true σ)
  tprove_pure
  trivial

-- Order of `tclear` arguments doesn't matter (filter is by membership);
-- the remaining list keeps the original positional order.
example : (p ∧ q ∧ r) |-tl- (q) → (p ∧ q ∧ r) |-tl- (q) := by
  intro h
  tstart hp hq hr
  tclear hr hp
  guard_target =ₛ Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- `tclear * - ...` clears every hypothesis except the listed ones.
example : (p ∧ q ∧ r) |-tl- (q) → (p ∧ q ∧ r) |-tl- (q) := by
  intro h
  tstart hp hq hr
  tclear * - hq
  guard_target =ₛ Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- The clear-except form preserves the original order of the kept hypotheses.
example : (p ∧ q ∧ r) |-tl- ([tlfml| p ∧ r]) → (p ∧ q ∧ r) |-tl- ([tlfml| p ∧ r]) := by
  intro h
  tstart hp hq hr
  tclear *- hp hr
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hr", r⟩] [tlfml| p ∧ r]
  exact pred_implies_refl _

-- With no names after the minus, the clear-except form clears all hypotheses.
example : (p ∧ q) |-tl- (⊤) := by
  tstart hp hq
  tclear * -
  guard_target =ₛ @Entails σ [] (@Lentil.tl_true σ)
  tprove_pure
  trivial

-- Clearing a name that isn't in the context is a no-op.
example : (p ∧ q) |-tl- (q) → (p ∧ q) |-tl- (q) := by
  intro h
  tstart hp hq
  tclear nonexistent
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] q
  exact h

-- Mid-proof use: derive a hypothesis with `thave`, then drop it.
example (lem : (p) |-tl- (q)) : (p) |-tl- (p) := by
  tstart hp
  thave hq := lem hp
  tclear hq
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

end Lentil.ProofMode.Test.Clear
