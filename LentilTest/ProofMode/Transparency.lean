import Lentil

/- Tests for type transparency in ordinary Lentil tactic workflows.

   Named predicates and formulas built with the temporal DSL should work with
   ordinary `def` transparency for `pred` and `exec`. The anonymous-action case
   separately checks an actual failure before enabling the `action` attribute.
   Lean requires passing through `irreducible` to restore `semireducible` on
   imported definitions; all attribute changes below remain local.
-/

namespace Lentil.ProofMode.Test.Transparency

open Lentil Lentil.ProofMode

set_option pp.unicode.fun false

section OrdinaryPredicates

-- Lean permits `[local semireducible]` only after `[local irreducible]`.
-- The first line is a transition; the final state is ordinary `def` transparency.
-- Both lines are redundant today, but keep this test condition if attributes change.
attribute [local irreducible] exec pred
attribute [local semireducible] exec pred

def localCondition {σ : Type u} (p q : σ → Prop) : pred σ :=
  [tlfml| ⌜ p ⌝ ∧ ◯ ⌜ q ⌝]

example {σ : Type u} (p q : pred σ) : (□ p ∧ ◇ q) |-tl- (◇ q) := by
  tstart hp hq
  tadvance hq
  tapply now_weaken_to_eventually
  tassumption

example {σ : Type u} (p : σ → Prop) : (◇ ⌜ p ⌝) |-tl- (◇ ⌜ p ⌝) := by
  tstart hp
  tadvance hp
  tapply now_weaken_to_eventually
  tassumption

example {σ : Type u} (p q : pred σ) :
    (◇ (p ∧ ◯ q)) |-tl- (◇ (p ∧ ◯ q)) := by
  tstart h
  tadvance h
  tapply now_weaken_to_eventually
  tassumption

example {σ : Type u} (p q : σ → Prop) :
    (◇ (localCondition p q)) |-tl- (◇ (localCondition p q)) := by
  tstart h
  tunfold localCondition at *
  tadvance h
  guard_target =ₛ Entails [⟨"h", [tlfml| ⌜ p ⌝ ∧ ◯ ⌜ q ⌝]⟩]
    [tlfml| ◇ (⌜ p ⌝ ∧ ◯ ⌜ q ⌝)]
  tapply now_weaken_to_eventually
  tassumption

example {σ : Type u} (p q : σ → Prop) :
    (localCondition p q) |-tl- (◯ ⌜ q ⌝) := by
  tstart h
  tdsimp only [localCondition] at h
  tfinite_window
  exact h.2

end OrdinaryPredicates

section Action

attribute [local irreducible] action
attribute [local semireducible] action

/--
error: tfinite_window: failed to synthesize exact finite-window approximation for [tlfml|⟨ fun s s' => p s ↔ q s' ⟩]
-/
#guard_msgs in
example {σ : Type u} (p q : σ → Prop) :
    (⌜ p ⌝ ↔ ◯ ⌜ q ⌝) =tl= ⟨ fun s s' => p s ↔ q s' ⟩ := by
  tfinite_window
  guard_target =ₛ (p s ↔ q s') ↔ (p s ↔ q s')
  exact Iff.rfl

attribute [local implicit_reducible] action

example {σ : Type u} (p q : σ → Prop) :
    (⌜ p ⌝ ↔ ◯ ⌜ q ⌝) =tl= ⟨ fun s s' => p s ↔ q s' ⟩ := by
  tfinite_window
  guard_target =ₛ (p s ↔ q s') ↔ (p s ↔ q s')
  exact Iff.rfl

end Action

end Lentil.ProofMode.Test.Transparency
