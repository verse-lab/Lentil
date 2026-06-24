import Lentil

/- Tests for finite-window sequent reduction. -/

namespace TLA.Test.StateFinite

open TLA

variable {σ : Type u}

example {init inv : σ → Prop} (hinit : ∀ s, init s → inv s) :
    (⌜ init ⌝) |-tla- (⌜ inv ⌝) := by
  tfinite_window
  aesop

example {inv : σ → Prop} {next : action σ}
    (hnext : ∀ s s', next s s' → inv s → inv s') :
    (⌜ inv ⌝ ∧ ⟨next⟩) |-tla- (◯ ⌜ inv ⌝) := by
  tfinite_window
  aesop

example {p q : σ → Prop} :
    (⌜ p ⌝ ∧ ◯ ⌜ q ⌝) |-tla- (◯ ⌜ q ⌝ ∧ ⌜ p ⌝) := by
  tfinite_window
  aesop

/--
error: tfinite_window: failed to synthesize a finite-window instance for [tlafml|□⌜ p ⌝ → □⌜ p ⌝]
-/
#guard_msgs in
example {p : σ → Prop} : (□ ⌜ p ⌝) |-tla- (□ ⌜ p ⌝) := by
  tfinite_window

end TLA.Test.StateFinite
