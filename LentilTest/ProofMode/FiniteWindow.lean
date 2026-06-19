import Lentil

/- Tests for running `tla_finite_window` directly on proof-mode `Entails` goals. -/

namespace TLA.ProofMode.Test.FiniteWindow

open TLA TLA.ProofMode

variable {σ : Type u}

example {p : σ → Prop} :
    (⌜ p ⌝) |-tla- (⌜ p ⌝) := by
  tla_start hp
  tla_finite_window
  exact hp

example {p q : σ → Prop} :
    (⌜ p ⌝ ∧ ⌜ q ⌝) |-tla- (⌜ q ⌝ ∧ ⌜ p ⌝) := by
  tla_start hp hq
  tla_finite_window
  exact ⟨hq, hp⟩

example {p q : σ → Prop} :
    Entails [⟨"hpq", [tlafml|⌜ p ⌝ ∧ ⌜ q ⌝]⟩] [tlafml|⌜ q ⌝ ∧ ⌜ p ⌝] := by
  tla_finite_window
  exact ⟨hpq.2, hpq.1⟩

example {p q : σ → Prop} {a : action σ}
    (h : ∀ s s', p s → a s s' → q s') :
    (⌜ p ⌝ ∧ ⟨a⟩) |-tla- (◯ ⌜ q ⌝) := by
  tla_start hp ha
  tla_finite_window
  exact h _ _ hp ha

example {p : σ → Prop} (h : ∀ s, p s) :
    Entails ([] : List (NamedPred σ)) (TLA.state_pred p) := by
  tla_finite_window
  exact h _

/--
error: tla_finite_window: failed to synthesize a finite-window instance for [tlafml|□⌜ p ⌝ → ⌜ p ⌝]
-/
#guard_msgs in
example {p : σ → Prop} :
    Entails [⟨"hp", [tlafml|□⌜ p ⌝]⟩] [tlafml|⌜ p ⌝] := by
  tla_finite_window

end TLA.ProofMode.Test.FiniteWindow
