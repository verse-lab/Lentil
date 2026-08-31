import Lentil

/- Tests for running `tfinite_window` directly on proof-mode `Entails` goals. -/

namespace Lentil.ProofMode.Test.FiniteWindow

open Lentil Lentil.ProofMode

variable {σ : Type u}

example {p : σ → Prop} :
    (⌜ p ⌝) |-tl- (⌜ p ⌝) := by
  tstart hp
  tfinite_window
  exact hp

example {p q : σ → Prop} :
    (⌜ p ⌝ ∧ ⌜ q ⌝) |-tl- (⌜ q ⌝ ∧ ⌜ p ⌝) := by
  tstart hp hq
  tfinite_window
  exact ⟨hq, hp⟩

example {p q : σ → Prop} :
    Entails [⟨"hpq", [tlfml|⌜ p ⌝ ∧ ⌜ q ⌝]⟩] [tlfml|⌜ q ⌝ ∧ ⌜ p ⌝] := by
  tfinite_window
  exact ⟨hpq.2, hpq.1⟩

example {p q : σ → Prop} {a : action σ}
    (h : ∀ s s', p s → a s s' → q s') :
    (⌜ p ⌝ ∧ ⟨a⟩) |-tl- (◯ ⌜ q ⌝) := by
  tstart hp ha
  tfinite_window
  exact h _ _ hp ha

example {p : σ → Prop} (h : ∀ s, p s) :
    Entails ([] : List (NamedPred σ)) [tlfml| ⌜ p ⌝] := by
  tfinite_window
  exact h _

example {p : σ → Prop} :
    Entails [⟨"hp", [tlfml|□⌜ p ⌝]⟩] [tlfml|⌜ p ⌝] := by
  tfinite_window
  exact hp

example {p : σ → Prop} :
    Entails [⟨"hp", [tlfml|□⌜ p ⌝]⟩] [tlfml|◯◯⌜ p ⌝] := by
  tfinite_window
  exact hp.2.2

example {p q : σ → Prop} :
    Entails [⟨"hp", [tlfml|□⌜ p ⌝]⟩, ⟨"hq", [tlfml|□⌜ q ⌝]⟩]
      [tlfml|◯(⌜ p ⌝ ∧ ⌜ q ⌝)] := by
  tfinite_window
  exact ⟨hp.2, hq.2⟩

end Lentil.ProofMode.Test.FiniteWindow
