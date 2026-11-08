import Lentil

namespace Lentil.Test.Modality

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

example (h : (p) |-tl- (q)) : (◯ p) |-tl- (◯ q) := by
  tmonotone
  exact h

example (h : (p ∧ q) |-tl- (r)) : (◯ p ∧ ◯ q) |-tl- (◯ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : (p ∧ q) |-tl- (r)) : (□ p ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

example (h : ((p → q) ∧ (q → r)) |-tl- (p → r)) :
    ((p ⇒ q) ∧ (q ⇒ r)) |-tl- (p ⇒ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails
    [⟨"hp", [tlfml| p → q]⟩, ⟨"hq", [tlfml| q → r]⟩] [tlfml| p → r]
  exact h

example (h : (p) |-tl- (q)) : (◇ p) |-tl- (◇ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

example (h : (p) |-tl- (q)) : (□ ◇ p) |-tl- (□ ◇ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

example (h : (◇ p) |-tl- (q)) : (□ ◇ p) |-tl- (□ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ◇ p]⟩] q
  exact h

example (h : (p) |-tl- (◇ q)) : (□ p) |-tl- (□ ◇ q) := by
  tstart hp
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩] [tlfml| ◇ q]
  exact h

example (h : (◇ p ∧ q) |-tl- (◇ r)) : (□ ◇ p ∧ □ q) |-tl- (□ ◇ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ◇ p]⟩, ⟨"hq", q⟩] [tlfml| ◇ r]
  exact h

example (h : (p ∧ q) |-tl- (r)) : (◇ □ p ∧ ◇ □ q) |-tl- (◇ □ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

section Structure

variable {α : Type} (ps qs : α → pred σ) (l : List α)

example (h : ((∀ x, ps x) ∧ q) |-tl- (r)) : ((∀ x, □ ps x) ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ∀ x, ps x]⟩, ⟨"hq", q⟩] r
  exact h

example (ps2 : α → α → pred σ) (h : ((∀ x, ∀ y, ps2 x y) ∧ q) |-tl- (r)) :
    ((∀ x, ∀ y, □ ps2 x y) ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ∀ x, ∀ y, ps2 x y]⟩, ⟨"hq", q⟩] r
  exact h

example (h : ((∀ x, ps x → ◇ qs x) ∧ p) |-tl- (p → ◇ r)) :
    ((∀ x, ps x ↝ qs x) ∧ □ p) |-tl- (p ↝ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ∀ x, ps x → ◇ qs x]⟩, ⟨"hq", p⟩] [tlfml| p → ◇ r]
  exact h

example (h : ((∃ x, ps x) ∧ (p ∨ q) ∧ ◯ r ∧ (⋀ x ∈ l, qs x)) |-tl- (r)) :
    ((∃ x, □ ps x) ∧ (□ p ∨ □ q) ∧ ◯ □ r ∧ (⋀ x ∈ l, □ qs x)) |-tl- (□ r) := by
  tstart h1 h2 h3 h4
  tmonotone
  guard_target =ₛ Entails [⟨"h1", [tlfml| ∃ x, ps x]⟩, ⟨"h2", [tlfml| p ∨ q]⟩,
    ⟨"h3", [tlfml| ◯ r]⟩, ⟨"h4", [tlfml| ⋀ x ∈ l, qs x]⟩] r
  exact h

example (h : ((∀ x, ps x) ∧ q) |-tl- (r)) : ((∀ x, ◯ ps x) ∧ ◯ q) |-tl- (◯ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| ∀ x, ps x]⟩, ⟨"hq", q⟩] r
  exact h

example (h : (□ p ∧ ◇ q) |-tl- (r)) : (□ ◯ p ∧ ◇ ◯ q) |-tl- (◯ r) := by
  tstart hp hq
  tmonotone
  guard_target =ₛ Entails [⟨"hp", [tlfml| □ p]⟩, ⟨"hq", [tlfml| ◇ q]⟩] r
  exact h

-- Binder names survive typeclass synthesis.
/--
trace: σ : Type u
p q r : pred σ
α : Type
ps qs : α → pred σ
l : List α
h : (∀ c, ps c → ◇q) |-tl- (q → ◇q)
⊢ ⏎
  hp : ∀ c, ps c → ◇q
  |-tl- q → ◇q
-/
#guard_msgs in
example (h : (∀ c, ps c → ◇ q) |-tl- (q → ◇ q)) : (∀ c, ps c ↝ q) |-tl- (q ↝ q) := by
  tstart hp
  tmonotone
  trace_state
  exact h

-- The error names the hypothesis that cannot be handled.
/--
error: tmonotone: cannot peel `□` from hypothesis hp (no `IntoAlways` instance applies):
  ∀ x, □ps x ∧ qs x
-/
#guard_msgs in
example : ((∀ x, □ ps x ∧ qs x) ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone

-- `◇□` does not commute with `∀` on the hypothesis side.
/--
error: tmonotone: no prefix of the goal is shared by all proof-mode hypotheses:
• hypothesis hp does not have the prefix `◇□`:
  ∀ x, ◇□ps x
• hypothesis hp does not have the prefix `◇`:
  ∀ x, ◇□ps x
-/
#guard_msgs in
example : ((∀ x, ◇ □ ps x) ∧ ◇ □ q) |-tl- (◇ □ r) := by
  tstart hp hq
  tmonotone

end Structure

end Lentil.Test.Modality
