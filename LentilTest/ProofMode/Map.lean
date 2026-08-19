import Lentil

namespace TLA.Test.Map

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

/-- The supported implication shape is below an explicit theorem parameter. -/
theorem parameterizedAndLeftRule (x y : pred σ) : (x ∧ y) |-tla- (x) := TLA.and_left

/-- The supported valid implication shape is below an explicit parameter. -/
theorem parameterizedValidAndLeftRule (x y : pred σ) : |-tla- ((x ∧ y) ⇒ x) := by
  rw [always_implies, ← always_intro]
  exact parameterizedAndLeftRule _ _

def customOp (_tag : Nat) (p : pred σ) : pred σ := p

@[tmap_mono]
theorem customOp_monotone (tag : Nat) {p q : pred σ} :
    (p ⇒ q) |-tla- (customOp tag p → customOp tag q) := by
  simp only [customOp]
  exact always_weaken

example (hpq : (p) |-tla- (q)) :
    ((□ ◇ ◯ p) ∧ r) |-tla- (□ ◇ ◯ q) := by
  tstart hp hr
  tmap hq := hp using hpq
  guard_target =ₛ Entails
    [⟨"hp", [tlafml| □ ◇ ◯ p]⟩, ⟨"hr", r⟩, ⟨"hq", [tlafml| □ ◇ ◯ q]⟩]
    [tlafml| □ ◇ ◯ q]
  tassumption

-- The replacement form preserves the source name and moves the mapped result
-- to the end of the temporal context, like `treplace`.
example (hpq : (p) |-tla- (q)) :
    ((□ p) ∧ r) |-tla- (□ q) := by
  tstart hp hr
  tmap hp using hpq
  guard_target =ₛ Entails
    [⟨"hr", r⟩, ⟨"hp", [tlafml| □ q]⟩]
    [tlafml| □ q]
  tassumption

-- `tmap` infers leading theorem parameters from the source predicate instead
-- of requiring the implication to be the outermost type constructor.
example : (□ (p ∧ q)) |-tla- (□ p) := by
  tstart hp
  tmap hp' := hp using parameterizedAndLeftRule
  tassumption

example : (◇ (p ∧ q)) |-tla- (◇ p) := by
  tstart hp
  tmap hp' := hp using parameterizedValidAndLeftRule
  tassumption

-- Registered operators compose with the built-in modalities, including when
-- the operator has parameters before its predicate argument.
example (hpq : (p) |-tla- (q)) :
    (customOp 37 [tlafml| □ p]) |-tla- (customOp 37 [tlafml| □ q]) := by
  tstart hp
  tmap hq := hp using hpq
  tassumption

example :
    ((p ⇒ q) ∧ (customOp 37 [tlafml| □ p])) |-tla-
      (customOp 37 [tlafml| □ q]) := by
  tstart hpq hp
  tmap hq := hp using hpq
  tassumption

example (hpq : |-tla- (p ⇒ q)) :
    (◇ □ p) |-tla- (◇ □ q) := by
  tstart hp
  tmap hq := hp using hpq
  tassumption

example :
    ((p ⇒ q) ∧ □ ◇ p) |-tla- (□ ◇ q) := by
  tstart hpq hp
  tmap hq := hp using hpq
  tassumption

example :
    ((p ⇒ q) ∧ □ ◇ p) |-tla- (□ ◇ q) := by
  tstart hpq hp
  tmap hp using hpq
  guard_target =ₛ Entails
    [⟨"hpq", [tlafml| p ⇒ q]⟩, ⟨"hp", [tlafml| □ ◇ q]⟩]
    [tlafml| □ ◇ q]
  tassumption

-- Pointwise state theorems require a source-driven `apply at` adapter and are
-- intentionally not accepted as global `tmap` rules for now.
example (P Q : σ → Prop) (_hPQ : ∀ s, P s → Q s) :
    (□ ◇ ⌜ P ⌝) |-tla- (□ ◇ ⌜ P ⌝) := by
  tstart hp
  fail_if_success tmap hq := hp using _hPQ
  tassumption

-- Stop when the rule lhs is reached, even when that lhs starts with a modality.
example (hpq : (□ p) |-tla- (□ q)) :
    (◇ □ p) |-tla- (◇ □ q) := by
  tstart hp
  tmap hq := hp using hpq
  tassumption

-- Numeric source locations use the same convention as the other proof-mode tactics.
example (hpq : (p) |-tla- (q)) :
    ((□ p) ∧ r) |-tla- (□ q) := by
  tstart hp hr
  tmap hq := 0 using hpq
  tassumption

end TLA.Test.Map
