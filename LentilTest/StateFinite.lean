import Lentil

/- Tests for finite-window sequent reduction. -/

namespace Lentil.Test.StateFinite

open Lentil

variable {σ : Type u}

example {init inv : σ → Prop} (hinit : ∀ s, init s → inv s) :
    (⌜ init ⌝) |-tl- (⌜ inv ⌝) := by
  tfinite_window
  guard_target =ₛ init s → inv s
  aesop

example {inv : σ → Prop} {next : action σ}
    (hnext : ∀ s s', next s s' → inv s → inv s') :
    (⌜ inv ⌝ ∧ ⟨next⟩) |-tl- (◯ ⌜ inv ⌝) := by
  tfinite_window
  guard_target =ₛ inv s ∧ next s s' → inv s'
  aesop

example {p q : σ → Prop} :
    (⌜ p ⌝ ∧ ◯ ⌜ q ⌝) |-tl- (◯ ⌜ q ⌝ ∧ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ p s ∧ q s' → q s' ∧ p s
  aesop

example {p : σ → Prop} :
    (□ ⌜ p ⌝) |-tl- (◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ p s ∧ p s' → p s'
  aesop

example {p : σ → Prop} :
    (□ ⌜ p ⌝) |-tl- (◯ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ p s ∧ p s' ∧ p s'' → p s''
  aesop

example {p q : σ → Prop} :
    (□ ⌜ p ⌝ ∧ □ ⌜ q ⌝) |-tl- (◯ (⌜ p ⌝ ∧ ⌜ q ⌝)) := by
  tfinite_window
  guard_target =ₛ (p s ∧ p s') ∧ q s ∧ q s' → p s' ∧ q s'
  aesop

example {a : action σ} :
    (□ ⟨a⟩) |-tl- (◯ ⟨a⟩) := by
  tfinite_window
  guard_target =ₛ a s s' ∧ a s' s'' → a s' s''
  aesop

-- The implication antecedent flips polarity recursively; this is not limited
-- to a leading proof-mode hypothesis.
example {p q : σ → Prop} :
    (⌜ p ⌝ → □ ⌜ q ⌝) |-tl- (⌜ p ⌝ → ◯ ⌜ q ⌝) := by
  tfinite_window
  guard_target =ₛ (p s → q s ∧ q s') → p s → q s'
  aesop

-- Negation flips polarity, so a negative occurrence of `□` in the conclusion
-- is also reducible.
example {p : σ → Prop} :
    (¬ ⌜ p ⌝) |-tl- (¬ □ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ ¬p s → ¬p s
  aesop

-- `□` is nested under negation and `◯`.  The outer hypothesis supplies the
-- two-state prefix needed by the shifted negative-always conclusion.
example {p : σ → Prop} :
    (□ ⌜ p ⌝) |-tl- (◯ (¬ □ (¬ ⌜ p ⌝))) := by
  tfinite_window
  guard_target =ₛ p s ∧ p s' → ¬¬p s'
  aesop

-- Two negations flip polarity twice and therefore make the nested `□`
-- necessary again in the implication antecedent.
example {p : σ → Prop} :
    (¬ ¬ □ ⌜ p ⌝) |-tl- (¬ ¬ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ ¬¬(p s ∧ p s') → ¬¬p s'
  aesop

-- A negated always occurs on the left of an implication which is itself in
-- hypothesis position.  The two contravariant steps cancel; the separate
-- `¬◯p` hypothesis establishes its finite two-state approximation.
example {p r : σ → Prop} :
    (((¬ □ ⌜ p ⌝) → ◯ ⌜ r ⌝) ∧ (¬ ◯ ⌜ p ⌝)) |-tl- (◯ ⌜ r ⌝) := by
  tfinite_window
  guard_target =ₛ (¬(p s ∧ p s') → r s') ∧ ¬p s' → r s'
  aesop

-- The same polarity path through `⇒ = □(· → ·)` requires `□` to expand a
-- body which is itself only directionally approximable.
example {p r : σ → Prop} :
    (((¬ □ ⌜ p ⌝) ⇒ ◯ ⌜ r ⌝) ∧ (¬ ◯ ⌜ p ⌝)) |-tl- (◯ ⌜ r ⌝) := by
  tfinite_window
  guard_target =ₛ (¬(p s ∧ p s') → r s') ∧ ¬p s' → r s'
  aesop

-- A larger enclosing window forces the `⇒` hypothesis itself to unroll and
-- use its directionally approximated body at the next suffix.
example {p r : σ → Prop} :
    (((¬ □ ⌜ p ⌝) ⇒ ◯ ⌜ r ⌝) ∧ (¬ ◯ ◯ ⌜ p ⌝)) |-tl- (◯ ◯ ⌜ r ⌝) := by
  tfinite_window
  guard_target =ₛ
    ((¬(p s ∧ p s' ∧ p s'') → r s') ∧
      (¬(p s' ∧ p s'') → r s'')) ∧ ¬p s'' → r s''
  aesop

-- Necessary approximation is recursive, so nested always hypotheses remain
-- usable even though the inner always has no exact finite window.
example {p : σ → Prop} :
    (□ □ ⌜ p ⌝) |-tl- (◯ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ
    (p s ∧ p s' ∧ p s'') ∧ (p s' ∧ p s'') ∧ p s'' → p s''
  aesop

-- `◇p` uses the dual of the necessary approximation of `□¬p`.  A larger
-- enclosing window therefore exposes every possible witness in that prefix.
example {p : σ → Prop} :
    (◯ ◯ ⌜ p ⌝) |-tl- (◇ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ p s'' → ¬(¬p s ∧ ¬p s' ∧ ¬p s'')
  aesop

example {a : action σ} :
    (◯ ⟨a⟩) |-tl- (◇ ⟨a⟩) := by
  tfinite_window
  guard_target =ₛ a s' s'' → ¬(¬a s s' ∧ ¬a s' s'')
  aesop

-- Negation flips the new sufficient approximation back to necessary polarity,
-- so a negated eventuality remains useful as a hypothesis.
example {p : σ → Prop} :
    (¬ ◇ ⌜ p ⌝) |-tl- (¬ ◯ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ ¬¬(¬p s ∧ ¬p s' ∧ ¬p s'') → ¬p s''
  aesop

-- The same approximation remains usable when nested below another `□`.
example {p : σ → Prop} :
    (□ (¬ ◇ ⌜ p ⌝)) |-tl- (¬ ◯ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ
    ¬¬(¬p s ∧ ¬p s' ∧ ¬p s'') ∧
      ¬¬(¬p s' ∧ ¬p s'') ∧ ¬¬¬p s'' → ¬p s''
  aesop

-- Binders preserve polarity pointwise, so their bodies may use directional
-- approximations rather than requiring exact finite windows.
example {α : Type v} {p : α → σ → Prop} :
    (∀ x, □ ⌜ p x ⌝) |-tl- (◯ (∀ x, ⌜ p x ⌝)) := by
  tfinite_window
  guard_target =ₛ (∀ x, p x s ∧ p x s') → ∀ x, p x s'
  aesop

example {α : Type v} {p : α → σ → Prop} :
    (∃ x, □ ⌜ p x ⌝) |-tl- (◯ (∃ x, ⌜ p x ⌝)) := by
  tfinite_window
  guard_target =ₛ (∃ x, p x s ∧ p x s') → ∃ x, p x s'
  aesop

-- Here the quantifier is inside `□`, so each tiled suffix contains one whole
-- pointwise quantified body rather than one independently tiled formula per x.
example {α : Type v} {p q : α → σ → Prop} :
    (□ (∀ x, ⌜ p x ⌝ ∧ ◯ ⌜ q x ⌝)) |-tl-
      (◯ ◯ (∀ x, ⌜ p x ⌝ ∧ ◯ ⌜ q x ⌝)) := by
  tfinite_window
  guard_target =ₛ
    ((∀ x, p x s ∧ q x s') ∧ (∀ x, p x s' ∧ q x s'') ∧
      (∀ x, p x s'' ∧ q x s''')) →
        ∀ x, p x s'' ∧ q x s'''
  aesop

-- Nested Boolean connectives are preserved pointwise while `□` tiles the
-- entire composite body over every suffix in the enclosing window.
example {p q r : σ → Prop} :
    (□ (⌜ p ⌝ ∧ (⌜ q ⌝ ∨ ¬ ⌜ r ⌝))) |-tl-
      (◯ ◯ (⌜ p ⌝ ∧ (⌜ q ⌝ ∨ ¬ ⌜ r ⌝))) := by
  tfinite_window
  guard_target =ₛ
    (p s ∧ (q s ∨ ¬r s)) ∧ (p s' ∧ (q s' ∨ ¬r s')) ∧
      p s'' ∧ (q s'' ∨ ¬r s'') → p s'' ∧ (q s'' ∨ ¬r s'')
  aesop

-- A disjunction combines the necessary approximations of both always
-- formulas without distributing the disjunction over the finite prefix.
example {p q : σ → Prop} :
    (□ ⌜ p ⌝ ∨ □ ⌜ q ⌝) |-tl- (◯ ◯ (⌜ p ⌝ ∨ ⌜ q ⌝)) := by
  tfinite_window
  guard_target =ₛ
    p s ∧ p s' ∧ p s'' ∨ q s ∧ q s' ∧ q s'' → p s'' ∨ q s''
  aesop

-- `⇒` expands at every suffix, including nested conjunction, negation, and
-- disjunction in its antecedent and consequent.
example {p q r t : σ → Prop} :
    ((((⌜ p ⌝ ∧ ¬ ⌜ q ⌝) ⇒ (⌜ r ⌝ ∨ ⌜ t ⌝)) ∧
      ◯ ◯ (⌜ p ⌝ ∧ ¬ ⌜ q ⌝))) |-tl- (◯ ◯ (⌜ r ⌝ ∨ ⌜ t ⌝)) := by
  tfinite_window
  guard_target =ₛ
    ((p s ∧ ¬q s → r s ∨ t s) ∧
      (p s' ∧ ¬q s' → r s' ∨ t s') ∧
      (p s'' ∧ ¬q s'' → r s'' ∨ t s'')) ∧
        p s'' ∧ ¬q s'' → r s'' ∨ t s''
  aesop

-- Binders, nested connectives, and temporal operators all retain their
-- pointwise polarity through a shared three-state window.
example {α : Type v} {p q r : α → σ → Prop} :
    ((∀ x, □ (⌜ p x ⌝ → (⌜ q x ⌝ ∧ ¬ ⌜ r x ⌝))) ∧
      ◯ ◯ (∃ x, ⌜ p x ⌝)) |-tl- (◯ ◯ (∃ x, ⌜ q x ⌝)) := by
  tfinite_window
  guard_target =ₛ
    ((∀ x, (p x s → q x s ∧ ¬r x s) ∧
      (p x s' → q x s' ∧ ¬r x s') ∧
      (p x s'' → q x s'' ∧ ¬r x s'')) ∧ ∃ x, p x s'') →
        ∃ x, q x s''
  grind

-- An action implication under `□` is rebuilt at each suffix at which its
-- two-state body still fits.
example {a : action σ} {p : σ → Prop} :
    (□ (⟨a⟩ → ◯ ⌜ p ⌝) ∧ ◯ ⟨a⟩) |-tl- (◯ ◯ ⌜ p ⌝) := by
  tfinite_window
  guard_target =ₛ
    ((a s s' → p s') ∧ (a s' s'' → p s'')) ∧ a s' s'' → p s''
  aesop

-- The sufficient approximation of a composite eventuality is the negation
-- of all failures of that whole body across the finite prefix.
example {p q r : σ → Prop} :
    (◯ ◯ (⌜ p ⌝ ∨ (⌜ q ⌝ ∧ ¬ ⌜ r ⌝))) |-tl-
      (◇ (⌜ p ⌝ ∨ (⌜ q ⌝ ∧ ¬ ⌜ r ⌝))) := by
  tfinite_window
  guard_target =ₛ
    p s'' ∨ q s'' ∧ ¬r s'' →
      ¬(¬(p s ∨ q s ∧ ¬r s) ∧ ¬(p s' ∨ q s' ∧ ¬r s') ∧
        ¬(p s'' ∨ q s'' ∧ ¬r s''))
  aesop

-- Conversely, this existential is inside `◇`; the whole quantified body is
-- negated and tiled by the `¬□¬` sufficient approximation.
example {α : Type v} {p q : α → σ → Prop} :
    (◯ ◯ (∃ x, ⌜ p x ⌝ ∧ ¬ ⌜ q x ⌝)) |-tl-
      (◇ (∃ x, ⌜ p x ⌝ ∧ ¬ ⌜ q x ⌝)) := by
  tfinite_window
  guard_target =ₛ
    (∃ x, p x s'' ∧ ¬q x s'') →
      ¬((¬∃ x, p x s ∧ ¬q x s) ∧ (¬∃ x, p x s' ∧ ¬q x s') ∧
        ¬∃ x, p x s'' ∧ ¬q x s'')
  aesop

-- This combines polarity changes through `⇒` and `¬□`, a composite body with
-- its own `◯`, disjunction, and differently shifted side conditions.
example {p q r t : σ → Prop} :
    (((¬ □ (⌜ p ⌝ ∧ ◯ ⌜ q ⌝)) ⇒
        (◯ ⌜ r ⌝ ∨ ◯ ◯ ⌜ t ⌝)) ∧
      (¬ ◯ ◯ (⌜ p ⌝ ∧ ◯ ⌜ q ⌝)) ∧
      (¬ ◯ ⌜ r ⌝)) |-tl- (◯ ◯ ⌜ t ⌝) := by
  tfinite_window
  guard_target =ₛ
    ((¬((p s ∧ q s') ∧ (p s' ∧ q s'') ∧ p s'' ∧ q s''') →
        r s' ∨ t s'') ∧
      (¬((p s' ∧ q s'') ∧ p s'' ∧ q s''') →
        r s'' ∨ t s''')) ∧
      ¬(p s'' ∧ q s''') ∧ ¬r s' → t s''
  aesop

example {p q : σ → Prop} (h : ∀ s, p s ↔ q s) :
    (⌜ p ⌝) =tl= (⌜ q ⌝) := by
  tfinite_window
  guard_target = p s ↔ q s
  exact h _

example {p q : σ → Prop} (h : ∀ s s', p s ↔ q s') :
    (⌜ p ⌝) =tl= (◯ ⌜ q ⌝) := by
  tfinite_window
  guard_target = p s ↔ q s'
  exact h _ _

/--
error: tfinite_window: failed to synthesize sufficient finite-window approximation for [tlfml|□⌜ p ⌝ → □⌜ p ⌝]
-/
#guard_msgs in
example {p : σ → Prop} : (□ ⌜ p ⌝) |-tl- (□ ⌜ p ⌝) := by
  tfinite_window

/--
error: tfinite_window: failed to synthesize sufficient finite-window approximation for [tlfml|□◇⌜ p ⌝ → ⌜ p ⌝]
-/
#guard_msgs in
example {p : σ → Prop} : (□ ◇ ⌜ p ⌝) |-tl- (⌜ p ⌝) := by
  tfinite_window

end Lentil.Test.StateFinite
