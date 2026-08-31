import Lentil

/- Tests for the `tnormalize` tactic.

   `tnormalize` is a `simp only [tlnormsimp]` over the lemmas:
     * `impl_intro`            : `|-tl- (p → q) = (p) |-tl- (q)`
     * `valid_eq_true_implies` : `|-tl- (p) = ((⊤) |-tl- (p))`
     * `impl_intro_add_r`      : `(r) |-tl- (p → q) = (r ∧ p) |-tl- (q)`
     * `and_assoc`             : right-associates conjunctions

   The intended end state is a single `(prems) |-tl- goal` sequent with a
   right-associated conjunction of premises. When the starting goal is a bare
   `|-tl- …`, the simp set inserts an explicit `⊤` premise (via
   `valid_eq_true_implies`) before peeling off implications, so the produced
   premise has the shape `⊤ ∧ …`.
-/

namespace Lentil.ProofMode.Test.Normalize

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r s : pred σ)

-- A naked validity becomes a sequent with `⊤` as the premise.
example : (⊤) |-tl- (p) → |-tl- (p) := by
  intro h
  tnormalize
  show (⊤) |-tl- (p)
  exact h

-- A single implication is unrolled into one premise. `valid_eq_true_implies`
-- fires first, adding a `⊤` to the premise side, before `impl_intro_add_r`
-- consumes the `→`.
example : (p) |-tl- (q) → |-tl- (p → q) := by
  intro h
  tnormalize
  show (p) |-tl- (q)
  exact h

-- Two-level implication: premises are right-associated.
example : (p ∧ q) |-tl- (r) → |-tl- (p → q → r) := by
  intro h
  tnormalize
  show (p ∧ q) |-tl- (r)
  exact h

-- Three-level implication.
example : (p ∧ q ∧ r) |-tl- (s) → |-tl- (p → q → r → s) := by
  intro h
  tnormalize
  show (p ∧ q ∧ r) |-tl- (s)
  exact h

-- Left-associated conjunction on the premise side gets re-associated via
-- `and_assoc`, so that `tstart` can subsequently match the right-associated
-- `repeatedAnd` shape. Because the goal already carries a premise, no `⊤`
-- is inserted.
example : (p ∧ q ∧ r) |-tl- (s) → ((p ∧ q) ∧ r) |-tl- (s) := by
  intro h
  tnormalize
  show (p ∧ q ∧ r) |-tl- (s)
  exact h

-- An implication mixed with an existing premise: `r |-tl- p → q` becomes
-- `(r ∧ p) |-tl- q` via `impl_intro_add_r`. No `⊤` is added.
example : (r ∧ p) |-tl- (q) → (r) |-tl- (p → q) := by
  intro h
  tnormalize
  show (r ∧ p) |-tl- (q)
  exact h

-- Conjunction nested inside an implication's premise.
example : (p ∧ q) |-tl- (r) → |-tl- ((p ∧ q) → r) := by
  intro h
  tnormalize
  show (p ∧ q) |-tl- (r)
  exact h

-- Idempotence: `tnormalize` does not fail on an already-normalized goal.
-- The `failIfUnchanged` option is disabled, so this should silently succeed.
example : (p) |-tl- (q) → (p) |-tl- (q) := by
  intro h
  tnormalize
  show (p) |-tl- (q)
  exact h

-- End-to-end: `tnormalize` followed by `tstart` produces a clean
-- proof-mode view, with the leading `⊤` showing up as its own labelled
-- hypothesis.
-- `p → q ∧ r → p` parses as `p → ((q ∧ r) → p)`. After `tnormalize` the
-- premises are flattened into `⊤ ∧ p ∧ q ∧ r` — four leaves, so `tstart`
-- needs four labels.
example : |-tl- (p → q ∧ r → p) := by
  tnormalize
  tstart hp hq hr
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] p
  tassumption

end Lentil.ProofMode.Test.Normalize
