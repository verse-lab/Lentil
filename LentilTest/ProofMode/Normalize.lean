import Lentil

/- Tests for the `tnormalize` tactic.

   `tnormalize` is a `simp only [tlanormsimp]` over the lemmas:
     * `impl_intro`            : `|-tla- (p → q) = (p) |-tla- (q)`
     * `valid_eq_true_implies` : `|-tla- (p) = ((⊤) |-tla- (p))`
     * `impl_intro_add_r`      : `(r) |-tla- (p → q) = (r ∧ p) |-tla- (q)`
     * `and_assoc`             : right-associates conjunctions

   The intended end state is a single `(prems) |-tla- goal` sequent with a
   right-associated conjunction of premises. When the starting goal is a bare
   `|-tla- …`, the simp set inserts an explicit `⊤` premise (via
   `valid_eq_true_implies`) before peeling off implications, so the produced
   premise has the shape `⊤ ∧ …`.
-/

namespace TLA.ProofMode.Test.Normalize

open TLA TLA.ProofMode

variable {σ : Type u} (p q r s : pred σ)

-- A naked validity becomes a sequent with `⊤` as the premise.
example : (⊤) |-tla- (p) → |-tla- (p) := by
  intro h
  tnormalize
  show (⊤) |-tla- (p)
  exact h

-- A single implication is unrolled into one premise. `valid_eq_true_implies`
-- fires first, adding a `⊤` to the premise side, before `impl_intro_add_r`
-- consumes the `→`.
example : (p) |-tla- (q) → |-tla- (p → q) := by
  intro h
  tnormalize
  show (p) |-tla- (q)
  exact h

-- Two-level implication: premises are right-associated.
example : (p ∧ q) |-tla- (r) → |-tla- (p → q → r) := by
  intro h
  tnormalize
  show (p ∧ q) |-tla- (r)
  exact h

-- Three-level implication.
example : (p ∧ q ∧ r) |-tla- (s) → |-tla- (p → q → r → s) := by
  intro h
  tnormalize
  show (p ∧ q ∧ r) |-tla- (s)
  exact h

-- Left-associated conjunction on the premise side gets re-associated via
-- `and_assoc`, so that `tstart` can subsequently match the right-associated
-- `repeatedAnd` shape. Because the goal already carries a premise, no `⊤`
-- is inserted.
example : (p ∧ q ∧ r) |-tla- (s) → ((p ∧ q) ∧ r) |-tla- (s) := by
  intro h
  tnormalize
  show (p ∧ q ∧ r) |-tla- (s)
  exact h

-- An implication mixed with an existing premise: `r |-tla- p → q` becomes
-- `(r ∧ p) |-tla- q` via `impl_intro_add_r`. No `⊤` is added.
example : (r ∧ p) |-tla- (q) → (r) |-tla- (p → q) := by
  intro h
  tnormalize
  show (r ∧ p) |-tla- (q)
  exact h

-- Conjunction nested inside an implication's premise.
example : (p ∧ q) |-tla- (r) → |-tla- ((p ∧ q) → r) := by
  intro h
  tnormalize
  show (p ∧ q) |-tla- (r)
  exact h

-- Idempotence: `tnormalize` does not fail on an already-normalized goal.
-- The `failIfUnchanged` option is disabled, so this should silently succeed.
example : (p) |-tla- (q) → (p) |-tla- (q) := by
  intro h
  tnormalize
  show (p) |-tla- (q)
  exact h

-- End-to-end: `tnormalize` followed by `tstart` produces a clean
-- proof-mode view, with the leading `⊤` showing up as its own labelled
-- hypothesis.
-- `p → q ∧ r → p` parses as `p → ((q ∧ r) → p)`. After `tnormalize` the
-- premises are flattened into `⊤ ∧ p ∧ q ∧ r` — four leaves, so `tstart`
-- needs four labels.
example : |-tla- (p → q ∧ r → p) := by
  tnormalize
  tstart hp hq hr
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] p
  tassumption

end TLA.ProofMode.Test.Normalize
