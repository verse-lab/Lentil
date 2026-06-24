import Lentil

/- Tests for the `tstart` tactic.

   `tstart` reshapes a goal of the form `(prem₁ ∧ … ∧ premₙ) |-tla- goal`
   into the `Entails [h₁ : prem₁, …, hₙ : premₙ] goal` proof-mode view, with
   the user supplying one name per premise. The list of premises is obtained
   by `splitAndIntoParts`, which treats the conjunction associatively; but the
   `change`-step assumes the premises are right-associated (since `Entails`
   reconstructs them via `foldrD tla_and tla_true`).
-/

namespace TLA.ProofMode.Test.Start

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Zero premises: `⊤ |-tla- p` should become `Entails [] p`.
example : (⊤) |-tla- (p) → (⊤) |-tla- (p) := by
  intro h
  tstart
  tcheck_goal Entails [] p
  exact h

-- One premise, single label.
example : (p) |-tla- (q) → (p) |-tla- (q) := by
  intro h
  tstart hp
  tcheck_goal Entails [⟨"hp", p⟩] q
  exact h

-- Two premises (right-associated by parser): `(p ∧ q) |-tla- r`
-- splits into a list of two named hypotheses, with the supplied labels
-- assigned in order.
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tstart hp hq
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

-- Three premises (right-associated): `p ∧ q ∧ r` parses as `p ∧ (q ∧ r)`,
-- which matches the `foldrD`-style reconstruction in `repeatedAnd`.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tstart a b c
  tcheck_goal Entails [⟨"a", p⟩, ⟨"b", q⟩, ⟨"c", r⟩] r
  exact h

-- The labels are recorded as strings of the identifier; unicode names are
-- preserved.
example : (p) |-tla- (p) := by
  tstart ψ
  tcheck_goal Entails [⟨"ψ", p⟩] p
  exact pred_implies_refl _

-- Wrong number of labels (too few).
/--
error: tstart expected 2 names, but got 1
-/
#guard_msgs in
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tstart hp
  exact h

-- Wrong number of labels (too many).
/--
error: tstart expected 1 names, but got 2
-/
#guard_msgs in
example : (p) |-tla- (q) → (p) |-tla- (q) := by
  intro h
  tstart hp hq
  exact h

-- Duplicate labels are rejected up front.
/--
error: tstart hypothesis names must be distinct
-/
#guard_msgs in
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tstart hp hp
  exact h

-- `tstart` only operates on `|-tla-` sequents; a `|-tla-`-free goal is
-- rejected with a message naming the offending type.
/--
error: tstart only supports goals reduced to a single |-tla- sequent, but got True
-/
#guard_msgs in
example : True := by
  tstart

end TLA.ProofMode.Test.Start
