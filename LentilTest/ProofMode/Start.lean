import Lentil

/- Tests for the `tla_start` tactic.

   `tla_start` reshapes a goal of the form `(prem₁ ∧ … ∧ premₙ) |-tla- goal`
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
  tla_start
  show Entails [] p
  exact h

-- One premise, single label.
example : (p) |-tla- (q) → (p) |-tla- (q) := by
  intro h
  tla_start hp
  show Entails [⟨"hp", p⟩] q
  exact h

-- Two premises (right-associated by parser): `(p ∧ q) |-tla- r`
-- splits into a list of two named hypotheses, with the supplied labels
-- assigned in order.
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tla_start hp hq
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

-- Three premises (right-associated): `p ∧ q ∧ r` parses as `p ∧ (q ∧ r)`,
-- which matches the `foldrD`-style reconstruction in `repeatedAnd`.
example : (p ∧ q ∧ r) |-tla- (r) → (p ∧ q ∧ r) |-tla- (r) := by
  intro h
  tla_start a b c
  show Entails [⟨"a", p⟩, ⟨"b", q⟩, ⟨"c", r⟩] r
  exact h

-- The labels are recorded as strings of the identifier; unicode names are
-- preserved.
example : (p) |-tla- (p) := by
  tla_start ψ
  show Entails [⟨"ψ", p⟩] p
  exact pred_implies_refl _

-- Wrong number of labels (too few).
/--
error: tla_start expected 2 names, but got 1
-/
#guard_msgs in
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tla_start hp
  exact h

-- Wrong number of labels (too many).
/--
error: tla_start expected 1 names, but got 2
-/
#guard_msgs in
example : (p) |-tla- (q) → (p) |-tla- (q) := by
  intro h
  tla_start hp hq
  exact h

-- Duplicate labels are rejected up front.
/--
error: tla_start hypothesis names must be distinct
-/
#guard_msgs in
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tla_start hp hp
  exact h

-- `tla_start` only operates on `|-tla-` sequents; a `|-tla-`-free goal is
-- rejected with a message naming the offending type.
/--
error: tla_start only supports goals reduced to a single |-tla- sequent, but got True
-/
#guard_msgs in
example : True := by
  tla_start

end TLA.ProofMode.Test.Start
