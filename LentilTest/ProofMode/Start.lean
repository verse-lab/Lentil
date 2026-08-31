import Lentil

/- Tests for the `tstart` tactic.

   `tstart` reshapes a goal of the form `(prem₁ ∧ … ∧ premₙ) |-tl- goal`
   into the `Entails [h₁ : prem₁, …, hₙ : premₙ] goal` proof-mode view, with
   the user supplying one name per premise. The list of premises is obtained
   by `splitAndIntoParts`, which treats the conjunction associatively; but the
   `change`-step assumes the premises are right-associated (since `Entails`
   reconstructs them via `foldrD tl_and tl_true`).
-/

namespace Lentil.ProofMode.Test.Start

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Zero premises: `⊤ |-tl- p` should become `Entails [] p`.
example : (⊤) |-tl- (p) → (⊤) |-tl- (p) := by
  intro h
  tstart
  guard_target =ₛ Entails [] p
  exact h

-- One premise, single label.
example : (p) |-tl- (q) → (p) |-tl- (q) := by
  intro h
  tstart hp
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

-- Two premises (right-associated by parser): `(p ∧ q) |-tl- r`
-- splits into a list of two named hypotheses, with the supplied labels
-- assigned in order.
example : (p ∧ q) |-tl- (r) → (p ∧ q) |-tl- (r) := by
  intro h
  tstart hp hq
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

-- Three premises (right-associated): `p ∧ q ∧ r` parses as `p ∧ (q ∧ r)`,
-- which matches the `foldrD`-style reconstruction in `repeatedAnd`.
example : (p ∧ q ∧ r) |-tl- (r) → (p ∧ q ∧ r) |-tl- (r) := by
  intro h
  tstart a b c
  guard_target =ₛ Entails [⟨"a", p⟩, ⟨"b", q⟩, ⟨"c", r⟩] r
  exact h

-- The labels are recorded as strings of the identifier; unicode names are
-- preserved.
example : (p) |-tl- (p) := by
  tstart ψ
  guard_target =ₛ Entails [⟨"ψ", p⟩] p
  exact pred_implies_refl _

-- Wrong number of labels (too few).
/--
error: tstart expected 2 names, but got 1
-/
#guard_msgs in
example : (p ∧ q) |-tl- (r) → (p ∧ q) |-tl- (r) := by
  intro h
  tstart hp
  exact h

-- Wrong number of labels (too many).
/--
error: tstart expected 1 names, but got 2
-/
#guard_msgs in
example : (p) |-tl- (q) → (p) |-tl- (q) := by
  intro h
  tstart hp hq
  exact h

-- Duplicate labels are rejected up front.
/--
error: tstart hypothesis names must be distinct
-/
#guard_msgs in
example : (p ∧ q) |-tl- (r) → (p ∧ q) |-tl- (r) := by
  intro h
  tstart hp hp
  exact h

-- `tstart` only operates on `|-tl-` sequents; a `|-tl-`-free goal is
-- rejected with a message naming the offending type.
/--
error: tstart only supports goals reduced to a single |-tl- sequent, but got True
-/
#guard_msgs in
example : True := by
  tstart

end Lentil.ProofMode.Test.Start
