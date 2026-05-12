import Lentil

/- Tests for the `tla_have` and `tla_suffices` tactics.

   Both take a hypothesis name, a `tlafml`, and a `by`-block:
     * `tla_have h : fml by tac` — `tac` proves `Entails hyps fml` from the
       current premises; the remaining main goal carries `⟨h, fml⟩` in the
       temporal context.
     * `tla_have h := t` — `t : |-tla- fml` is added as a temporal hypothesis
       named `h`.
     * `tla_suffices h : fml by tac` — `tac` closes the original goal using
       the new hypothesis `⟨h, fml⟩`; the remaining main goal is to prove
       `fml` from the current premises.
-/

namespace TLA.ProofMode.Test.Have

open TLA TLA.ProofMode

variable {σ : Type u} (a b c : pred σ)

/-! ## `tla_have` -/

-- Basic: justify `hb : b` from the existing `ha : a` via a lemma, then use it.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb : b by
    tla_apply lem
    show Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Multi-step `by`-block: nested `tla_*` tactics work as expected.
example (lem1 : (a) |-tla- (b)) (lem2 : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tla_start ha
  tla_have hc : c by
    tla_apply lem2
    tla_apply lem1
    show Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  show Entails [⟨"ha", a⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, hc⟩ ; exact hc

-- "Duplicate" an existing hyp under a different name (the by-block just
-- restates the hyp via reflexivity).
example : (a) |-tla- (a) := by
  tla_start ha
  tla_have ha' : a by
    show Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  show Entails [⟨"ha", a⟩, ⟨"ha'", a⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Add a valid TLA fact as a temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The term can be an expression, and the new hypothesis is appended.
example (lem : |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tla_start ha hc
  tla_have hb := (show |-tla- (b) from lem)
  show Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

/-! ## `tla_suffices` -/

-- Basic: reduce the goal `a` to a stronger `a` (trivially via `pred_implies_refl`),
-- then prove the stronger one with the original `lem`.
example (lem : (b) |-tla- (a)) : (b) |-tla- (a) := by
  tla_start hb
  tla_suffices hsuff : a by
    show Entails [⟨"hb", b⟩, ⟨"hsuff", a⟩] a
    intro _ ⟨_, h⟩ ; exact h
  show Entails [⟨"hb", b⟩] a
  exact lem

-- Use `tla_rcases` inside `tla_suffices`' `by`-block to destructure the new
-- hypothesis and discharge the goal. The remaining main goal is the stronger
-- conjunction, which we close with the supplied lemma.
example (lem : (a) |-tla- (b ∧ c)) : (a) |-tla- (c) := by
  tla_start ha
  tla_suffices hbc : b ∧ c by
    tla_rcases hbc with ⟨hb, hc⟩
    show Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  show Entails [⟨"ha", a⟩] [tlafml| b ∧ c]
  exact lem

/-! ## Interplay between the two -/

-- Use `tla_have` then `tla_suffices` together: introduce a derived hyp, then
-- reduce the goal further.
example (lemAB : (a) |-tla- (b)) (lemBC : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tla_start ha
  tla_have hb : b by
    tla_apply lemAB
    show Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tla_suffices hc : c by
    show Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] c
  tla_apply lemBC
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

end TLA.ProofMode.Test.Have
