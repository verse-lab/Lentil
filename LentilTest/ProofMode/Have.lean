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

-- Add a residual implication from a `pred_implies` theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have h := lem
  show Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tla_apply h ha

-- Supply an existing temporal hypothesis directly to the theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem ha
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Lean arguments can be supplied before temporal proof-mode arguments.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem (0 + 1) ha
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The direct theorem prefix can also be kept as a residual implication.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have h := lem 0
  show Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tla_apply h ha

-- Anonymous `tla_have := ...` appends an internal temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have := lem
  show Entails [⟨"ha", a⟩, ⟨"this", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Valid implication chains share the same mixed-argument path as `tla_apply`.
example (lem : |-tla- (a → b → c)) : (a ∧ b) |-tla- (c) := by
  tla_start ha hb
  tla_have hc := lem ha hb
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Tuple temporal arguments conjunct multiple proof-mode hypotheses.
example (lem : (a ∧ b) |-tla- (c)) : (a ∧ b) |-tla- (c) := by
  tla_start ha hb
  tla_have hc := lem ⟨ha, hb⟩
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- The head can be a temporal hypothesis already in the proof-mode context.
example : ([tlafml| (a → b) ∧ a]) |-tla- (b) := by
  tla_start h ha
  tla_have hb := h ha
  show Entails [⟨"h", [tlafml| a → b]⟩, ⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

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
  tla_suffices hsuff : a ∧ a by
    show Entails [⟨"hb", b⟩, ⟨"hsuff", [tlafml| a ∧ a]⟩] a
    tla_rcases hsuff with ⟨h, h'⟩
    tla_apply h
  show Entails [⟨"hb", b⟩] [tlafml| a ∧ a]
  tla_split_ands <;> tla_apply lem hb

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

example (lem1 : |-tla- (a ∨ b)) (lem2 : |-tla- (a → c)) :
  (b → c) |-tla- (c) := by
  tla_start hbc
  -- Allowing uninstantiated metavariables that will be resolved later
  tla_have h := TLA.or_elim
  tla_specialize h lem1
  tla_apply h lem2 hbc

end TLA.ProofMode.Test.Have
