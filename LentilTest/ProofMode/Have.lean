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
    tla_check_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Multi-step `by`-block: nested `tla_*` tactics work as expected.
example (lem1 : (a) |-tla- (b)) (lem2 : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tla_start ha
  tla_have hc : c by
    tla_apply lem2
    tla_apply lem1
    tla_check_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, hc⟩ ; exact hc

-- "Duplicate" an existing hyp under a different name (the by-block just
-- restates the hyp via reflexivity).
example : (a) |-tla- (a) := by
  tla_start ha
  tla_have ha' : a by
    tla_check_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"ha'", a⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Add a valid TLA fact as a temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The restricted prime form accepts formula syntax as theorem arguments.
example (lem : ∀ p : pred σ, |-tla- (p → p)) : (a) |-tla- (a) := by
  tla_start ha
  tla_have' h := lem (a ∧ b)
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (a ∧ b) → (a ∧ b)]⟩] a
  tla_assumption

-- The prime form can keep a formula-instantiated theorem as a residual implication.
example (lem : ∀ p : pred σ, (p) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tla_start ha hc
  tla_have' h := lem (a ∧ c)
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"h", [tlafml| (a ∧ c) → b]⟩] b
  tla_apply h ⟨ha, hc⟩

-- Lean arguments before the theorem shape are consumed before temporal arguments.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have' hb := lem (0 + 1) ha
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Valid implication chains still specialize through proof-mode hypotheses.
example (lem : |-tla- (a → b → c)) : (a ∧ b) |-tla- (c) := by
  tla_start ha hb
  tla_have' hc := lem ha hb
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Formula arguments and tuple temporal arguments can appear in the same application.
example (lem : ∀ p : pred σ, (p) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tla_start ha hc
  tla_have' hb := lem (a ∧ c) ⟨ha, hc⟩
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

-- Explicit and implicit predicate parameters can appear in the same theorem.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (a) |-tla- ((b ∧ c) → a) := by
  tla_start ha
  tla_have' h := lem (b ∧ c) ha
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (b ∧ c) → a]⟩] [tlafml| (b ∧ c) → a]
  tla_apply h

-- The `@` form exposes implicit theorem arguments to positional arguments.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (a) |-tla- ((b ∧ c) → a) := by
  tla_start ha
  tla_have' h := @lem a (b ∧ c) ha
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (b ∧ c) → a]⟩] [tlafml| (b ∧ c) → a]
  tla_apply h

-- Missing trailing theorem arguments are inserted as ordinary Lean holes.
example : (⊥) |-tla- (a ↝ b) := by
  tla_start h
  tla_have' hw := wf1 a b
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tla_apply hw
  tla_contradiction

-- Add a residual implication from a `pred_implies` theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have h := lem
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tla_apply h ha

-- Supply an existing temporal hypothesis directly to the theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem ha
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Replace a named proof-mode hypothesis with a theorem derived from it.
example (lem : (a) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tla_start ha hc
  tla_replace ha := lem ha
  tla_check_goal Entails [⟨"hc", c⟩, ⟨"ha", b⟩] b
  tla_assumption

-- Lean arguments can be supplied before temporal proof-mode arguments.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem (0 + 1) ha
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The direct theorem prefix can also be kept as a residual implication.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have h := lem 0
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tla_apply h ha

-- Anonymous `tla_have := ...` appends an internal temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have := lem
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"this", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Valid implication chains share the same mixed-argument path as `tla_apply`.
example (lem : |-tla- (a → b → c)) : (a ∧ b) |-tla- (c) := by
  tla_start ha hb
  tla_have hc := lem ha hb
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Tuple temporal arguments conjunct multiple proof-mode hypotheses.
example (lem : (a ∧ b) |-tla- (c)) : (a ∧ b) |-tla- (c) := by
  tla_start ha hb
  tla_have hc := lem ⟨ha, hb⟩
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- The head can be a temporal hypothesis already in the proof-mode context.
example : ([tlafml| (a → b) ∧ a]) |-tla- (b) := by
  tla_start h ha
  tla_have hb := h ha
  tla_check_goal Entails [⟨"h", [tlafml| a → b]⟩, ⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

-- The term can be an expression, and the new hypothesis is appended.
example (lem : |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tla_start ha hc
  tla_have hb := (show |-tla- (b) from lem)
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

/-! ## `tla_suffices` -/

-- Basic: reduce the goal `a` to a stronger `a` (trivially via `pred_implies_refl`),
-- then prove the stronger one with the original `lem`.
example (lem : (b) |-tla- (a)) : (b) |-tla- (a) := by
  tla_start hb
  tla_suffices hsuff : a ∧ a by
    tla_check_goal Entails [⟨"hb", b⟩, ⟨"hsuff", [tlafml| a ∧ a]⟩] a
    tla_rcases hsuff with ⟨h, h'⟩
    tla_apply h
  tla_check_goal Entails [⟨"hb", b⟩] [tlafml| a ∧ a]
  tla_split_ands <;> tla_apply lem hb

-- Use `tla_rcases` inside `tla_suffices`' `by`-block to destructure the new
-- hypothesis and discharge the goal. The remaining main goal is the stronger
-- conjunction, which we close with the supplied lemma.
example (lem : (a) |-tla- (b ∧ c)) : (a) |-tla- (c) := by
  tla_start ha
  tla_suffices hbc : b ∧ c by
    tla_rcases hbc with ⟨hb, hc⟩
    tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  tla_check_goal Entails [⟨"ha", a⟩] [tlafml| b ∧ c]
  exact lem

/-! ## Interplay between the two -/

-- Use `tla_have` then `tla_suffices` together: introduce a derived hyp, then
-- reduce the goal further.
example (lemAB : (a) |-tla- (b)) (lemBC : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tla_start ha
  tla_have hb : b by
    tla_apply lemAB
    tla_check_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tla_suffices hc : c by
    tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] c
  tla_apply lemBC
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

example (lem1 : |-tla- (a ∨ b)) (lem2 : |-tla- (a → c)) :
  (b → c) |-tla- (c) := by
  tla_start hbc
  -- Allowing uninstantiated metavariables that will be resolved later
  tla_have h := TLA.or_elim
  tla_specialize h lem1
  tla_apply h lem2 hbc

example (q : (i : Nat) → i < n → pred σ) :
    (∃ j : Nat, ∃ hltj, (q j hltj)) |-tla- (⊤) := by
  -- intro p
  tla_start h
  tla_rcases h with ⟨j, h⟩
  -- NOTE: If we do not specify `p` here, unification will unfold related definitions
  tla_have := (TLA.find_min (p := fun j_ => [tlafml| ∃ hltj, (q j_ hltj)]) j) h
  tla_obtain ⟨j, hle, ⟨hltj, htmp⟩, hmin⟩ := this
  intro _ _
  trivial

end TLA.ProofMode.Test.Have
