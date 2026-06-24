import Lentil

/- Tests for the `thave` and `tsuffices` tactics.

   Both take a hypothesis name, a `tlafml`, and a `by`-block:
     * `thave h : fml by tac` — `tac` proves `Entails hyps fml` from the
       current premises; the remaining main goal carries `⟨h, fml⟩` in the
       temporal context.
     * `thave h := t` — `t : |-tla- fml` is added as a temporal hypothesis
       named `h`.
     * `tsuffices h : fml by tac` — `tac` closes the original goal using
       the new hypothesis `⟨h, fml⟩`; the remaining main goal is to prove
       `fml` from the current premises.
-/

namespace TLA.ProofMode.Test.Have

open TLA TLA.ProofMode

variable {σ : Type u} (a b c : pred σ)

/-! ## `thave` -/

-- Basic: justify `hb : b` from the existing `ha : a` via a lemma, then use it.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave hb : b by
    tapply lem
    tcheck_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Multi-step `by`-block: nested `t*` tactics work as expected.
example (lem1 : (a) |-tla- (b)) (lem2 : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tstart ha
  thave hc : c by
    tapply lem2
    tapply lem1
    tcheck_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, hc⟩ ; exact hc

-- "Duplicate" an existing hyp under a different name (the by-block just
-- restates the hyp via reflexivity).
example : (a) |-tla- (a) := by
  tstart ha
  thave ha' : a by
    tcheck_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"ha'", a⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Add a valid TLA fact as a temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave hb := lem
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The restricted prime form accepts formula syntax as theorem arguments.
example (lem : ∀ p : pred σ, |-tla- (p → p)) : (a) |-tla- (a) := by
  tstart ha
  thave' h := lem (a ∧ b)
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (a ∧ b) → (a ∧ b)]⟩] a
  tassumption

-- The prime form can keep a formula-instantiated theorem as a residual implication.
example (lem : ∀ p : pred σ, (p) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tstart ha hc
  thave' h := lem (a ∧ c)
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"h", [tlafml| (a ∧ c) → b]⟩] b
  tapply h ⟨ha, hc⟩

-- Lean arguments before the theorem shape are consumed before temporal arguments.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave' hb := lem (0 + 1) ha
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Valid implication chains still specialize through proof-mode hypotheses.
example (lem : |-tla- (a → b → c)) : (a ∧ b) |-tla- (c) := by
  tstart ha hb
  thave' hc := lem ha hb
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Formula arguments and tuple temporal arguments can appear in the same application.
example (lem : ∀ p : pred σ, (p) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tstart ha hc
  thave' hb := lem (a ∧ c) ⟨ha, hc⟩
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

-- Explicit and implicit predicate parameters can appear in the same theorem.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (a) |-tla- ((b ∧ c) → a) := by
  tstart ha
  thave' h := lem (b ∧ c) ha
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (b ∧ c) → a]⟩] [tlafml| (b ∧ c) → a]
  tapply h

-- The `@` form exposes implicit theorem arguments to positional arguments.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (a) |-tla- ((b ∧ c) → a) := by
  tstart ha
  thave' h := @lem a (b ∧ c) ha
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| (b ∧ c) → a]⟩] [tlafml| (b ∧ c) → a]
  tapply h

-- Missing trailing theorem arguments are inserted as ordinary Lean holes.
example : (⊥) |-tla- (a ↝ b) := by
  tstart h
  thave' hw := wf1 a b
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tapply hw
  tcontradiction

-- Add a residual implication from a `pred_implies` theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave h := lem
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tapply h ha

-- Supply an existing temporal hypothesis directly to the theorem.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave hb := lem ha
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Replace a named proof-mode hypothesis with a theorem derived from it.
example (lem : (a) |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tstart ha hc
  treplace ha := lem ha
  tcheck_goal Entails [⟨"hc", c⟩, ⟨"ha", b⟩] b
  tassumption

-- Lean arguments can be supplied before temporal proof-mode arguments.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave hb := lem (0 + 1) ha
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- The direct theorem prefix can also be kept as a residual implication.
example (lem : ∀ _ : Nat, (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave h := lem 0
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"h", [tlafml| a → b]⟩] b
  tapply h ha

-- Anonymous `thave := ...` appends an internal temporal hypothesis.
example (lem : |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave := lem
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"this", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Valid implication chains share the same mixed-argument path as `tapply`.
example (lem : |-tla- (a → b → c)) : (a ∧ b) |-tla- (c) := by
  tstart ha hb
  thave hc := lem ha hb
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Tuple temporal arguments conjunct multiple proof-mode hypotheses.
example (lem : (a ∧ b) |-tla- (c)) : (a ∧ b) |-tla- (c) := by
  tstart ha hb
  thave hc := lem ⟨ha, hb⟩
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- The head can be a temporal hypothesis already in the proof-mode context.
example : ([tlafml| (a → b) ∧ a]) |-tla- (b) := by
  tstart h ha
  thave hb := h ha
  tcheck_goal Entails [⟨"h", [tlafml| a → b]⟩, ⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

-- The term can be an expression, and the new hypothesis is appended.
example (lem : |-tla- (b)) : (a ∧ c) |-tla- (b) := by
  tstart ha hc
  thave hb := (show |-tla- (b) from lem)
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, _, hb⟩ ; exact hb

/-! ## `tsuffices` -/

-- Basic: reduce the goal `a` to a stronger `a` (trivially via `pred_implies_refl`),
-- then prove the stronger one with the original `lem`.
example (lem : (b) |-tla- (a)) : (b) |-tla- (a) := by
  tstart hb
  tsuffices hsuff : a ∧ a by
    tcheck_goal Entails [⟨"hb", b⟩, ⟨"hsuff", [tlafml| a ∧ a]⟩] a
    trcases hsuff with ⟨h, h'⟩
    tapply h
  tcheck_goal Entails [⟨"hb", b⟩] [tlafml| a ∧ a]
  tsplit_ands <;> tapply lem hb

-- Use `trcases` inside `tsuffices`' `by`-block to destructure the new
-- hypothesis and discharge the goal. The remaining main goal is the stronger
-- conjunction, which we close with the supplied lemma.
example (lem : (a) |-tla- (b ∧ c)) : (a) |-tla- (c) := by
  tstart ha
  tsuffices hbc : b ∧ c by
    trcases hbc with ⟨hb, hc⟩
    tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  tcheck_goal Entails [⟨"ha", a⟩] [tlafml| b ∧ c]
  exact lem

/-! ## Interplay between the two -/

-- Use `thave` then `tsuffices` together: introduce a derived hyp, then
-- reduce the goal further.
example (lemAB : (a) |-tla- (b)) (lemBC : (b) |-tla- (c)) :
    (a) |-tla- (c) := by
  tstart ha
  thave hb : b by
    tapply lemAB
    tcheck_goal Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tsuffices hc : c by
    tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    intro _ ⟨_, _, hc⟩ ; exact hc
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] c
  tapply lemBC
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

example (lem1 : |-tla- (a ∨ b)) (lem2 : |-tla- (a → c)) :
  (b → c) |-tla- (c) := by
  tstart hbc
  -- Allowing uninstantiated metavariables that will be resolved later
  thave h := TLA.or_elim
  tspecialize h lem1
  tapply h lem2 hbc

example (q : (i : Nat) → i < n → pred σ) :
    (∃ j : Nat, ∃ hltj, (q j hltj)) |-tla- (⊤) := by
  -- intro p
  tstart h
  trcases h with ⟨j, h⟩
  -- NOTE: If we do not specify `p` here, unification will unfold related definitions
  thave := (TLA.find_min (p := fun j_ => [tlafml| ∃ hltj, (q j_ hltj)]) j) h
  tobtain ⟨j, hle, ⟨hltj, htmp⟩, hmin⟩ := this
  intro _ _
  trivial

end TLA.ProofMode.Test.Have
