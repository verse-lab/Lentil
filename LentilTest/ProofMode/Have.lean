import Lentil

/- Tests for the `thave` and `tsuffices` tactics.

   Both take a hypothesis name, a `tlfml`, and a `by`-block:
     * `thave h : fml by tac` — `tac` proves `Entails hyps fml` from the
       current premises; the remaining main goal carries `⟨h, fml⟩` in the
       temporal context.
     * `thave h := t` — `t : |-tl- fml` is added as a temporal hypothesis
       named `h`.
     * `tsuffices h : fml by tac` — `tac` closes the original goal using
       the new hypothesis `⟨h, fml⟩`; the remaining main goal is to prove
       `fml` from the current premises.
-/

namespace Lentil.ProofMode.Test.Have

open Lentil Lentil.ProofMode

variable {σ : Type u} (a b c : pred σ)

/-! ## `thave` -/

-- Basic: justify `hb : b` from the existing `ha : a` via a lemma, then use it.
example (lem : (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave hb : b by
    tapply lem
    guard_target =ₛ Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- Multi-step `by`-block: nested `t*` tactics work as expected.
example (lem1 : (a) |-tl- (b)) (lem2 : (b) |-tl- (c)) :
    (a) |-tl- (c) := by
  tstart ha
  thave hc : c by
    tapply lem2
    tapply lem1
    guard_target =ₛ Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hc", c⟩] c
  tassumption

-- "Duplicate" an existing hyp under a different name (the by-block just
-- restates the hyp via reflexivity).
example : (a) |-tl- (a) := by
  tstart ha
  thave ha' : a by
    guard_target =ₛ Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"ha'", a⟩] a
  tassumption

-- Add a valid LTL fact as a temporal hypothesis.
example (lem : |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave hb := lem
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- The restricted prime form accepts formula syntax as theorem arguments.
example (lem : ∀ p : pred σ, |-tl- (p → p)) : (a) |-tl- (a) := by
  tstart ha
  thave' h := lem (a ∧ b)
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", [tlfml| (a ∧ b) → (a ∧ b)]⟩] a
  tassumption

-- The prime form can keep a formula-instantiated theorem as a residual implication.
example (lem : ∀ p : pred σ, (p) |-tl- (b)) : (a ∧ c) |-tl- (b) := by
  tstart ha hc
  thave' h := lem (a ∧ c)
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"h", [tlfml| (a ∧ c) → b]⟩] b
  tapply h ⟨ha, hc⟩

-- Lean arguments before the theorem shape are consumed before temporal arguments.
example (lem : ∀ _ : Nat, (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave' hb := lem (0 + 1) ha
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- Valid implication chains still specialize through proof-mode hypotheses.
example (lem : |-tl- (a → b → c)) : (a ∧ b) |-tl- (c) := by
  tstart ha hb
  thave' hc := lem ha hb
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  tassumption

-- Formula arguments and tuple temporal arguments can appear in the same application.
example (lem : ∀ p : pred σ, (p) |-tl- (b)) : (a ∧ c) |-tl- (b) := by
  tstart ha hc
  thave' hb := lem (a ∧ c) ⟨ha, hc⟩
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  tassumption

-- Explicit and implicit predicate parameters can appear in the same theorem.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tl- (q → p)) :
    (a) |-tl- ((b ∧ c) → a) := by
  tstart ha
  thave' h := lem (b ∧ c) ha
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", [tlfml| (b ∧ c) → a]⟩] [tlfml| (b ∧ c) → a]
  tapply h

-- The `@` form exposes implicit theorem arguments to positional arguments.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tl- (q → p)) :
    (a) |-tl- ((b ∧ c) → a) := by
  tstart ha
  thave' h := @lem a (b ∧ c) ha
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", [tlfml| (b ∧ c) → a]⟩] [tlfml| (b ∧ c) → a]
  tapply h

-- Missing trailing theorem arguments are inserted as ordinary Lean holes.
example : (⊥) |-tl- (a ↝ b) := by
  tstart h
  thave' hw := @wf1 _ a b
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tapply hw
  tcontradiction

-- Formula parameters that are determined by a temporal argument stay implicit.
example : (□ a) |-tl- (a) := by
  tstart hall
  thave ha := always_weaken hall
  tapply ha

-- Intermediate formulas are inferred from the temporal theorem arguments.
example (hab : |-tl- (a ↝ b)) (hbc : |-tl- (b ↝ c)) :
    (⊤) |-tl- (a ↝ c) := by
  tstart
  thave hac := leads_to_trans hab hbc
  tapply hac

-- Add a residual implication from a `pred_implies` theorem.
example (lem : (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave h := lem
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", [tlfml| a → b]⟩] b
  tapply h ha

-- Supply an existing temporal hypothesis directly to the theorem.
example (lem : (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave hb := lem ha
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- Replace a named proof-mode hypothesis with a theorem derived from it.
example (lem : (a) |-tl- (b)) : (a ∧ c) |-tl- (b) := by
  tstart ha hc
  treplace ha := lem ha
  guard_target =ₛ Entails [⟨"hc", c⟩, ⟨"ha", b⟩] b
  tassumption

-- Lean arguments can be supplied before temporal proof-mode arguments.
example (lem : ∀ _ : Nat, (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave hb := lem (0 + 1) ha
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- The direct theorem prefix can also be kept as a residual implication.
example (lem : ∀ _ : Nat, (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave h := lem 0
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", [tlfml| a → b]⟩] b
  tapply h ha

-- Anonymous `thave := ...` appends an internal temporal hypothesis.
example (lem : |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave := lem
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"this", b⟩] b
  tassumption

-- Valid implication chains share the same mixed-argument path as `tapply`.
example (lem : |-tl- (a → b → c)) : (a ∧ b) |-tl- (c) := by
  tstart ha hb
  thave hc := lem ha hb
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  tassumption

-- Tuple temporal arguments conjunct multiple proof-mode hypotheses.
example (lem : (a ∧ b) |-tl- (c)) : (a ∧ b) |-tl- (c) := by
  tstart ha hb
  thave hc := lem ⟨ha, hb⟩
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  tassumption

-- The head can be a temporal hypothesis already in the proof-mode context.
example : ([tlfml| (a → b) ∧ a]) |-tl- (b) := by
  tstart h ha
  thave hb := h ha
  guard_target =ₛ Entails [⟨"h", [tlfml| a → b]⟩, ⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

-- The term can be an expression, and the new hypothesis is appended.
example (lem : |-tl- (b)) : (a ∧ c) |-tl- (b) := by
  tstart ha hc
  thave hb := (show |-tl- (b) from lem)
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hc", c⟩, ⟨"hb", b⟩] b
  tassumption

section UnificationTest

private def inferenceMarker {α : Type v} {β : Type u} (x : α) : pred (α × β) :=
  fun e i => (e i).1 = x

private def inferenceSample {α : Type v} {β : Type u}
    (family : α → pred (α × β)) : pred (α × β) :=
  fun e i => family (e i).1 e i

private opaque inferenceWrap {γ : Type w} : pred γ → pred γ := fun formula => formula

-- Reflected arguments constrain implicit theorem parameters before the
-- resulting temporal fact is added to the proof-mode context.
example {α : Type v} {β : Type u} (x : α)
    (rule : ∀ {family : α → pred (α × β)} {y : α},
      (inferenceMarker y ∧ inferenceSample family) |-tl- (family y)) :
    letI formula : pred (α × β) :=
      [tlfml|
        inferenceMarker x →
        inferenceSample (fun y => inferenceWrap (inferenceMarker y)) →
        inferenceWrap (inferenceMarker x)
      ]
    |-tl- (formula) := by
  tnormalize
  tstart hx hp
  thave result := (rule) ⟨hx, hp⟩
  tassumption

-- Keep a single reflected premise in its original syntactic form. Wrapping it
-- in `repeatedAnd [p]` makes unification unfold `inferenceSample` first, after
-- which `family` occurs at a non-pattern argument and can no longer be inferred.
example {α : Type v} {β : Type u}
    (rule : ∀ {family : α → pred (α × β)}, (inferenceSample family) |-tl- (⊤)) :
    (inferenceSample (α := α) (β := β)
      (fun y => inferenceWrap (inferenceMarker (β := β) y))) |-tl- (⊤) := by
  tstart hp
  thave result := rule hp
  tassumption

-- Ordinary Lean arguments can precede the reflected argument, while a
-- conclusion-only parameter remains available to later proof-mode tactics.
example (rule : ∀ _ : Nat, ∀ {result : pred σ}, (a) |-tl- (result)) :
    (a) |-tl- (b) := by
  tstart ha
  thave result := rule 0 ha
  tassumption

end UnificationTest

/-! ## `tsuffices` -/

-- Basic: reduce the goal `a` to a stronger `a` (trivially via `pred_implies_refl`),
-- then prove the stronger one with the original `lem`.
example (lem : (b) |-tl- (a)) : (b) |-tl- (a) := by
  tstart hb
  tsuffices hsuff : a ∧ a by
    guard_target =ₛ Entails [⟨"hb", b⟩, ⟨"hsuff", [tlfml| a ∧ a]⟩] a
    trcases hsuff with ⟨h, h'⟩
    tapply h
  guard_target =ₛ Entails [⟨"hb", b⟩] [tlfml| a ∧ a]
  tsplit_ands <;> tapply lem hb

-- Use `trcases` inside `tsuffices`' `by`-block to destructure the new
-- hypothesis and discharge the goal. The remaining main goal is the stronger
-- conjunction, which we close with the supplied lemma.
example (lem : (a) |-tl- (b ∧ c)) : (a) |-tl- (c) := by
  tstart ha
  tsuffices hbc : b ∧ c by
    trcases hbc with ⟨hb, hc⟩
    guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    tassumption
  guard_target =ₛ Entails [⟨"ha", a⟩] [tlfml| b ∧ c]
  exact lem

/-! ## Interplay between the two -/

-- Use `thave` then `tsuffices` together: introduce a derived hyp, then
-- reduce the goal further.
example (lemAB : (a) |-tl- (b)) (lemBC : (b) |-tl- (c)) :
    (a) |-tl- (c) := by
  tstart ha
  thave hb : b by
    tapply lemAB
    guard_target =ₛ Entails [⟨"ha", a⟩] a
    exact pred_implies_refl _
  tsuffices hc : c by
    guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
    tassumption
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] c
  tapply lemBC
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] b
  tassumption

example (lem1 : |-tl- (a ∨ b)) (lem2 : |-tl- (a → c)) :
  (b → c) |-tl- (c) := by
  tstart hbc
  -- Allowing uninstantiated metavariables that will be resolved later
  thave h := Lentil.or_elim
  tspecialize h lem1
  tapply h lem2 hbc

example (q : (i : Nat) → i < n → pred σ) :
    (∃ j : Nat, ∃ hltj, (q j hltj)) |-tl- (⊤) := by
  -- intro p
  tstart h
  trcases h with ⟨j, h⟩
  -- NOTE: If we do not specify `p` here, unification will unfold related definitions
  thave := (Lentil.find_min (p := fun j_ => [tlfml| ∃ hltj, (q j_ hltj)]) j) h
  tobtain ⟨j, hle, ⟨hltj, htmp⟩, hmin⟩ := this
  tprove_pure
  trivial

-- Replacing one of two identically named hypotheses preserves the other one.
example (lemB : (a) |-tl- (b)) (lemC : (a) |-tl- (c)) : (a) |-tl- (b) := by
  tstart h
  thave h := lemB h
  treplace h := lemC h
  guard_target =ₛ Entails [⟨"h", b⟩, ⟨"h", c⟩] b
  tassumption

end Lentil.ProofMode.Test.Have
