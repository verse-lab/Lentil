import Lentil

/- Tests for the `tapply` tactic. -/

namespace TLA.ProofMode.Test.Apply

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Backward apply of a `q |-tla- r` lemma reduces the goal to producing `q`.
example (lem : (q) |-tla- (r)) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tstart hp
  tapply lem
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h

-- Direct application also accepts a valid implication theorem.
example (lem : |-tla- (p → q)) : (p) |-tla- (q) := by
  tstart hp
  tapply lem
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Mixed application: a proof-mode hypothesis can be supplied as an argument.
example (lem : (p) |-tla- (q)) : (p) |-tla- (q) := by
  tstart hp
  -- tapply lem hp
  thave := lem hp
  tapply this

-- Lean arguments before the temporal theorem shape are consumed before
-- residual temporal premises become subgoals.
example (lem : ∀ _ : Nat, (p) |-tla- (q)) : (p) |-tla- (q) := by
  tstart hp
  tapply lem 0
  guard_target =ₛ Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Once a Lean argument has exposed the theorem, temporal arguments are handled
-- by `tspecialize`.
example (lem : ∀ _ : Nat, (p) |-tla- (q)) : (p) |-tla- (q) := by
  tstart hp
  tapply lem (0 + 1) hp

-- Valid implication chains accept multiple proof-mode arguments.
example (lem : |-tla- (p → q → r)) : (p ∧ q) |-tla- (r) := by
  tstart hp hq
  tapply lem hp hq

-- Supplying only part of a chain leaves the residual premise as a proof-mode subgoal.
example (lem : |-tla- (p → q → s → r)) : (p ∧ q ∧ s) |-tla- (r) := by
  tstart hp hq hs
  tapply lem hp
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hs", s⟩] [tlafml| q ∧ s]
  tsplit_ands <;> tassumption

-- Tuple arguments are flattened into the selected temporal premises.
example (lem : (p ∧ q) |-tla- (r)) : (p ∧ q) |-tla- (r) := by
  tstart hp hq
  tapply lem ⟨hp, hq⟩

-- The restricted prime form accepts formula syntax as theorem arguments.
example (lem : ∀ p : pred σ, (p) |-tla- (r)) : (p ∧ q) |-tla- (r) := by
  tstart hp hq
  tapply' lem (p ∧ q)
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] [tlafml| p ∧ q]
  tsplit_ands <;> tassumption

-- Lean arguments before the theorem shape are consumed before temporal arguments.
example (lem : ∀ _ : Nat, (p) |-tla- (q)) : (p) |-tla- (q) := by
  tstart hp
  tapply' lem (0 + 1) hp

-- Valid implication chains specialize through proof-mode hypotheses.
example (lem : |-tla- (p → q → r)) : (p ∧ q) |-tla- (r) := by
  tstart hp hq
  tapply' lem hp hq

-- Formula arguments and tuple temporal arguments can appear in the same application.
example (lem : ∀ p : pred σ, (p) |-tla- (r)) : (p ∧ q) |-tla- (r) := by
  tstart hp hq
  tapply' lem (p ∧ q) ⟨hp, hq⟩

-- Explicit and implicit predicate parameters can appear in the same theorem.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (p) |-tla- ((q ∧ s) → p) := by
  tstart hp
  tapply' lem (q ∧ s) hp

-- The `@` form exposes implicit theorem arguments to positional arguments.
example (lem : ∀ {p : pred σ} (q : pred σ), (p) |-tla- (q → p)) :
    (p) |-tla- ((q ∧ s) → p) := by
  tstart hp
  tapply' @lem p (q ∧ s) hp

-- The head being applied can itself be a proof-mode temporal hypothesis.
example : ([tlafml| (p → q) ∧ p]) |-tla- (q) := by
  tstart h hp
  tapply h hp

-- Bare identifiers in the Lean local context win over temporal hypotheses.
example {P : Prop} (hpure : P) (lem : |-tla- (⌞ P ⌟ → q)) : (p) |-tla- (q) := by
  tstart hp
  tapply lem hpure

example (lem1 : |-tla- (a ∨ b)) (lem2 : |-tla- (a → c)) :
  (b → c) |-tla- (c) := by
  tstart hbc
  tapply TLA.or_elim
  tsplit_ands
  · tapply lem1
  · tapply lem2
  · tassumption

-- Predicate parameters of inference rules are inferred from the target and
-- the temporal premises created by backward application.
example : (a ∧ (a → b)) |-tla- (b) := by
  tstart ha hab
  tapply TLA.modus_ponens
  tsplit_ands <;> tassumption

-- Applying `wf1` with its action arguments supplied should still infer the
-- state predicates from the current goal.
example (next act : action σ) : (⊥) |-tla- (p ↝ q) := by
  tstart h
  tapply wf1 (next := next) (a := act)
  tcontradiction

example : (⊥) |-tla- (a ↝ b) := by
  tstart h
  tapply (wf1 _ _)
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tcontradiction

-- The prime form infers the formula parameters from the target and may omit
-- the explicit action arguments by inserting ordinary Lean holes.
example : (⊥) |-tla- (a ↝ b) := by
  tstart h
  tapply' wf1
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tcontradiction

-- With `@`, implicit arguments such as the state type are supplied positionally.
example : (⊥) |-tla- (a ↝ b) := by
  tstart h
  tapply' @wf1 _ a b
  on_goal 2=> exact fun _ _ => False
  on_goal 2=> exact fun _ _ => False
  tcontradiction

section UnificationTest

private def inferenceMarker {α : Type v} {β : Type u} (x : α) : pred (α × β) :=
  fun e i => (e i).1 = x

private def inferenceSample {α : Type v} {β : Type u}
    (family : α → pred (α × β)) : pred (α × β) :=
  fun e i => family (e i).1 e i

private opaque inferenceWrap {γ : Type w} : pred γ → pred γ := fun formula => formula

-- The predicate family and point are constrained by reflected temporal
-- arguments. They must remain assignable until those arguments are inspected.
example {α : Type v} {β : Type u} (x : α)
    (rule : ∀ {family : α → pred (α × β)} {y : α},
      (inferenceMarker y ∧ inferenceSample family) |-tla- (family y)) :
    letI formula : pred (α × β) :=
      [tlafml|
        inferenceMarker x →
        inferenceSample (fun y => inferenceWrap (inferenceMarker y)) →
        inferenceWrap (inferenceMarker x)
      ]
    |-tla- (formula) := by
  tnormalize
  tstart hx hp
  tapply (rule) ⟨hx, hp⟩

-- Parameters are still inferred when some temporal premises remain as
-- backward-application goals.
example {α : Type v} {β : Type u} (x : α) (r : pred (α × β))
    (rule : ∀ {family : α → pred (α × β)} {y : α} {premise : pred (α × β)},
      (inferenceMarker y ∧ inferenceSample family) |-tla- (premise → family y)) :
    letI formula : pred (α × β) :=
      [tlafml|
        inferenceMarker x →
        inferenceSample (fun y => inferenceWrap (inferenceMarker y)) →
        r →
        inferenceWrap (inferenceMarker x)
      ]
    |-tla- (formula) := by
  tnormalize
  tstart hx hp hr
  tapply (rule (premise := r)) ⟨hx, hp⟩
  tassumption

-- An implicit parameter appearing only in the conclusion remains assignable
-- until backward application compares it with the current target. An ordinary
-- Lean argument may precede the reflected temporal argument.
example (rule : ∀ _ : Nat, ∀ {result : pred σ}, (p) |-tla- (result)) :
    (p) |-tla- (q) := by
  tstart hp
  tapply rule 0 hp

end UnificationTest

end TLA.ProofMode.Test.Apply
