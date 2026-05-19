import Lentil

/- Tests for `tla_rintro`. -/

namespace TLA.ProofMode.Test.RIntro

open TLA TLA.ProofMode

variable {σ : Type u} (p q r s : pred σ)

-- For universal quantifiers, `tla_rintro` behaves like Lean's `rintro`.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) →
    (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tla_start
  tla_rintro n
  show Entails [] (P n)
  intro e _
  exact h e True.intro n

-- Pure antecedents are introduced into the Lean context and may be destructured.
example (Q R : Prop) (h : Q → R → (p) |-tla- (q)) :
    (p) |-tla- (⌞ Q ∧ R ⌟ → q) := by
  tla_start hp
  tla_rintro ⟨hQ, hR⟩
  show Entails [⟨"hp", p⟩] q
  exact h hQ hR

-- Temporal antecedents are introduced as proof-mode hypotheses and then
-- destructured with `tla_rcases`.
example : (p) |-tla- ((q ∧ r) → q) := by
  tla_start hp
  tla_rintro ⟨hq, hr⟩
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] q
  intro _ ⟨_, hq, _⟩ ; exact hq

-- Existential temporal antecedents introduce a Lean witness and a temporal hyp.
example (P : Nat → pred σ) :
    (⊤) |-tla- ((∃ n : Nat, (P n)) → (∃ n : Nat, (P n))) := by
  tla_start
  tla_rintro ⟨n, hp⟩
  show Entails [⟨"hp", P n⟩] [tlafml| ∃ n : Nat, (P n)]
  intro _ hp
  exact ⟨n, hp⟩

-- Mixed introductions proceed from left to right.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (((P n) ∧ q) → r → (P n))) := by
  tla_start
  tla_rintro n ⟨hp, hq⟩ hr
  show Entails [⟨"hp", P n⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] (P n)
  intro _ ⟨hp, _⟩ ; exact hp

-- Numeric `tla_rcases` targets the chosen proof-mode hypothesis, even when
-- names are duplicated.
example (lem1 : (p) |-tla- (p ∧ q)) (lem2 : (p) |-tla- (q ∧ r)) :
    (p) |-tla- (q) := by
  tla_start hp
  tla_have h := lem1 hp
  tla_have h := lem2 hp
  tla_rcases 2 with ⟨hq, hr⟩
  show Entails [⟨"hp", p⟩, ⟨"h", [tlafml| p ∧ q]⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] q
  intro _ ⟨_, _, hq, _⟩ ; exact hq

-- A temporal antecedent `q ∨ r` is case-split with a parenthesized
-- alternation; the later pattern `hs` is introduced into both subgoals.
example : (p) |-tla- ((q ∨ r) → s → (q ∨ r)) := by
  tla_start hp
  tla_rintro (hq | hr) hs
  · intro _ ⟨_, hq, _⟩ ; exact Or.inl hq
  · intro _ ⟨_, hr, _⟩ ; exact Or.inr hr

-- A later tuple pattern is destructured in both case-split subgoals.
example : (p) |-tla- ((q ∨ r) → (q ∧ r) → q) := by
  tla_start hp
  tla_rintro (hq | hr) ⟨hc, hd⟩
  · intro _ ⟨_, _, hc, _⟩ ; exact hc
  · intro _ ⟨_, _, hc, _⟩ ; exact hc

-- Two successive case-splitting patterns: the second must fan out over both
-- subgoals produced by the first. Four bullets pin the goal count.
example : (p) |-tla- ((q ∨ r) → (q ∨ r) → ⊤) := by
  tla_start hp
  tla_rintro (hq1 | hr1) (hq2 | hr2)
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro

end TLA.ProofMode.Test.RIntro
