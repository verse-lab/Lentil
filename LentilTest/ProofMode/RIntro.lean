import Lentil

/- Tests for `trintro`. -/

namespace TLA.ProofMode.Test.RIntro

open TLA TLA.ProofMode

variable {σ : Type u} (p q r s : pred σ)

-- For universal quantifiers, `trintro` behaves like Lean's `rintro`.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (P n)) →
    (⊤) |-tla- (∀ n : Nat, (P n)) := by
  intro h
  tstart
  trintro n
  guard_target =ₛ Entails [] (P n)
  thave htop : ⊤ by
    tprove_pure
    trivial
  thave hall := h htop n
  tassumption

-- Pure antecedents are introduced into the Lean context and may be destructured.
example (Q R : Prop) (h : Q → R → (p) |-tla- (q)) :
    (p) |-tla- (⌞ Q ∧ R ⌟ → q) := by
  tstart hp
  trintro ⟨hQ, hR⟩
  guard_target =ₛ Entails [⟨"hp", p⟩] q
  exact h hQ hR

-- Temporal antecedents are introduced as proof-mode hypotheses and then
-- destructured with `trcases`.
example : (p) |-tla- ((q ∧ r) → q) := by
  tstart hp
  trintro ⟨hq, hr⟩
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] q
  tassumption

-- Existential temporal antecedents introduce a Lean witness and a temporal hyp.
example (P : Nat → pred σ) :
    (⊤) |-tla- ((∃ n : Nat, (P n)) → (∃ n : Nat, (P n))) := by
  tstart
  trintro ⟨n, hp⟩
  guard_target =ₛ Entails [⟨"hp", P n⟩] [tlafml| ∃ n : Nat, (P n)]
  texists n
  tassumption

-- Mixed introductions proceed from left to right.
example (P : Nat → pred σ) :
    (⊤) |-tla- (∀ n : Nat, (((P n) ∧ q) → r → (P n))) := by
  tstart
  trintro n ⟨hp, hq⟩ hr
  guard_target =ₛ Entails [⟨"hp", P n⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] (P n)
  tassumption

-- Numeric `trcases` targets the chosen proof-mode hypothesis, even when
-- names are duplicated.
example (lem1 : (p) |-tla- (p ∧ q)) (lem2 : (p) |-tla- (q ∧ r)) :
    (p) |-tla- (q) := by
  tstart hp
  thave h := lem1 hp
  thave h := lem2 hp
  trcases 2 with ⟨hq, hr⟩
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"h", [tlafml| p ∧ q]⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] q
  tassumption

-- A temporal antecedent `q ∨ r` is case-split with a parenthesized
-- alternation; the later pattern `hs` is introduced into both subgoals.
example : (p) |-tla- ((q ∨ r) → s → (q ∨ r)) := by
  tstart hp
  trintro (hq | hr) hs
  · tleft
    tassumption
  · tright
    tassumption

-- A later tuple pattern is destructured in both case-split subgoals.
example : (p) |-tla- ((q ∨ r) → (q ∧ r) → q) := by
  tstart hp
  trintro (hq | hr) ⟨hc, hd⟩
  · tassumption
  · tassumption

-- Two successive case-splitting patterns: the second must fan out over both
-- subgoals produced by the first. Four bullets pin the goal count.
example : (p) |-tla- ((q ∨ r) → (q ∨ r) → ⊤) := by
  tstart hp
  trintro (hq1 | hr1) (hq2 | hr2)
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial

-- `trintro -` introduces a temporal antecedent and immediately clears it.
example : (p) |-tla- (q → p) := by
  -- The discarded antecedent's internal name must not collide with this `h`.
  tstart h
  trintro -
  guard_target =ₛ Entails [⟨"h", p⟩] p
  tassumption

end TLA.ProofMode.Test.RIntro
