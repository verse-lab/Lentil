import Lentil

/- Tests for the `tla_apply` tactic.

   Two forms:
     * Backward:  `tla_apply lem`
         If `lem : mid |-tla- goal` and the current goal is `Entails Γ goal`,
         the new goal becomes `Entails Γ mid` (via `Entails_trans`).
     * Forward:   `tla_apply lem at h₁ … hₙ as out`
         If `lem : (p₁ ∧ … ∧ pₙ) |-tla- new` and `Γ` contains hypotheses
         named `h₁, …, hₙ` with those predicates, the new goal contains an
         additional hypothesis `out : new` appended at the end. A leading
         `-` on a name (e.g. `-h₁`) marks the hypothesis for removal.
-/

namespace TLA.ProofMode.Test.Apply

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

/-! ## Backward form -/

-- Backward apply of a `q |-tla- r` lemma reduces an `Entails [hp : p] r` goal
-- to producing `q` from `p`.
example (lem : (q) |-tla- (r)) (h : (p) |-tla- (q)) : (p) |-tla- (r) := by
  tla_start hp
  tla_apply lem
  show Entails [⟨"hp", p⟩] q
  exact h

-- Backward apply where the supplied lemma already discharges the goal.
example : (p) |-tla- (p) := by
  tla_start hp
  tla_apply (show (p) |-tla- (p) from pred_implies_refl _)
  show Entails [⟨"hp", p⟩] p
  exact pred_implies_refl _

-- Chained backward applies.
example (lem1 : (r) |-tla- (q)) (lem2 : (p) |-tla- (r)) : (p) |-tla- (q) := by
  tla_start hp
  tla_apply lem1
  show Entails [⟨"hp", p⟩] r
  exact lem2

/-! ## Forward form -/

-- Forward apply: from `hp : p` derive `hq : q` via lemma `p |-tla- q`. The
-- new hypothesis is appended at the end of the hypothesis list.
example (lem : (p) |-tla- (q)) : (p) |-tla- ([tlafml| p ∧ q]) := by
  tla_start hp
  tla_apply lem at hp as hq
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩] [tlafml| p ∧ q]
  intro _ ⟨hp, hq⟩
  exact ⟨hp, hq⟩

-- Forward apply consuming a hypothesis: `-hp` drops `hp` after producing `hq`.
example (lem : (p) |-tla- (q)) : (p) |-tla- (q) := by
  tla_start hp
  tla_apply lem at -hp as hq
  show Entails [⟨"hq", q⟩] q
  exact pred_implies_refl _

-- Forward apply using multiple hypotheses to derive a new one.
example (lem : (p ∧ q) |-tla- (r)) : (p ∧ q) |-tla- (r) := by
  tla_start hp hq
  tla_apply lem at hp hq as hr
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] r
  intro _ ⟨_, _, hr⟩ ; exact hr

-- Mixed: consume `hp`, retain `hq`, produce `hr`.
example (lem : (p ∧ q) |-tla- (r)) : (p ∧ q) |-tla- ([tlafml| q ∧ r]) := by
  tla_start hp hq
  tla_apply lem at -hp hq as hr
  show Entails [⟨"hq", q⟩, ⟨"hr", r⟩] [tlafml| q ∧ r]
  intro _ ⟨hq, hr⟩ ; exact ⟨hq, hr⟩

-- Selecting hypotheses out of order: `lem`'s premise list is fed in the order
-- given in the `at …` clause, independent of the order in the context.
example (lem : (q ∧ p) |-tla- (r)) : (p ∧ q) |-tla- (r) := by
  tla_start hp hq
  tla_apply lem at hq hp as hr
  show Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] r
  intro _ ⟨_, _, hr⟩ ; exact hr

end TLA.ProofMode.Test.Apply
