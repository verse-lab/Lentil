import Lentil

/- Tests for the `tla_pull_pure` tactic.

   `tla_pull_pure h`, where `h : ⌞Q⌟` is a pure-fact hypothesis in the current
   temporal context, removes that hypothesis from the temporal context and
   adds `h : Q` to Lean's local context. The soundness theorem composes
   `Entails_revert` and `Entails_pure_fact_intro`.
-/

namespace TLA.ProofMode.Test.PurePred

open TLA TLA.ProofMode

variable {σ : Type u} (a b : pred σ)

-- Basic: pull a single pure fact, use it at the Lean level.
example (Q : Prop) (lem : Q → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟) |-tla- (a) := by
  tla_start ha hQ
  tla_pull_pure hQ
  -- `hQ : Q` is now in the Lean ctx; the temporal list dropped its `⟨"hQ", ⌞Q⌟⟩`.
  show Entails [⟨"ha", a⟩] a
  exact lem hQ

-- Pull from the middle of the list — the rest of the order is preserved.
example (Q : Prop) :
    (a ∧ ⌞ Q ⌟ ∧ b) |-tla- (a) := by
  tla_start ha hQ hb
  tla_pull_pure hQ
  show Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Pull and then use the pulled fact in subsequent reasoning.
example (Q : Prop) (lem : Q → (a) |-tla- (b)) :
    (a ∧ ⌞ Q ⌟) |-tla- (b) := by
  tla_start ha hQ
  tla_pull_pure hQ
  tla_apply (lem hQ)
  show Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

-- Multiple pure facts can be pulled in sequence.
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tla_start ha hQ hR
  tla_pull_pure hQ
  tla_pull_pure hR
  show Entails [⟨"ha", a⟩] a
  exact lem hQ hR

-- Multiple pure facts in one invocation (space-separated, like `tla_clear`).
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tla_start ha hQ hR
  tla_pull_pure hQ hR
  show Entails [⟨"ha", a⟩] a
  exact lem hQ hR

end TLA.ProofMode.Test.PurePred
