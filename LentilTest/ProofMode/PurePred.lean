import Lentil

/- Tests for the `tpull_pure` tactic.

   `tpull_pure h`, where `h : ⌞Q⌟` is a pure-fact hypothesis in the current
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
  tstart ha hQ
  tpull_pure hQ
  tcheck_goal_form
  -- `hQ : Q` is now in the Lean ctx; the temporal list dropped its `⟨"hQ", ⌞Q⌟⟩`.
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact lem hQ

-- Pull from the middle of the list — the rest of the order is preserved.
example (Q : Prop) :
    (a ∧ ⌞ Q ⌟ ∧ b) |-tla- (a) := by
  tstart ha hQ hb
  tpull_pure hQ
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Pull and then use the pulled fact in subsequent reasoning.
example (Q : Prop) (lem : Q → (a) |-tla- (b)) :
    (a ∧ ⌞ Q ⌟) |-tla- (b) := by
  tstart ha hQ
  tpull_pure hQ
  tcheck_goal_form
  tapply' lem hQ
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

-- Multiple pure facts can be pulled in sequence.
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tstart ha hQ hR
  tpull_pure hQ
  tcheck_goal_form
  tpull_pure hR
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact lem hQ hR

-- Multiple pure facts in one invocation (space-separated, like `tclear`).
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tstart ha hQ hR
  tpull_pure hQ hR
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact lem hQ hR

end TLA.ProofMode.Test.PurePred
