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
  -- `hQ : Q` is now in the Lean ctx; the temporal list dropped its `⟨"hQ", ⌞Q⌟⟩`.
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem hQ

-- Pull from the middle of the list — the rest of the order is preserved.
example (Q : Prop) :
    (a ∧ ⌞ Q ⌟ ∧ b) |-tla- (a) := by
  tstart ha hQ hb
  tpull_pure hQ
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  tassumption

-- Pull and then use the pulled fact in subsequent reasoning.
example (Q : Prop) (lem : Q → (a) |-tla- (b)) :
    (a ∧ ⌞ Q ⌟) |-tla- (b) := by
  tstart ha hQ
  tpull_pure hQ
  guard_target =ₛ Entails [⟨"ha", a⟩] b
  tapply' lem hQ
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

-- Multiple pure facts can be pulled in sequence.
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tstart ha hQ hR
  tpull_pure hQ
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hR", [tlafml| ⌞ R ⌟]⟩] a
  tpull_pure hR
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem hQ hR

-- Multiple pure facts in one invocation (space-separated, like `tclear`).
example (Q R : Prop) (lem : Q → R → (a) |-tla- (a)) :
    (a ∧ ⌞ Q ⌟ ∧ ⌞ R ⌟) |-tla- (a) := by
  tstart ha hQ hR
  tpull_pure hQ hR
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact lem hQ hR

-- Basic: pull a single pure fact, use it at the Lean level.
example (b c : Nat) : (a ∧ ⌞ b ≤ c ⌟) |-tla- (a) := by
  tstart ha hQ
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hQ", [tlafml| ⌞ b ≤ c ⌟]⟩] a
  tpull_pure hQ
  guard_hyp hQ :ₛ b ≤ c
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  tapply ha

end TLA.ProofMode.Test.PurePred
