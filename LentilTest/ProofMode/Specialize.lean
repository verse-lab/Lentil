import Lentil

/- Tests for the `tspecialize` tactic.

   `tspecialize h arg₁ … argₙ` repeatedly specializes the temporal
   hypothesis named `h`, replacing it in place. Arguments specialize either
   `∀` binders, temporal implications using proof-mode hypotheses, or pure
   implications using Lean-local proof hypotheses.
-/

namespace TLA.ProofMode.Test.Specialize

open TLA TLA.ProofMode

variable {σ : Type u} (a b c : pred σ)

-- Specialize a `∀` hypothesis with a Lean term.
example (P : Nat → pred σ) : (∀ n : Nat, (P n)) |-tla- (P 0) := by
  tstart h
  tspecialize h 0
  guard_target =ₛ Entails [⟨"h", P 0⟩] (P 0)
  tassumption

-- Universal specialization also accepts proof-valued witnesses.
example (Q : Prop) (hQ : Q) (P : Q → pred σ) :
    (∀ h : Q, (P h)) |-tla- (P hQ) := by
  tstart h
  tspecialize h hQ
  guard_target =ₛ Entails [⟨"h", P hQ⟩] (P hQ)
  tassumption

-- Multiple arguments specialize nested `∀` binders left-to-right.
example (P : Nat → Nat → pred σ) :
    (∀ x : Nat, ∀ y : Nat, (P x y)) |-tla- (P 1 2) := by
  tstart h
  tspecialize h 1 2
  guard_target =ₛ Entails [⟨"h", P 1 2⟩] (P 1 2)
  tassumption

-- Mixed specialization: a `∀` binder followed by a temporal implication.
example (P Q : Nat → pred σ) :
    ((∀ n : Nat, (P n) → (Q n)) ∧ (P 0)) |-tla- (Q 0) := by
  tstart h hp
  tspecialize h 0 hp
  guard_target =ₛ Entails [⟨"h", Q 0⟩, ⟨"hp", P 0⟩] (Q 0)
  tassumption

-- Temporal implication specialization keeps the premise hypothesis.
example : ((a → b) ∧ a) |-tla- (b) := by
  tstart h ha
  tspecialize h ha
  guard_target =ₛ Entails [⟨"h", b⟩, ⟨"ha", a⟩] b
  tassumption

-- Pure implication specialization uses a Lean-local proof.
example (Q : Prop) (hQ : Q) : (⌞ Q ⌟ → a) |-tla- (a) := by
  tstart h
  tspecialize h hQ
  guard_target =ₛ Entails [⟨"h", a⟩] a
  tassumption

-- The specialized hypothesis keeps its original position in the context.
example (P : Nat → pred σ) :
    (a ∧ (∀ n : Nat, (P n)) ∧ b) |-tla- (P 3) := by
  tstart ha h hb
  tspecialize h 3
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"h", P 3⟩, ⟨"hb", b⟩] (P 3)
  tassumption

-- Error: the named temporal hypothesis does not exist.
/--
error: tspecialize: hypothesis 'missing' not found in the goal's Entails list
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tstart ha
  tspecialize missing 0

-- Error: implication argument is neither a Lean-local proof nor a temporal hyp.
/--
error: tspecialize: temporal hypothesis 'ha' not found in the goal's Entails list
-/
#guard_msgs in
example : (a → b) |-tla- (b) := by
  tstart h
  tspecialize h ha

-- Error: the selected hypothesis cannot be specialized.
/--
error: tspecialize: hypothesis 'ha' is not a ∀ or implication; got a
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tstart ha
  tspecialize ha 0

-- Error: temporal implication arguments must name proof-mode hypotheses.
/--
error: tspecialize: temporal hypothesis 'n' not found in the goal's Entails list
-/
#guard_msgs in
example (n : Nat) : (a → b) |-tla- (b) := by
  tstart h
  tspecialize h n

end TLA.ProofMode.Test.Specialize
