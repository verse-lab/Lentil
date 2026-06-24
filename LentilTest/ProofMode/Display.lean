import Lentil
-- `Lentil.ProofMode.Display` is not pulled in by the umbrella `Lentil` import
-- (it's not listed in `Lentil.lean`), so we import it explicitly here. Without
-- this, `delabEntails` is never registered and `Entails …` prints in its raw
-- structural form.
import Lentil.ProofMode.Display

/- Tests for the proof-mode delaborator (`delabEntails`).

   `Entails hyps goal` is rendered as a multi-line proof-mode view:
       h₁ : p₁
       h₂ : p₂
       ⋮
       |-tla- goal
   We assert this by capturing `#check` output with `#guard_msgs`.
-/

namespace TLA.ProofMode.Test.Display

open TLA TLA.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Empty hypothesis list: just `|-tla- goal`.
/-- info: |-tla- p : Prop -/
#guard_msgs in
#check (Entails [] p : Prop)

-- Single hypothesis on its own line.
/-- info: hp : p
|-tla- q : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩] q : Prop)

-- Multiple hypotheses each on their own line, in list order.
/-- info: hp : p
hq : q
|-tla- r : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r : Prop)

-- Goal renders through the tlafml delaborator, so TLA conjunction notation is
-- preserved.
/-- info: hp : p
hq : q
hr : r
|-tla- p ∧ q ∧ r : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] [tlafml| p ∧ q ∧ r] : Prop)

-- Unicode hypothesis label is preserved (the name string becomes an `Ident`).
/-- info: ψ : p
|-tla- p : Prop -/
#guard_msgs in
#check (Entails [⟨"ψ", p⟩] p : Prop)

-- Temporal operators in the goal render through the tlafml notation.
/-- info: hp : p
|-tla- □p : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩] [tlafml| □ p] : Prop)

-- Hypotheses can also carry temporal predicates.
/-- info: hp : □p
|-tla- ◇p : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| ◇ p] : Prop)

-- Sanity-check that the same shape is produced by `tstart`: after the
-- tactic runs, the goal is a real `Entails …` and thus rendered via the
-- proof-mode delaborator. `tcheck_goal` confirms the named term shape.
example : (p ∧ q) |-tla- (r) → (p ∧ q) |-tla- (r) := by
  intro h
  tstart hp hq
  tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

end TLA.ProofMode.Test.Display
