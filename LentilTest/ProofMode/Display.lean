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
       |-tl- goal
   We assert this by capturing `#check` output with `#guard_msgs`.
-/

namespace Lentil.ProofMode.Test.Display

open Lentil Lentil.ProofMode

variable {σ : Type u} (p q r : pred σ)

-- Empty hypothesis list: just `|-tl- goal`.
/-- info: |-tl- p : Prop -/
#guard_msgs in
#check (Entails [] p : Prop)

-- Single hypothesis on its own line.
/-- info: hp : p
|-tl- q : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩] q : Prop)

-- Multiple hypotheses each on their own line, in list order.
/-- info: hp : p
hq : q
|-tl- r : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r : Prop)

-- Goal renders through the tlfml delaborator, so LTL conjunction notation is
-- preserved.
/-- info: hp : p
hq : q
hr : r
|-tl- p ∧ q ∧ r : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩, ⟨"hq", q⟩, ⟨"hr", r⟩] [tlfml| p ∧ q ∧ r] : Prop)

-- Unicode hypothesis label is preserved (the name string becomes an `Ident`).
/-- info: ψ : p
|-tl- p : Prop -/
#guard_msgs in
#check (Entails [⟨"ψ", p⟩] p : Prop)

-- Temporal operators in the goal render through the tlfml notation.
/-- info: hp : p
|-tl- □p : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", p⟩] [tlfml| □ p] : Prop)

-- Hypotheses can also carry temporal predicates.
/-- info: hp : □p
|-tl- ◇p : Prop -/
#guard_msgs in
#check (Entails [⟨"hp", [tlfml| □ p]⟩] [tlfml| ◇ p] : Prop)

-- Sanity-check that the same shape is produced by `tstart`: after the
-- tactic runs, the goal is a real `Entails …` and thus rendered via the
-- proof-mode delaborator. `guard_target =ₛ` confirms the named term shape.
example : (p ∧ q) |-tl- (r) → (p ∧ q) |-tl- (r) := by
  intro h
  tstart hp hq
  guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
  exact h

end Lentil.ProofMode.Test.Display
