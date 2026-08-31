import Lentil

/- Tests for the `trename` tactic.

   `trename old => new` rewrites the name of the (first) hypothesis in the
   current `Entails` sequent whose name matches `old`, leaving the pred and
   the relative order of the list unchanged. If `old` is not in the list, the
   tactic is a silent no-op — `Entails_rename` filters by `findIdx?`, which
   returns `none` in that case.
-/

namespace Lentil.ProofMode.Test.Rename

open Lentil Lentil.ProofMode

variable {σ : Type u} (a b c : pred σ)

-- Rename a single hypothesis.
example : (a) |-tl- (a) := by
  tstart ha
  trename ha => h
  guard_target =ₛ Entails [⟨"h", a⟩] a
  exact pred_implies_refl _

-- Rename preserves position and pred.
example : (a ∧ b ∧ c) |-tl- (b) := by
  tstart ha hb hc
  trename hb => hMid
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hMid", b⟩, ⟨"hc", c⟩] b
  tassumption

-- Renaming an unknown name is a no-op.
example : (a ∧ b) |-tl- (a) := by
  tstart ha hb
  trename noSuchHyp => hX
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  tassumption

-- Multiple renames chain.
example : (a ∧ b) |-tl- (a) := by
  tstart ha hb
  trename ha => x
  trename hb => y
  guard_target =ₛ Entails [⟨"x", a⟩, ⟨"y", b⟩] a
  tassumption

-- Renaming after `thave`: the freshly-derived hypothesis can be renamed.
example (lem : (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart ha
  thave hb := lem ha
  trename hb => result
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"result", b⟩] b
  tassumption

-- Rename to the same name is a no-op (just verifies it doesn't choke).
example : (a) |-tl- (a) := by
  tstart ha
  trename ha => ha
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end Lentil.ProofMode.Test.Rename
