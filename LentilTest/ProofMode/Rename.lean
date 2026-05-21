import Lentil

/- Tests for the `tla_rename` tactic.

   `tla_rename old => new` rewrites the name of the (first) hypothesis in the
   current `Entails` sequent whose name matches `old`, leaving the pred and
   the relative order of the list unchanged. If `old` is not in the list, the
   tactic is a silent no-op — `Entails_rename` filters by `findIdx?`, which
   returns `none` in that case.
-/

namespace TLA.ProofMode.Test.Rename

open TLA TLA.ProofMode

variable {σ : Type u} (a b c : pred σ)

-- Rename a single hypothesis.
example : (a) |-tla- (a) := by
  tla_start ha
  tla_rename ha => h
  tla_check_goal Entails [⟨"h", a⟩] a
  exact pred_implies_refl _

-- Rename preserves position and pred.
example : (a ∧ b ∧ c) |-tla- (b) := by
  tla_start ha hb hc
  tla_rename hb => hMid
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hMid", b⟩, ⟨"hc", c⟩] b
  intro _ ⟨_, hb, _⟩ ; exact hb

-- Renaming an unknown name is a no-op.
example : (a ∧ b) |-tla- (a) := by
  tla_start ha hb
  tla_rename noSuchHyp => hX
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Multiple renames chain.
example : (a ∧ b) |-tla- (a) := by
  tla_start ha hb
  tla_rename ha => x
  tla_rename hb => y
  tla_check_goal Entails [⟨"x", a⟩, ⟨"y", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Renaming after `tla_have`: the freshly-derived hypothesis can be renamed.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tla_start ha
  tla_have hb := lem ha
  tla_rename hb => result
  tla_check_goal Entails [⟨"ha", a⟩, ⟨"result", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Rename to the same name is a no-op (just verifies it doesn't choke).
example : (a) |-tla- (a) := by
  tla_start ha
  tla_rename ha => ha
  tla_check_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end TLA.ProofMode.Test.Rename
