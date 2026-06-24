import Lentil

/- Tests for the `trename` tactic.

   `trename old => new` rewrites the name of the (first) hypothesis in the
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
  tstart ha
  trename ha => h
  tcheck_goal Entails [⟨"h", a⟩] a
  exact pred_implies_refl _

-- Rename preserves position and pred.
example : (a ∧ b ∧ c) |-tla- (b) := by
  tstart ha hb hc
  trename hb => hMid
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hMid", b⟩, ⟨"hc", c⟩] b
  intro _ ⟨_, hb, _⟩ ; exact hb

-- Renaming an unknown name is a no-op.
example : (a ∧ b) |-tla- (a) := by
  tstart ha hb
  trename noSuchHyp => hX
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Multiple renames chain.
example : (a ∧ b) |-tla- (a) := by
  tstart ha hb
  trename ha => x
  trename hb => y
  tcheck_goal Entails [⟨"x", a⟩, ⟨"y", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- Renaming after `thave`: the freshly-derived hypothesis can be renamed.
example (lem : (a) |-tla- (b)) : (a) |-tla- (b) := by
  tstart ha
  thave hb := lem ha
  trename hb => result
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"result", b⟩] b
  intro _ ⟨_, hb⟩ ; exact hb

-- Rename to the same name is a no-op (just verifies it doesn't choke).
example : (a) |-tla- (a) := by
  tstart ha
  trename ha => ha
  tcheck_goal Entails [⟨"ha", a⟩] a
  exact pred_implies_refl _

end TLA.ProofMode.Test.Rename
