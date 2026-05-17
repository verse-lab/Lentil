import Lentil.ProofMode.Tactics.Apply
import Lentil.ProofMode.Tactics.Clear
import Lentil.ProofMode.Tactics.Exists
import Lentil.ProofMode.Tactics.Have
import Lentil.ProofMode.Tactics.Intro
import Lentil.ProofMode.Tactics.Normalize
import Lentil.ProofMode.Tactics.PurePred
import Lentil.ProofMode.Tactics.RCases
import Lentil.ProofMode.Tactics.Rename
import Lentil.ProofMode.Tactics.Revert
import Lentil.ProofMode.Tactics.Rewrite
import Lentil.ProofMode.Tactics.Simp
import Lentil.ProofMode.Tactics.Specialize
import Lentil.ProofMode.Tactics.SplitAnds
import Lentil.ProofMode.Tactics.Start

/-
NOTE: On the soundness theorems corresponding to these tactics:
(not including `normalize` and `start`)
- `clear`: simple inclusion reasoning
- `exists`, `intro`: basically reducing to existing rules
- `revert`: basically the inversion of `intro`
- `pull_pure`: `revert` + `intro`
- `rename`: a very special case of inclusion reasoning (eq)
- `rcases`: reducing to `revert`
- `specialize`: general logic of filling in the LHS of an implication
- `have`/`suffices`: reducing to `specialize`
- `apply`: reducing to `have` then `specialize`
- `rewrite`: hide unselected proof-mode locations behind a local continuation,
  run Lean's `rewrite`, then reconstruct the `Entails` sequent
- `simp`/`dsimp`: run Lean's simplifiers as direct `conv` visits to selected
  proof-mode locations

NOTE: Currently, after applying meta soundness theorems, we almost always need a
post simplification step for the goal, which might be fragile in certain cases.
Probably, a better way is to (partially) compute the resulting goal at the meta
level, and then convert the goal to it by defeq?
-/
