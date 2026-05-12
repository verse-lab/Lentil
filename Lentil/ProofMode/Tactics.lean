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
- `apply`: kind of new and complicated, not quite depending on the others
- `have`/`suffices`: reducing to `apply`
- `specialize`: reducing to `apply`

-/
