import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

attribute [tlanormsimp ↓] impl_intro valid_eq_true_implies impl_intro_add_r and_assoc and_true true_and

macro "tla_normalize" : tactic => `(tactic| simp -$(mkIdent `failIfUnchanged) only [tlanormsimp])

end TLA.ProofMode
