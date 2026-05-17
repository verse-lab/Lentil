import Lentil.ProofMode.Location

namespace TLA.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

/-
`tla_simp` and `tla_dsimp` are implemented directly with `conv`, separately
from `tla_rewrite`'s local-`let` hiding pipeline. The simplifier does not create
rewrite-theorem premise goals, so we can visit each selected expression inside
the literal `Entails` target and run the requested conv tactic there.

For a proof-mode hypothesis at index `i`, the conv path is:

  `Entails` argument 1, then `i` tails of the list, then the head
  `NamedPred`, then its predicate field.

The goal predicate is just argument 2 of `Entails`.
-/

private def runConvAtProofModeLocations
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (mkConv : TacticM (TSyntax `conv)) : TacticM Unit := do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal
    | throwError "tla_simp: goal is not an Entails sequent"
  let loc ← parseRewriteLocation hyps loc? "tla_simp"
  for idx in loc.idxs do
    runConvAtPath (hypPredConvPath idx) (← mkConv)
  if loc.includeGoal then
    runConvAtPath #[2] (← mkConv)
where
  runConvAtPath (path : Array Nat) (convTac : TSyntax `conv) : TacticM Unit := do
    let path ← path.mapM fun x => `(Lean.Parser.Tactic.Conv.enterArg| $(Syntax.mkNatLit x):num)
    evalTactic <| ← `(tactic| conv => enter [$[$path],*] ; $convTac:conv)
  hypPredConvPath (idx : Nat) : Array Nat :=
    [1] ++ List.replicate idx 2 ++ [1, 2] |>.toArray

syntax (name := tlaSimp) "tla_simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (Lean.Parser.Tactic.location)? : tactic

syntax (name := tlaDsimp) "tla_dsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")?
  (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| tla_simp $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]? $[$loc]?) => do
    runConvAtProofModeLocations loc do
      `(conv| simp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)
  | `(tactic| tla_dsimp $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]? $[$loc]?) => do
    runConvAtProofModeLocations loc do
      `(conv| dsimp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)

end TLA.ProofMode
