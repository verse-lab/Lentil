import Lentil.ProofMode.Location

namespace TLA.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

/-
`tsimp` and `tdsimp` are implemented directly with `conv`, separately
from `trewrite`'s local-`let` hiding pipeline. The simplifier does not create
rewrite-theorem premise goals, so we can visit each selected expression inside
the literal `Entails` target and run the requested conv tactic there.

For a proof-mode hypothesis at index `i`, the conv path is:

  `Entails` argument 1, then `i` tails of the list, then the head
  `NamedPred`, then its predicate field.

The goal predicate is just argument 2 of `Entails`.
-/

private def runConvAtProofModeLocations
    (tacticName : String)
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (mkConv : TacticM (TSyntax `conv)) : TacticM Unit := do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal
    | throwError "{tacticName}: goal is not an Entails sequent"
  let loc ← parseRewriteLocation hyps loc? tacticName
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

/--
`tsimp` simplifies predicates in a proof-mode goal or selected proof-mode
hypotheses, using Lean's `simp` arguments.

With no location, it simplifies the goal predicate. For example,
```lean
tsimp [heq]
```
simplifies the goal using `heq`. With a location,
```lean
tsimp [heq] at hp hq
```
simplifies only the temporal hypotheses `hp` and `hq`.
-/
syntax (name := tlaSimp) "tsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (Lean.Parser.Tactic.location)? : tactic

/--
`tdsimp` definitionally simplifies predicates in a proof-mode goal or
selected proof-mode hypotheses, using Lean's `dsimp` arguments.

For example, if `hp` has predicate `wrap p` and `wrap` unfolds to the identity,
then
```lean
tdsimp [wrap] at hp
```
changes `hp` to have predicate `p`.
-/
syntax (name := tlaDsimp) "tdsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")?
  (Lean.Parser.Tactic.location)? : tactic

syntax (name := tlaUnfold) "tunfold" (ppSpace colGt ident)+ (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| tsimp $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]? $[$loc]?) => do
    runConvAtProofModeLocations "tsimp" loc do
      `(conv| simp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)
  | `(tactic| tdsimp $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]? $[$loc]?) => do
    runConvAtProofModeLocations "tdsimp" loc do
      `(conv| dsimp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)
  | `(tactic| tunfold $defs:ident* $[$loc]?) => do
    runConvAtProofModeLocations "tunfold" loc do
      `(conv| unfold $defs:ident*)

end TLA.ProofMode
