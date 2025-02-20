import Lean

open Lean Meta Elab

/-- Add a single theorem to the environment by providing its name, type and proof. -/
def simpleAddTheorem (name : Name) (lvlParams : List Name) (type value : Expr) (nonComputable? : Bool) : CoreM Unit := do
  let thm := Declaration.thmDecl <| mkTheoremValEx name lvlParams type value []
  if nonComputable? then
    addDecl <| thm
    setEnv <| addNoncomputable (← getEnv) name
  else
    addAndCompile thm

/-- Prove a theorem at the level of `MetaM`, without going into the proof mode. -/
def simpleProveTheorem (name : Name) (lvlParams : List Name) (type : Expr) (proofScript : TSyntax `term)
    (nonComputable? : Bool) : MetaM Unit := do
  let proof ← liftCommandElabM <| Command.liftTermElabM do
    -- when things go wrong, print the proof goal
    let proof ← Term.elabTermAndSynthesize proofScript type
    if proof.hasSorry then
      trace[lentil.debug] "theorem {name} : {type} := {proofScript}"
    -- it is **SUPER WEIRD** that without adding this check, `proof` would still contain
    -- level metavariables, and `instantiateMVars` would not work as expected!
    check proof
    instantiateMVars proof
  simpleAddTheorem name lvlParams type proof nonComputable?
