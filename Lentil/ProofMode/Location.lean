import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

syntax temporalHypLoc := (ident <|> num)

/-- Locations for proof-mode hypotheses. Can be a name or an index. -/
inductive TemporalHypLoc where
  | byName (name : String)
  | byIdx (idx : Nat)

def parseTemporalHypLoc (pos : TSyntax ``TLA.ProofMode.temporalHypLoc) (errorMsg : MessageData) : TacticM TemporalHypLoc := do
  match pos with
  | `(temporalHypLoc| $id:ident) => pure <| .byName <| toString id.getId
  | `(temporalHypLoc| $num:num) => pure <| .byIdx <| num.getNat
  | _ => throwError errorMsg

def quoteTemporalHypLoc : TemporalHypLoc → TSyntax `term
  | .byName name => quote name
  | .byIdx idx => quote idx

def findByTemporalHypLoc (xs : List (String × α)) : TemporalHypLoc → Option (String × α)
  | .byName name => xs.find? fun x => x.1 == name
  | .byIdx idx => xs[idx]?

end TLA.ProofMode
