import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

syntax temporalHypLoc := (ident <|> num)

/-- Locations for proof-mode hypotheses. Can be a name or an index. -/
inductive TemporalHypLoc where
  | byName (name : String)
  | byIdx (idx : Nat)

def parseTemporalHypLoc (pos : Syntax) (errorMsg : MessageData) : TacticM TemporalHypLoc := do
  -- FIXME: Is this too hacky? It seems that matching on both `term` and `temporalHypLoc` is
  -- necessary in certain cases, but is there a better way to do this?
  match pos with
  | `(term| $id:ident) | `(temporalHypLoc| $id:ident) => pure <| .byName <| toString id.getId
  | `(term| $num:num) | `(temporalHypLoc| $num:num) => pure <| .byIdx <| num.getNat
  | _ => throwError errorMsg

def quoteTemporalHypLoc : TemporalHypLoc → TSyntax `term
  | .byName name => quote name
  | .byIdx idx => quote idx

def findByTemporalHypLoc (xs : List (String × α)) : TemporalHypLoc → Option (String × α)
  | .byName name => xs.find? fun x => x.1 == name
  | .byIdx idx => xs[idx]?

/-- Locations for `rewrite`/`simp`-like tactics. -/
structure RewriteLocation where
  idxs : Array Nat
  includeGoal : Bool

def parseRewriteLocation
    (hyps : List (String × Expr))
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (errorMsgPrefix : String) : TacticM RewriteLocation := do
  match loc? with
  | none => return ⟨#[], true⟩
  | some loc =>
    -- Reuse the logic for location expansion from Lean
    -- NOTE: `expandOptLocation` does not work here, it seems
    let loc := expandLocation loc
    match loc with
    | Location.wildcard =>
      return ⟨Array.range hyps.length, true⟩
    | Location.targets stxs includeGoal =>
      let idxs ← stxs.mapM fun x => do
        let hypLoc ← parseTemporalHypLoc x m!"{errorMsgPrefix}: unsupported location {x}; expected a proof-mode hypothesis name or index"
        match hypLoc with
        | .byName name =>
          let some idx := hyps.findIdx? fun hyp => hyp.1 == name
            | throwError "{errorMsgPrefix}: hypothesis {name} not found in the goal"
          pure idx
        | .byIdx idx =>
          if idx < hyps.length then pure idx else throwError "{errorMsgPrefix}: hypothesis index {idx} is out of bounds"
      return ⟨idxs, includeGoal⟩

end TLA.ProofMode
