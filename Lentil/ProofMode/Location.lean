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

def quoteTemporalHypLoc : TemporalHypLoc → TacticM (TSyntax ``temporalHypLoc)
  | .byName name => `(temporalHypLoc| $(mkIdent (.mkSimple name)):ident)
  | .byIdx idx => `(temporalHypLoc| $(Syntax.mkNatLit idx):num)

def quoteTemporalHypLocToTerm : TemporalHypLoc → TSyntax `term
  | .byName name => quote name
  | .byIdx idx => quote idx

def findIdxByTemporalHypLoc? (xs : List (String × α)) : TemporalHypLoc →
    Option (Nat × String × α)
  | .byName name =>
    match xs.findFinIdx? (fun x => x.1 == name) with
    | some idx => some (idx, xs[idx])
    | none => none
  | .byIdx idx => xs[idx]?.map fun x => (idx, x.1, x.2)

def findByTemporalHypLoc? (xs : List (String × α)) (loc : TemporalHypLoc) :
    Option (String × α) :=
  findIdxByTemporalHypLoc? xs loc |>.map Prod.snd

def findIdxByTemporalHypLoc [Monad m] [MonadError m] (xs : List (String × α))
    (loc : TemporalHypLoc) (errorMsgPrefix errorMsgSuffix : String) :
    m (Nat × String × α) := do
  match findIdxByTemporalHypLoc? xs loc with
  | some res => pure res
  | none =>
    match loc with
    | .byName name => throwError m!"{errorMsgPrefix}: hypothesis '{name}' not found in {errorMsgSuffix}"
    | .byIdx idx => throwError m!"{errorMsgPrefix}: hypothesis index {idx} not found in {errorMsgSuffix}"

def findByTemporalHypLoc [Monad m] [MonadError m] (xs : List (String × α)) (loc : TemporalHypLoc) (errorMsgPrefix errorMsgSuffix : String) : m (String × α) := do
  let (_, res) ← findIdxByTemporalHypLoc xs loc errorMsgPrefix errorMsgSuffix
  return res

/-- If `tm` is a bare identifier that names a proof-mode hypothesis in `hyps`,
return that name. Lean locals shadow proof-mode hypotheses. -/
def temporalHypNameOfBareTerm? (hyps : List (String × α)) (tm : Term) :
    TacticM (Option String) := withMainContext do
  let some id ← LentilLib.termIdent? tm | return none
  if (← getLCtx).findFromUserName? id.getId |>.isSome then
    return none
  let name := toString id.getId
  return if hyps.any (fun ⟨hypName, _⟩ => hypName == name) then some name else none

def temporalHypLocOfBareTerm? (hyps : List (String × α)) (tm : Term) :
    TacticM (Option TemporalHypLoc) := do
  return (← temporalHypNameOfBareTerm? hyps tm).map .byName

/-- Locations for `rewrite`/`simp`-like tactics. -/
structure RewriteLocation where
  idxs : Array Nat
  includeGoal : Bool
  isWildCard : Bool

def parseRewriteLocation
    (hyps : List (String × Expr))
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (errorMsgPrefix : String) : TacticM RewriteLocation := do
  match loc? with
  | none => return ⟨#[], true, false⟩
  | some loc =>
    -- Reuse the logic for location expansion from Lean
    -- NOTE: `expandOptLocation` does not work here, it seems
    let loc := expandLocation loc
    match loc with
    | Location.wildcard =>
      return ⟨Array.range hyps.length, true, true⟩
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
      return ⟨idxs, includeGoal, false⟩

end TLA.ProofMode
