module

public import Lentil.ProofMode.Basic

public meta section

open Lean

namespace Lentil.ProofMode

syntax tlPmHyp := ident " : " tlfml
syntax tlPmEntails := ppDedent(ppLine tlPmHyp)* ppDedent(ppLine "|-tl- " tlfml)

open PrettyPrinter.Delaborator SubExpr

def delabNameInNamedPred : DelabM Ident := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  let some s := parseStringLit? e | failure
  pure <| mkIdent <| Name.mkSimple s

def delabNamedPred : DelabM (TSyntax ``tlPmHyp) := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  unless e.isAppOfArity' ``Lentil.ProofMode.NamedPred.mk 3 do
    failure
  let fml ← withAppArg delab_tlfml_inner
  let nm ← withAppFn <| withAppArg delabNameInNamedPred
  `(tlPmHyp| $nm:ident : $fml:tlfml)

partial def delabNamedPredList : DelabM (List (TSyntax ``tlPmHyp)) := do
  let e ← getExpr
  if e.isAppOfArity' ``List.nil 1 then
    return []
  if e.isAppOfArity' ``List.cons 3 then
    -- List.cons {α} head tail   →  args 0,1,2
    let head ← withAppFn <| withAppArg delabNamedPred
    let tail ← withAppArg delabNamedPredList
    return head :: tail
  failure

def delabEntails : Delab := do
  let e ← getExpr
  unless e.isAppOfArity' ``Lentil.ProofMode.Entails 3 do failure
  -- Entails {σ} hyps goal   →  args 0,1,2
  let hyps ← withAppFn <| withAppArg delabNamedPredList
  let hyps := hyps.toArray
  let goal ← withAppArg delab_tlfml_inner
  let q ← `(tlPmEntails| $hyps:tlPmHyp* |-tl- $goal:tlfml)
  -- NOTE: This is a hack, but making `tlPmEntails` a `term` might again introduce some
  -- weird parsing errors, so just "pretend" the result is a `term` and display it
  pure ⟨q⟩

attribute [delab app.Lentil.ProofMode.Entails] delabEntails

end Lentil.ProofMode
