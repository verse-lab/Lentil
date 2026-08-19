import Lentil.Basic

/-! Attributes and their registries used by proof-mode tactics. -/

namespace TLA.ProofMode

open Lean Meta

section ModalityUnfold

/-- Declarations tagged with `[tla_modality_unfold]`. -/
initialize tlaModalityUnfoldExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name := `tlaModalityUnfoldExt
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun s ns =>
        ns.foldl (init := s) fun s n => s.insert n
    addEntryFn := fun s n => s.insert n
  }

def hasTlaModalityUnfoldAttr (env : Environment) (decl : Name) : Bool :=
  (tlaModalityUnfoldExt.getState env).contains decl

/-- Marking definitions whose head may hide a leading modality operator. -/
initialize registerBuiltinAttribute {
  name := `tla_modality_unfold
  descr := "definitions whose head may be unfolded by proof-mode modality tactics"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `tla_modality_unfold kind
    modifyEnv fun env => tlaModalityUnfoldExt.addEntry env decl
}

end ModalityUnfold

section TMapMono

/-! `@[tmap_mono]` registers a unary predicate operator through a theorem of either
form `|-tla- ((p ⇒ q) → (op p → op q))` or
`(p ⇒ q) |-tla- (op p → op q)`. The registered theorem is strong enough for
`tmap` to transport both global implications and proof-mode `always_implies`
hypotheses through `op`. -/

def recognizeAlwaysImplies? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match_expr e with
  | TLA.always_implies _ lhs rhs => return (lhs, rhs)
  | TLA.always _ a =>
    match_expr a with
    | TLA.tla_implies _ lhs rhs => return (lhs, rhs)
    | _ => return none
  | _ => return none

/-- Extract `op` from either supported statement form of `@[tmap_mono]`. -/
private def tmapMonotoneOperator? (type : Expr) : MetaM (Option Name) :=
  forallTelescope type fun _ body => do
    match_expr body with
    | TLA.valid _ formula =>
        match_expr formula with
        | TLA.tla_implies _ stableImplication mappedImplication =>
            tmapMonotoneOperatorFrom? stableImplication mappedImplication
        | _ => return none
    | TLA.pred_implies _ stableImplication mappedImplication =>
        tmapMonotoneOperatorFrom? stableImplication mappedImplication
    | _ => return none
where
  /-- Extract the registered operator after the outer theorem representation has
  been normalized to its stable premise and mapped conclusion. -/
  tmapMonotoneOperatorFrom?
    (stableImplication mappedImplication : Expr) : MetaM (Option Name) := do
  let some (p, q) ← recognizeAlwaysImplies? stableImplication
    | return none
  match_expr mappedImplication with
  | TLA.tla_implies _ opP opQ =>
      let .app opForP p' := opP | return none
      let .app opForQ q' := opQ | return none
      unless ← isDefEq p' p do return none
      unless ← isDefEq q' q do return none
      unless ← isDefEq opForP opForQ do return none
      return opForP.getAppFn'.constName?
  | _ => return none

/-- Declarations tagged with `[tmap_mono]`.
Each entry has type `Name × Name`, corresponding to `(opname, theoremName)`. -/
initialize tmapMonotoneExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    name := `tmapMonotoneExt
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun state moduleEntries =>
        moduleEntries.foldl (init := state) fun state (op, theoremName) =>
          state.insert op theoremName
    addEntryFn := fun state (op, theoremName) => state.insert op theoremName
  }

/-- Find the theorem registered for an operator head with `@[tmap_mono]`. -/
def findTmapMonotonicity? (env : Environment) (operator : Name) : Option Name :=
  (tmapMonotoneExt.getState env).find? operator

/-- Register either supported monotonicity theorem form so that `tmap` can
descend through applications of `op`. -/
initialize registerBuiltinAttribute {
  name := `tmap_mono
  descr := "monotone predicate operators recognized by the `tmap` tactic"
  add := fun theoremName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwAttrMustBeGlobal `tmap_mono kind
    let operator? ← MetaM.run' do
      tmapMonotoneOperator? (← getConstInfo theoremName).type
    let some operator := operator?
      | throwError "@[tmap_mono] expects one of the forms\n  \
          |-tla- ((p ⇒ q) → (op p → op q))\n  \
          (p ⇒ q) |-tla- (op p → op q)\nbut '{theoremName}' has a different shape"
    let env ← getEnv
    if let some existing := findTmapMonotonicity? env operator then
      throwError "operator '{operator}' already has @[tmap_mono] theorem '{existing}'"
    modifyEnv fun env => tmapMonotoneExt.addEntry env (operator, theoremName)
}

end TMapMono

end TLA.ProofMode
