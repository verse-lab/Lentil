import Lean
import Lentil.Utils.MetaUtil
import Lentil.Utils.SyntaxUtil
import Lentil.Utils.MiscLemmas

open Lean

register_option lentil.pp.useDelab : Bool := {
  defValue := true
  descr := "Use the delaborator from `Lentil.Basic` for delaboration. "
}

register_option lentil.pp.autoRenderSatisfies : Bool := {
  defValue := true
  descr := "Automatically render an application `p e` as `e |=tla= p` when `p` is a TLA formula. "
}

/-- Marking the non-temporal parts of TLA. -/
register_simp_attr tla_nontemporal_def

/-- Marking the TLA definitions. -/
register_simp_attr tlasimp_def

/-- Marking the things to simplify when explicitly reasoning about `exec`. -/
register_simp_attr execsimp

/-- Marking the definitions unfolded by `tfinite_window`. -/
register_simp_attr tla_finite_window_def

/-- Marking the theorems that can be simplify reasoning at the TLA level. -/
register_simp_attr tlasimp

/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tladual

/-- Marking the theorems that are used for normalizing sequents. -/
register_simp_attr tlanormsimp

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

initialize registerTraceClass `lentil.debug
