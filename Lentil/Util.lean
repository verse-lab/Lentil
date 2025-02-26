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

/-- Marking the theorems that can be simplify reasoning at the TLA level. -/
register_simp_attr tlasimp

/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tladual

initialize registerTraceClass `lentil.debug
