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
  descr := "Automatically render an application `p e` as `e |=tl= p` when `p` is a LTL formula. "
}

/-- Marking the non-temporal parts of Lentil. -/
register_simp_attr tl_nontemporal_def

/-- Marking the LTL definitions. -/
register_simp_attr tlsimp_def

/-- Marking the things to simplify when explicitly reasoning about `exec`. -/
register_simp_attr execsimp

/-- Marking the definitions unfolded by `tfinite_window`. -/
register_simp_attr tl_finite_window_def

/-- Marking the theorems that can be simplify reasoning at the LTL level. -/
register_simp_attr tlsimp

/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tldual

/-- Marking the theorems that are used for normalizing sequents. -/
register_simp_attr tlnormsimp

initialize registerTraceClass `lentil.debug
