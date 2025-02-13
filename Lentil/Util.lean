import Lean

open Lean

def binderIdentToFunBinder (stx : TSyntax ``binderIdent) : MacroM (TSyntax ``Parser.Term.funBinder) :=
  match stx with
  | `(binderIdent| $x:ident) =>  `(Parser.Term.funBinder| $x:ident )
  | `(binderIdent| _ ) =>  `(Parser.Term.funBinder| _ )
  | _ => Macro.throwUnsupported

register_option lentil.pp.using_delab : Bool := {
  defValue := true
  descr := "Use Delab instead of Unexpander for delaboration. "
}

register_simp_attr tlasimp_def
register_simp_attr tlasimp
register_simp_attr tladual      -- experimental
