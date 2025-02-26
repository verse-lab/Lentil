import Lean

open Lean

namespace LentilLib

def binderIdentToFunBinder (stx : TSyntax ``binderIdent) : MacroM (TSyntax ``Parser.Term.funBinder) :=
  match stx with
  | `(binderIdent| $x:ident) =>  `(Parser.Term.funBinder| $x:ident )
  | `(binderIdent| _ ) =>  `(Parser.Term.funBinder| _ )
  | _ => Macro.throwUnsupported

end LentilLib
