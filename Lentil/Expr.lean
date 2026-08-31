import Lean
import Lentil.Basic

namespace Lentil.Expr

open Lean Meta

partial def splitAndIntoParts (p : Expr) : MetaM (List Expr) := do
  match_expr p with
  | Lentil.tl_and _ a b =>
    let as ← splitAndIntoParts a
    let bs ← splitAndIntoParts b
    pure (as ++ bs)
  | _ => pure [p]

partial def splitImplicationsIntoParts (p : Expr) (cutAnd? : Bool := true) : MetaM (List Expr × Expr) := do
  match_expr p with
  | Lentil.tl_implies _ p q =>
    let ps ← if cutAnd? then splitAndIntoParts p else pure [p]
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure ([], p)

def splitPredImpliesIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | Lentil.pred_implies _ p q =>
    let ps ← splitAndIntoParts p
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | Lentil.valid _ body => splitImplicationsIntoParts body
  -- | Lentil.valid_initial _ body => splitImplicationsIntoParts body
  | _ => throwError "not a |-tl- statement"

/-- Given some LTL related expression and return the type of the state
    (i.e., the argument after `Lentil.pred`).
    While this could be done via `inferType`, just peeking the expression
    should be much "cheaper". -/
def peekStateType (p : Expr) : Option Expr :=
  match_expr p with
  | Lentil.pred_implies σ _ _ => .some σ
  | Lentil.valid σ _ => .some σ
  -- | Lentil.valid_initial σ _ => .some σ
  | _ => .none

end Lentil.Expr
