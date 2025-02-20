import Lean
import Lentil.Rules.Basic

/-! Gadgets for providing different variants of a proven theorem. -/

namespace TLA.Expr

open Lean Meta

-- need to take care of the implicit type argument below

partial def splitAndIntoParts (p : Expr) : MetaM (List Expr) := do
  match_expr p with
  | TLA.tla_and _ a b =>
    let as ← splitAndIntoParts a
    let bs ← splitAndIntoParts b
    pure (as ++ bs)
  | _ => pure [p]

partial def splitImplicationsIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.tla_implies _ p q =>
    let ps ← splitAndIntoParts p
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure ([], p)

def splitPredImpliesIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.pred_implies _ p q =>
    let ps ← splitAndIntoParts p
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | TLA.valid _ body => splitImplicationsIntoParts body
  | _ => throwError "not a |-tla- statement"

/-- Given some TLA related expression and return the type of the state
    (i.e., the argument after `TLA.pred`).
    While this could be done via `inferType`, just peeking the expression
    should be much "cheaper". -/
def peekStateType (p : Expr) : Option Expr :=
  match_expr p with
  | TLA.pred_implies σ _ _ => .some σ
  | TLA.valid σ _ => .some σ
  | _ => .none

end TLA.Expr

namespace TLA.Deriving

open Lean Meta Core Elab TLA.Expr

-- does not assume dependency from `ps` to `q`
def assembleUnderCommonContextShape (σ : Expr) (ps : List Expr) (q : Expr) : MetaM Expr := do
  withLocalDeclD `Γ (← mkAppM ``TLA.pred #[σ]) fun Γ => do
    let ps' ← ps.toArray.mapM fun p => mkAppM ``TLA.pred_implies #[Γ, p]
    let q' ← mkAppM ``TLA.pred_implies #[Γ, q]
    let body ← mkArrowN ps' q'
    mkForallFVars #[Γ] body

partial def assembleSeparatedPredImplications (ps : List Expr) (q : Expr) : MetaM Expr := do
  let build p := do
    let (ps, q) ← simplify [] p
    match List.getLast? ps with
    | none => mkAppM ``TLA.valid #[q]
    | some p =>
      let ps := List.dropLast ps
      let conj ← ps.foldrM (fun pp conj => mkAppM ``TLA.tla_and #[pp, conj]) p
      mkAppM ``TLA.pred_implies #[conj, q]
  let ps' ← ps.mapM build
  let q' ← build q
  let res ← mkArrowN ps'.toArray q'
  pure res
where simplify (ps : List Expr) (q : Expr) : MetaM (List Expr × Expr) := do
  -- currently only do very simple simplification:
  -- if `p` is empty while `q` is `always_implies` then turn it into `tla_implies`
  -- if `q` is `tla_implies` then split it into parts
  -- FIXME: might enhance this to allow definitionally equal pattern matching, like the one in `Qq`?
  match_expr q with
  | TLA.always_implies _ a b =>
    if ps.isEmpty then
      simplify [] (← mkAppM ``TLA.tla_implies #[a, b])
    else
      pure (ps, q)
  | TLA.tla_implies _ _ _ =>
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure (ps, q)

-- inspired by how `to_additive` is implemented in Mathlib
/-- For a TLA theorem whose conclusion is a single `TLA.pred_implies` or
    `TLA.valid`, this function automatically derives its several equivalent
    or weakened versions, which might be easier to use elsewhere.

    For example, consider the following statement:
    ```
    |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) ⇒ (p' ↝ q'))
    ```

    One useful, but weaker version is:
    ```
    (p') |-tla- (p) → (q) |-tla- (q') → (p ↝ q) |-tla- (p' ↝ q')
    ```
    which is derived by repeatly applying `impl_decouple`, `impl_intro` and `always_intro`.

    Another useful and equivalent version is:
    ```
    ∀ Γ, (Γ) |-tla- (p' ⇒ p) → (Γ) |-tla- (q ⇒ q') → (Γ) |-tla- ((p ↝ q) ⇒ (p' ↝ q'))
    ```
    which can be used in case we want to keep the context `Γ`.
-/
def deriveForPredImpliesOrValid (nm : Name) : CoreM Unit := do
  -- get the type of the statement directly from its `ConstInfo`
  let info ← getConstInfo nm
  let ty := info.type
  let lvlParams := info.levelParams
  let noncomputable? := isNoncomputable (← getEnv) nm
  MetaM.run' do
    let (thmName1, thmStmt1, thmName2, thmStmt2) ←
      forallTelescope ty fun xs body => do
        let (ps, q) ← splitPredImpliesIntoParts body
        let .some σ := peekStateType body | unreachable!
        -- here we list the theorem statements to be automatically derived
        let thmStmt1 ← assembleUnderCommonContextShape σ ps q
        let thmStmt1 ← mkForallFVars xs thmStmt1
        let thmName1 := nm ++ `with_context

        let thmStmt2 ← assembleSeparatedPredImplications ps q
        let thmStmt2 ← mkForallFVars xs thmStmt2
        let thmName2 := nm ++ `weakened
        pure (thmName1, thmStmt1, thmName2, thmStmt2)

    simpleProveTheorem thmName1 lvlParams thmStmt1
      -- HACK: sometimes `aesop` is powerful enough to solve the goal;
      -- in that case, the `have` may introduce something with unresolvable universe levels
      -- since the thing brought by `have` is not used in the proof term.
      -- to avoid this, we add a separate branch where there is no `have`.
      (← `(term| by solve
        | tla_nontemporal_simp ; aesop
        | have := @$(mkIdent nm) ; tla_nontemporal_simp ; aesop)) noncomputable?
    simpleProveTheorem thmName2 lvlParams thmStmt2
      (← do
        let htmp ← mkIdent <$> mkFreshUserName `htmp
        let htmp' ← mkIdent <$> mkFreshUserName `htmp'
        let introNames ← ty.getForallBinderNames.toArray.mapM (mkIdent <$> mkFreshUserName ·)
        `(term| by solve
        | tla_nontemporal_simp ; aesop
        | intro $introNames* ; have $htmp := @$(mkIdent nm) $introNames*
          (try rw [← impl_intro] at $htmp:ident)
          repeat (first
            | (solve
              | tla_nontemporal_simp ; aesop)
            | have $htmp' := @$htmp ; clear $htmp ; have $htmp := @TLA.impl_decouple _ _ _ $htmp' ; clear $htmp'
            | unfold TLA.always_implies at $htmp:ident
            | rw [← TLA.always_intro] at $htmp:ident
            | intro $htmp':ident ; specialize $htmp $htmp' ; clear $htmp'
            | rw [TLA.and_valid_split, and_imp] at $htmp:ident
          ))) noncomputable?

end TLA.Deriving

/--
For a TLA theorem with this attribute in the form of a single
`TLA.pred_implies` or `TLA.valid`, its different variants will be derived.
See the docstring of `TLA.Deriving.deriveForPredImpliesOrValid` for more details.
-/
syntax (name := tlaDerive) "tla_derive" : attr

open Lean TLA.Deriving in
initialize registerBuiltinAttribute {
  name := `tlaDerive
  descr := ""
  add := fun src _ _ => do _ ← deriveForPredImpliesOrValid src
  applicationTime := .afterTypeChecking
}
