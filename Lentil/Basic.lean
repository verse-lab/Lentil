module

public import Lean
public import Batteries.Util.ExtendedBinder
public import Lentil.Util

open Lean LentilLib

@[expose] public section

/-! ## A Shallow-Embedding of Linear Temporal Logic -/

namespace Lentil

/-! NOTE: There are multiple ways to formalize the concept of infinite sequences.
    Here, we follow the definition from `coq-tla`, while an alternative is to define
    infinite sequence as a coinductive datatype (like `Stream` in Rocq/Agda).

    Lean also comes with a definition of `Stream`, but it is a type class instead of
    a datatype, and the sequences generated from it are not necessarily infinite
    (in the sense that it may generate finite sequences). So here we do not use it.
-/

def exec (σ : Type u) := Nat → σ
def pred (σ : Type u) := exec σ → Nat → Prop
def state_pred {σ : Type u} (f : σ → Prop) : pred σ :=
  fun e i => f (e i)
def action (σ : Type u) := σ → σ → Prop
def action_pred {σ : Type u} (a : action σ) : pred σ :=
  fun e i => a (e i) (e (i + 1))

def pure_pred {α : Type u} (p : Prop) : pred α := state_pred (fun _ => p)
def tl_true {α : Type u} : pred α := pure_pred True
def tl_false {α : Type u} : pred α := pure_pred False

def tl_and {α : Type u} (p q : pred α) : pred α := fun e i => p e i ∧ q e i
def tl_or {α : Type u} (p q : pred α) : pred α := fun e i => p e i ∨ q e i
def tl_implies {α : Type u} (p q : pred α) : pred α := fun e i => p e i → q e i
def tl_not {α : Type u} (p : pred α) : pred α := fun e i => ¬ p e i
def tl_forall {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun e i => ∀ x, p x e i
def tl_exists {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun e i => ∃ x, p x e i

-- NOTE: this all could be automatically lifted, but to avoid dependency circles, we don't do that
instance {α : Type u} : Std.Commutative (@tl_and α) := by
  constructor ; intros ; unfold tl_and ; funext e i ; ac_rfl

instance {α : Type u} : Std.Associative (@tl_and α) := by
  constructor ; intros ; unfold tl_and ; funext e i ; ac_rfl

instance {α : Type u} : Std.Commutative (@tl_or α) := by
  constructor ; intros ; unfold tl_or ; funext e i ; ac_rfl

instance {α : Type u} : Std.Associative (@tl_or α) := by
  constructor ; intros ; unfold tl_or ; funext e i ; ac_rfl

def exec.drop {α : Type u} (k : Nat) (σ : exec α) : exec α := λ n => σ (n + k)
def exec.take {α : Type u} (k : Nat) (σ : exec α) : List α := List.range k |>.map σ
def exec.take_from {α : Type u} (start k : Nat) (σ : exec α) : List α := List.range' start k |>.map σ

def always {α : Type u} (p : pred α) : pred α := fun e i => ∀ k, p e (i + k)
def eventually {α : Type u} (p : pred α) : pred α := fun e i => ∃ k, p e (i + k)
def later {α : Type u} (p : pred α) : pred α := fun e i => p e (i + 1)

theorem exec.take_length {α : Type u} (k : Nat) (σ : exec α) : (σ.take k).length = k := by
  simp [exec.take]

theorem exec.drop_drop {α : Type u} (k l : Nat) (σ : exec α) : (σ.drop k).drop l = σ.drop (k + l) := by
  funext n ; simp [exec.drop] ; ac_rfl

def exec.satisfies {α : Type u} (p : pred α) (σ : exec α) (i : Nat) : Prop := p σ i
def pred_implies {α : Type u} (p q : pred α) : Prop := ∀ (σ : exec α) i, p σ i → q σ i
def pred_implies_initial {α : Type u} (p q : pred α) : Prop := ∀ (σ : exec α), p σ 0 → q σ 0
def valid_initial {α : Type u} (p : pred α) : Prop := ∀ (σ : exec α), p σ 0
def valid {α : Type u} (p : pred α) : Prop := ∀ (σ : exec α) i, p σ i
def equiv_init {α : Type u} (p q : pred α) : Prop := ∀ (σ : exec α), p σ 0 ↔ q σ 0

@[refl] theorem pred_implies_refl {α : Type u} (p : pred α) : pred_implies p p := fun _ _ => id

theorem pred_implies_trans {p q r : pred α} : pred_implies p q → pred_implies q r → pred_implies p r := by
  intros h1 h2 e i hp ; exact h2 e i (h1 e i hp)

def enabled {α : Type u} (a : action α) (s : α) : Prop := ∃ s', a s s'
def tl_enabled {α : Type u} (a : action α) : pred α := state_pred (enabled a)

-- HMM this is kind of awkward: we need `Std.Commutative` and `Std.Associative` to be able
-- to work on finset.
-- FIXME: how about removing this, and instead using `∀ ..., ... ∈ ... → ...`? do we really need this generic `fold`?
/-- A customized typeclass to express structures that can be folded upon. -/
class Foldable (c : Type u → Type v) where
  fold {α : Type u} {β : Type w} (op : β → β → β) [Std.Commutative op] [Std.Associative op]
    (b : β) (f : α → β) (s : c α) : β

instance : Foldable List where
  fold op _ _ b f s := List.foldr (op <| f ·) b s

theorem Foldable.list_index_form_change {α : Type u} {β : Type w} (op : β → β → β) [inst1 : Std.Commutative op] [inst2 : Std.Associative op]
    (b : β) (f : α → β) (l : List α) :
  Foldable.fold op b f l = Foldable.fold op b (f <| l[·]) (List.finRange l.length) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [Foldable.fold, List.finRange_succ] at *
    rw [ih] ; apply congrArg
    rw [List.foldr_map] ; simp

def tl_bigwedge {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tl_and tl_true f s

def tl_bigvee {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tl_or tl_false f s

def tl_until {α : Type u} (p q : pred α) : pred α :=
  fun e i => ∃ k, q e (i + k) ∧ ∀ l, l < k → p e (i + l)

end Lentil

/-! ## Syntax for LTL Notations

    Our notations for LTL formulas intersect with those for plain Lean terms,
    so to avoid potentially ambiguity(?), we define a new syntax category `tlfml`
    for LTL formulas and define macro rules for expanding formulas in `tlfml` into
    Lean terms.
-/

declare_syntax_cat tlfml
syntax (priority := low) term:lead : tlfml
syntax "(" tlfml ")" : tlfml
syntax "⌜ " term " ⌝" : tlfml
syntax "⌞ " term " ⌟" : tlfml
syntax "⟨ " term " ⟩" : tlfml
syntax "⊤" : tlfml
syntax "⊥" : tlfml
syntax tlfml_heading_op := "¬" <|> "□" <|> "◇" <|> "◯"
syntax:max tlfml_heading_op tlfml:40 : tlfml
syntax:max "Enabled" term:lead : tlfml
-- HMM why `syntax:arg ... ...:max` does not work, when we need multiple layers like `□ ◇ p`?
syntax:25 tlfml:26 " → " tlfml:25 : tlfml
syntax:35 tlfml:36 " ∧ " tlfml:35 : tlfml
syntax:30 tlfml:31 " ∨ " tlfml:30 : tlfml
syntax:29 tlfml:30 " ↝ " tlfml:29 : tlfml
syntax:37 tlfml:38 " 𝑈 " tlfml:37 : tlfml
syntax:27 tlfml:28 " ⇒ " tlfml:27 : tlfml
syntax:arg "𝒲ℱ" term:lead : tlfml

-- the way how binders are defined and how they are expanded is taken from `Mathlib.Order.SetNotation`
open Batteries.ExtendedBinder in
syntax "∀ " extBinder ", " tlfml : tlfml
open Batteries.ExtendedBinder in
syntax "∃ " extBinder ", " tlfml : tlfml

syntax tlfml_bigop := "⋀ " <|> "⋁ "
syntax tlfml_bigop binderIdent " ∈ " term ", " tlfml : tlfml

syntax "[tlfml|" tlfml "]" : term

macro_rules
  | `([tlfml| ( $f:tlfml ) ]) => `([tlfml| $f ])
  | `([tlfml| ⌜ $t:term ⌝ ]) => `(Lentil.state_pred $t)
  | `([tlfml| ⌞ $t:term ⌟ ]) => `(Lentil.pure_pred $t)
  | `([tlfml| ⟨ $t:term ⟩ ]) => `(Lentil.action_pred $t)
  | `([tlfml| ⊤ ]) => `(Lentil.tl_true)
  | `([tlfml| ⊥ ]) => `(Lentil.tl_false)
  | `([tlfml| $op:tlfml_heading_op $f:tlfml ]) => do
    let opterm ← match op with
      | `(tlfml_heading_op|¬) => `(Lentil.tl_not)
      | `(tlfml_heading_op|□) => `(Lentil.always)
      | `(tlfml_heading_op|◇) => `(Lentil.eventually)
      | `(tlfml_heading_op|◯) => `(Lentil.later)
      | _ => Macro.throwUnsupported
    `($opterm [tlfml| $f ])
  | `([tlfml| Enabled $t:term ]) => `(Lentil.tl_enabled $t)
  | `([tlfml| $f1:tlfml → $f2:tlfml ]) => `(Lentil.tl_implies [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| $f1:tlfml ∧ $f2:tlfml ]) => `(Lentil.tl_and [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| $f1:tlfml ∨ $f2:tlfml ]) => `(Lentil.tl_or [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| $f1:tlfml 𝑈 $f2:tlfml ]) => `(Lentil.tl_until [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| ∀ $x:ident, $f:tlfml]) => `(Lentil.tl_forall fun $x:ident => [tlfml| $f ])
  | `([tlfml| ∀ $x:ident : $t, $f:tlfml]) => `(Lentil.tl_forall fun $x:ident : $t => [tlfml| $f ])
  | `([tlfml| ∃ $x:ident, $f:tlfml]) => `(Lentil.tl_exists fun $x:ident => [tlfml| $f ])
  | `([tlfml| ∃ $x:ident : $t, $f:tlfml]) => `(Lentil.tl_exists fun $x:ident : $t => [tlfml| $f ])
  | `([tlfml| $op:tlfml_bigop $x:binderIdent ∈ $l:term, $f:tlfml]) =>
    -- HMM why the `⟨x.raw⟩` coercion does not work here, so that we have to define `binderIdentToFunBinder`?
    match op with
    | `(tlfml_bigop|⋀ ) => do `(Lentil.tl_bigwedge (fun $(← binderIdentToFunBinder x) => [tlfml| $f ]) $l)
    | `(tlfml_bigop|⋁ ) => do `(Lentil.tl_bigvee (fun $(← binderIdentToFunBinder x) => [tlfml| $f ]) $l)
    | _ => Macro.throwUnsupported
  | `([tlfml| $t:term ]) => `($t)

-- these definitions are not necessarily required, but for delaboration purposes
def Lentil.leads_to {α : Type u} (p q : Lentil.pred α) : Lentil.pred α := [tlfml| □ (p → ◇ q) ]
def Lentil.always_implies {α : Type u} (p q : Lentil.pred α) : Lentil.pred α := [tlfml| □ (p → q) ]
def Lentil.weak_fairness {α : Type u} (a : action α) : pred α := [tlfml| □ ((□ (Enabled a)) → ◇ ⟨a⟩)]

macro_rules
  | `([tlfml| $f1:tlfml ↝ $f2:tlfml ]) => `(Lentil.leads_to [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| $f1:tlfml ⇒ $f2:tlfml ]) => `(Lentil.always_implies [tlfml| $f1 ] [tlfml| $f2 ])
  | `([tlfml| 𝒲ℱ $t:term ]) => `(Lentil.weak_fairness $t)

/- NOTE: we can use something fancier like `ᴛʟᴀ`, but currently these characters cannot be
   easily typed in Lean VSCode extension, so anyway -/
syntax:max tlfml:max " |-tl- " tlfml:max : term
syntax:55 "|-tl- " tlfml:55 : term
syntax:max tlfml:max " |-tl[0]- " tlfml:max : term
syntax:55 "|-tl[0]- " tlfml:55 : term
syntax:max tlfml:max " =tl= " tlfml:max : term
syntax term " |=tl[" term "]=" tlfml : term
syntax term " |=tl= " tlfml : term

macro_rules
  | `($f1:tlfml |-tl- $f2:tlfml) => `(Lentil.pred_implies [tlfml| $f1 ] [tlfml| $f2 ])
  | `(|-tl- $f1:tlfml) => `(Lentil.valid [tlfml| $f1 ])
  | `($f1:tlfml |-tl[0]- $f2:tlfml) => `(Lentil.pred_implies_initial [tlfml| $f1 ] [tlfml| $f2 ])
  | `(|-tl[0]- $f1:tlfml) => `(Lentil.valid_initial [tlfml| $f1 ])
  | `($f1:tlfml =tl= $f2:tlfml) => `([tlfml| $f1 ] = [tlfml| $f2 ])
  | `($e:term |=tl[$i:term]= $f:tlfml) => `(Lentil.exec.satisfies [tlfml| $f ] $e $i)
  | `($e:term |=tl= $f:tlfml) => `(Lentil.exec.satisfies [tlfml| $f ] $e 0)

end

/-! ## Pretty-Printing for LTL Notations

    Everything below runs at elaboration time only, so it lives in the `meta`
    phase of this module. -/

public meta section

/-- Converting a syntax in `term` category into `tlfml`.
    This is useful in the cases where we want to eliminate the redundant `[tlfml| ... ]`
    wrapper of some sub-formula when it is inside a `tlfml`. -/
def Lentil.syntax_term_to_tlfml [Monad m] [MonadQuotation m] (stx : TSyntax `term) : m (TSyntax `tlfml) := do
  match stx with
  | `([tlfml| $f:tlfml ]) => pure f
  | `(term|$t:term) => `(tlfml| $t:term )

/-- Converting a syntax in `term` category into `tlfml`,
    by inserting `[tlfml| ... ]` wrapper if needed.  -/
def Lentil.syntax_tlfml_to_term [Monad m] [MonadQuotation m] (stx : TSyntax `tlfml) : m (TSyntax `term) := do
  match stx with
  | `(tlfml| $t:term ) => pure t
  | f => `(term|[tlfml| $f:tlfml ])

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open PrettyPrinter.Delaborator SubExpr in
def Lentil.delab_binder_body_as_tlfml (body : Term) : DelabM (Ident × TSyntax `tlfml) := do
  match body with
  | `(fun $a:ident => $stx) | `(fun ($a:ident : $_) => $stx) =>
      pure (a, (← Lentil.syntax_term_to_tlfml stx))
  | _ =>
    -- we cannot go back to call `delab` on the whole term since that would result in dead recursion!
    -- FIXME: it seems that the terminfo on `x` and `bodyapp` can get wrong here
    let x := mkIdent <| .mkSimple "x"
    let bodyapp ← `(term| $body $x )
    pure (x, (← `(tlfml| $bodyapp:term )))

open PrettyPrinter.Delaborator SubExpr in
def Lentil.delab_tlfml_app
    (check_applicable : Expr → Nat → Bool)
    (inner : DelabM (TSyntax `tlfml)) : Delab :=
  whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
    let e ← getExpr
    if check_applicable e 0
    then inner >>= Lentil.syntax_tlfml_to_term
    else whenPPOption (fun o => o.get lentil.pp.autoRenderSatisfies.name true) do
      if check_applicable e 1
      then
        let res ← withAppFn inner
        let e ← withAppArg delab
        `(term| $e |=tl= $res)
      else failure

-- heavily inspired by https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
partial def delab_tlfml_inner : DelabM (TSyntax `tlfml) := do
  let e ← getExpr
  let stx ← do
    /- NOTE: we could get rid of the nesting of `withAppFn` and `withAppArg`
       by having something more general, but currently doing so does not
       give much benefit -/
    -- let argstxs ← withAppFnArgs (pure []) fun l => do
    --   let x ← delab_tlfml_inner
    --   pure <| x :: l
    let fn := e.getAppFn'.constName
    match fn with
    | ``Lentil.tl_true => `(tlfml| ⊤ )
    | ``Lentil.tl_false => `(tlfml| ⊥ )
    | ``Lentil.state_pred | ``Lentil.pure_pred | ``Lentil.action_pred | ``Lentil.tl_enabled | ``Lentil.weak_fairness =>
      let t ← withAppArg delab
      match fn with
      | ``Lentil.state_pred => `(tlfml| ⌜ $t:term ⌝ )
      | ``Lentil.pure_pred => `(tlfml| ⌞ $t:term ⌟ )
      | ``Lentil.action_pred => `(tlfml| ⟨ $t:term ⟩ )
      | ``Lentil.tl_enabled => `(tlfml| Enabled $t:term )
      | ``Lentil.weak_fairness => `(tlfml| 𝒲ℱ $t:term )
      | _ => unreachable!
    | ``Lentil.tl_not | ``Lentil.always | ``Lentil.eventually | ``Lentil.later =>
      let f ← withAppArg delab_tlfml_inner
      match fn with
      | ``Lentil.tl_not => `(tlfml| ¬ $f:tlfml )
      | ``Lentil.always => `(tlfml| □ $f:tlfml )
      | ``Lentil.eventually => `(tlfml| ◇ $f:tlfml )
      | ``Lentil.later => `(tlfml| ◯ $f:tlfml )
      | _ => unreachable!
    | ``Lentil.tl_and | ``Lentil.tl_or | ``Lentil.tl_implies | ``Lentil.leads_to | ``Lentil.tl_until | ``Lentil.always_implies =>
      let f1 ← withAppFn <| withAppArg delab_tlfml_inner
      let f2 ← withAppArg delab_tlfml_inner
      match fn with
      | ``Lentil.tl_and => `(tlfml| $f1:tlfml ∧ $f2:tlfml)
      | ``Lentil.tl_or => `(tlfml| $f1:tlfml ∨ $f2:tlfml)
      | ``Lentil.tl_implies => `(tlfml| $f1:tlfml → $f2:tlfml)
      | ``Lentil.leads_to => `(tlfml| $f1:tlfml ↝ $f2:tlfml)
      | ``Lentil.tl_until => `(tlfml| $f1:tlfml 𝑈 $f2:tlfml)
      | ``Lentil.always_implies => `(tlfml| $f1:tlfml ⇒ $f2:tlfml)
      | _ => unreachable!
    | ``Lentil.tl_forall | ``Lentil.tl_exists =>
      /- we are not sure about whether the argument is a `fun _ => _` or something else,
         so here we first `delab` the argument and then look into it;
         this seems to work, as `delab` would also call `delab_tlfml_inner` on the argument,
         so that we can match the inner syntax of `f` and use `Lentil.syntax_term_to_tlfml`? -/
      let body ← withAppArg delab
      let (a, stx) ← Lentil.delab_binder_body_as_tlfml body
      match fn with
      | ``Lentil.tl_forall => do `(tlfml| ∀ $a:ident, $stx )
      | ``Lentil.tl_exists => do `(tlfml| ∃ $a:ident, $stx )
      | _ => unreachable!
    | ``Lentil.tl_bigwedge | ``Lentil.tl_bigvee =>
      let body ← withAppFn <| withAppArg delab
      let l ← withAppArg delab
      let (a, stx) ← Lentil.delab_binder_body_as_tlfml body
      match fn with
      | ``Lentil.tl_bigwedge => do `(tlfml| ⋀ $a:ident ∈ $l, $stx )
      | ``Lentil.tl_bigvee => do `(tlfml| ⋁ $a:ident ∈ $l, $stx )
      | _ => unreachable!
    | _ =>
      -- in this case, `e` may not even be an `.app`, so directly delab it
      -- with `Lentil.syntax_term_to_tlfml` might look nicer
      Lentil.syntax_term_to_tlfml (← delab)
  annAsTerm stx

open PrettyPrinter.Delaborator SubExpr in
partial def delab_tlfml : Delab := Lentil.delab_tlfml_app (fun e offset =>
  -- need to consider implicit arguments below in comparing `e.getAppNumArgs'`
  let fn := e.getAppFn.constName;
    (List.elem fn [``Lentil.state_pred, ``Lentil.pure_pred, ``Lentil.action_pred, ``Lentil.tl_enabled, ``Lentil.weak_fairness,
        ``Lentil.tl_not, ``Lentil.always, ``Lentil.eventually, ``Lentil.later]
      && e.getAppNumArgs' == 2 + offset) ||
    (List.elem fn [``Lentil.tl_and, ``Lentil.tl_or, ``Lentil.tl_implies, ``Lentil.leads_to, ``Lentil.tl_until, ``Lentil.always_implies,
        ``Lentil.tl_forall, ``Lentil.tl_exists]
      && e.getAppNumArgs' == 3 + offset) ||
    (List.elem fn [``Lentil.tl_true, ``Lentil.tl_false]
      && e.getAppNumArgs' == 1 + offset) ||
    (List.elem fn [``Lentil.tl_bigwedge, ``Lentil.tl_bigvee]
      && e.getAppNumArgs' == 6 + offset)
  ) delab_tlfml_inner

attribute [delab app.Lentil.state_pred, delab app.Lentil.pure_pred, delab app.Lentil.action_pred, delab app.Lentil.tl_enabled, delab app.Lentil.weak_fairness] delab_tlfml
attribute [delab app.Lentil.tl_not, delab app.Lentil.always, delab app.Lentil.eventually, delab app.Lentil.later] delab_tlfml
attribute [delab app.Lentil.tl_and, delab app.Lentil.tl_or, delab app.Lentil.tl_implies, delab app.Lentil.leads_to, delab app.Lentil.tl_until, delab app.Lentil.always_implies] delab_tlfml
attribute [delab app.Lentil.tl_true, delab app.Lentil.tl_false] delab_tlfml
attribute [delab app.Lentil.tl_forall, delab app.Lentil.tl_exists] delab_tlfml
attribute [delab app.Lentil.tl_bigwedge, delab app.Lentil.tl_bigvee] delab_tlfml

@[app_unexpander Lentil.pred_implies] def Lentil.unexpand_pred_implies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `(($(← Lentil.syntax_term_to_tlfml stx1)) |-tl- ($(← Lentil.syntax_term_to_tlfml stx2)))
  | _ => throw ()

@[app_unexpander Lentil.pred_implies_initial] def Lentil.unexpand_pred_implies_initial : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `(($(← Lentil.syntax_term_to_tlfml stx1)) |-tl[0]- ($(← Lentil.syntax_term_to_tlfml stx2)))
  | _ => throw ()

@[app_unexpander Lentil.valid] def Lentil.unexpand_valid : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `(|-tl- ($(← Lentil.syntax_term_to_tlfml stx)))
  | _ => throw ()

@[app_unexpander Lentil.valid_initial] def Lentil.unexpand_valid_initial : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `(|-tl[0]- ($(← Lentil.syntax_term_to_tlfml stx)))
  | _ => throw ()

@[app_unexpander Lentil.exec.satisfies] def Lentil.unexpand_satisfies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2 0) => do `($stx2 |=tl= $(← Lentil.syntax_term_to_tlfml stx1))
  | `($_ $stx1 $stx2 $i) => do `($stx2 |=tl[$i]= $(← Lentil.syntax_term_to_tlfml stx1))
  | _ => throw ()

@[app_unexpander Eq] def Lentil.unexpand_tl_eq : Lean.PrettyPrinter.Unexpander
  | `($_ [tlfml| $f1:tlfml ] [tlfml| $f2:tlfml ]) => `(($f1) =tl= ($f2))
  | `($_ [tlfml| $f1:tlfml ] $t2:term) => do `(($f1) =tl= ($(← `(tlfml| $t2:term ))))
  | `($_ $t1:term [tlfml| $f2:tlfml ]) => do `(($(← `(tlfml| $t1:term ))) =tl= ($f2))
  | _ => throw ()       -- NOTE: we don't want all equalities to be rendered into equalities between LTL formulas!

/-- info: Nat.zero.succ = Nat.zero : Prop -/
#guard_msgs in
#check (Nat.succ Nat.zero = Nat.zero)

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Syntax.lean
open PrettyPrinter Parenthesizer in
@[category_parenthesizer tlfml]
def tlfml.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tlfml true wrapParens prec $
    parenthesizeCategoryCore `tlfml prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
