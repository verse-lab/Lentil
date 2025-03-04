import Lean
import Batteries.Util.ExtendedBinder
import Lentil.Util

open Lean LentilLib

/-! ## A Shallow-Embedding of TLA -/

namespace TLA

/-! NOTE: There are multiple ways to formalize the concept of infinite sequences.
    Here, we follow the definition from `coq-tla`, while an alternative is to define
    infinite sequence as a coinductive datatype (like `Stream` in Rocq/Agda).

    Lean also comes with a definition of `Stream`, but it is a type class instead of
    a datatype, and the sequences generated from it are not necessarily infinite
    (in the sense that it may generate finite sequences). So here we do not use it.
-/

def exec (σ : Type u) := Nat → σ
def pred (σ : Type u) := exec σ → Prop
def state_pred {σ : Type u} (f : σ → Prop) : pred σ :=
  fun e => f (e 0)
def action (σ : Type u) := σ → σ → Prop
def action_pred {σ : Type u} (a : action σ) : pred σ :=
  fun e => a (e 0) (e 1)

def pure_pred {α : Type u} (p : Prop) : pred α := state_pred (fun _ => p)
def tla_true {α : Type u} : pred α := pure_pred True
def tla_false {α : Type u} : pred α := pure_pred False

def tla_and {α : Type u} (p q : pred α) : pred α := fun σ => p σ ∧ q σ
def tla_or {α : Type u} (p q : pred α) : pred α := fun σ => p σ ∨ q σ
def tla_implies {α : Type u} (p q : pred α) : pred α := fun σ => p σ → q σ
def tla_not {α : Type u} (p : pred α) : pred α := fun σ => ¬ p σ
def tla_forall {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∀ x, p x σ
def tla_exists {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∃ x, p x σ

-- NOTE: this all could be automatically lifted, but to avoid dependency circles, we don't do that
instance {α : Type u} : Std.Commutative (@tla_and α) := by
  constructor ; intros ; unfold tla_and ; funext e ; ac_rfl

instance {α : Type u} : Std.Associative (@tla_and α) := by
  constructor ; intros ; unfold tla_and ; funext e ; ac_rfl

instance {α : Type u} : Std.Commutative (@tla_or α) := by
  constructor ; intros ; unfold tla_or ; funext e ; ac_rfl

instance {α : Type u} : Std.Associative (@tla_or α) := by
  constructor ; intros ; unfold tla_or ; funext e ; ac_rfl

def exec.drop {α : Type u} (k : Nat) (σ : exec α) : exec α := λ n => σ (n + k)
def exec.take {α : Type u} (k : Nat) (σ : exec α) : List α := List.range k |>.map σ
def exec.take_from {α : Type u} (start k : Nat) (σ : exec α) : List α := List.range' start k |>.map σ

def always {α : Type u} (p : pred α) : pred α := λ σ => ∀ k, p <| σ.drop k
def eventually {α : Type u} (p : pred α) : pred α := λ σ => ∃ k, p <| σ.drop k
def later {α : Type u} (p : pred α) : pred α := λ σ => p <| σ.drop 1

theorem exec.drop_drop {α : Type u} (k l : Nat) (σ : exec α) : (σ.drop k).drop l = σ.drop (k + l) := by
  funext n ; simp [exec.drop] ; ac_rfl

def exec.satisfies {α : Type u} (p : pred α) (σ : exec α) : Prop := p σ
def valid {α : Type u} (p : pred α) : Prop := ∀ (σ : exec α), σ.satisfies p
def pred_implies {α : Type u} (p q : pred α) : Prop := ∀ (σ : exec α), σ.satisfies p → σ.satisfies q

@[refl] theorem pred_implies_refl {α : Type u} (p : pred α) : pred_implies p p := (fun _ => id)

theorem pred_implies_trans {p q r : pred α} : pred_implies p q → pred_implies q r → pred_implies p r := by
  intros h1 h2 e hp ; apply h2 ; apply h1 ; assumption

def enabled {α : Type u} (a : action α) (s : α) : Prop := ∃ s', a s s'
def tla_enabled {α : Type u} (a : action α) : pred α := state_pred (enabled a)

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

def tla_bigwedge {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tla_and tla_true f s

def tla_bigvee {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tla_or tla_false f s

def tla_until {α : Type u} (p q : pred α) : pred α := λ σ => ∃ i, (q <| σ.drop i) ∧ ∀ j < i, (p <| σ.drop j)

end TLA

/-! ## Syntax for TLA Notations

    Our notations for TLA formulas intersect with those for plain Lean terms,
    so to avoid potentially ambiguity(?), we define a new syntax category `tlafml`
    for TLA formulas and define macro rules for expanding formulas in `tlafml` into
    Lean terms.
-/

declare_syntax_cat tlafml
syntax (priority := low) term:max : tlafml
syntax "(" tlafml ")" : tlafml
syntax "⌜ " term " ⌝" : tlafml
syntax "⌞ " term " ⌟" : tlafml
syntax "⟨ " term " ⟩" : tlafml
syntax "⊤" : tlafml
syntax "⊥" : tlafml
syntax tlafml_heading_op := "¬" <|> "□" <|> "◇" <|> "◯"
syntax:max tlafml_heading_op tlafml:40 : tlafml
syntax:max "Enabled" term:40 : tlafml
-- HMM why `syntax:arg ... ...:max` does not work, when we need multiple layers like `□ ◇ p`?
syntax:15 tlafml:16 " → " tlafml:15 : tlafml
syntax:35 tlafml:36 " ∧ " tlafml:35 : tlafml
syntax:30 tlafml:31 " ∨ " tlafml:30 : tlafml
syntax:20 tlafml:21 " ↝ " tlafml:20 : tlafml
syntax:25 tlafml:26 " 𝑈 " tlafml:25 : tlafml
syntax:17 tlafml:18 " ⇒ " tlafml:17 : tlafml
syntax:arg "𝒲ℱ" term:max : tlafml

-- the way how binders are defined and how they are expanded is taken from `Mathlib.Order.SetNotation`
open Batteries.ExtendedBinder in
syntax "∀ " extBinder ", " tlafml:51 : tlafml
open Batteries.ExtendedBinder in
syntax "∃ " extBinder ", " tlafml:51 : tlafml

syntax tlafml_bigop := "⋀ " <|> "⋁ "
syntax tlafml_bigop binderIdent " ∈ " term ", " tlafml : tlafml

syntax "[tlafml|" tlafml "]" : term

macro_rules
  | `([tlafml| ( $f:tlafml ) ]) => `([tlafml| $f ])
  | `([tlafml| ⌜ $t:term ⌝ ]) => `(TLA.state_pred $t)
  | `([tlafml| ⌞ $t:term ⌟ ]) => `(TLA.pure_pred $t)
  | `([tlafml| ⟨ $t:term ⟩ ]) => `(TLA.action_pred $t)
  | `([tlafml| ⊤ ]) => `(TLA.tla_true)
  | `([tlafml| ⊥ ]) => `(TLA.tla_false)
  | `([tlafml| $op:tlafml_heading_op $f:tlafml ]) => do
    let opterm ← match op with
      | `(tlafml_heading_op|¬) => `(TLA.tla_not)
      | `(tlafml_heading_op|□) => `(TLA.always)
      | `(tlafml_heading_op|◇) => `(TLA.eventually)
      | `(tlafml_heading_op|◯) => `(TLA.later)
      | _ => Macro.throwUnsupported
    `($opterm [tlafml| $f ])
  | `([tlafml| Enabled $t:term ]) => `(TLA.tla_enabled $t)
  | `([tlafml| $f1:tlafml → $f2:tlafml ]) => `(TLA.tla_implies [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∧ $f2:tlafml ]) => `(TLA.tla_and [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∨ $f2:tlafml ]) => `(TLA.tla_or [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml 𝑈 $f2:tlafml ]) => `(TLA.tla_until [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| ∀ $x:ident, $f:tlafml]) => `(TLA.tla_forall fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∀ $x:ident : $t, $f:tlafml]) => `(TLA.tla_forall fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident, $f:tlafml]) => `(TLA.tla_exists fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident : $t, $f:tlafml]) => `(TLA.tla_exists fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| $op:tlafml_bigop $x:binderIdent ∈ $l:term, $f:tlafml]) =>
    -- HMM why the `⟨x.raw⟩` coercion does not work here, so that we have to define `binderIdentToFunBinder`?
    match op with
    | `(tlafml_bigop|⋀ ) => do `(TLA.tla_bigwedge (fun $(← binderIdentToFunBinder x) => [tlafml| $f ]) $l)
    | `(tlafml_bigop|⋁ ) => do `(TLA.tla_bigvee (fun $(← binderIdentToFunBinder x) => [tlafml| $f ]) $l)
    | _ => Macro.throwUnsupported
  | `([tlafml| $t:term ]) => `($t)

-- these definitions are not necessarily required, but for delaboration purposes
def TLA.leads_to {α : Type u} (p q : TLA.pred α) : TLA.pred α := [tlafml| □ (p → ◇ q) ]
def TLA.always_implies {α : Type u} (p q : TLA.pred α) : TLA.pred α := [tlafml| □ (p → q) ]
def TLA.weak_fairness {α : Type u} (a : action α) : pred α := [tlafml| □ ((□ (Enabled a)) → ◇ ⟨a⟩)]

macro_rules
  | `([tlafml| $f1:tlafml ↝ $f2:tlafml ]) => `(TLA.leads_to [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ⇒ $f2:tlafml ]) => `(TLA.always_implies [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| 𝒲ℱ $t:term ]) => `(TLA.weak_fairness $t)

/- NOTE: we can use something fancier like `ᴛʟᴀ`, but currently these characters cannot be
   easily typed in Lean VSCode extension, so anyway -/
syntax:max tlafml:max " |-tla- " tlafml:max : term
syntax:max "|-tla- " tlafml:max : term
syntax:max tlafml:max " =tla= " tlafml:max : term
syntax term " |=tla= " tlafml : term

macro_rules
  | `($f1:tlafml |-tla- $f2:tlafml) => `(TLA.pred_implies [tlafml| $f1 ] [tlafml| $f2 ])
  | `(|-tla- $f1:tlafml) => `(TLA.valid [tlafml| $f1 ])
  | `($f1:tlafml =tla= $f2:tlafml) => `([tlafml| $f1 ] = [tlafml| $f2 ])
  | `($e:term |=tla= $f:tlafml) => `(TLA.exec.satisfies [tlafml| $f ] $e)

/-! ## Pretty-Printing for TLA Notations -/

/-- Converting a syntax in `term` category into `tlafml`.
    This is useful in the cases where we want to eliminate the redundant `[tlafml| ... ]`
    wrapper of some sub-formula when it is inside a `tlafml`. -/
def TLA.syntax_term_to_tlafml [Monad m] [MonadQuotation m] (stx : TSyntax `term) : m (TSyntax `tlafml) := do
  match stx with
  | `([tlafml| $f:tlafml ]) => pure f
  | `(term|$t:term) => `(tlafml| $t:term )

/-- Converting a syntax in `term` category into `tlafml`,
    by inserting `[tlafml| ... ]` wrapper if needed.  -/
def TLA.syntax_tlafml_to_term [Monad m] [MonadQuotation m] (stx : TSyntax `tlafml) : m (TSyntax `term) := do
  match stx with
  | `(tlafml| $t:term ) => pure t
  | f => `(term|[tlafml| $f:tlafml ])

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

-- heavily inspired by https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
partial def delab_tlafml_inner : DelabM (TSyntax `tlafml) := do
  let e ← getExpr
  let stx ← do
    /- NOTE: we could get rid of the nesting of `withAppFn` and `withAppArg`
       by having something more general, but currently doing so does not
       give much benefit -/
    -- let argstxs ← withAppFnArgs (pure []) fun l => do
    --   let x ← delab_tlafml_inner
    --   pure <| x :: l
    let fn := e.getAppFn'.constName
    match fn with
    | ``TLA.tla_true => `(tlafml| ⊤ )
    | ``TLA.tla_false => `(tlafml| ⊥ )
    | ``TLA.state_pred | ``TLA.pure_pred | ``TLA.action_pred | ``TLA.tla_enabled | ``TLA.weak_fairness =>
      let t ← withAppArg delab
      match fn with
      | ``TLA.state_pred => `(tlafml| ⌜ $t:term ⌝ )
      | ``TLA.pure_pred => `(tlafml| ⌞ $t:term ⌟ )
      | ``TLA.action_pred => `(tlafml| ⟨ $t:term ⟩ )
      | ``TLA.tla_enabled => `(tlafml| Enabled $t:term )
      | ``TLA.weak_fairness => `(tlafml| 𝒲ℱ $t:term )
      | _ => unreachable!
    | ``TLA.tla_not | ``TLA.always | ``TLA.eventually | ``TLA.later =>
      let f ← withAppArg delab_tlafml_inner
      match fn with
      | ``TLA.tla_not => `(tlafml| ¬ $f:tlafml )
      | ``TLA.always => `(tlafml| □ $f:tlafml )
      | ``TLA.eventually => `(tlafml| ◇ $f:tlafml )
      | ``TLA.later => `(tlafml| ◯ $f:tlafml )
      | _ => unreachable!
    | ``TLA.tla_and | ``TLA.tla_or | ``TLA.tla_implies | ``TLA.leads_to | ``TLA.tla_until | ``TLA.always_implies =>
      let f1 ← withAppFn <| withAppArg delab_tlafml_inner
      let f2 ← withAppArg delab_tlafml_inner
      match fn with
      | ``TLA.tla_and => `(tlafml| $f1:tlafml ∧ $f2:tlafml)
      | ``TLA.tla_or => `(tlafml| $f1:tlafml ∨ $f2:tlafml)
      | ``TLA.tla_implies => `(tlafml| $f1:tlafml → $f2:tlafml)
      | ``TLA.leads_to => `(tlafml| $f1:tlafml ↝ $f2:tlafml)
      | ``TLA.tla_until => `(tlafml| $f1:tlafml 𝑈 $f2:tlafml)
      | ``TLA.always_implies => `(tlafml| $f1:tlafml ⇒ $f2:tlafml)
      | _ => unreachable!
    | ``TLA.tla_forall | ``TLA.tla_exists =>
      /- we are not sure about whether the argument is a `fun _ => _` or something else,
         so here we first `delab` the argument and then look into it;
         this seems to work, as `delab` would also call `delab_tlafml_inner` on the argument,
         so that we can match the inner syntax of `f` and use `TLA.syntax_term_to_tlafml`? -/
      let body ← withAppArg delab
      let (a, stx) ← get_bindername_funbody body
      match fn with
      | ``TLA.tla_forall => do `(tlafml| ∀ $a:ident, $stx )
      | ``TLA.tla_exists => do `(tlafml| ∃ $a:ident, $stx )
      | _ => unreachable!
    | ``TLA.tla_bigwedge | ``TLA.tla_bigvee =>
      let body ← withAppFn <| withAppArg delab
      let l ← withAppArg delab
      let (a, stx) ← get_bindername_funbody body
      match fn with
      | ``TLA.tla_bigwedge => do `(tlafml| ⋀ $a:ident ∈ $l, $stx )
      | ``TLA.tla_bigvee => do `(tlafml| ⋁ $a:ident ∈ $l, $stx )
      | _ => unreachable!
    | _ =>
      -- in this case, `e` may not even be an `.app`, so directly delab it
      `(tlafml| $(← delab):term )
  annAsTerm stx
where get_bindername_funbody (body : Term) : DelabM (Ident × TSyntax `tlafml) := do
  match body with
  | `(fun $a:ident => $stx) | `(fun ($a:ident : $_) => $stx) => pure (a, (← TLA.syntax_term_to_tlafml stx))
  | _ =>
    -- we cannot go back to call `delab` on the whole term since that would result in dead recursion!
    -- FIXME: it seems that the terminfo on `x` and `bodyapp` can get wrong here
    let x := mkIdent <| .mkSimple "x"
    let bodyapp ← `(term| $body $x )
    pure (x, (← `(tlafml| $bodyapp:term )))

open PrettyPrinter.Delaborator SubExpr in
partial def delab_tlafml : Delab := whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  let fn := e.getAppFn.constName
  -- need to consider implicit arguments below in comparing `e.getAppNumArgs'`
  let check_applicable (offset : Nat) :=
    (List.elem fn [``TLA.state_pred, ``TLA.pure_pred, ``TLA.action_pred, ``TLA.tla_enabled, ``TLA.weak_fairness,
        ``TLA.tla_not, ``TLA.always, ``TLA.eventually, ``TLA.later]
      && e.getAppNumArgs' == 2 + offset) ||
    (List.elem fn [``TLA.tla_and, ``TLA.tla_or, ``TLA.tla_implies, ``TLA.leads_to, ``TLA.tla_until, ``TLA.always_implies,
        ``TLA.tla_forall, ``TLA.tla_exists]
      && e.getAppNumArgs' == 3 + offset) ||
    (List.elem fn [``TLA.tla_true, ``TLA.tla_false]
      && e.getAppNumArgs' == 1 + offset) ||
    (List.elem fn [``TLA.tla_bigwedge, ``TLA.tla_bigvee]
      && e.getAppNumArgs' == 6 + offset)
  if check_applicable 0
  then delab_tlafml_inner >>= TLA.syntax_tlafml_to_term
  else whenPPOption (fun o => o.get lentil.pp.autoRenderSatisfies.name true) do
    if check_applicable 1
    then
      let res ← withAppFn delab_tlafml_inner
      let e ← withAppArg delab
      `(term| $e |=tla= $res)
    else failure

attribute [delab app.TLA.state_pred, delab app.TLA.pure_pred, delab app.TLA.action_pred, delab app.TLA.tla_enabled, delab app.TLA.weak_fairness] delab_tlafml
attribute [delab app.TLA.tla_not, delab app.TLA.always, delab app.TLA.eventually, delab app.TLA.later] delab_tlafml
attribute [delab app.TLA.tla_and, delab app.TLA.tla_or, delab app.TLA.tla_implies, delab app.TLA.leads_to, delab app.TLA.tla_until, delab app.TLA.always_implies] delab_tlafml
attribute [delab app.TLA.tla_true, delab app.TLA.tla_false] delab_tlafml
attribute [delab app.TLA.tla_forall, delab app.TLA.tla_exists] delab_tlafml
attribute [delab app.TLA.tla_bigwedge, delab app.TLA.tla_bigvee] delab_tlafml

@[app_unexpander TLA.pred_implies] def TLA.unexpand_pred_implies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `(($(← TLA.syntax_term_to_tlafml stx1)) |-tla- ($(← TLA.syntax_term_to_tlafml stx2)))
  | _ => throw ()

@[app_unexpander TLA.valid] def TLA.unexpand_valid : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `(|-tla- ($(← TLA.syntax_term_to_tlafml stx)))
  | _ => throw ()

@[app_unexpander TLA.exec.satisfies] def TLA.unexpand_satisfies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `($stx2 |=tla= $(← TLA.syntax_term_to_tlafml stx1))
  | _ => throw ()

@[app_unexpander Eq] def TLA.unexpand_tla_eq : Lean.PrettyPrinter.Unexpander
  | `($_ [tlafml| $f1:tlafml ] [tlafml| $f2:tlafml ]) => `(($f1) =tla= ($f2))
  | `($_ [tlafml| $f1:tlafml ] $t2:term) => do `(($f1) =tla= ($(← `(tlafml| $t2:term ))))
  | `($_ $t1:term [tlafml| $f2:tlafml ]) => do `(($(← `(tlafml| $t1:term ))) =tla= ($f2))
  | _ => throw ()       -- NOTE: we don't want all equalities to be rendered into equalities between TLA formulas!

/-- info: Nat.zero.succ = Nat.zero : Prop -/
#guard_msgs in
#check (Nat.succ Nat.zero = Nat.zero)

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Syntax.lean
open PrettyPrinter Parenthesizer in
@[category_parenthesizer tlafml]
def tlafml.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tlafml true wrapParens prec $
    parenthesizeCategoryCore `tlafml prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
