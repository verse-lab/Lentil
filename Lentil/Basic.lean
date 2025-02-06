import Lean
import Batteries.Util.ExtendedBinder

open Lean

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
def tla_forall {α : Type u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∀ x, p x σ
def tla_exists {α : Type u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∃ x, p x σ

-- HMM how to automatically derive all these kinds?
instance {α : Type u} : Std.Commutative (@tla_and α) := by
  constructor ; intros ; unfold tla_and ; funext e ; ac_rfl

instance {α : Type u} : Std.Associative (@tla_and α) := by
  constructor ; intros ; unfold tla_and ; funext e ; ac_rfl

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

theorem pred_implies_trans {p q r : pred α} : pred_implies p q → pred_implies q r → pred_implies p r := by
  intros h1 h2 e hp ; apply h2 ; apply h1 ; assumption

def enabled {α : Type u} (a : action α) (s : α) : Prop := ∃ s', a s s'
def tla_enabled {α : Type u} (a : action α) : pred α := state_pred (enabled a)

end TLA

/-! ## Syntax and Pretty-Printing for TLA Notations -/

declare_syntax_cat tlafml
syntax (priority := low) term:max : tlafml
syntax "(" tlafml ")" : tlafml
syntax "⌜ " term " ⌝" : tlafml
syntax "⌞ " term " ⌟" : tlafml
syntax "⟨ " term " ⟩" : tlafml
syntax "⊤" : tlafml
syntax "⊥" : tlafml
syntax:max "¬" tlafml:40 : tlafml
syntax:max "Enabled" term:40 : tlafml
syntax:max "□" tlafml:40 : tlafml
syntax:max "◇" tlafml:40 : tlafml
syntax:max "◯" tlafml:40 : tlafml
-- HMM why `syntax:arg ... ...:max` does not work, when we need multiple layers like `□ ◇ p`?
syntax:15 tlafml:16 " → " tlafml:15 : tlafml
syntax:35 tlafml:36 " ∧ " tlafml:35 : tlafml
syntax:30 tlafml:31 " ∨ " tlafml:30 : tlafml
syntax:20 tlafml:21 " ↝ " tlafml:20 : tlafml
syntax:arg "𝒲ℱ" term:max : tlafml

-- the way how binders are defined and how they are expanded is taken from `Mathlib.Order.SetNotation`
open Batteries.ExtendedBinder in
syntax "∀ " extBinder ", " tlafml:51 : tlafml
open Batteries.ExtendedBinder in
syntax "∃ " extBinder ", " tlafml:51 : tlafml

syntax "⋀ " binderIdent " ∈ " term ", " tlafml : tlafml

syntax "[tlafml|" tlafml "]" : term

macro_rules
  | `([tlafml| ( $f:tlafml ) ]) => `([tlafml| $f ])
  | `([tlafml| ⌜ $t:term ⌝ ]) => `(TLA.state_pred $t)
  | `([tlafml| ⌞ $t:term ⌟ ]) => `(TLA.pure_pred $t)
  | `([tlafml| ⟨ $t:term ⟩ ]) => `(TLA.action_pred $t)
  | `([tlafml| ⊤ ]) => `(TLA.tla_true)
  | `([tlafml| ⊥ ]) => `(TLA.tla_false)
  | `([tlafml| ¬ $f:tlafml ]) => `(TLA.tla_not [tlafml| $f ])
  | `([tlafml| Enabled $t:term ]) => `(TLA.tla_enabled $t)
  | `([tlafml| □ $f:tlafml ]) => `(TLA.always [tlafml| $f ])
  | `([tlafml| ◇ $f:tlafml ]) => `(TLA.eventually [tlafml| $f ])
  | `([tlafml| ◯ $f:tlafml ]) => `(TLA.later [tlafml| $f ])
  | `([tlafml| $f1:tlafml → $f2:tlafml ]) => `(TLA.tla_implies [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∧ $f2:tlafml ]) => `(TLA.tla_and [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∨ $f2:tlafml ]) => `(TLA.tla_or [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| ∀ $x:ident, $f:tlafml]) => `(TLA.tla_forall fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∀ $x:ident : $t, $f:tlafml]) => `(TLA.tla_forall fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident, $f:tlafml]) => `(TLA.tla_exists fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident : $t, $f:tlafml]) => `(TLA.tla_exists fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| ⋀ $x:ident ∈ $l:term, $f:tlafml]) => `(List.foldr (fun $x => TLA.tla_and ([tlafml| $f ])) TLA.tla_true $l)
  | `([tlafml| ⋀ _ ∈ $l:term, $f:tlafml]) => `(List.foldr (fun _ => TLA.tla_and ([tlafml| $f ])) TLA.tla_true $l)
  | `([tlafml| $t:term ]) => `($t)

-- these definitions are not necessarily required, but for delaboration purposes
def TLA.leads_to {α : Type u} (p q : TLA.pred α) : TLA.pred α := [tlafml| □ (p → ◇ q) ]
def TLA.weak_fairness {α : Type u} (a : action α) : pred α := [tlafml| □ ((□ (Enabled a)) → ◇ ⟨a⟩)]

macro_rules
  | `([tlafml| $f1:tlafml ↝ $f2:tlafml ]) => `(TLA.leads_to [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| 𝒲ℱ $t:term ]) => `(TLA.weak_fairness $t)

-- FIXME: use something fancier like `ᴛʟᴀ`
syntax:max tlafml:max " |-tla- " tlafml:max : term
syntax:max "|-tla- " tlafml:max : term
syntax:max tlafml:max " =tla= " tlafml:max : term
syntax term " |=tla= " tlafml : term

macro_rules
  | `($f1:tlafml |-tla- $f2:tlafml) => `(TLA.pred_implies [tlafml| $f1 ] [tlafml| $f2 ])
  | `(|-tla- $f1:tlafml) => `(TLA.valid [tlafml| $f1 ])
  | `($f1:tlafml =tla= $f2:tlafml) => `([tlafml| $f1 ] = [tlafml| $f2 ])
  | `($e:term |=tla= $f:tlafml) => `(TLA.exec.satisfies [tlafml| $f ] $e)

-- doing a trick here, since it seems that `app_unexpander` cannot detect the case where a term is directly used as `tlafml`
-- e.g., try removing the second branch and `#check forall (p : TLA.pred Prop), (p) |-tla- (p)`
def TLA.tlafml_syntax_coe (stx : TSyntax `term) : Lean.PrettyPrinter.UnexpandM (TSyntax `tlafml) := do
  match stx with
  | `([tlafml| $f:tlafml ]) => pure f
  | `(term|$t:term) => `(tlafml| $t:term )

-- FIXME: it would be desirable to derive the things below automatically
@[app_unexpander TLA.pure_pred] def TLA.unexpand_pure_pred : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `([tlafml| ⌞ $p ⌟ ])
  | _ => throw ()

@[app_unexpander TLA.state_pred] def TLA.unexpand_state_pred : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `([tlafml| ⌜ $p ⌝ ])
  | _ => throw ()

@[app_unexpander TLA.action_pred] def TLA.unexpand_action_pred : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `([tlafml| ⟨ $p ⟩ ])
  | _ => throw ()

@[app_unexpander TLA.tla_enabled] def TLA.unexpand_tla_enabled : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `([tlafml| Enabled $p ])
  | _ => throw ()

@[app_unexpander TLA.tla_true] def TLA.unexpand_tla_true : Lean.PrettyPrinter.Unexpander
  | `($_) => `([tlafml| ⊤ ])

@[app_unexpander TLA.tla_false] def TLA.unexpand_tla_false : Lean.PrettyPrinter.Unexpander
  | `($_) => `([tlafml| ⊥ ])

@[app_unexpander TLA.tla_and] def TLA.unexpand_tla_and : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `([tlafml| $(← TLA.tlafml_syntax_coe stx1) ∧ $(← TLA.tlafml_syntax_coe stx2)])
  | _ => throw ()

@[app_unexpander TLA.tla_or] def TLA.unexpand_tla_or : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `([tlafml| $(← TLA.tlafml_syntax_coe stx1) ∨ $(← TLA.tlafml_syntax_coe stx2)])
  | _ => throw ()

@[app_unexpander TLA.tla_implies] def TLA.unexpand_tla_implies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `([tlafml| $(← TLA.tlafml_syntax_coe stx1) → $(← TLA.tlafml_syntax_coe stx2)])
  | _ => throw ()

@[app_unexpander TLA.tla_not] def TLA.unexpand_tla_not : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `([tlafml| ¬ $(← TLA.tlafml_syntax_coe stx) ])
  | _ => throw ()

@[app_unexpander TLA.always] def TLA.unexpand_always : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `([tlafml| □ $(← TLA.tlafml_syntax_coe stx) ])
  | _ => throw ()

@[app_unexpander TLA.eventually] def TLA.unexpand_eventually : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `([tlafml| ◇ $(← TLA.tlafml_syntax_coe stx) ])
  | _ => throw ()

@[app_unexpander TLA.later] def TLA.unexpand_later : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `([tlafml| ◯ $(← TLA.tlafml_syntax_coe stx) ])
  | _ => throw ()

@[app_unexpander TLA.leads_to] def TLA.unexpand_leads_to : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `([tlafml| $(← TLA.tlafml_syntax_coe stx1) ↝ $(← TLA.tlafml_syntax_coe stx2)])
  | _ => throw ()

@[app_unexpander TLA.weak_fairness] def TLA.unexpand_weak_fairness : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `([tlafml| 𝒲ℱ $p ])
  | _ => throw ()

@[app_unexpander TLA.tla_forall] def TLA.unexpand_tla_forall : Lean.PrettyPrinter.Unexpander
  | `($_ fun $a:ident => $stx)
  | `($_ fun ($a:ident : $_) => $stx) => do `([tlafml| ∀ $a:ident, ($(← TLA.tlafml_syntax_coe stx)) ])
  | _ => throw ()

@[app_unexpander TLA.tla_exists] def TLA.unexpand_tla_exists : Lean.PrettyPrinter.Unexpander
  | `($_ fun $a:ident => $stx)
  | `($_ fun ($a:ident : $_) => $stx) => do `([tlafml| ∃ $a:ident, ($(← TLA.tlafml_syntax_coe stx)) ])
  | _ => throw ()

@[app_unexpander TLA.pred_implies] def TLA.unexpand_pred_implies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `(($(← TLA.tlafml_syntax_coe stx1)) |-tla- ($(← TLA.tlafml_syntax_coe stx2)))
  | _ => throw ()

@[app_unexpander TLA.valid] def TLA.unexpand_valid : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `(|-tla- ($(← TLA.tlafml_syntax_coe stx)))
  | _ => throw ()

@[app_unexpander TLA.exec.satisfies] def TLA.unexpand_satisfies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `($stx2 |=tla= $(← TLA.tlafml_syntax_coe stx1))
  | _ => throw ()

@[app_unexpander Eq] def TLA.unexpand_tla_eq : Lean.PrettyPrinter.Unexpander
  | `($_ [tlafml| $f1:tlafml ] [tlafml| $f2:tlafml ]) => `(($f1) =tla= ($f2))
  | `($_ [tlafml| $f1:tlafml ] $t2:term) => do `(($f1) =tla= ($(← `(tlafml| $t2:term ))))
  | `($_ $t1:term [tlafml| $f2:tlafml ]) => do `(($(← `(tlafml| $t1:term ))) =tla= ($f2))
  | _ => throw ()

@[app_unexpander List.foldr] def TLA.unexpand_tla_and_bigwedge : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 [tlafml| ⊤ ] $l:term) =>
    -- HMM directly writing `$stx1` as `(fun ...)` above does not work?
    match stx1 with
    | `(fun $x:ident => $stx)
    | `(fun ($x:ident : $_) => $stx) =>
      match stx with
      | `(TLA.tla_and $stx') => do `([tlafml| ⋀ $x:ident ∈ $l:term, $(← TLA.tlafml_syntax_coe stx')])
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()

register_simp_attr tlasimp_def
register_simp_attr tlasimp
register_simp_attr tladual      -- experimental
