import Aesop
import Batteries.Tactic.Basic
import Lentil.Basic

open Lean

namespace TLA

syntax "try_unfold_at_all" ident+ : tactic
macro_rules
  | `(tactic| try_unfold_at_all $idt:ident ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt:ident $idts:ident* ) => `(tactic| (try unfold $idt at *) ; try_unfold_at_all $idts* )

macro "tla_unfold" : tactic =>
  `(tactic| (try_unfold_at_all leads_to weak_fairness tla_and tla_or tla_not tla_implies tla_forall tla_exists tla_true tla_false always eventually later tla_until state_pred pure_pred valid pred_implies exec.satisfies tla_bigwedge tla_bigvee)
     <;> (try (dsimp only [Foldable.fold] at *)))

attribute [tlasimp_def] leads_to weak_fairness tla_and tla_or tla_not tla_implies tla_forall tla_exists tla_true tla_false
  always eventually later tla_until state_pred pure_pred
  valid pred_implies exec.satisfies exec.drop_drop
  tla_bigwedge tla_bigvee Foldable.fold

macro "tla_unfold_simp" : tactic => `(tactic| (simp [tlasimp_def] at *))

attribute [tla_nontemporal_def] tla_and tla_or tla_not tla_implies tla_forall tla_exists tla_true tla_false
  state_pred pure_pred
  valid pred_implies exec.satisfies
  tla_bigwedge tla_bigvee Foldable.fold

macro "tla_nontemporal_simp" : tactic => `(tactic| (simp [tla_nontemporal_def] at *))

/-- Create a conjunction of `o(_) ∧ o(_) ∧ ... ∧ o(_)`, where `o` is a heading op like `□`. -/
def make_conjunction_of_holes (headingop : TSyntax `tlafml_heading_op) (n : Nat) : MacroM (TSyntax `tlafml) := do
  let q : TSyntax `term ← `(term|_)
  match n with
  | 0 => Macro.throwUnsupported
  | 1 => do
    `(tlafml| ($headingop:tlafml_heading_op ($q:term)) )
  | n' + 1 => do
    let res ← make_conjunction_of_holes headingop n'
    `(tlafml| ($headingop:tlafml_heading_op ($q:term)) ∧ $res:tlafml )

/-- Give `And.intro t1 (And.intro t2 ...)`, where `tms = [t1, t2, ...]`. -/
def make_conjunction_of_terms (tms : List (TSyntax `term)) : MacroM (TSyntax `term) := do
  match tms with
  | [] => Macro.throwUnsupported
  | [t] => `(term| $t)
  | t :: tms' =>
    let res ← make_conjunction_of_terms tms'
    `(term| And.intro $t ($res) )

/-- Given that `ti : e |=tla= □ pi`, `tla_merge_always' t1, t2, ..., tn => h` creates
    a new hypothesis `h : e |=tla= □ p1 ∧ □ p2 ∧ ... ∧ □ pn`. -/
macro "tla_merge_always'" tmss:term,+ "=>" h:ident : tactic => do
  let tms := tmss.getElems
  let headingop ← `(tlafml_heading_op| □ )
  let fml ← make_conjunction_of_holes headingop tms.size
  let conj ← make_conjunction_of_terms tms.toList
  `(tactic| ((have $h : (_ |=tla= $fml:tlafml) := $conj) ; (try dsimp only [exec.satisfies] at $h:ident)))

end TLA
