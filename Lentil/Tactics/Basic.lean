import Aesop
import Batteries.Tactic.Basic
import Lentil.Basic

open Lean Meta Elab Tactic

namespace TLA

syntax "try_unfold_at_all" ident+ : tactic
macro_rules
  | `(tactic| try_unfold_at_all $idt:ident ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt:ident $idts:ident* ) => `(tactic| (try unfold $idt at *) ; try_unfold_at_all $idts* )

attribute [tlasimp_def] leads_to weak_fairness tla_and tla_or tla_not tla_implies tla_forall texists tla_true tla_false always_implies
  always eventually later tla_until state_pred pure_pred action_pred
  valid pred_implies exec.satisfies exec.drop_drop
  tla_bigwedge tla_bigvee Foldable.fold

attribute [execsimp] exec.drop Nat.add_zero Nat.zero_add

macro "tunfold_defs" : tactic => `(tactic| (try dsimp only [tlasimp_def] at *))

macro "tunfold_defs'" : tactic => `(tactic| (tunfold_defs ; (try dsimp only [execsimp] at *)))

macro "tunfold_simp" : tactic => `(tactic| (simp [tlasimp_def] at *))

macro "tunfold_simp'" : tactic => `(tactic| (tunfold_simp ; (try simp only [execsimp] at *)))

attribute [tla_nontemporal_def] tla_and tla_or tla_not tla_implies tla_forall texists tla_true tla_false
  state_pred pure_pred action_pred
  valid pred_implies exec.satisfies
  tla_bigwedge tla_bigvee Foldable.fold

macro "tnontemporal_simp" : tactic => `(tactic| (simp [tla_nontemporal_def] at *))

/-- Normalize a sequent goal into a validity goal, by definitional equality. -/
def changePredImpliesToValid : TacticM Unit := withMainContext do
  let target ← getMainTarget
  match_expr target.headBeta.cleanupAnnotations with
  | TLA.pred_implies _ p q =>
    let imp ← mkAppM ``TLA.tla_implies #[p, q]
    let target' ← mkAppM ``TLA.valid #[imp]
    let goal ← getMainGoal
    replaceMainGoal [← goal.change target']
  | _ =>
    pure ()

end TLA
