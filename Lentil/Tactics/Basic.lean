module

public import Aesop
public import Batteries.Tactic.Basic
public import Batteries.Tactic.PermuteGoals
public import Lentil.Basic

open Lean Meta Elab Tactic

namespace Lentil

@[expose] public section

syntax "try_unfold_at_all" ident+ : tactic
macro_rules
  | `(tactic| try_unfold_at_all $idt:ident ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt:ident $idts:ident* ) => `(tactic| (try unfold $idt at *) ; try_unfold_at_all $idts* )

attribute [tlsimp_def] leads_to weak_fairness tl_and tl_or tl_not tl_implies tl_forall tl_exists tl_true tl_false always_implies
  always eventually later tl_until state_pred pure_pred action_pred
  valid pred_implies exec.satisfies exec.drop_drop
  tl_bigwedge tl_bigvee Foldable.fold
  valid_initial equiv_init

attribute [execsimp] exec.drop Nat.add_zero Nat.zero_add

macro "tunfold_defs" : tactic => `(tactic| (try dsimp only [tlsimp_def] at *))

macro "tunfold_defs'" : tactic => `(tactic| (tunfold_defs ; (try dsimp only [execsimp] at *)))

macro "tunfold_simp" : tactic => `(tactic| (simp [tlsimp_def] at *))

macro "tunfold_simp'" : tactic => `(tactic| (tunfold_simp ; (try simp only [execsimp] at *)))

attribute [tl_nontemporal_def] tl_and tl_or tl_not tl_implies tl_forall tl_exists tl_true tl_false
  state_pred pure_pred action_pred
  valid pred_implies exec.satisfies
  tl_bigwedge tl_bigvee Foldable.fold
  equiv_init valid_initial

macro "tnontemporal_simp" : tactic => `(tactic| (simp [tl_nontemporal_def] at *))

end

public meta section

/-- Normalize a sequent goal into a validity goal, by definitional equality. -/
def changePredImpliesToValid : TacticM Unit := withMainContext do
  let target ← getMainTarget
  match_expr target.headBeta.cleanupAnnotations with
  | Lentil.pred_implies _ p q =>
    let imp ← mkAppM ``Lentil.tl_implies #[p, q]
    let target' ← mkAppM ``Lentil.valid #[imp]
    let goal ← getMainGoal
    replaceMainGoal [← goal.change target']
  | _ =>
    pure ()

end

end Lentil
