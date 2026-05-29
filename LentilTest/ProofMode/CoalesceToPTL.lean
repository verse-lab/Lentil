import Lentil

/- Tests for `tla_coalesce_to_ptl`. -/

namespace TLA.ProofMode.Test.CoalesceToPTL

open TLA TLA.ProofMode
open Lean Meta Elab Tactic

variable {σ : Type u}

private def throwUnexpectedTarget (expected : String) (target : Expr) : MetaM α :=
  throwError "expected coalesced target shape: {expected}{indentExpr target}"

private def getPredImpliesTarget : TacticM (Expr × Expr) := withMainContext do
  let target ← cleanupAnnotAndMore (← getMainTarget)
  match_expr target with
  | TLA.pred_implies _ p q => return (p, q)
  | _ => throwUnexpectedTarget "raw TLA sequent" target

private def guardSame (expected : String) (p q : Expr) : MetaM Unit := do
  unless ← isDefEq p q do
    throwError "expected matching {expected} formulas{indentExpr p}{indentExpr q}"

elab "guard_until_refl_target" : tactic => withMainContext do
  let (lhs, rhs) ← getPredImpliesTarget
  match_expr lhs with
  | TLA.tla_until _ p q =>
    unless p.isFVar && q.isFVar do
      throwUnexpectedTarget "until over two fresh atoms" lhs
    match_expr rhs with
    | TLA.tla_until _ p' q' =>
      guardSame "until-left" p p'
      guardSame "until-right" q q'
    | _ => throwUnexpectedTarget "until on the right-hand side" rhs
  | _ => throwUnexpectedTarget "until on the left-hand side" lhs

elab "guard_forall_always_and_target" : tactic => withMainContext do
  let (lhs, rhs) ← getPredImpliesTarget
  match_expr lhs with
  | TLA.tla_forall _ _ lhsF =>
    match_expr rhs with
    | TLA.tla_forall _ _ rhsF =>
      lambdaTelescope lhsF fun xs lhsBody => do
        unless xs.size == 1 do
          throwUnexpectedTarget "unary forall on the left-hand side" lhs
        let rhsBody := (mkAppN rhsF xs).headBeta
        match_expr lhsBody with
        | TLA.always _ lhsAlways =>
          match_expr rhsBody with
          | TLA.always _ rhsAlways =>
            match_expr lhsAlways with
            | TLA.tla_and _ p q =>
              match_expr rhsAlways with
              | TLA.tla_and _ p' q' =>
                guardSame "left conjunct atom" p p'
                guardSame "right conjunct atom" q q'
              | _ => throwUnexpectedTarget "conjunction under right always" rhsAlways
            | _ => throwUnexpectedTarget "conjunction under left always" lhsAlways
          | _ => throwUnexpectedTarget "always under right forall" rhsBody
        | _ => throwUnexpectedTarget "always under left forall" lhsBody
    | _ => throwUnexpectedTarget "forall on the right-hand side" rhs
  | _ => throwUnexpectedTarget "forall on the left-hand side" lhs

elab "guard_forall_always_and_implies_left_target" : tactic => withMainContext do
  let (lhs, rhs) ← getPredImpliesTarget
  match_expr lhs with
  | TLA.tla_forall _ _ lhsF =>
    match_expr rhs with
    | TLA.tla_forall _ _ rhsF =>
      lambdaTelescope lhsF fun xs lhsBody => do
        unless xs.size == 1 do
          throwUnexpectedTarget "unary forall on the left-hand side" lhs
        let rhsBody := (mkAppN rhsF xs).headBeta
        match_expr lhsBody with
        | TLA.always _ lhsAlways =>
          match_expr rhsBody with
          | TLA.always _ rhsAlways =>
            match_expr lhsAlways with
            | TLA.tla_and _ p _ =>
              guardSame "left conjunct and goal atom" p rhsAlways
            | _ => throwUnexpectedTarget "conjunction under left always" lhsAlways
          | _ => throwUnexpectedTarget "always under right forall" rhsBody
        | _ => throwUnexpectedTarget "always under left forall" lhsBody
    | _ => throwUnexpectedTarget "forall on the right-hand side" rhs
  | _ => throwUnexpectedTarget "forall on the left-hand side" lhs

elab "guard_entails_two_always_target" : tactic => withMainContext do
  let target ← cleanupAnnotAndMore (← getMainTarget)
  match_expr target with
  | Entails _ hypsExpr goal =>
    let some (_, [("hP", hP), ("hQ", hQ)]) ← recognizeHypsList hypsExpr
      | throwUnexpectedTarget "two named proof-mode hypotheses" target
    match_expr hP with
    | TLA.always _ p =>
      match_expr hQ with
      | TLA.always _ q =>
        unless p.isFVar && q.isFVar do
          throwUnexpectedTarget "always hypotheses over fresh atoms" target
        match_expr goal with
        | TLA.always _ g => guardSame "first hypothesis and goal atom" p g
        | _ => throwUnexpectedTarget "always proof-mode goal" goal
      | _ => throwUnexpectedTarget "always second proof-mode hypothesis" hQ
    | _ => throwUnexpectedTarget "always first proof-mode hypothesis" hP
  | _ => throwUnexpectedTarget "proof-mode Entails goal" target

elab "guard_entails_always_hyp_atom_goal" : tactic => withMainContext do
  let target ← cleanupAnnotAndMore (← getMainTarget)
  match_expr target with
  | Entails _ hypsExpr goal =>
    let some (_, [("hP", hP)]) ← recognizeHypsList hypsExpr
      | throwUnexpectedTarget "one named proof-mode hypothesis" target
    match_expr hP with
    | TLA.always _ p => guardSame "hypothesis atom and goal atom" p goal
    | _ => throwUnexpectedTarget "always proof-mode hypothesis" hP
  | _ => throwUnexpectedTarget "proof-mode Entails goal" target

example (P : σ → Prop) : (⌜ P ⌝) |-tla- (⌜ P ⌝) := by
  tla_coalesce_to_ptl
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (P Q : σ → Prop) : (□ ⌜ P ⌝ ∧ □ ⌜ Q ⌝) |-tla- (□ ⌜ P ⌝) := by
  tla_start hP hQ
  tla_coalesce_to_ptl
  guard_entails_two_always_target
  tla_monotone
  tla_assumption

example (P : σ → Prop) : (□ ⌜ P ⌝) |-tla- (⌜ P ⌝) := by
  tla_start hP
  tla_coalesce_to_ptl
  guard_entails_always_hyp_atom_goal
  tla_toggle_goal_under_always
  tla_monotone
  tla_assumption

example (P : σ → Prop) : (⌜ P ⌝) |-tla- (◯ ⌜ P ⌝ → ◇ ⌜ P ⌝) := by
  tla_coalesce_to_ptl
  guard_target =
    TLA.pred_implies ptlAtom (TLA.tla_implies (TLA.later ptlAtom) (TLA.eventually ptlAtom))
  intro e hP hLater
  exact later_weaken_to_eventually _ e hLater

example (P Q : σ → Prop) : (⌜ P ⌝ 𝑈 ⌜ Q ⌝) |-tla- (⌜ P ⌝ 𝑈 ⌜ Q ⌝) := by
  tla_coalesce_to_ptl
  guard_until_refl_target
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, ⌜ P x ⌝) |-tla- (∀ x, ⌜ P x ⌝) := by
  tla_coalesce_to_ptl
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, ⌜ P x ⌝) |-tla- (∀ x, ⌜ P x ⌝) := by
  tla_coalesce_to_ptl (binders := .ignore)
  guard_target =
    TLA.pred_implies (TLA.tla_forall fun x => ptlAtom x)
      (TLA.tla_forall fun x => ptlAtom x)
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, □ ⌜ P x ⌝) |-tla- (∀ x, □ ⌜ P x ⌝) := by
  tla_coalesce_to_ptl (binders := .ignore)
  guard_target =
    TLA.pred_implies (TLA.tla_forall fun x => TLA.always (ptlAtom x))
      (TLA.tla_forall fun x => TLA.always (ptlAtom x))
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, □ ⌜ P x ⌝) |-tla- (∀ y, □ ⌜ P y ⌝) := by
  tla_coalesce_to_ptl (binders := .ignore)
  guard_target =
    TLA.pred_implies (TLA.tla_forall fun x => TLA.always (ptlAtom x))
      (TLA.tla_forall fun y => TLA.always (ptlAtom y))
  exact pred_implies_refl _

example {α : Type v} (P Q : α → σ → Prop) :
    (∀ x, □ (⌜ P x ⌝ ∧ ⌜ Q x ⌝)) |-tla- (∀ x, □ ⌜ P x ⌝) := by
  tla_coalesce_to_ptl (binders := .ignore)
  guard_forall_always_and_implies_left_target
  intro e h x k
  exact (h x k).1

example (a : action σ) : (𝒲ℱ a) |-tla- (𝒲ℱ a) := by
  tla_coalesce_to_ptl (abstractOpaque := true)
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (P Q : σ → Prop) : (⌜ P ⌝ ↝ ⌜ Q ⌝) |-tla- (⌜ P ⌝ ↝ ⌜ Q ⌝) := by
  tla_coalesce_to_ptl (abstractOpaque := true)
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (P Q : σ → Prop) : (⌜ P ⌝ ⇒ ⌜ Q ⌝) |-tla- (⌜ P ⌝ ⇒ ⌜ Q ⌝) := by
  tla_coalesce_to_ptl (abstractOpaque := true)
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tla- (p) := by
  tla_coalesce_to_ptl (abstractOpaque := true)
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tla- (p) := by
  tla_coalesce_to_ptl (level := .formula)
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example (P Q : σ → Prop) :
    (□ (⌜ P ⌝ ∧ ⌜ Q ⌝)) |-tla- (□ (⌜ P ⌝ ∧ ⌜ Q ⌝)) := by
  tla_coalesce_to_ptl (level := .modal)
  guard_target = TLA.pred_implies (TLA.always ptlAtom) (TLA.always ptlAtom)
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tla- (p) := by
  tla_coalesce_to_ptl (config := { level := .formula : CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

section ConfigMatrix

variable {α : Type v} (P : α → σ → Prop) (p : pred σ)

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .leaves, abstractOpaque := false :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .leaves, abstractOpaque := true :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .modal, abstractOpaque := false :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .modal, abstractOpaque := true :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .formula, abstractOpaque := false :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .block, level := .formula, abstractOpaque := true :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .leaves, abstractOpaque := false :
      CoalesceConfig })
  guard_target =
    TLA.pred_implies
      (TLA.tla_forall fun x => TLA.always (TLA.tla_and (ptlAtom x) p))
      (TLA.tla_forall fun x => TLA.always (TLA.tla_and (ptlAtom x) p))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .leaves, abstractOpaque := true :
      CoalesceConfig })
  guard_forall_always_and_target
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .modal, abstractOpaque := false :
      CoalesceConfig })
  guard_target =
    TLA.pred_implies (TLA.tla_forall fun x => TLA.always (ptlAtom x))
      (TLA.tla_forall fun x => TLA.always (ptlAtom x))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .modal, abstractOpaque := true :
      CoalesceConfig })
  guard_target =
    TLA.pred_implies (TLA.tla_forall fun x => TLA.always (ptlAtom x))
      (TLA.tla_forall fun x => TLA.always (ptlAtom x))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .formula, abstractOpaque := false :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tla- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tla_coalesce_to_ptl
    (config := {
      binders := .ignore, level := .formula, abstractOpaque := true :
      CoalesceConfig })
  guard_target = TLA.pred_implies ptlAtom ptlAtom
  exact pred_implies_refl _

end ConfigMatrix

/--
error: tla_coalesce_to_ptl: found no non-PTL predicate blocks to abstract
-/
#guard_msgs in
example (p : pred σ) : (□ p) |-tla- (□ p) := by
  tla_coalesce_to_ptl

/--
error: tla_coalesce_to_ptl: found no non-PTL predicate blocks to abstract
-/
#guard_msgs in
example (a : action σ) : (𝒲ℱ a) |-tla- (𝒲ℱ a) := by
  tla_coalesce_to_ptl

/--
error: tla_coalesce_to_ptl: expected a TLA validity goal, raw TLA sequent, or proof-mode Entails goal
-/
#guard_msgs in
example : True := by
  tla_coalesce_to_ptl

end TLA.ProofMode.Test.CoalesceToPTL
