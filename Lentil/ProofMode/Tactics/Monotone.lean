import Lentil.ProofMode.Basic
import Lentil.Rules.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

def mapHypPreds {σ : Type u} (f : pred σ → pred σ) (hyps : List (NamedPred σ)) :
    List (NamedPred σ) :=
  hyps.map fun h => { h with pred := f h.pred }

theorem mapHypPreds_preds {σ : Type u} (f : pred σ → pred σ) (hyps : List (NamedPred σ)) :
  (mapHypPreds f hyps).map NamedPred.pred = (hyps.map NamedPred.pred).map f := by
  simp [mapHypPreds]

section

variable {σ : Type u}

theorem repeatedAnd_map_later (ps : List (pred σ)) :
  repeatedAnd (ps.map TLA.later) = TLA.later (repeatedAnd ps) :=
  repeatedAnd_map_comm ps TLA.later (by funext e ; tunfold_simp) later_and

theorem repeatedAnd_map_always (ps : List (pred σ)) :
  repeatedAnd (ps.map TLA.always) = TLA.always (repeatedAnd ps) :=
  repeatedAnd_map_comm ps TLA.always (by funext e ; tunfold_simp) (by intro p q ; symm ; apply always_and)

theorem repeatedAnd_map_eventually_always (ps : List (pred σ)) :
  repeatedAnd (ps.map (fun p => TLA.eventually (TLA.always p))) =
    TLA.eventually (TLA.always (repeatedAnd ps)) :=
  repeatedAnd_map_comm ps (TLA.eventually ∘ TLA.always) (by funext e ; tunfold_simp) (by intro p q ; symm ; apply eventually_always_and_distrib)

variable {hyps : List (NamedPred σ)} {goal : pred σ}

private theorem Entails_monotone_aux (f : pred σ → pred σ)
  (h : ∀ ps, repeatedAnd (ps.map f) = f (repeatedAnd ps))
  (hmono : ∀ (p q : pred σ), (p) |-tla- (q) → ((f p)) |-tla- ((f q))) :
  Entails hyps goal → Entails (mapHypPreds f hyps) (f goal) := by
  unfold Entails ; intro hh
  rw [mapHypPreds_preds, h]
  exact hmono _ _ hh

theorem Entails_later_monotone :
  Entails hyps goal → Entails (mapHypPreds TLA.later hyps) (TLA.later goal) :=
  Entails_monotone_aux TLA.later repeatedAnd_map_later TLA.later_monotone

theorem Entails_always_monotone :
  Entails hyps goal → Entails (mapHypPreds TLA.always hyps) (TLA.always goal) :=
  Entails_monotone_aux TLA.always repeatedAnd_map_always TLA.always_monotone

theorem Entails_eventually_always_monotone :
  Entails hyps goal →
  Entails (mapHypPreds (fun p => TLA.eventually (TLA.always p)) hyps)
    (TLA.eventually (TLA.always goal)) :=
  Entails_monotone_aux (TLA.eventually ∘ TLA.always) repeatedAnd_map_eventually_always eventually_always_monotone

theorem Entails_eventually_monotone_single {name : String} {p : pred σ}
  (h : hyps = [⟨name, p⟩]) :
  Entails hyps goal →
  Entails (mapHypPreds TLA.eventually hyps) (TLA.eventually goal) := by
  subst hyps ; exact TLA.eventually_monotone p goal

theorem Entails_always_eventually_monotone_single {name : String} {p : pred σ}
  (h : hyps = [⟨name, p⟩]) :
  Entails hyps goal →
  Entails (mapHypPreds (fun p => TLA.always (TLA.eventually p)) hyps)
    (TLA.always (TLA.eventually goal)) := by
  subst hyps ; exact TLA.always_eventually_monotone p goal

end

private def monotoneKinds : List ((Expr → Option Expr) × Name) := [
  (matchFirstTwo ``TLA.always ``TLA.eventually, ``Entails_always_eventually_monotone_single),
  (matchFirstTwo ``TLA.eventually ``TLA.always, ``Entails_eventually_always_monotone),
  (matchFirst ``TLA.later, ``Entails_later_monotone),
  (matchFirst ``TLA.always, ``Entails_always_monotone),
  (matchFirst ``TLA.eventually, ``Entails_eventually_monotone_single),
]
where
  matchFirst (nm : Name) (e : Expr) : Option Expr :=
    if e.getAppFn'.isConstOf nm then (if h : e.isApp = true then some (e.appArg h) else none) else none
  matchFirstTwo (nm1 nm2 : Name) (e : Expr) : Option Expr :=
    matchFirst nm1 e |>.bind (matchFirst nm2)

private def findMonotonePeel? (hyps : List (String × Expr)) (goal : Expr) :
    MetaM (Option (Name × List (String × Expr) × Expr)) := do
  let recognizeDirect (e : Expr) : Option (Name × Expr) :=
    monotoneKinds.findSome? fun (recognizer, nm) => recognizer e |>.map (fun p => (nm, p))
  let recognize (e : Expr) := recognizeWithTlaModalityHeadUnfold? recognizeDirect e
  let some (nm, peeledGoal) ← recognize goal
    | return none
  let mut peeledHyps := []
  for (name, pred) in hyps do
    let some (nm', peeledPred) ← recognize pred | return none
    unless nm' == nm do
      return none
    peeledHyps := (name, peeledPred) :: peeledHyps
  return some (nm, peeledHyps.reverse, peeledGoal)

/-- A not quite useful fallback to non-proof-mode case. -/
private def rawMonotone : TacticM Unit := do
  evalTactic <| ← `(tactic|
    first
    | apply TLA.always_eventually_monotone
    | apply TLA.eventually_always_monotone
    | apply TLA.later_monotone
    | apply TLA.always_monotone
    | apply TLA.eventually_monotone)

private def proofModeMonotone : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target | rawMonotone
  -- TODO This pattern of recognizing the hypotheses from the goal is prevalent.
  -- Can we wrap it?
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tmonotone: failed to read the hypotheses from the goal"
  let some (nm, peeledHyps, peeledGoal) ← findMonotonePeel? hyps goal
    | throwError "tmonotone: expected every proof-mode hypothesis and the goal to have a common monotone temporal prefix"
  let peeledHypsExpr ← toHypsList hypTy peeledHyps
  let thm ← do
    if nm ∈ [``Entails_eventually_monotone_single, ``Entails_always_eventually_monotone_single] then
      unless peeledHyps.length == 1 do
        throwError "tmonotone: this modality can only be peeled from a single proof-mode hypothesis"
      mkAppOptM nm #[none, some peeledHypsExpr, some peeledGoal, none, none, some (← mkEqRefl peeledHypsExpr)]
    else
      mkAppOptM nm #[none, some peeledHypsExpr, some peeledGoal]
  let gs ← g.apply thm
  replaceMainGoal gs

/--
`tmonotone` removes a common monotone temporal prefix from the proof-mode
context and goal.

For example, if every temporal hypothesis and the goal are prefixed by `□`, then
```lean
tmonotone
```
turns a context such as `hp : □ p`, `hq : □ q` with goal `□ r` into
`hp : p`, `hq : q` with goal `r`.

It also supports `◯` and `◇□` over multiple hypotheses, and the single-hypothesis
cases for `◇` and `□◇`.

When the outer modality is hidden behind a definition tagged with
`[tla_modality_unfold]`, this tactic unfolds only that expression head while
recognizing the prefix. This includes the built-in wrappers `TLA.always_implies`
(`⇒`), `TLA.leads_to` (`↝`), and `TLA.weak_fairness` (`𝒲ℱ`).

Outside proof mode it applies the corresponding raw monotonicity theorem:
```lean
tmonotone
```
changes a raw goal `□ p |-tla- □ q` to `p |-tla- q`.
-/
syntax (name := tlaMonotoneTac) "tmonotone" : tactic

elab_rules : tactic
  | `(tactic| tmonotone) => proofModeMonotone

end TLA.ProofMode
