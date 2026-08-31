import Lentil.ProofMode.Basic
import Lentil.Rules.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

def mapHypPreds {σ : Type u} (f : pred σ → pred σ) (hyps : List (NamedPred σ)) :
    List (NamedPred σ) :=
  hyps.map fun h => { h with pred := f h.pred }

theorem mapHypPreds_append {σ : Type u} (f : pred σ → pred σ) (pre post : List (NamedPred σ)) :
  mapHypPreds f (pre ++ post) = mapHypPreds f pre ++ mapHypPreds f post := by
  simp [mapHypPreds]

theorem mapHypPreds_preds {σ : Type u} (f : pred σ → pred σ) (hyps : List (NamedPred σ)) :
  (mapHypPreds f hyps).map NamedPred.pred = (hyps.map NamedPred.pred).map f := by
  simp [mapHypPreds]

section

variable {σ : Type u}

theorem repeatedAnd_map_later (ps : List (pred σ)) :
  repeatedAnd (ps.map Lentil.later) = Lentil.later (repeatedAnd ps) :=
  repeatedAnd_map_comm ps Lentil.later (by funext e i ; tunfold_simp) later_and

theorem repeatedAnd_map_always (ps : List (pred σ)) :
  repeatedAnd (ps.map Lentil.always) = Lentil.always (repeatedAnd ps) :=
  repeatedAnd_map_comm ps Lentil.always (by funext e i ; tunfold_simp) (by intro p q ; symm ; apply always_and)

theorem repeatedAnd_map_eventually_always (ps : List (pred σ)) :
  repeatedAnd (ps.map (fun p => Lentil.eventually (Lentil.always p))) =
    Lentil.eventually (Lentil.always (repeatedAnd ps)) :=
  repeatedAnd_map_comm ps (Lentil.eventually ∘ Lentil.always) (by funext e i ; tunfold_simp) (by intro p q ; symm ; apply eventually_always_and_distrib)

variable {hyps : List (NamedPred σ)} {goal : pred σ}

private theorem Entails_monotone_aux (f : pred σ → pred σ)
  (h : ∀ ps, repeatedAnd (ps.map f) = f (repeatedAnd ps))
  (hmono : ∀ {p q : pred σ}, (p) |-tl- (q) → ((f p)) |-tl- ((f q))) :
  Entails hyps goal → Entails (mapHypPreds f hyps) (f goal) := by
  unfold Entails ; intro hh
  rw [mapHypPreds_preds, h]
  exact hmono hh

theorem Entails_later_monotone :
  Entails hyps goal → Entails (mapHypPreds Lentil.later hyps) (Lentil.later goal) :=
  Entails_monotone_aux Lentil.later repeatedAnd_map_later Lentil.later_monotone

theorem Entails_always_monotone :
  Entails hyps goal → Entails (mapHypPreds Lentil.always hyps) (Lentil.always goal) :=
  Entails_monotone_aux Lentil.always repeatedAnd_map_always Lentil.always_monotone

theorem Entails_eventually_always_monotone :
  Entails hyps goal →
  Entails (mapHypPreds (fun p => Lentil.eventually (Lentil.always p)) hyps)
    (Lentil.eventually (Lentil.always goal)) :=
  Entails_monotone_aux (Lentil.eventually ∘ Lentil.always) repeatedAnd_map_eventually_always eventually_always_monotone

theorem Entails_eventually_monotone_single {name : String} {p : pred σ}
  (h : hyps = [⟨name, p⟩]) :
  Entails hyps goal →
  Entails (mapHypPreds Lentil.eventually hyps) (Lentil.eventually goal) := by
  subst hyps ; exact Lentil.eventually_monotone (p := p) (q := goal)

theorem Entails_always_eventually_monotone_single {name : String} {p : pred σ}
  (h : hyps = [⟨name, p⟩]) :
  Entails hyps goal →
  Entails (mapHypPreds (fun p => Lentil.always (Lentil.eventually p)) hyps)
    (Lentil.always (Lentil.eventually goal)) := by
  subst hyps ; exact Lentil.always_eventually_monotone (p := p) (q := goal)

end

/-- Remove one application of `modality`. This direct variant does not unfold
the expression head; it is useful when recognizing several alternatives at once. -/
def peelTlModalityDirect? (modality : Name) (e : Expr) : Option Expr :=
  if e.getAppFn'.isConstOf modality then
    if h : e.isApp = true then some (e.appArg h) else none
  else
    none

/-- As `peelTlModalityDirect?`, but allowing a definition tagged with `[tl_modality_unfold]` at the
expression head. This is shared with the other modality tactics. -/
def peelTlModality? (modality : Name) (e : Expr) : MetaM (Option Expr) :=
  recognizeWithTlModalityHeadUnfold? (peelTlModalityDirect? modality) e

/- The order is significant: `tmonotone` peels `□◇` and `◇□` in one step when
possible, before falling back to their outer modality. These composite cases
exist because proof mode must also distribute the prefix over the conjunction of
all hypotheses; that is separate from ordinary one-formula monotonicity. -/
private def monotoneKinds : List ((Expr → Option Expr) × Name) := [
  (matchFirstTwo ``Lentil.always ``Lentil.eventually, ``Entails_always_eventually_monotone_single),
  (matchFirstTwo ``Lentil.eventually ``Lentil.always, ``Entails_eventually_always_monotone),
  (peelTlModalityDirect? ``Lentil.later, ``Entails_later_monotone),
  (peelTlModalityDirect? ``Lentil.always, ``Entails_always_monotone),
  (peelTlModalityDirect? ``Lentil.eventually, ``Entails_eventually_monotone_single),
]
where
  matchFirstTwo (outer inner : Name) (e : Expr) : Option Expr :=
    peelTlModalityDirect? outer e >>= peelTlModalityDirect? inner

private def findMonotonePeel? (hyps : List (String × Expr)) (goal : Expr) :
    MetaM (Option (Name × List (String × Expr) × Expr)) := do
  let recognizeDirect (e : Expr) : Option (Name × Expr) :=
    monotoneKinds.findSome? fun (recognizer, nm) => recognizer e |>.map (fun p => (nm, p))
  let recognize (e : Expr) := recognizeWithTlModalityHeadUnfold? recognizeDirect e
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
    | apply Lentil.always_eventually_monotone
    | apply Lentil.eventually_always_monotone
    | apply Lentil.later_monotone
    | apply Lentil.always_monotone
    | apply Lentil.eventually_monotone)

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
    -- `◇` does not distribute over a conjunction. The two theorems below are
    -- therefore deliberately restricted to a singleton proof-mode context.
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
`[tl_modality_unfold]`, this tactic unfolds only that expression head while
recognizing the prefix. This includes the built-in wrappers `Lentil.always_implies`
(`⇒`), `Lentil.leads_to` (`↝`), and `Lentil.weak_fairness` (`𝒲ℱ`).

Outside proof mode it applies the corresponding raw monotonicity theorem:
```lean
tmonotone
```
changes a raw goal `□ p |-tl- □ q` to `p |-tl- q`.
-/
syntax (name := tlMonotoneTac) "tmonotone" : tactic

elab_rules : tactic
  | `(tactic| tmonotone) => proofModeMonotone

end Lentil.ProofMode
