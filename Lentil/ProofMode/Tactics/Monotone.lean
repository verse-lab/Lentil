module

public import Lentil.ProofMode.Basic
public import Lentil.ProofMode.Classes
public import Lentil.Rules.Basic

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

@[expose] public section

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

/- NOTE: On the design of `HypsInto`.

Why an inductive predicate rather than a recursive (fold-style) definition, e.g.
`HypsInto f (⟨_, p⟩ :: hs) (⟨_, q⟩ :: qs) := ((p) |-tl- (f q)) ∧ HypsInto f hs qs`:
- A certificate built from `nil` and `cons` syntactically has the type
  `HypsInto f (⟨name, p⟩ :: …) (⟨name, q⟩ :: …)`, so it matches the premise of the
  reflection theorems directly, and unification can even read `hyps` and `peeled` off
  it. A fold-style certificate is a chain of `∧`s that only matches after unfolding the
  definition (which fails, e.g., under reducible transparency), so `hyps` and `peeled`
  must be given explicitly.
- The constructors enforce the shape: equal lengths and the same names. A fold needs
  explicit cases for mismatched lists; one based on `List.zip` would silently truncate,
  leaving extra hypotheses in `peeled` unjustified.
- `induction` on the certificate gives exactly the two cases of `HypsInto.entails`.

Why not a typeclass over the whole context, with instances for `nil` and `cons`:
instance search could then build the certificate in a single query, but when one
hypothesis has no instance, the query only reports that the class cannot be synthesized
for the entire context, without saying which hypothesis is to blame. The tactics
instead query one instance per hypothesis (`mkHypsInto`), so that the error names the
hypothesis and the missing class. Per-hypothesis processing also leaves room for steps
outside typeclass search: the syntactic fast path for `[tl_modality_unfold]` heads, and
restoring binder names (`alignBinders`). A whole-context class fits better when failure
is not an error, e.g., when hypotheses without an instance may simply be dropped. -/

/-- `hyps` and `peeled` have the same names, and each hypothesis `p` in `hyps`
entails `f q` for the corresponding `q` in `peeled`. The modality tactics build
it from one typeclass instance per hypothesis (see `Lentil.ProofMode.Classes`);
`HypsInto Lentil.always hyps hyps` says that every hypothesis is stable under `□`. -/
inductive HypsInto (f : pred σ → pred σ) : List (NamedPred σ) → List (NamedPred σ) → Prop where
  | nil : HypsInto f [] []
  | cons {name : String} {p q : pred σ} {hyps peeled : List (NamedPred σ)} :
      (p) |-tl- (f q) → HypsInto f hyps peeled →
      HypsInto f (⟨name, p⟩ :: hyps) (⟨name, q⟩ :: peeled)

theorem HypsInto.entails {f : pred σ → pred σ} {hyps peeled : List (NamedPred σ)}
    (h : HypsInto f hyps peeled) :
    (repeatedAnd (hyps.map NamedPred.pred)) |-tl-
      (repeatedAnd ((mapHypPreds f peeled).map NamedPred.pred)) := by
  induction h with
  | nil => exact pred_implies_refl _
  | cons hp _ ih =>
    simp only [mapHypPreds, List.map_cons, repeatedAnd_cons]
    rw [and_pred_implies_split]
    exact ⟨pred_implies_trans Lentil.and_left hp, pred_implies_trans Lentil.and_right ih⟩

variable {hyps : List (NamedPred σ)} {goal : pred σ}

private theorem Entails_monotone_aux (f : pred σ → pred σ)
  (h : ∀ ps, repeatedAnd (ps.map f) = f (repeatedAnd ps))
  (hmono : ∀ {p q : pred σ}, (p) |-tl- (q) → ((f p)) |-tl- ((f q))) :
  Entails hyps goal → Entails (mapHypPreds f hyps) (f goal) := by
  unfold Entails ; intro hh
  rw [mapHypPreds_preds, h]
  exact hmono hh

theorem Entails_later_monotone {peeled : List (NamedPred σ)} (h : HypsInto Lentil.later hyps peeled) :
    Entails peeled goal → Entails hyps (Lentil.later goal) := by
  intro hg
  unfold Entails at hg ⊢
  refine pred_implies_trans h.entails ?_
  rw [mapHypPreds_preds, repeatedAnd_map_later]
  exact later_monotone hg

theorem Entails_always_monotone {peeled : List (NamedPred σ)} (h : HypsInto Lentil.always hyps peeled) :
    Entails peeled goal → Entails hyps (Lentil.always goal) := by
  intro hg
  unfold Entails at hg ⊢
  refine pred_implies_trans h.entails ?_
  rw [mapHypPreds_preds, repeatedAnd_map_always]
  exact always_monotone hg

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

end

public meta section

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

/-! ### Per-hypothesis evidence

The modality tactics treat each proof-mode hypothesis separately. A leading
modality, possibly behind a `[tl_modality_unfold]` head, is recognized
syntactically; otherwise a typeclass from `Lentil.ProofMode.Classes` decides,
which also looks through the structure of the hypothesis. The per-hypothesis
proofs are assembled into the `HypsInto` premise of a reflection theorem, and a
failure names the hypothesis that could not be handled. -/

/-- Typeclass synthesis returns the peeled formula with binder names taken from
the instances, and with eta-reduced functions: `∀ c, □ p c` peels to
`tl_forall p`, not `∀ c, p c`. Restore the binder structure of the original
hypothesis `src`: walk `src` and `e` in parallel through applications of the
same constant, and wherever `src` has a `λ`, rename or eta-expand the
corresponding part of `e`. The result is definitionally equal to `e`. -/
partial def alignBinders (src e : Expr) : MetaM Expr := do
  match src, e with
  -- Temporal quantifiers use lambdas as their arguments, so the binders
  -- whose names we restore here are `.lam`.
  | .lam n _ b _, .lam _ t b' bi =>
    withLocalDecl n bi t fun x => do
      mkLambdaFVars #[x] (← alignBinders (b.instantiate1 x) (b'.instantiate1 x))
  | .lam n _ b _, _ =>
    let .forallE _ t _ bi ← whnf (← inferType e) | return e
    withLocalDecl n bi t fun x => do
      mkLambdaFVars #[x] (← alignBinders (b.instantiate1 x) (mkApp e x))
  | .app .., .app .. =>
    let (srcFn, srcArgs) := src.withApp fun a b => (a, b)
    let (eFn, eArgs) := e.withApp fun a b => (a, b)
    let some srcName := srcFn.constName? | return e
    let some eName := eFn.constName? | return e
    unless srcName == eName && srcArgs.size == eArgs.size do
      return e
    return mkAppN eFn (← (srcArgs.zip eArgs).mapM fun (s, a) => alignBinders s a)
  | _, _ => return e

/-- Peel `modality` from a hypothesis `p`: return `q` with a proof of
`p |-tl- modality q`. A leading `modality` is peeled syntactically; otherwise
the typeclass `cls` with its projection `proj` (`IntoAlways`, `IntoLater`)
decides. -/
def peelHypInto? (modality cls proj : Name) (p : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some q ← peelTlModality? modality p then
    -- If we successfully peeled the modality syntactically, the proof is just `pred_implies_refl`
    let ty ← mkAppM ``Lentil.pred_implies #[p, ← mkAppM modality #[q]]
    return some (q, ← mkExpectedTypeHint (← mkAppM ``Lentil.pred_implies_refl #[p]) ty)
  let q ← mkFreshExprMVar (← inferType p)
  let some inst ← (try synthInstance? (← mkAppM cls #[p, q]) catch _ => pure none)
    | return none
  let q ← alignBinders p (← instantiateMVars q)
  return some (q, ← mkAppOptM proj #[none, some p, some q, some inst])

/-- Assemble `HypsInto f hyps peeled` from the per-hypothesis results of `peel`,
or return the first hypothesis that `peel` rejects. -/
def mkHypsInto (f : Expr) (hyps : List (String × Expr))
    (peel : Expr → MetaM (Option (Expr × Expr))) :
    MetaM (Except (String × Expr) (List (String × Expr) × Expr)) := do
  let mut items := #[]
  for (name, p) in hyps do
    let some (q, pf) ← peel p | return .error (name, p)
    items := items.push (name, p, q, pf)
  let nil ← mkAppOptM ``HypsInto.nil #[none, some f]
  let proof ← items.foldrM (init := nil) fun (name, p, q, pf) rest =>
    mkAppOptM ``HypsInto.cons
      #[none, some f, some (toExpr name), some p, some q, none, none, some pf, some rest]
  return .ok (items.toList.map fun (name, _, q, _) => (name, q), proof)

private inductive MonotoneRule where
  /-- Peel each hypothesis via a modality, a typeclass, and its projection. -/
  | viaClass (modality cls proj thm : Name)
  /-- Peel the same syntactic prefix from the goal and hypotheses. -/
  | syntactic (thm : Name) (singleHyp : Bool)

/-- A prefix that `tmonotone` can remove. -/
private structure MonotoneKind where
  label : String
  /-- Recognizes the prefix on the goal, and on hypotheses for a syntactic rule. -/
  recognizer : Expr → Option Expr
  rule : MonotoneRule

/- The order is significant: `tmonotone` peels `□◇` and `◇□` in one step when
possible, before falling back to their outer modality. These composite cases
exist because proof mode must also distribute the prefix over the conjunction of
all hypotheses; that is separate from ordinary one-formula monotonicity. -/
private def monotoneKinds : List MonotoneKind := [
  { label := "□◇", recognizer := matchFirstTwo ``Lentil.always ``Lentil.eventually,
    rule := .syntactic ``Entails_always_eventually_monotone_single (singleHyp := true) },
  { label := "◇□", recognizer := matchFirstTwo ``Lentil.eventually ``Lentil.always,
    rule := .syntactic ``Entails_eventually_always_monotone (singleHyp := false) },
  { label := "◯", recognizer := peelTlModalityDirect? ``Lentil.later,
    rule := .viaClass ``Lentil.later ``IntoLater ``IntoLater.into_later ``Entails_later_monotone },
  { label := "□", recognizer := peelTlModalityDirect? ``Lentil.always,
    rule := .viaClass ``Lentil.always ``IntoAlways ``IntoAlways.into_always ``Entails_always_monotone },
  { label := "◇", recognizer := peelTlModalityDirect? ``Lentil.eventually,
    rule := .syntactic ``Entails_eventually_monotone_single (singleHyp := true) },
]
where
  matchFirstTwo (outer inner : Name) (e : Expr) : Option Expr :=
    peelTlModalityDirect? outer e >>= peelTlModalityDirect? inner

/-- Why `kind` does not apply to the hypothesis `name : p`. -/
private def monotoneStuckMsg (kind : MonotoneKind) (name : String) (p : Expr) : MessageData :=
  let p := MessageData.ofFormatWithInfosM <|
    PrettyPrinter.ppExprWithInfos p (delab := do
      return ⟨(← delab_tlfml_inner).raw⟩)
  match kind.rule with
  | .viaClass _ cls _ _ =>
    m!"cannot peel `{kind.label}` from hypothesis {name} \
      (no `{.ofConstName cls}` instance applies):{indentD p}"
  | .syntactic .. => m!"hypothesis {name} does not have the prefix `{kind.label}`:{indentD p}"

/-- Try each prefix of the goal across the whole sequent before falling back to
a shorter one. Returns the reflection theorem applied to the peeled context
and goal, including `HypsInto` evidence for a typeclass rule. On failure,
returns for each prefix of the goal the first hypothesis that does not have it. -/
private def findMonotoneRule (σ hypTy hypsExpr : Expr) (hyps : List (String × Expr)) (goal : Expr) :
    MetaM (Except (Array (MonotoneKind × String × Expr)) Expr) := do
  let mut stuck := #[]
  for kind in monotoneKinds do
    let recognize (e : Expr) := recognizeWithTlModalityHeadUnfold? kind.recognizer e
    let some peeledGoal ← recognize goal | continue
    match kind.rule with
    | .viaClass modality cls proj thm =>
      let f ← mkAppOptM modality #[some σ]
      match ← mkHypsInto f hyps (peelHypInto? modality cls proj) with
      | .ok (peeledHyps, h) =>
        let peeledHypsExpr ← toHypsList hypTy peeledHyps
        return .ok (← mkAppOptM thm #[none, some hypsExpr, some peeledGoal, some peeledHypsExpr, some h])
      | .error (name, p) => stuck := stuck.push (kind, name, p)
    | .syntactic thm singleHyp =>
      let mut peeledHyps := #[]
      let mut failed := none
      for (name, pred) in hyps do
        match ← recognize pred with
        | some peeledPred => peeledHyps := peeledHyps.push (name, peeledPred)
        | none =>
          failed := some (name, pred)
          break
      match failed with
      | none =>
        let peeledHypsExpr ← toHypsList hypTy peeledHyps.toList
        let thm ← if singleHyp then
          -- `◇` and `□◇` do not distribute over a conjunction of hypotheses.
          unless peeledHyps.size == 1 do
            throwError "tmonotone: this modality can only be peeled from a single proof-mode hypothesis"
          mkAppOptM thm #[none, some peeledHypsExpr, some peeledGoal, none, none, some (← mkEqRefl peeledHypsExpr)]
        else
          mkAppOptM thm #[none, some peeledHypsExpr, some peeledGoal]
        return .ok thm
      | some (name, p) => stuck := stuck.push (kind, name, p)
  return .error stuck

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
  let_expr Entails σ hypsExpr goal := target | rawMonotone
  -- TODO This pattern of recognizing the hypotheses from the goal is prevalent.
  -- Can we wrap it?
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tmonotone: failed to read the hypotheses from the goal"
  let thm ← match ← findMonotoneRule σ hypTy hypsExpr hyps goal with
    | .ok thm => pure thm
    | .error stuck =>
      match stuck.toList with
      | [] => throwError
        "tmonotone: the goal has no monotone temporal prefix (`□`, `◯`, `◇`, `□◇` or `◇□`)"
      | [(kind, name, p)] => throwError "tmonotone: {monotoneStuckMsg kind name p}"
      | stuck =>
        let details := stuck.map fun (kind, name, p) => m!"\n• {monotoneStuckMsg kind name p}"
        throwError (m!"tmonotone: no prefix of the goal is shared by all proof-mode hypotheses:"
          ++ .joinSep details "")
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

For `□` and `◯`, a hypothesis may also carry the prefix underneath other
connectives: typeclass search for `IntoAlways` or `IntoLater` (see
`Lentil.ProofMode.Classes`) looks through `∀`, `∃`, `∧`, `∨`, `⋀`, `⋁` and `◯`
(resp. `□`, `◇`), so for instance `hp : ∀ x, □ p x` becomes `hp : ∀ x, p x`.
For other connectives, add an instance. When a hypothesis cannot be handled, the
error message names it.

When the outer modality is hidden behind a definition tagged with
`[tl_modality_unfold]`, this tactic unfolds only that expression head while
recognizing the prefix. This includes the built-in wrappers `Lentil.always_implies`
(`⇒`), `Lentil.leads_to` (`↝`), `Lentil.weak_fairness` (`𝒲ℱ`), and
`Lentil.strong_fairness` (`𝒮ℱ`).

Outside proof mode it applies the corresponding raw monotonicity theorem:
```lean
tmonotone
```
changes a raw goal `□ p |-tl- □ q` to `p |-tl- q`.
-/
syntax (name := tlMonotoneTac) "tmonotone" : tactic

elab_rules : tactic
  | `(tactic| tmonotone) => proofModeMonotone

end

end Lentil.ProofMode
