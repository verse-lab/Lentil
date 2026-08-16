import Lean
import Lentil.ProofMode.Basic
import Lentil.Tactics.Basic

open Lean

namespace TLA

/-!
This file implements a finite-window reduction for local TLA obligations.

The older `simp_finite_exec_goal` tactic unfolds a TLA formula on an explicit
trace, then tries to discover and generalize the finitely many trace cells that
remain. That is fragile: the tactic has to rediscover finite dependence from
the unfolded goal shape.

Here the finite dependence is part of the certificate. A `FiniteWindow p n`
contains a curried finite predicate `core` over exactly `n` states, together
with a theorem saying that evaluating `p` on a trace is equivalent to evaluating
`core` on the first `n` states of that trace. The tactic uses instance search to
find a sufficient `HasWindowApprox p n`, applies the certificate theorem,
introduces the `n` state variables, and simplifies the resulting `core`. Exact
`HasFiniteWindow` certificates lift to both approximation directions, while
temporal hypotheses such as `□p` can provide only a necessary approximation.

For sequents, `tfinite_window` first changes `p |-tla- q` by definitional
equality into `|-tla- p → q`, so the rest of the pipeline only handles validity
goals.
-/

/-- A curried predicate over `n` consecutive states.

For example, `IteratedHomPred 2 σ` reduces to `σ → σ → ULift Prop`. The `ULift`
in the base case is deliberate: for universe-polymorphic `σ : Type u`, the
successor case lives in `Type u`, so the base proposition also has to be lifted
into `Type u`. The user-facing goals are later simplified through `.down`. -/
def IteratedHomPred : Nat → Type u → Type u
  | 0, _ => ULift.{u} Prop
  | n + 1, σ => σ → IteratedHomPred n σ

namespace IteratedHomPred

/-- Evaluate a curried finite predicate on `n` consecutive states of a trace,
starting at index `i`. -/
def evalExec {σ : Type u} : {n : Nat} → IteratedHomPred n σ → exec σ → Nat → Prop
  | 0, p, _, _ => p.down
  | _ + 1, p, e, i => evalExec (p (e i)) e (i + 1)

/-- View an `n`-state core as an `m`-state core when `n ≤ m`, ignoring the
additional trailing states. This is used to combine two formulas with different
window sizes into a common `max` window. -/
def weaken {σ : Type u} : {n m : Nat} → n ≤ m → IteratedHomPred n σ → IteratedHomPred m σ
  | 0, 0, _, p => p
  | 0, m + 1, _, p => fun _ => weaken (Nat.zero_le m) p
  | n + 1, 0, h, _ => False.elim (Nat.not_succ_le_zero n h)
  | _ + 1, _ + 1, h, p => fun s => weaken (Nat.le_of_succ_le_succ h) (p s)

/-- Weakening does not change how a core evaluates on any trace. -/
theorem evalExec_weaken {σ : Type u} :
    ∀ {n m : Nat} (h : n ≤ m) (p : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (weaken h p) e i ↔ evalExec p e i
  | 0, 0, _, _, _, _ => Iff.rfl
  | 0, m + 1, _, p, e, i => evalExec_weaken (Nat.zero_le m) p e (i + 1)
  | n + 1, 0, h, _, _, _ => False.elim (Nat.not_succ_le_zero n h)
  | _ + 1, _ + 1, h, p, e, i =>
    evalExec_weaken (Nat.le_of_succ_le_succ h) (p (e i)) e (i + 1)

/- Pointwise logical constructors for cores of the same width, with lemmas
describing their behavior under `evalExec`. Binary connectives and binders
share the same recursion shape, so the generic constructors below keep the
named logical constructors small. -/

def mkNot {σ : Type u} : {n : Nat} → IteratedHomPred n σ → IteratedHomPred n σ
  | 0, p => ULift.up (¬ p.down)
  | _ + 1, p => fun s => mkNot (p s)

theorem evalExec_mkNot {σ : Type u} :
    ∀ {n : Nat} (p : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkNot p) e i ↔ ¬ evalExec p e i
  | 0, _, _, _ => Iff.rfl
  | _ + 1, p, e, i => evalExec_mkNot (p (e i)) e (i + 1)

def mkBinary {σ : Type u} (op : Prop → Prop → Prop) :
    {n : Nat} → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ
  | 0, p, q => ULift.up (op p.down q.down)
  | _ + 1, p, q => fun s => mkBinary op (p s) (q s)

theorem evalExec_mkBinary {σ : Type u} (op : Prop → Prop → Prop) :
    ∀ {n : Nat} (p q : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkBinary op p q) e i ↔ op (evalExec p e i) (evalExec q e i)
  | 0, _, _, _, _ => Iff.rfl
  | _ + 1, p, q, e, i => evalExec_mkBinary op (p (e i)) (q (e i)) e (i + 1)

def mkAnd {σ : Type u} : {n : Nat} → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p ∧ q)

theorem evalExec_mkAnd {σ : Type u} :
    ∀ {n : Nat} (p q : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkAnd p q) e i ↔ evalExec p e i ∧ evalExec q e i :=
  evalExec_mkBinary (fun p q => p ∧ q)

def mkOr {σ : Type u} : {n : Nat} → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p ∨ q)

theorem evalExec_mkOr {σ : Type u} :
    ∀ {n : Nat} (p q : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkOr p q) e i ↔ evalExec p e i ∨ evalExec q e i :=
  evalExec_mkBinary (fun p q => p ∨ q)

def mkImplies {σ : Type u} : {n : Nat} → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p → q)

theorem evalExec_mkImplies {σ : Type u} :
    ∀ {n : Nat} (p q : IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkImplies p q) e i ↔ (evalExec p e i → evalExec q e i) :=
  evalExec_mkBinary (fun p q => p → q)

def mkBinder {σ : Type u} {α : Sort v} (op : (α → Prop) → Prop) :
    {n : Nat} → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ
  | 0, p => ULift.up (op fun x => (p x).down)
  | _ + 1, p => fun s => mkBinder op (fun x => p x s)

theorem evalExec_mkBinder {σ : Type u} {α : Sort v} (op : (α → Prop) → Prop) :
    ∀ {n : Nat} (p : α → IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkBinder op p) e i ↔ op (fun x => evalExec (p x) e i)
  | 0, _, _, _ => Iff.rfl
  | _ + 1, p, e, i => evalExec_mkBinder op (fun x => p x (e i)) e (i + 1)

def mkForall {σ : Type u} {α : Sort v} : {n : Nat} → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ :=
  mkBinder (fun p => ∀ x, p x)

theorem evalExec_mkForall {σ : Type u} {α : Sort v} :
    ∀ {n : Nat} (p : α → IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkForall p) e i ↔ ∀ x, evalExec (p x) e i :=
  evalExec_mkBinder (fun p => ∀ x, p x)

def mkExists {σ : Type u} {α : Sort v} : {n : Nat} → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ :=
  mkBinder (fun p => ∃ x, p x)

theorem evalExec_mkExists {σ : Type u} {α : Sort v} :
    ∀ {n : Nat} (p : α → IteratedHomPred n σ) (e : exec σ),
      ∀ i, evalExec (mkExists p) e i ↔ ∃ x, evalExec (p x) e i :=
  evalExec_mkBinder (fun p => ∃ x, p x)

end IteratedHomPred

/-- Universal closure of a finite core over all its state arguments. -/
def IteratedForall {σ : Type u} : {n : Nat} → IteratedHomPred n σ → Prop
  | 0, p => p.down
  | _ + 1, p => ∀ s, IteratedForall (p s)

/-- A universally closed finite core holds on every `n`-state window of every
trace. -/
theorem IteratedForall.evalExec {σ : Type u} :
    ∀ {n : Nat} {p : IteratedHomPred n σ}, IteratedForall p →
      ∀ e i, IteratedHomPred.evalExec p e i
  | 0, _, h, _, _ => h
  | _ + 1, _, h, e, i => IteratedForall.evalExec (h (e i)) e (i + 1)

/-- The relationship between a finite core and its temporal formula. -/
inductive ApproxDir where
  /-- The core characterizes the formula exactly. -/
  | exact
  /-- The core is strong enough to prove the formula. -/
  | sufficient
  /-- The formula implies the core. -/
  | necessary

namespace ApproxDir

/-- The semantic guarantee carried by a window approximation.

`exact` identifies the formula with its finite core, `sufficient` makes the
core strong enough to prove the formula, and `necessary` records only what the
formula implies about the finite core. -/
def Sound (dir : ApproxDir) (core formula : Prop) : Prop :=
  match dir with
  | .exact => formula ↔ core
  | .sufficient => core → formula
  | .necessary => formula → core

/-- Negation and implication antecedents reverse one-way polarity while exact
certificates remain exact. -/
abbrev flip : ApproxDir → ApproxDir
  | .exact => .exact
  | .sufficient => .necessary
  | .necessary => .sufficient

end ApproxDir

/-- `WindowApprox dir p n` represents `p` by a predicate over the first `n`
states of a trace, with the guarantee selected by `dir`.

An exact approximation characterizes `p`; a sufficient approximation can be
used to prove `p`; and a necessary approximation records finite information
that follows from `p`.  The latter two directions let `tfinite_window` use
temporal formulas such as `□p` in hypotheses without claiming that they are
determined by a finite trace prefix. -/
structure WindowApprox {σ : Type u} (dir : ApproxDir) (p : pred σ) (n : Nat) where
  core : IteratedHomPred n σ
  sound : ∀ e i, dir.Sound (IteratedHomPred.evalExec core e i) (p e i)

/-- A computable family of directional finite-window approximations, indexed
by the enclosing window size.

The minimum window is an output parameter so instance synthesis can compute a
canonical bound for `p`.  `tfinite_window` uses the resulting finite core to
produce the finite-state goal. -/
class HasWindowApprox {σ : Type u} (dir : ApproxDir) (p : pred σ)
    (min : outParam Nat) where
  /-- An approximation scheme rather than one fixed certificate: for each
  concrete enclosing window `w` above `min`, `build w` computes an approximation
  specialized to `w`.

  The result may use the additional states instead of merely weakening a
  smaller core and ignoring them.  This allows connectives to choose one common
  window for their subformulas and lets `□p`, for example, expose a longer
  finite prefix when the enclosing obligation has a larger window. -/
  build : ∀ w, min ≤ w → WindowApprox dir p w

/-- `FiniteWindow p n` means that `p` can be represented exactly as a predicate
over the first `n` states of a trace. -/
abbrev FiniteWindow {σ : Type u} (p : pred σ) (n : Nat) :=
  WindowApprox .exact p n

/-- A computable exact finite-window certificate.

The window is an output parameter so that instance synthesis can compute a
canonical bound for `p`.  The certificate itself is data, because
`tfinite_window` uses its `core` field to produce the finite-state goal. -/
abbrev HasFiniteWindow {σ : Type u} (p : pred σ) (n : outParam Nat) :=
  HasWindowApprox .exact p n

theorem FiniteWindow.iff_of_eval {σ : Type u} {p : pred σ} {n : Nat}
    (h : FiniteWindow p n) (e : exec σ) (i : Nat) :
    p e i ↔ IteratedHomPred.evalExec h.core e i :=
  h.sound e i

/-- Enlarge an exact certificate without changing its meaning. -/
def FiniteWindow.weaken {σ : Type u} {p : pred σ} {n w : Nat}
    (hp : FiniteWindow p n) (h : n ≤ w) : FiniteWindow p w where
  core := IteratedHomPred.weaken h hp.core
  sound := by
    intro e i
    rw [IteratedHomPred.evalExec_weaken]
    exact hp.iff_of_eval e i

def FiniteWindow.toSufficient {σ : Type u} {p : pred σ} {w : Nat}
    (hp : FiniteWindow p w) : WindowApprox .sufficient p w where
  core := hp.core
  sound := by
    intro e i he
    exact (FiniteWindow.iff_of_eval hp e i).mpr he

def FiniteWindow.toNecessary {σ : Type u} {p : pred σ} {w : Nat}
    (hp : FiniteWindow p w) : WindowApprox .necessary p w where
  core := hp.core
  sound := by
    intro e i he
    exact (FiniteWindow.iff_of_eval hp e i).mp he

-- Try exact ones first when synthesizing for sufficient or necessary approximations
instance (priority := default + 100) hasWindowApproxSufficientOfFinite
    {σ : Type u} (p : pred σ) (n : Nat) [hp : HasFiniteWindow p n] :
    HasWindowApprox .sufficient p n where
  build w h := FiniteWindow.toSufficient (hp.build w h)

instance (priority := default + 100) hasWindowApproxNecessaryOfFinite
    {σ : Type u} (p : pred σ) (n : Nat) [hp : HasFiniteWindow p n] :
    HasWindowApprox .necessary p n where
  build w h := FiniteWindow.toNecessary (hp.build w h)

/-- Extract the canonical exact certificate from the unified class. -/
def finiteWindowOfHasFiniteWindow {σ : Type u} {p : pred σ} {n : Nat}
    [h : HasFiniteWindow p n] : FiniteWindow p n :=
  h.build n (Nat.le_refl n)

/-- If an exact finite core holds for every choice of its state arguments, then
the predicate it represents is valid. -/
theorem FiniteWindow.valid_of_forall {σ : Type u} {p : pred σ} {n : Nat}
    (h : FiniteWindow p n) : IteratedForall h.core → valid p := by
  intro hcore e i
  exact (h.iff_of_eval e i).mpr (IteratedForall.evalExec hcore e i)

theorem HasFiniteWindow.valid_of_forall {σ : Type u} {p : pred σ} {n : Nat}
    [h : HasFiniteWindow p n] :
    IteratedForall (h.build n (Nat.le_refl n)).core → valid p :=
  fun hcore e i => FiniteWindow.iff_of_eval (h.build n (Nat.le_refl n)) e i |>.mpr
    (IteratedForall.evalExec hcore e i)

section FiniteWindowInstances

def finiteWindowPure {σ : Type u} (P : Prop) : FiniteWindow (pure_pred (α := σ) P) 0 where
  core := ULift.up P
  sound := by simp [ApproxDir.Sound, pure_pred, state_pred, IteratedHomPred.evalExec]

instance hasFiniteWindowPure {σ : Type u} (P : Prop) : HasFiniteWindow (pure_pred (α := σ) P) 0 where
  build _ h := (finiteWindowPure P).weaken h

instance hasFiniteWindowTrue {σ : Type u} : HasFiniteWindow (tla_true (α := σ)) 0 :=
  hasFiniteWindowPure True

instance hasFiniteWindowFalse {σ : Type u} : HasFiniteWindow (tla_false (α := σ)) 0 :=
  hasFiniteWindowPure False

def finiteWindowState {σ : Type u} (p : σ → Prop) : FiniteWindow (state_pred p) 1 where
  core := fun s => ULift.up (p s)
  sound := by simp [ApproxDir.Sound, state_pred, IteratedHomPred.evalExec]

instance hasFiniteWindowState {σ : Type u} (p : σ → Prop) : HasFiniteWindow (state_pred p) 1 where
  build _ h := (finiteWindowState p).weaken h

def finiteWindowAction {σ : Type u} (a : action σ) : FiniteWindow (action_pred a) 2 where
  core := fun s s' => ULift.up (a s s')
  sound := by simp [ApproxDir.Sound, action_pred, IteratedHomPred.evalExec]

instance hasFiniteWindowAction {σ : Type u} (a : action σ) : HasFiniteWindow (action_pred a) 2 where
  build _ h := (finiteWindowAction a).weaken h

def finiteWindowEnabled {σ : Type u} (a : action σ) : FiniteWindow (tla_enabled a) 1 :=
  finiteWindowState (enabled a)

instance hasFiniteWindowEnabled {σ : Type u} (a : action σ) : HasFiniteWindow (tla_enabled a) 1 where
  build _ h := (finiteWindowEnabled a).weaken h

end FiniteWindowInstances

/-! Directional instances. Temporal formulas need not have exact certificates:
in particular, `□p` has a necessary approximation, suitable for a hypothesis,
but no sufficient approximation, which would be unsound for a finite prefix. -/

theorem WindowApprox.valid_of_forall_sufficient {σ : Type u} {p : pred σ} {n : Nat}
    (h : WindowApprox .sufficient p n) : IteratedForall h.core → valid p := by
  intro hcore e i
  exact h.sound e i (IteratedForall.evalExec hcore e i)

/-- Soundness theorem used by `tfinite_window` for directional certificates. -/
theorem HasWindowApprox.valid_of_forall_sufficient {σ : Type u} {p : pred σ} {n : Nat}
    [h : HasWindowApprox .sufficient p n] :
    IteratedForall (h.build n (Nat.le_refl n)).core → valid p :=
  (h.build n (Nat.le_refl n)).valid_of_forall_sufficient

/-! Polarity-generic propositional constructors.  The same definitions cover
exact, sufficient, and necessary certificates; `grind` discharges the three
small propositional cases after the direction is exposed. -/

section WindowApproxInstances

/-- Combine two approximations of the same direction using a connective that
is monotone in both arguments. -/
def WindowApprox.binary {σ : Type u} {dir : ApproxDir} {p q : pred σ} {w : Nat}
    (op : Prop → Prop → Prop)
    (op_mono : ∀ {p p' q q' : Prop}, (p → p') → (q → q') → op p q → op p' q')
    (hp : WindowApprox dir p w) (hq : WindowApprox dir q w) :
    WindowApprox dir (fun e i => op (p e i) (q e i)) w where
  core := IteratedHomPred.mkBinary op hp.core hq.core
  sound := by
    intro e i
    rw [IteratedHomPred.evalExec_mkBinary]
    have hps := hp.sound e i
    have hqs := hq.sound e i
    cases dir <;> simp only [ApproxDir.Sound] at hps hqs ⊢ <;> grind

def WindowApprox.and {σ : Type u} {dir : ApproxDir} {p q : pred σ} {w : Nat}
    (hp : WindowApprox dir p w) (hq : WindowApprox dir q w) :
    WindowApprox dir (tla_and p q) w :=
  WindowApprox.binary (fun p q => p ∧ q) (by grind) hp hq

def WindowApprox.or {σ : Type u} {dir : ApproxDir} {p q : pred σ} {w : Nat}
    (hp : WindowApprox dir p w) (hq : WindowApprox dir q w) :
    WindowApprox dir (tla_or p q) w :=
  WindowApprox.binary (fun p q => p ∨ q) (by grind) hp hq

/-- Combine a uniformly sized family of approximations of the same direction
using a monotone binder. -/
def WindowApprox.binder {σ : Type u} {α : Sort v} {dir : ApproxDir}
    (op : (α → Prop) → Prop)
    (op_mono : ∀ {p q : α → Prop}, (∀ x, p x → q x) → op p → op q)
    {p : α → pred σ} {w : Nat} (hp : ∀ x, WindowApprox dir (p x) w) :
    WindowApprox dir (fun e i => op (fun x => p x e i)) w where
  core := IteratedHomPred.mkBinder op (fun x => (hp x).core)
  sound := by
    intro e i
    rw [IteratedHomPred.evalExec_mkBinder]
    have hps := fun x => (hp x).sound e i
    cases dir <;> simp only [ApproxDir.Sound] at hps ⊢ <;> grind

def WindowApprox.not {σ : Type u} {dir : ApproxDir} {p : pred σ} {w : Nat}
    (hp : WindowApprox dir.flip p w) : WindowApprox dir (tla_not p) w where
  core := IteratedHomPred.mkNot hp.core
  sound := by
    intro e i
    rw [IteratedHomPred.evalExec_mkNot]
    have hps := hp.sound e i
    cases dir <;>
      simp only [ApproxDir.flip, ApproxDir.Sound, tla_not] at hps ⊢ <;> grind

def WindowApprox.implies {σ : Type u} {dir : ApproxDir} {p q : pred σ} {w : Nat}
    (hp : WindowApprox dir.flip p w) (hq : WindowApprox dir q w) :
    WindowApprox dir (tla_implies p q) w where
  core := IteratedHomPred.mkImplies hp.core hq.core
  sound := by
    intro e i
    rw [IteratedHomPred.evalExec_mkImplies]
    have hps := hp.sound e i
    have hqs := hq.sound e i
    cases dir <;>
      simp only [ApproxDir.flip, ApproxDir.Sound, tla_implies] at hps hqs ⊢ <;> grind

def WindowApprox.later {σ : Type u} {dir : ApproxDir} {p : pred σ} {w : Nat}
    (hp : WindowApprox dir p w) : WindowApprox dir (TLA.later p) (w + 1) where
  core := fun _ => hp.core
  sound := by
    intro e i
    cases dir <;>
      simpa [ApproxDir.Sound, TLA.later, IteratedHomPred.evalExec] using hp.sound e (i + 1)

instance hasWindowApproxAnd {σ : Type u} {dir : ApproxDir} (p q : pred σ) (n m : Nat)
    [hp : HasWindowApprox dir p n] [hq : HasWindowApprox dir q m] :
    HasWindowApprox dir (tla_and p q) (max n m) where
  build w h := WindowApprox.and
    (hp.build w (Nat.le_trans (Nat.le_max_left n m) h))
    (hq.build w (Nat.le_trans (Nat.le_max_right n m) h))

instance hasWindowApproxOr {σ : Type u} {dir : ApproxDir} (p q : pred σ) (n m : Nat)
    [hp : HasWindowApprox dir p n] [hq : HasWindowApprox dir q m] :
    HasWindowApprox dir (tla_or p q) (max n m) where
  build w h := WindowApprox.or
    (hp.build w (Nat.le_trans (Nat.le_max_left n m) h))
    (hq.build w (Nat.le_trans (Nat.le_max_right n m) h))

instance hasWindowApproxForall {σ : Type u} {α : Sort v} {dir : ApproxDir}
    (p : α → pred σ) (n : Nat) [hp : ∀ x, HasWindowApprox dir (p x) n] :
    HasWindowApprox dir (tla_forall p) n where
  build w h := WindowApprox.binder (fun r => ∀ x, r x)
    (by grind) (fun x => (hp x).build w h)

instance hasWindowApproxExists {σ : Type u} {α : Sort v} {dir : ApproxDir}
    (p : α → pred σ) (n : Nat) [hp : ∀ x, HasWindowApprox dir (p x) n] :
    HasWindowApprox dir (tla_exists p) n where
  build w h := WindowApprox.binder (fun r => ∃ x, r x)
    (by grind) (fun x => (hp x).build w h)

instance hasWindowApproxNot {σ : Type u} {dir : ApproxDir} (p : pred σ) (n : Nat)
    [hp : HasWindowApprox dir.flip p n] : HasWindowApprox dir (tla_not p) n where
  build w h := WindowApprox.not (hp.build w h)

instance hasWindowApproxImplies {σ : Type u} {dir : ApproxDir}
    (p q : pred σ) (n m : Nat)
    [hp : HasWindowApprox dir.flip p n] [hq : HasWindowApprox dir q m] :
    HasWindowApprox dir (tla_implies p q) (max n m) where
  build w h := WindowApprox.implies
    (hp.build w (Nat.le_trans (Nat.le_max_left n m) h))
    (hq.build w (Nat.le_trans (Nat.le_max_right n m) h))

def windowApproxLater {σ : Type u} {dir : ApproxDir} {p : pred σ} {n : Nat}
    (hp : HasWindowApprox dir p n) :
    ∀ w, n + 1 ≤ w → WindowApprox dir (later p) w
  | 0, h => False.elim (by omega)
  | w + 1, h => (hp.build w (by omega)).later

instance hasWindowApproxLater {σ : Type u} {dir : ApproxDir} (p : pred σ) (n : Nat)
    [hp : HasWindowApprox dir p n] : HasWindowApprox dir (later p) (n + 1) where
  build w h := windowApproxLater hp w h

namespace IteratedHomPred

/-- Tile an `n`-state core across the current state and the next `k` states,
producing the core for `p ∧ ◯p ∧ ⋯ ∧ ◯^[k]p`.

The last copy of `p` starts `k` states later, so the resulting core observes
`n + k` states.  For example, if `p` is a state predicate, depth `2` produces
the three-state core `p s₀ ∧ p s₁ ∧ p s₂`. -/
def tile {σ : Type u} {n : Nat} (core : IteratedHomPred n σ) :
    (k : Nat) → IteratedHomPred (n + k) σ
  | 0 => core
  | k + 1 =>
      mkAnd
        (weaken (by omega) core)
        (fun _ => tile core k)

theorem evalExec_tile {σ : Type u} {p : pred σ} {n : Nat}
    (hp : FiniteWindow p n) : ∀ (k : Nat) (e : exec σ) (i : Nat),
    evalExec (tile hp.core k) e i ↔ alwaysPrefix p k e i
  | 0, e, i => by
      simpa [alwaysPrefix, tile] using (FiniteWindow.iff_of_eval hp e i).symm
  | k + 1, e, i => by
      rw [alwaysPrefix]
      simp only [tla_and, later]
      rw [tile, evalExec_mkAnd, evalExec_weaken]
      rw [FiniteWindow.iff_of_eval hp e]
      exact and_congr Iff.rfl (evalExec_tile hp k e (i + 1))

end IteratedHomPred

/-- The prefix of depth `k` occupies the body's window followed by `k`
additional states. -/
def finiteWindowAlwaysPrefix {σ : Type u} {p : pred σ} {n : Nat}
    (hp : FiniteWindow p n) (k : Nat) : FiniteWindow (alwaysPrefix p k) (n + k) where
  core := IteratedHomPred.tile hp.core k
  sound e i := (IteratedHomPred.evalExec_tile hp k e i).symm

/-- `□p` is safe in necessary polarity: at an enclosing width `w`, weaken it
to the finite prefix of depth `w - n`, where `n` is the exact width of `p`. -/
instance (priority := default + 100) hasWindowApproxNecessaryAlways {σ : Type u} (p : pred σ) (n : Nat)
    [HasFiniteWindow p n] : HasWindowApprox .necessary (always p) n where
  build w h :=
    let hp : FiniteWindow p n := finiteWindowOfHasFiniteWindow
    let hprefix : FiniteWindow (alwaysPrefix p (w - n)) w :=
      (finiteWindowAlwaysPrefix hp (w - n)).weaken (by omega)
    {
      core := hprefix.core
      sound := by
        intro e i halways
        apply (hprefix.iff_of_eval e i).mp
        exact always_weaken_n (p := p) (w - n) e i halways
    }

/-- Reuse a necessary approximation of `p` for `□p`, retaining the consequence
available at the current suffix. -/
def WindowApprox.ofAlways {σ : Type u} {p : pred σ} {w : Nat}
    (hp : WindowApprox .necessary p w) :
    WindowApprox .necessary (always p) w where
  core := hp.core
  sound := fun e i halways => hp.sound e i (always_weaken (p := p) e i halways)

/-- Add the current-suffix approximation of `p` to an approximation of `□p`
on the next suffix, producing the next wider approximation of `□p`. -/
def WindowApprox.alwaysCons {σ : Type u} {p : pred σ} {w : Nat}
    (hp : WindowApprox .necessary p (w + 1))
    (htail : WindowApprox .necessary (always p) w) :
    WindowApprox .necessary (always p) (w + 1) :=
  let hstep := WindowApprox.and hp htail.later
  {
    core := hstep.core
    sound := by
      intro e i halways
      apply hstep.sound e i
      rw [← always_unroll]
      exact halways
  }

-- NOTE: Recursing on `w - n` would be shorter, but transporting the resulting
-- `n + (w - n)`-wide core back to width `w` leaves a dependent `cast` in the
-- generated core, preventing `tfinite_window` from simplifying it reliably.
/-- Tile a necessary approximation scheme over every suffix which has at least
its minimum window left, rebuilding the approximation at each remaining width. -/
def HasWindowApprox.tile {σ : Type u} {p : pred σ} {n : Nat}
    (hp : HasWindowApprox .necessary p n) :
    ∀ w, n ≤ w → WindowApprox .necessary (always p) w
  | 0, h => (hp.build 0 h).ofAlways
  | w + 1, h =>
      if hn : n = w + 1 then
        (hp.build (w + 1) h).ofAlways
      else
        WindowApprox.alwaysCons
          (hp.build (w + 1) h)
          (HasWindowApprox.tile hp w (by omega))

instance hasWindowApproxNecessaryAlwaysOfApprox {σ : Type u} (p : pred σ) (n : Nat)
    [hp : HasWindowApprox .necessary p n] :
    HasWindowApprox .necessary (always p) n where
  build w h := hp.tile w h

/-- Interpret a sufficient approximation of `¬□¬p` as one of `◇p`.  The core
is unchanged; only its semantic guarantee is transported across the duality. -/
def WindowApprox.eventuallyOfDual {σ : Type u} {p : pred σ} {w : Nat}
    (hp : WindowApprox .sufficient (tla_not (always (tla_not p))) w) :
    WindowApprox .sufficient (eventually p) w where
  core := hp.core
  sound := by
    intro e hcore
    rw [eventually_to_always]
    exact hp.sound e hcore

-- NOTE: `eventuallyOfDual` performs only the final duality conversion for one
-- concrete window.  The instance below is the typeclass-facing interface, so
-- it exposes the natural premise `HasWindowApprox .sufficient p n` and builds
-- the intermediate `¬p`, `□¬p`, and `¬□¬p` approximations internally.
/-- A sufficient approximation of `◇p` is the dual of the necessary
approximation of `□¬p`. -/
instance hasWindowApproxSufficientEventually {σ : Type u} (p : pred σ) (n : Nat)
    [hp : HasWindowApprox .sufficient p n] :
    HasWindowApprox .sufficient (eventually p) n where
  build w h :=
    let hnot : HasWindowApprox .necessary (tla_not p) n :=
      { build := fun w h => WindowApprox.not (dir := .necessary) (hp.build w h) }
    (WindowApprox.not (dir := .sufficient) (hnot.tile w h)).eventuallyOfDual

-- Typeclass search does not unfold the `⇒` wrapper while matching instance
-- heads, so expose its underlying `□(p → q)` necessary approximation explicitly.
instance hasWindowApproxNecessaryAlwaysImplies {σ : Type u} (p q : pred σ) (n : Nat)
    [hpq : HasWindowApprox .necessary (tla_implies p q) n] :
    HasWindowApprox .necessary (always_implies p q) n where
  build w h := hpq.tile w h

end WindowApproxInstances

attribute [tla_finite_window_def]
  Nat.max_def Nat.reduceAdd Nat.reduceSub Nat.reduceEqDiff Nat.reduceLeDiff
  IteratedForall
  finiteWindowOfHasFiniteWindow
  hasFiniteWindowPure hasFiniteWindowTrue hasFiniteWindowFalse
  hasFiniteWindowState hasFiniteWindowAction hasFiniteWindowEnabled
  finiteWindowPure
  finiteWindowState finiteWindowAction finiteWindowEnabled
  ApproxDir.Sound ApproxDir.flip
  FiniteWindow.weaken FiniteWindow.toSufficient FiniteWindow.toNecessary
  hasWindowApproxSufficientOfFinite hasWindowApproxNecessaryOfFinite
  WindowApprox.binary WindowApprox.binder
  WindowApprox.and WindowApprox.or WindowApprox.not
  WindowApprox.implies WindowApprox.later
  hasWindowApproxAnd hasWindowApproxOr
  hasWindowApproxForall hasWindowApproxExists hasWindowApproxNot
  hasWindowApproxImplies windowApproxLater hasWindowApproxLater
  finiteWindowAlwaysPrefix IteratedHomPred.tile
  hasWindowApproxNecessaryAlways
  WindowApprox.ofAlways WindowApprox.alwaysCons
  HasWindowApprox.tile hasWindowApproxNecessaryAlwaysOfApprox
  WindowApprox.eventuallyOfDual hasWindowApproxSufficientEventually
  hasWindowApproxNecessaryAlwaysImplies
  IteratedHomPred.weaken IteratedHomPred.mkAnd
  IteratedHomPred.mkOr IteratedHomPred.mkNot
  IteratedHomPred.mkImplies IteratedHomPred.mkBinary
  IteratedHomPred.mkForall IteratedHomPred.mkExists
  IteratedHomPred.mkBinder

attribute [tla_finite_window_def ↓] dreduceIte dreduceDIte reduceIte reduceDIte

open Elab Tactic Meta

private def sufficientWindowApproxOf (p : Expr) : MetaM (Expr × Nat) := do
  let win ← mkFreshExprMVar (some (mkConst ``Nat))
  let instTy ← mkAppM ``HasWindowApprox #[mkConst ``ApproxDir.sufficient, p, win]
  let inst ←
    try synthInstance instTy
    catch _ => throwError "tfinite_window: failed to synthesize a sufficient finite-window approximation for {p}"
  let win ← instantiateMVars win
  let win ← withTransparency .all <| whnf win
  let some n ← (Lean.Meta.evalNat win).run
    | throwError "tfinite_window: synthesized finite window did not reduce to a numeral: {win}"
  return (inst, n)

private def introFiniteStates (n : Nat) : TacticM Unit := do
  let g ← getMainGoal
  let names := (List.range n).map stateName
  let (_, g') ← liftMetaM <| g.introN n names
  replaceMainGoal [g']
where
  stateName (idx : Nat) : Name :=
    Name.mkSimple <| "s" ++ String.ofList (List.replicate idx '\'')

private def changeProofModeEntailsToValidRepeatedImplies : TacticM (List Name) := withMainContext do
  let g ← getMainGoal
  let target ← ProofMode.cleanupAnnotAndMore (← g.getType)
  let some (_, hypsExpr, _, hyps, goal) ← ProofMode.recognizeCanonicalEntails target
    | return []
  let thm ← mkAppOptM ``TLA.ProofMode.Entails_of_valid_repeatedImplies
    #[none, some hypsExpr, some goal]
  let gs ← g.apply thm
  let [g] := gs
    | throwError "tfinite_window: unexpected number of goals after converting proof-mode Entails goal (got {gs.length}, expected 1)"
  replaceMainGoal [g]
  let implicationChain ← hyps.foldrM (init := goal) fun (_, hyp) acc =>
    mkAppM ``TLA.tla_implies #[hyp, acc]
  let newTarget ← mkAppM ``TLA.valid #[implicationChain]
  let g ← getMainGoal
  replaceMainGoal [← g.change newTarget]
  return hyps.map fun (name, _) => Name.mkSimple name

/--
Reduce a TLA obligation whose proof only needs a bounded execution prefix to an
ordinary Lean proposition over explicit states.

The tactic accepts validity goals (`|-tla- p`), sequents (`p |-tla- q`), and
proof-mode `Entails` goals.  It computes one finite window for the whole
obligation, introduces its states as `s`, `s'`, `s''`, and so on, and leaves the
resulting non-temporal proposition for subsequent tactics to prove.  For
example, it turns

```lean
(⌜ inv ⌝ ∧ ⟨next⟩) |-tla- (◯ ⌜ inv ⌝)
```

into a goal of the following shape:

```lean
s s' : σ
⊢ inv s ∧ next s s' → inv s'
```

“Needs a bounded execution prefix” refers to the obligation as a whole, not to
every temporal formula appearing in it.  State predicates observe one state,
action predicates observe two, and each `◯` shifts the required window by one.
An assumption such as `□p` may be used through all copies of `p` that fall
inside the selected window.  Dually, a conclusion such as `◇p` may be proved by
a witness within that window.

The tactic fails when the requested direction cannot be justified by any finite
prefix.  In particular, a positive `□p` cannot be proved from a finite prefix,
and an assumed `◇p` does not provide a uniformly bounded witness.  Additional
predicate forms can be supported by defining suitable `HasFiniteWindow` or
directional `HasWindowApprox` instances.
-/
elab "tfinite_window" : tactic => withMainContext do
  let proofModeHypNames ← changeProofModeEntailsToValidRepeatedImplies
  -- Work only with validity goals. Sequents are definitional aliases for
  -- validity of temporal implication.
  changePredImpliesToValid
  -- Instance search computes the canonical minimum window. The directional
  -- certificate is then built at that common enclosing width.
  let (inst, n) ← withMainContext do
    let target ← getMainTarget
    let target := target.headBeta.cleanupAnnotations
    match_expr target with
    | TLA.valid _ p => sufficientWindowApproxOf p
    | _ => throwError "tfinite_window: goal is not a TLA validity goal, but {target}"
  -- Replace the temporal goal by the finite core obligation, then expose the
  -- core as ordinary state variables.
  -- Apply at the meta level to avoid synthesizing instance twice
  let thm ← mkAppOptM ``HasWindowApprox.valid_of_forall_sufficient
    #[none, none, none, some inst]
  let g ← getMainGoal
  let gs ← g.apply thm
  let [g] := gs | throwError "tfinite_window: unexpected number of goals after applying finite-window validity theorem (got {gs.length}, expected 1)"
  replaceMainGoal [g]
  introFiniteStates n
  -- The core still contains the instance constructors and computed `max` widths;
  -- reducing them produces the expected first-order state predicate goal.
  withMainContext do evalTactic <| ← `(tactic| dsimp +$(mkIdent `instances) -$(mkIdent `failIfUnchanged) only [$(mkIdent `tla_finite_window_def):ident])
  unless proofModeHypNames.isEmpty do
    let g ← getMainGoal
    let (_, g') ← liftMetaM <| g.introN proofModeHypNames.length proofModeHypNames
    replaceMainGoal [g']

end TLA
