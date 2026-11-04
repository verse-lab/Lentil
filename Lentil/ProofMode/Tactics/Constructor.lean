module

public import Lentil.ProofMode.Tactics.Exists
public import Lentil.ProofMode.Tactics.SplitAnds

namespace Lentil.ProofMode

open Lean Meta Elab Tactic

@[expose] public section

section

variable {σ : Type u} {hyps : List (NamedPred σ)}

-- NOTE: The binder names follow the fields of `And`, `Iff` and `Exists`, so the
-- goals created by `tconstructor` get the same tags as those of `constructor`.

theorem Entails_and_intro {a b : pred σ} (left : Entails hyps a) (right : Entails hyps b) :
    Entails hyps (tl_and a b) :=
  Entails_and_split.mpr ⟨left, right⟩

theorem Entails_iff_intro {a b : pred σ}
    (mp : Entails hyps (tl_implies a b)) (mpr : Entails hyps (tl_implies b a)) :
    Entails hyps (tl_iff a b) := by
  rw [Lentil.tl_iff_def] ; exact Entails_and_intro mp mpr

theorem Entails_exists_intro {α : Sort v} {p : α → pred σ} (w : α) (h : Entails hyps (p w)) :
    Entails hyps (tl_exists p) :=
  Entails_exists w h

end

end

public meta section

/--
`tconstructor` splits the proof-mode goal by the introduction rule of its
outermost connective, like Lean's `constructor`. It is the converse of
destructuring a temporal hypothesis with a tuple pattern of `trcases`.

* For `p ∧ q`, it creates the goals `p` and `q`.
* For `p ↔ q`, it creates the goals `p → q` and `q → p`.
* For `∃ x, p x`, it creates the goal `p ?w` for a metavariable witness `?w`,
  followed by a goal for `?w` itself. Assigning `?w` while proving `p ?w`, for
  example by `tassumption`, also closes the witness goal; `texists` supplies
  the witness upfront instead.

Unlike `tsplit_ands`, only the outermost conjunction is split.
-/
syntax (name := tlConstructorTac) "tconstructor" : tactic

elab_rules : tactic
  | `(tactic| tconstructor) => withMainContext do
    let g ← getMainGoal
    let target ← cleanupAnnotAndMore (← g.getType)
    let_expr Entails _ _ goal := target
      | throwError "tconstructor: goal is not a proof-mode Entails goal, but {target}"
    let thm ← match_expr goal with
      | Lentil.tl_and _ _ _ => pure ``Entails_and_intro
      | Lentil.tl_iff _ _ _ => pure ``Entails_iff_intro
      | Lentil.tl_exists _ _ _ => pure ``Entails_exists_intro
      | _ => throwError "tconstructor: goal predicate is not a ∧, ↔ or ∃; got {goal}"
    replaceMainGoal (← g.apply (← mkConstWithFreshMVarLevels thm))

end

end Lentil.ProofMode
