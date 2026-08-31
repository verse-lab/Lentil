import Lentil

/- Tests for `tcoalesce_to_ptl`. -/

namespace Lentil.ProofMode.Test.CoalesceToPTL

open Lentil Lentil.ProofMode

variable {σ : Type u}

example (P : σ → Prop) : (⌜ P ⌝) |-tl- (⌜ P ⌝) := by
  tcoalesce_to_ptl
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (P Q : σ → Prop) : (□ ⌜ P ⌝ ∧ □ ⌜ Q ⌝) |-tl- (□ ⌜ P ⌝) := by
  tstart hP hQ
  tcoalesce_to_ptl
  rename_i p
  guard_target =ₛ
    Entails [⟨"hP", [tlfml| □ p]⟩, ⟨"hQ", [tlfml| □ ptlAtom]⟩] [tlfml| □ p]
  tmonotone
  tassumption

example (P : σ → Prop) : (□ ⌜ P ⌝) |-tl- (⌜ P ⌝) := by
  tstart hP
  tcoalesce_to_ptl
  guard_target =ₐ Entails [⟨"hP", [tlfml| □ ptlAtom]⟩] ptlAtom
  ttoggle_goal_under_always
  tmonotone
  tassumption

example (P : σ → Prop) : (⌜ P ⌝) |-tl- (◯ ⌜ P ⌝ → ◇ ⌜ P ⌝) := by
  tcoalesce_to_ptl
  guard_target =ₛ ((ptlAtom) |-tl- (◯ ptlAtom → ◇ ptlAtom))
  tstart hP ; tapply' later_weaken_to_eventually

example (P Q : σ → Prop) : (⌜ P ⌝ 𝑈 ⌜ Q ⌝) |-tl- (⌜ P ⌝ 𝑈 ⌜ Q ⌝) := by
  tcoalesce_to_ptl
  rename_i p
  guard_target =ₛ ((p 𝑈 ptlAtom) |-tl- (p 𝑈 ptlAtom))
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, ⌜ P x ⌝) |-tl- (∀ x, ⌜ P x ⌝) := by
  tcoalesce_to_ptl
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, ⌜ P x ⌝) |-tl- (∀ x, ⌜ P x ⌝) := by
  tcoalesce_to_ptl (binders := .ignore)
  guard_target = ((∀ x, ptlAtom x) |-tl- (∀ x, ptlAtom x))
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, □ ⌜ P x ⌝) |-tl- (∀ x, □ ⌜ P x ⌝) := by
  tcoalesce_to_ptl (binders := .ignore)
  guard_target =ₛ ((∀ x, □ ptlAtom x) |-tl- (∀ x, □ ptlAtom x))
  exact pred_implies_refl _

example {α : Type v} (P : α → σ → Prop) :
    (∀ x, □ ⌜ P x ⌝) |-tl- (∀ y, □ ⌜ P y ⌝) := by
  tcoalesce_to_ptl (binders := .ignore)
  guard_target =ₛ ((∀ x, □ ptlAtom x) |-tl- (∀ y, □ ptlAtom y))
  exact pred_implies_refl _

example {α : Type v} (P Q : α → σ → Prop) :
    (∀ x, □ (⌜ P x ⌝ ∧ ⌜ Q x ⌝)) |-tl- (∀ x, □ ⌜ P x ⌝) := by
  tcoalesce_to_ptl (binders := .ignore)
  rename_i atomP
  guard_target =ₐ
    ((∀ x, □ (atomP x ∧ ptlAtom x)) |-tl- (∀ x, □ atomP x))
  tstart h ; tsimp only [always_and] at h ; tintro x ; tapply Lentil.and_left ; tapply h x

example (a : action σ) : (𝒲ℱ a) |-tl- (𝒲ℱ a) := by
  tcoalesce_to_ptl (abstractOpaque := true)
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (P Q : σ → Prop) : (⌜ P ⌝ ↝ ⌜ Q ⌝) |-tl- (⌜ P ⌝ ↝ ⌜ Q ⌝) := by
  tcoalesce_to_ptl (abstractOpaque := true)
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (P Q : σ → Prop) : (⌜ P ⌝ ⇒ ⌜ Q ⌝) |-tl- (⌜ P ⌝ ⇒ ⌜ Q ⌝) := by
  tcoalesce_to_ptl (abstractOpaque := true)
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tl- (p) := by
  tcoalesce_to_ptl (abstractOpaque := true)
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tl- (p) := by
  tcoalesce_to_ptl (level := .formula)
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example (P Q : σ → Prop) :
    (□ (⌜ P ⌝ ∧ ⌜ Q ⌝)) |-tl- (□ (⌜ P ⌝ ∧ ⌜ Q ⌝)) := by
  tcoalesce_to_ptl (level := .modal)
  guard_target =ₛ ((□ ptlAtom) |-tl- (□ ptlAtom))
  exact pred_implies_refl _

example (p : pred σ) : (p) |-tl- (p) := by
  tcoalesce_to_ptl (config := { level := .formula : CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

section ConfigMatrix

variable {α : Type v} (P : α → σ → Prop) (p : pred σ)

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .leaves, abstractOpaque := false :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .leaves, abstractOpaque := true :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .modal, abstractOpaque := false :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .modal, abstractOpaque := true :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .formula, abstractOpaque := false :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .block, level := .formula, abstractOpaque := true :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .leaves, abstractOpaque := false :
      CoalesceConfig })
  guard_target =
    ((∀ x, □ (ptlAtom x ∧ p)) |-tl- (∀ x, □ (ptlAtom x ∧ p)))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .leaves, abstractOpaque := true :
      CoalesceConfig })
  rename_i atomP
  guard_target =ₐ
    ((∀ x, □ (atomP x ∧ ptlAtom)) |-tl- (∀ x, □ (atomP x ∧ ptlAtom)))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .modal, abstractOpaque := false :
      CoalesceConfig })
  guard_target =ₛ ((∀ x, □ ptlAtom x) |-tl- (∀ x, □ ptlAtom x))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .modal, abstractOpaque := true :
      CoalesceConfig })
  guard_target =ₛ ((∀ x, □ ptlAtom x) |-tl- (∀ x, □ ptlAtom x))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .formula, abstractOpaque := false :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

example : (∀ x, □ (⌜ P x ⌝ ∧ p)) |-tl- (∀ x, □ (⌜ P x ⌝ ∧ p)) := by
  tcoalesce_to_ptl
    (config := {
      binders := .ignore, level := .formula, abstractOpaque := true :
      CoalesceConfig })
  guard_target =ₛ ((ptlAtom) |-tl- (ptlAtom))
  exact pred_implies_refl _

end ConfigMatrix

/--
error: tcoalesce_to_ptl: found no non-PTL predicate blocks to abstract
-/
#guard_msgs in
example (p : pred σ) : (□ p) |-tl- (□ p) := by
  tcoalesce_to_ptl

/--
error: tcoalesce_to_ptl: found no non-PTL predicate blocks to abstract
-/
#guard_msgs in
example (a : action σ) : (𝒲ℱ a) |-tl- (𝒲ℱ a) := by
  tcoalesce_to_ptl

/--
error: tcoalesce_to_ptl: expected a LTL validity goal, raw LTL sequent, or proof-mode Entails goal
-/
#guard_msgs in
example : True := by
  tcoalesce_to_ptl

end Lentil.ProofMode.Test.CoalesceToPTL
