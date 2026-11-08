module

public import Lean
public import Lentil.Rules.Basic
public import Lentil.Gadgets.TheoremDeriving
public import Lentil.ProofMode.Tactics
public import Lentil.ProofMode.Display

@[expose] public section

/-! Theorems about the leads-to operator. -/

open Classical

namespace Lentil

section leads_to

variable {σ : Type u}

theorem leads_to_refl {p : pred σ} : |-tl- (p ↝ p) := by
  unfold Lentil.leads_to
  rw [← always_intro, impl_intro]
  exact now_weaken_to_eventually

theorem leads_to_or_lhs {p q r : pred σ} :
    ((p ↝ r) ∧ (q ↝ r)) =tl= ((p ∨ q) ↝ r) := by
  unfold leads_to ; rw [← always_and, or_in_imp_lhs]

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tl- ((p x) ↝ q)) ↔ (Γ) |-tl- ((tl_exists p) ↝ q) := by
  tunfold_simp ; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tl- (p ↝ q)) ↔ (Γ) |-tl- (⌞ φ ⌟ ∧ p ↝ q) := by
  tunfold_simp ; aesop

@[tl_derive]
theorem leads_to_conseq {p p' q q' : pred σ} :
  |-tl- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) → (p' ↝ q')) := by
  tunfold_simp ; intro e i h1 h2 h k hp'
  specialize h _ (h1 _ hp') ; rcases h with ⟨k1, h⟩
  specialize h2 (k + k1) ; exists k1 ; grind

@[tl_derive]
theorem leads_to_trans {p q r : pred σ} :
  |-tl- ((p ↝ q) → (q ↝ r) → (p ↝ r)) := by
  tunfold_simp ; intro e i h1 h2 k hp
  rcases h1 k hp with ⟨k1, hq⟩
  rcases h2 (k + k1) (by simpa [Nat.add_assoc] using hq) with ⟨k2, hr⟩
  exists k1 + k2
  simpa [Nat.add_assoc] using hr

theorem leads_to_combine {Γ Γ' p1 q1 p2 q2 : pred σ}
  (h1 : (□ Γ ∧ Γ') |-tl- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tl- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tl- □ q1) (h2' : (q2 ∧ □ Γ) |-tl- □ q2) :
  (□ Γ ∧ Γ') |-tl- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tunfold_simp ; intro e i hΓ hΓ' k hp1 hp2
  rcases h1 e i hΓ hΓ' k hp1 with ⟨k1, hq1⟩
  rcases h2 e i hΓ hΓ' k hp2 with ⟨k2, hq2⟩
  exists k1 + k2
  constructor
  · have hq1' := h1' e (i + k + k1) hq1
      (fun l => by simpa [Nat.add_assoc] using hΓ (k + k1 + l)) k2
    simpa [Nat.add_assoc] using hq1'
  · have hq2' := h2' e (i + k + k2) hq2
      (fun l => by simpa [Nat.add_assoc] using hΓ (k + k2 + l)) k1
    have heq : i + k + k2 + k1 = i + k + (k1 + k2) := by omega
    simpa [heq] using hq2'

@[tl_derive]
theorem leads_to_strengthen_lhs {p q inv : pred σ} :
  |-tl- (□ inv → (p ∧ inv ↝ q) → (p ↝ q)) := by
  tunfold_simp ; aesop

/-- The lattice rule. Over a well-founded relation `r`, if every stage `F c`
leads to the goal or to a smaller stage, every stage leads to the goal. The
proof is `WellFounded.induction`, with leads-to algebra at every step:
`leads_to_exists` and `leads_to_pure_pred_and` spread "some smaller stage" over
the stages, `leads_to_or_lhs` absorbs the goal branch, and `leads_to_trans`
chains. -/
theorem leads_to_lattice {α : Sort v} {r : α → α → Prop} (hwf : WellFounded r)
    (F : α → pred σ) (G : pred σ) :
    (∀ c, F c ↝ (G ∨ ∃ d, ⌞ r d c ⌟ ∧ F d)) |-tl- (∀ c, F c ↝ G) := by
  tstart hLattice
  tintro c
  induction c using WellFounded.induction hwf
  rename_i c ih
  thave h := hLattice c
  ttoggle_goal_under_always
  treplace h := always_weaken h
  trewrite [eventually_or, or_in_imp_rhs] at h
  trcases h with (h | h)
  on_goal 1=> tapply h
  tintro h1 ; tspecialize h h1 ; tclear h1
  tadvance h
  trcases h with ⟨d, hr, hd⟩ ; tpull_pure hr
  trevert hd
  ttoggle_goal_under_always
  exact ih _ hr

end leads_to

end Lentil
