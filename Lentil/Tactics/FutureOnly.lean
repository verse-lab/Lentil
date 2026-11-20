module

public import Lentil.Rules.Basic

public section

namespace Lentil

/-- A predicate is future-only if its truth at a position depends only on the infinite
suffix starting there, including the current state. Dropping `k` states moves
position `i + k` of the original execution to position `i` of the suffix. -/
class FutureOnly {σ : Type u} (p : pred σ) : Prop where
  drop_iff : ∀ (e : exec σ) (k i : Nat), p (e.drop k) i ↔ p e (i + k)

namespace FutureOnly

theorem drop_zero_iff {σ : Type u} {p : pred σ} [h : FutureOnly p]
    (e : exec σ) (i : Nat) : p (e.drop i) 0 ↔ p e i := by
  simpa using h.drop_iff e i 0

theorem valid_iff_valid_initial {σ : Type u} {p : pred σ}
    [FutureOnly p] : valid p ↔ valid_initial p := by
  constructor
  · intro h e
    exact h e 0
  · intro h e i
    exact (drop_zero_iff (p := p) e i).mp (h (e.drop i))

theorem pred_implies_iff_pred_implies_initial {σ : Type u} {p q : pred σ}
    [FutureOnly (tl_implies p q)] : pred_implies p q ↔ pred_implies_initial p q := by
  simpa [pred_implies, pred_implies_initial, valid, valid_initial, tl_implies]
    using (valid_iff_valid_initial (p := tl_implies p q))

end FutureOnly

/- Base future-only formulas. -/

instance futureOnlyState {σ : Type u} (P : σ → Prop) :
    FutureOnly (state_pred P) where
  drop_iff := by
    intro _ _ _
    rfl

instance futureOnlyPure {σ : Type u} (P : Prop) :
    FutureOnly (pure_pred (α := σ) P) := futureOnlyState _

instance futureOnlyTrue {σ : Type u} : FutureOnly (tl_true (α := σ)) :=
  futureOnlyPure _

instance futureOnlyFalse {σ : Type u} : FutureOnly (tl_false (α := σ)) :=
  futureOnlyPure _

instance futureOnlyAction {σ : Type u} (a : action σ) :
    FutureOnly (action_pred a) where
  drop_iff := by
    intro e k i
    simp [action_pred, exec.drop]
    rw [show i + 1 + k = i + k + 1 by omega]

instance futureOnlyEnabled {σ : Type u} (a : action σ) :
    FutureOnly (tl_enabled a) where
  drop_iff := by
    intro _ _ _
    rfl

/- Compositional future-only formulas. -/

instance futureOnlyAnd {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (tl_and p q) where
  drop_iff := by
    intro e k i
    simp [tl_and, FutureOnly.drop_iff]

instance futureOnlyOr {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (tl_or p q) where
  drop_iff := by
    intro e k i
    simp [tl_or, FutureOnly.drop_iff]

instance futureOnlyNot {σ : Type u} (p : pred σ) [FutureOnly p] :
    FutureOnly (tl_not p) where
  drop_iff := by
    intro e k i
    simp [tl_not, FutureOnly.drop_iff]

instance futureOnlyImplies {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (tl_implies p q) where
  drop_iff := by
    intro e k i
    simp [tl_implies, FutureOnly.drop_iff]

instance futureOnlyForall {σ : Type u} {α : Sort v} (p : α → pred σ)
    [∀ x, FutureOnly (p x)] :
    FutureOnly (tl_forall p) where
  drop_iff := by
    intro e k i
    simp [tl_forall, FutureOnly.drop_iff]

instance futureOnlyExists {σ : Type u} {α : Sort v} (p : α → pred σ)
    [∀ x, FutureOnly (p x)] :
    FutureOnly (tl_exists p) where
  drop_iff := by
    intro e k i
    simp [tl_exists, FutureOnly.drop_iff]

instance futureOnlyLater {σ : Type u} (p : pred σ) [FutureOnly p] :
    FutureOnly (later p) where
  drop_iff := by
    intro e k i
    simpa [later, show i + 1 + k = i + k + 1 by omega]
      using FutureOnly.drop_iff (p := p) e k (i + 1)

instance futureOnlyUntil {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (tl_until p q) where
  drop_iff := by
    intro e k i
    constructor
    · intro h
      rcases h with ⟨n, hq, hp⟩
      refine ⟨n, ?_, ?_⟩
      · have hq' := (FutureOnly.drop_iff (p := q) e k (i + n)).mp hq
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq'
      · intro l hlt
        have hp' := (FutureOnly.drop_iff (p := p) e k (i + l)).mp (hp l hlt)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp'
    · intro h
      rcases h with ⟨n, hq, hp⟩
      refine ⟨n, ?_, ?_⟩
      · exact (FutureOnly.drop_iff (p := q) e k (i + n)).mpr (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq)
      · intro l hlt
        exact (FutureOnly.drop_iff (p := p) e k (i + l)).mpr (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp l hlt)

instance futureOnlyAlways {σ : Type u} (p : pred σ) [FutureOnly p] :
    FutureOnly (always p) := by
  rw [always_as_until] ; infer_instance

instance futureOnlyEventually {σ : Type u} (p : pred σ) [FutureOnly p] :
    FutureOnly (eventually p) := by
  rw [eventually_as_until] ; infer_instance

instance futureOnlyLeadsTo {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (leads_to p q) := by
  unfold leads_to ; infer_instance

instance futureOnlyAlwaysImplies {σ : Type u} (p q : pred σ)
    [FutureOnly p] [FutureOnly q] :
    FutureOnly (always_implies p q) := by
  unfold always_implies ; infer_instance

instance futureOnlyWeakFairness {σ : Type u} (a : action σ) :
    FutureOnly (weak_fairness a) := by
  unfold weak_fairness ; infer_instance

end Lentil
