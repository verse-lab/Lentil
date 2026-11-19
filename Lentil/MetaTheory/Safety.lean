module

public import Lentil.Tactics.FiniteWindow

public section

namespace Lentil

variable {σ : Type u}

-- TODO Give `safetyClosure` a notation like `𝒞`
/-- For each length `k`, some execution satisfying `P` at `i` agrees with `e`
on the interval `[i, i + k)`. At `i = 0` this is the safety closure of the
set of executions satisfying `P` initially (Alpern and Schneider, *Defining Liveness*). -/
@[expose] def safetyClosure (P : pred σ) : pred σ := fun e i =>
  ∀ k, ∃ t, e.take_from i k = t.take_from i k ∧ P t i

/-- An execution satisfying `P` witnesses every prefix required by its closure. -/
theorem safetyClosure_extensive (P : pred σ) : (P) |-tl- (safetyClosure P) :=
  fun e _ hp _ => ⟨e, rfl, hp⟩

/-- Safety closure preserves temporal entailment. -/
theorem safetyClosure_monotone {P Q : pred σ} (h : (P) |-tl- (Q)) :
    (safetyClosure P) |-tl- (safetyClosure Q) := by
  intro e i hp k
  obtain ⟨t, agree, ht⟩ := hp k
  exact ⟨t, agree, h t i ht⟩

/-- A safety property is equal to its safety closure. If it fails at `i`,
some finite prefix starting at `i` rules out every satisfying continuation. -/
class IsSafety (P : pred σ) : Prop where
  closure_eq : safetyClosure P = P

theorem IsSafety.by_def : IsSafety P ↔ safetyClosure P = P := ⟨fun h => h.closure_eq, fun h => ⟨h⟩⟩

/-- A property is safe exactly when its safety closure entails it. -/
theorem safetyClosure_implies_iff_isSafety {P : pred σ} :
    ((safetyClosure P) |-tl- (P)) ↔ IsSafety P := by
  rw [IsSafety.by_def, pred_eq_iff_iff] ; simp [safetyClosure_extensive]

/-- The safety closure of `P` implies every safety property implied by `P`. -/
theorem safetyClosure_least {P Q : pred σ} [hQ : IsSafety Q] (h : (P) |-tl- (Q)) :
    (safetyClosure P) |-tl- (Q) := by
  simpa only [hQ.closure_eq] using safetyClosure_monotone h

namespace IsSafety

/-- The finite bad-prefix characterization of Alpern and Schneider
(*Defining Liveness*, §2), applied at each evaluation position `i`. -/
theorem iff_bad_prefix {P : pred σ} :
  IsSafety P ↔
    ∀ e i, (e |=tl[i]= ¬ P) → ∃ k, ∀ t, e.take_from i k = t.take_from i k → (t |=tl[i]= ¬ P) := by
  rw [← safetyClosure_implies_iff_isSafety, contraposition_for_pred_implies]
  tunfold_simp ; unfold safetyClosure ; simp

/-- Take the prefix at the exact window width. Its satisfying extension and the
original execution evaluate the same finite core. -/
instance (priority := low) ofFiniteWindow (P : pred σ) {n : Nat} [HasFiniteWindow P n] :
    IsSafety P := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h
  obtain ⟨t, agree, ht⟩ := h n
  let cert := finiteWindowOfHasFiniteWindow (p := P) (n := n)
  rwa [cert.iff_of_eval e i, IteratedHomPred.evalExec_congr cert.core agree, ← cert.iff_of_eval t i]

instance and (P Q : pred σ) [IsSafety P] [IsSafety Q] : IsSafety (tl_and P Q) := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h
  exact ⟨safetyClosure_least and_left e i h, safetyClosure_least and_right e i h⟩

instance forallPred {α : Sort v} (P : α → pred σ) [∀ x, IsSafety (P x)] :
    IsSafety (tl_forall P) := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h x
  exact safetyClosure_least (P := (tl_forall P)) (fun _ _ ht => ht x) e i h

instance or (P Q : pred σ) [hP : IsSafety P] [hQ : IsSafety Q] : IsSafety (tl_or P Q) := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h
  by_cases hp : P e i
  · exact Or.inl hp
  · -- A bad prefix for P forces every longer witnessing prefix to use Q.
    obtain ⟨k, bad⟩ := iff_bad_prefix.mp hP e i hp
    apply Or.inr
    rw [← hQ.closure_eq]
    intro n
    obtain ⟨t, agree, ht | ht⟩ := h (max k n)
    · exact (bad t (exec.take_from_eq_of_subinterval agree (by omega) (by omega)) ht).elim
    · exact ⟨t, exec.take_from_eq_of_subinterval agree (by omega) (by omega), ht⟩

private theorem at_offset (P : pred σ) [hP : IsSafety P] (d : Nat) :
    IsSafety (fun e i => P e (i + d)) := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h
  change P e (i + d)
  rw [← hP.closure_eq]
  intro k
  obtain ⟨t, agree, ht⟩ := h (d + k)
  exact ⟨t, exec.take_from_eq_of_subinterval agree (by omega) (by omega), ht⟩

instance laterPred (P : pred σ) [IsSafety P] : IsSafety (later P) := at_offset P 1

instance alwaysPred (P : pred σ) [IsSafety P] : IsSafety (always P) :=
  @forallPred σ Nat (fun d e i => P e (i + d)) (at_offset P)

instance bigwedge {α : Type v} (P : α → pred σ) [∀ x, IsSafety (P x)] (xs : List α) :
    IsSafety (tl_bigwedge P xs) := by
  induction xs with
  | nil => exact inferInstanceAs (IsSafety (σ := σ) [tlfml| ⊤])
  | cons x xs ih => exact @and σ (P x) _ inferInstance ih

instance bigvee {α : Type v} (P : α → pred σ) [∀ x, IsSafety (P x)] (xs : List α) :
    IsSafety (tl_bigvee P xs) := by
  induction xs with
  | nil => exact inferInstanceAs (IsSafety (σ := σ) [tlfml| ⊥])
  | cons x xs ih => exact @or σ (P x) _ inferInstance ih

/-
-- FIXME: This should be generalized to arbitrary finite types, not just `Fin n`.
instance existsFin {n : Nat} (P : Fin n → pred σ) [∀ x, IsSafety (P x)] :
    IsSafety (tl_exists P) := by
  have eq : (⋁ x ∈ List.finRange n, P x) =tl= (∃ x, P x) := by
    rw [bigvee_exists_list P]
    funext e i
    simp [tl_exists, tl_and, pure_pred, state_pred]
  rw [← eq]
  infer_instance

/-- Release in Lentil's existing syntax. At each offset `d`, either `Q` holds
there or `P` held at one of the finitely many earlier positions. -/
instance release (P Q : pred σ) [IsSafety P] [IsSafety Q] :
    IsSafety [tlfml| ¬ (¬ P 𝑈 ¬ Q)] := by
  let shifted (R : pred σ) (d : Nat) : pred σ := fun e i => R e (i + d)
  haveI (d : Nat) : IsSafety (shifted P d) := at_offset P d
  haveI (d : Nat) : IsSafety (shifted Q d) := at_offset Q d
  let atDepth (d : Nat) := [tlfml| (shifted Q d) ∨ ∃ j : Fin d, shifted P j]
  suffices (¬ (¬ P 𝑈 ¬ Q)) =tl= (∀ d, atDepth d) by
    rw [this]
    exact forallPred atDepth
  classical
  funext e i
  apply propext
  simp [atDepth, shifted, tl_not, tl_until, tl_forall, tl_exists, tl_or, Fin.exists_iff,
    Classical.or_iff_not_imp_left]
-/

instance closure (P : pred σ) : IsSafety (safetyClosure P) := by
  apply safetyClosure_implies_iff_isSafety.mp
  intro e i h k
  obtain ⟨t, het, ht⟩ := h k
  obtain ⟨v, htv, hv⟩ := ht k
  exact ⟨v, het.trans htv, hv⟩

end IsSafety

theorem safetyClosure_idem (P : pred σ) :
    (safetyClosure (safetyClosure P)) =tl= (safetyClosure P) := IsSafety.closure_eq

/-- A prefix extension satisfying both conjuncts witnesses the closure of each. -/
theorem safetyClosure_and_split (P Q : pred σ) :
    (safetyClosure [tlfml| P ∧ Q]) |-tl- ((safetyClosure P) ∧ (safetyClosure Q)) := by
  intro e i h
  exact ⟨safetyClosure_monotone and_left e i h, safetyClosure_monotone and_right e i h⟩

/-- Safety closure distributes over binary disjunction. -/
theorem safetyClosure_or (P Q : pred σ) :
    (safetyClosure [tlfml| P ∨ Q]) =tl= ((safetyClosure P) ∨ (safetyClosure Q)) := by
  have h : (P ∨ Q) |-tl- ((safetyClosure P) ∨ (safetyClosure Q)) :=
    fun e i => Or.imp (safetyClosure_extensive P e i) (safetyClosure_extensive Q e i)
  funext e i
  apply propext
  exact ⟨safetyClosure_least h e i, fun hpq =>
    Or.elim hpq (safetyClosure_monotone or_inl e i) (safetyClosure_monotone or_inr e i)⟩

end Lentil
