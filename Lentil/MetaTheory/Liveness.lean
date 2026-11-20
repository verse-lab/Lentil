module

public import Lentil.Tactics.FutureOnly
public import Lentil.MetaTheory.Safety

public section

namespace Lentil

variable {σ : Type u}

/-- A liveness property is dense in the prefix topology. At every position
`i`, each finite prefix starting at `i` admits an execution satisfying `P` there
(Alpern and Schneider, *Defining Liveness*, §§3–4). -/
class IsLiveness (P : pred σ) : Prop where
  closure_eq : (safetyClosure P) =tl= (⊤)

theorem IsLiveness.by_def : IsLiveness P ↔ (safetyClosure P) =tl= (⊤) :=
  ⟨fun h => h.closure_eq, fun h => ⟨h⟩⟩

namespace IsLiveness

/-- The witness agrees with the given execution on `[i, i + k)`. At `i = 0`
this is the finite-prefix extension condition of Alpern and Schneider. -/
theorem iff_extend_prefix {P : pred σ} :
    IsLiveness P ↔
      ∀ (e : exec σ) (i k : Nat), ∃ t, e.take_from i k = t.take_from i k ∧ (t |=tl[i]= P) := by
  erw [by_def, funext_iff]
  simp only [funext_iff, eq_iff_iff, safetyClosure] ; tunfold_simp

/-- A property is live exactly when every safety property it entails equals `⊤`. -/
theorem iff_safety_consequences {P : pred σ} :
    IsLiveness P ↔ ∀ S : pred σ, IsSafety S → ((P) |-tl- (S)) → ((S) =tl= (⊤)) := by
  constructor
  · intro live S safe entails
    have h := safetyClosure_least entails
    rw [live.closure_eq] at h
    exact (pred_eq_iff_iff _ _).mpr ⟨fun _ _ _ => trivial, h⟩
  · intro h
    exact ⟨h (safetyClosure P) inferInstance (safetyClosure_extensive P)⟩

instance top : IsLiveness (σ := σ) tl_true := ⟨IsSafety.closure_eq⟩

/-- Weakening a liveness property preserves its satisfying extension for each prefix. -/
theorem of_entails {P Q : pred σ} [hP : IsLiveness P] (h : (P) |-tl- (Q)) : IsLiveness Q := by
  apply iff_extend_prefix.mpr
  intro e i k
  obtain ⟨t, agree, hp⟩ := iff_extend_prefix.mp hP e i k
  exact ⟨t, agree, h t i hp⟩

instance orLeft (P Q : pred σ) [IsLiveness P] : IsLiveness (tl_or P Q) :=
  of_entails (P := P) or_inl

instance orRight (P Q : pred σ) [IsLiveness Q] : IsLiveness (tl_or P Q) :=
  of_entails (P := Q) or_inr

instance impliesRight (P Q : pred σ) [IsLiveness Q] : IsLiveness (tl_implies P Q) :=
  of_entails (P := Q) fun _ _ hq _ => hq

/-- A single live branch suffices to witness the existential. -/
theorem exists_of_witness {α : Sort v} (P : α → pred σ) (x : α) [IsLiveness (P x)] :
    IsLiveness (tl_exists P) :=
  of_entails (P := P x) fun _ _ hp => ⟨x, hp⟩

instance existsPred {α : Sort v} [h : Nonempty α] (P : α → pred σ) [∀ x, IsLiveness (P x)] :
    IsLiveness (tl_exists P) := by
  obtain ⟨x⟩ := h
  exact exists_of_witness P x

instance eventuallyPred (P : pred σ) [IsLiveness P] : IsLiveness (eventually P) :=
  of_entails (P := P) now_weaken_to_eventually

instance untilRight (P Q : pred σ) [IsLiveness Q] : IsLiveness (tl_until P Q) :=
  of_entails (P := Q) fun _ _ hq => ⟨0, hq, fun _ h => (Nat.not_lt_zero _ h).elim⟩

/-- For future-only `P` on a nonempty state space, a tail satisfying `□ P`
can be appended after any finite prefix. Conversely, extend the empty prefix
and take the suffix starting where `□ P` holds. -/
theorem eventuallyAlways_of_suffix {P : pred σ} [Nonempty σ] [FutureOnly P] :
    (∃ w, (w |=tl= □ P)) ↔ IsLiveness (eventually (always P)) := by
  constructor
  · rintro ⟨w, hw⟩
    apply iff_extend_prefix.mpr
    intro e i k
    let t : exec σ := fun j => if j < i + k then e j else w (j - (i + k))
    have drop_eq : t.drop (i + k) = w := by
      funext n
      simp [exec.drop, t, Nat.not_lt_of_ge (Nat.le_add_left (i + k) n)]
    refine ⟨t, exec.take_from_eq_iff.mpr (fun j hj => ?_), k, ?_⟩
    · simp [t, hj.2]
    · apply (FutureOnly.drop_zero_iff (p := always P) t (i + k)).mp
      rwa [drop_eq]
  · intro live
    obtain ⟨s⟩ := ‹Nonempty σ›
    obtain ⟨t, _, k, hk⟩ := iff_extend_prefix.mp live (fun _ => s) 0 0
    refine ⟨t.drop k, (FutureOnly.drop_zero_iff (p := always P) t k).mpr ?_⟩
    simpa only [Nat.zero_add] using hk

theorem alwaysEventually_of_eventuallyAlways {P : pred σ} [IsLiveness (eventually (always P))] :
    IsLiveness (always (eventually P)) :=
  of_entails (P := (eventually (always P))) fun e i ⟨k, hk⟩ d =>
    ⟨k, by simpa [Nat.add_right_comm] using hk d⟩

theorem eventually_of_alwaysEventually {P : pred σ} [IsLiveness (always (eventually P))] :
    IsLiveness (eventually P) :=
  of_entails (P := (always (eventually P))) always_weaken

/-- A constant execution witnesses `□ ⌜p⌝` whenever some state satisfies `p`. -/
instance eventuallyAlwaysState (p : σ → Prop) [hp : Nonempty {s // p s}] :
    IsLiveness (eventually (always (state_pred p))) := by
  obtain ⟨⟨s, hs⟩⟩ := hp
  letI : Nonempty σ := ⟨s⟩
  exact eventuallyAlways_of_suffix.mp ⟨fun _ => s, fun _ => hs⟩

instance alwaysEventuallyState (p : σ → Prop) [Nonempty {s // p s}] :
    IsLiveness (always (eventually (state_pred p))) := alwaysEventually_of_eventuallyAlways

instance eventuallyState (p : σ → Prop) [Nonempty {s // p s}] :
    IsLiveness (eventually (state_pred p)) := eventually_of_alwaysEventually

instance leadsTo (P Q : pred σ) [IsLiveness (always (eventually Q))] : IsLiveness (leads_to P Q) :=
  of_entails (P := (always (eventually Q))) fun _ _ h d _ => h d

/-- The liveness factor in the safety–liveness decomposition of `P`.
Inside the closure, take a satisfying extension of the prefix. Outside it,
the original execution already satisfies the implication. -/
instance livenessPart (P : pred σ) : IsLiveness (tl_implies (safetyClosure P) P) := by
  apply iff_extend_prefix.mpr
  intro e i k
  by_cases hc : (e |=tl[i]= safetyClosure P)
  · obtain ⟨t, agree, hp⟩ := hc k
    exact ⟨t, agree, fun _ => hp⟩
  · exact ⟨e, rfl, fun h => (hc h).elim⟩

end IsLiveness

/-- A property has both safety and liveness exactly when it holds on every execution at every position. -/
theorem isSafety_and_isLiveness_iff_eq_top {P : pred σ} :
    (IsSafety P ∧ IsLiveness P) ↔ ((P) =tl= (⊤)) := by
  constructor
  · rintro ⟨safe, live⟩
    exact safe.closure_eq.symm.trans live.closure_eq
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

/-- Every property is the conjunction of its safety closure and a liveness
property (Alpern and Schneider, *Defining Liveness*, Theorem 1). -/
theorem safety_liveness_decomposition (P : pred σ) :
    (P) =tl= ((safetyClosure P) ∧ ((safetyClosure P) → P)) := by
  funext e i
  exact propext ⟨fun hp => ⟨safetyClosure_extensive P e i hp, fun _ => hp⟩,
    fun ⟨hc, h⟩ => h hc⟩

end Lentil
