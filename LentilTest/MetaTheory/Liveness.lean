import Lentil

namespace Lentil.Test.Liveness

example (p : σ → Prop) (hp : ∃ s, p s) : IsLiveness[◇ ⌜p⌝] := by
  letI : Nonempty {s // p s} := hp.elim fun s hs => ⟨⟨s, hs⟩⟩
  infer_instance

-- An alternating tail satisfies the action at every step.
example : IsLiveness[◇ □ ⟨fun (s t : Bool) => t = !s⟩] := by
  apply IsLiveness.eventuallyAlways_of_suffix.mp
  let w : exec Bool := Nat.rec false (fun _ b => !b)
  exact ⟨w, fun _ => rfl⟩

-- A false-to-true transition cannot occur at two consecutive positions of a tail.
example : ¬ IsLiveness[◇ □ ⟨fun (s t : Bool) => s = false ∧ t = true⟩] := by
  intro live
  obtain ⟨w, hw⟩ := IsLiveness.eventuallyAlways_of_suffix.mpr live
  exact Bool.noConfusion ((hw 1).1.symm.trans (hw 0).2)

-- Reading state 0 can invalidate an otherwise satisfying tail when it is appended.
example : (∃ w : exec Bool, (w |=tl= □ (fun e _ => e 0 = true))) ∧
    ¬ IsLiveness[◇ □ (fun (e : exec Bool) _ => e 0 = true)] := by
  refine ⟨⟨fun _ => true, fun _ => rfl⟩, ?_⟩
  intro h
  obtain ⟨t, agree, k, hk⟩ := IsLiveness.iff_extend_prefix.mp h (fun _ => false) 0 1
  have h0 : false = t 0 := exec.take_from_eq_iff.mp agree 0 (by decide)
  exact Bool.noConfusion (h0.trans (hk 0))

-- In each disjunction only one operand is known to be live.
example (P Q : pred σ) [IsLiveness P] : IsLiveness[◇ ((Q ∨ P) ∨ Q)] := inferInstance

example (P Q : pred σ) [IsLiveness Q] : IsLiveness[P → P 𝑈 Q] := inferInstance

example (P : Nat → pred σ) [∀ n, IsLiveness (P n)] : IsLiveness[∃ n, P n] := inferInstance

example (P : pred σ) (p : σ → Prop) [Nonempty {s // p s}] :
    IsLiveness[P ↝ ⌜p⌝] := inferInstance

example (a : action σ) : IsLiveness[𝒮ℱ a] ∧ IsLiveness[𝒲ℱ a] :=
  ⟨inferInstance, inferInstance⟩

-- Both factors in the decomposition are recognized through typeclass inference.
example (P : pred σ) : IsSafety[𝒞 P] ∧ IsLiveness[𝒞 P → P] :=
  ⟨inferInstance, inferInstance⟩

-- At i > 0 a witness for P can change the preceding state. A witness for ◯ P
-- at position 0 must preserve that state as soon as the prefix has length 1.
private def previousTrue (e : exec Bool) (i : Nat) : Prop := i = 0 ∨ e (i - 1) = true

example : IsLiveness previousTrue ∧ ¬ IsLiveness[◯ previousTrue] := by
  constructor
  · apply IsLiveness.iff_extend_prefix.mpr
    intro e i k
    let t : exec Bool := fun j => if j < i then true else e j
    refine ⟨t, exec.take_from_eq_iff.mpr (fun j hj => ?_), ?_⟩
    · simp [t, Nat.not_lt_of_ge hj.1]
    · cases i with
      | zero => exact Or.inl rfl
      | succ i => exact Or.inr (by simp [t])
  · intro h
    obtain ⟨t, agree, ht⟩ := IsLiveness.iff_extend_prefix.mp h (fun _ => false) 0 1
    have h0 : false = t 0 := exec.take_from_eq_iff.mp agree 0 (by decide)
    simp [exec.satisfies, later, previousTrue, ← h0] at ht

end Lentil.Test.Liveness
