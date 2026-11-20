import Lentil

namespace Lentil.Test.MachineClosure

-- Exact certificates also cover negated and compound finite-window formulas.
example (P : pred σ) {n : Nat} [HasFiniteWindow P n] : IsSafety[¬ P] := inferInstance

example (p : σ → Prop) (a : action σ) :
    IsSafety[¬ ⌜p⌝ ↔ ◯ ¬ ⟨a⟩] := inferInstance

example (init : σ → Prop) (step : action σ) :
    safetyClosure [tlfml| ⌜init⌝ ∧ □ ⟨step⟩] = [tlfml| ⌜init⌝ ∧ □ ⟨step⟩] :=
  IsSafety.closure_eq

-- Every finite all-false prefix still admits an extension that eventually reaches true.
example : ¬ IsSafety[◇ ⌜fun b : Bool => b = true⌝] := by
  intro hs
  let e : exec Bool := fun _ => false
  have hn : ¬ [tlfml| ◇ ⌜fun b => b = true⌝] e 0 := by simp [eventually, state_pred, e]
  obtain ⟨k, bad⟩ := IsSafety.iff_bad_prefix.mp hs e 0 hn
  let t : exec Bool := fun j => decide (k ≤ j)
  apply bad t (exec.take_from_eq_iff.mpr ?_) ⟨k, ?_⟩
  · intro j hj
    simp [e, t, show ¬ k ≤ j by omega]
  · simp [state_pred, t]

-- At the initial position, the window is the ordinary prefix of length k.
example (P : pred σ) (e : exec σ) :
    safetyClosure P e 0 ↔ ∀ k, ∃ t, e.take k = t.take k ∧ P t 0 := by
  simp only [safetyClosure, exec.take_from, exec.take, List.range_eq_range']

-- At position 1, the witness may change state 0 and must preserve state 1.
example (e : exec Bool) :
    safetyClosure (fun t i => i = 1 ∧ t 0 = true ∧ t i = false) e 1 ↔ e 1 = false := by
  constructor
  · intro h
    obtain ⟨t, hp, _, _, ht⟩ := h 1
    change [e 1] = [t 1] at hp
    exact (List.cons.inj hp).1.trans ht
  · intro he k
    let t : exec Bool := fun j => if j = 0 then true else e j
    refine ⟨t, ?_, rfl, by simp [t], by simpa [t] using he⟩
    apply List.map_congr_left
    intro j hj
    have hpos := (List.mem_range'_1.mp hj).1
    simp [t, show j ≠ 0 by omega]

end Lentil.Test.MachineClosure
