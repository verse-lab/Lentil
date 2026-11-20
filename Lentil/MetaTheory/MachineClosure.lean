module

public import Lentil.MetaTheory.Liveness
public import Lentil.Rules.SF

@[expose] public section

namespace Lentil

variable {σ : Type u}

/-- `S` is the safety part of the specification, typically its initial condition
and allowed steps. `F` is an additional temporal requirement, such as weak or
strong fairness for an action. The pair is *machine closed* when the safety
closure of the complete specification `S ∧ F` equals `S`
(Abadi and Lamport, *The Existence of Refinement Mappings*, §2.3). -/
def MachineClosed (S F : pred σ) : Prop := safetyClosure (tl_and S F) = S

/-- Inside `MachineClosed[S, F]`, write two Lentil temporal formulas, with the
safety part first and the additional requirement second. For example,
`MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒲ℱ a]` says that each finite prefix of a legal
execution can be extended to a legal execution satisfying weak fairness for `a`.
When both arguments are already Lean terms `S F : pred σ`, write `MachineClosed S F`. -/
scoped macro:max "MachineClosed[" s:tlfml ", " f:tlfml "]" : term =>
  `(Lentil.MachineClosed [tlfml| $s] [tlfml| $f])

/-- With unrestricted safety, machine closure requires a satisfying continuation
of every finite prefix, exactly the liveness condition on `P`. -/
theorem machineClosed_true_iff_isLiveness {P : pred σ} :
    MachineClosed[⊤, P] ↔ IsLiveness P := by
  unfold MachineClosed
  rw [true_and]
  exact ⟨fun h => ⟨h⟩, fun h => h.closure_eq⟩

/-- A single strongly fair action is machine closed when its steps are legal
and the machine can stutter in every state. For TLA's `SF_w(A)`, pass the
nonstuttering action `fun s t => A s t ∧ w s ≠ w t` as `a`.
This is a single-action instance of Abadi and Lamport,
*An Old-Fashioned Recipe for Real Time*, Proposition 1. -/
theorem machineClosed_singleSF (init : σ → Prop) (step a : action σ)
    (stutter : ∀ s, step s s) (sub : ∀ s t, a s t → step s t) :
    MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒮ℱ a] := by
  classical
  funext e start
  apply propext
  refine ⟨safetyClosure_least and_left e start, ?_⟩
  intro he k
  simp only [tl_and, state_pred, always, action_pred] at he ⊢
  let advance (s : σ) := if h : enabled a s then h.choose else s
  have taken {s : σ} (h : enabled a s) : a s (advance s) := by
    simpa [advance, h] using h.choose_spec
  -- Copy e through start + k, then take a whenever it is enabled.
  let t : exec σ := Nat.rec (e 0) (fun i s => if i < start + k then e (i + 1) else advance s)
  have agrees (i : Nat) (hi : i ≤ start + k) : t i = e i := by
    cases i with
    | zero => rfl
    | succ i => exact ite_eq_left hi
  have tail (i : Nat) (hi : start + k ≤ i) : t (i + 1) = advance (t i) :=
    ite_eq_right (Nat.not_lt_of_ge hi)
  refine ⟨t, exec.take_from_eq_iff.mpr (fun j hj => (agrees j (Nat.le_of_lt hj.2)).symm), ⟨?_, ?_⟩, ?_⟩
  · rw [agrees start (by omega)]
    exact he.1
  · intro j
    by_cases hj : j < k
    · rw [agrees (start + j) (by omega), agrees (start + j + 1) (by omega)]
      exact he.2 j
    · rw [tail (start + j) (by omega)]
      by_cases ha : enabled a (t (start + j))
      · exact sub _ _ (taken ha)
      · simpa [advance, ha] using stutter (t (start + j))
  · simp only [sf_as_implies, tl_implies, always, eventually, tl_enabled, state_pred,
      action_pred]
    intro hen i
    obtain ⟨j, ha⟩ := hen (i + k)
    refine ⟨k + j, ?_⟩
    rw [tail (start + i + (k + j)) (by omega)]
    exact taken (by simpa only [Nat.add_assoc] using ha)

/-- The same extension also meets weak fairness for the chosen action. -/
theorem machineClosed_singleWF (init : σ → Prop) (step a : action σ)
    (stutter : ∀ s, step s s) (sub : ∀ s t, a s t → step s t) :
    MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒲ℱ a] := by
  have hsf := machineClosed_singleSF init step a stutter sub
  unfold MachineClosed at hsf
  funext e i
  apply propext
  refine ⟨safetyClosure_least and_left e i, ?_⟩
  intro he k
  rw [← hsf] at he
  obtain ⟨t, agree, ht, fair⟩ := he k
  exact ⟨t, agree, ht, sf_implies_wf t i fair⟩

/-- With all initial states and steps allowed, every prefix has a strongly fair extension. -/
instance IsLiveness.strongFairness (a : action σ) : IsLiveness[𝒮ℱ a] := by
  apply machineClosed_true_iff_isLiveness.mp
  have h := machineClosed_singleSF (fun _ => True) (fun _ _ => True) a
    (fun _ => trivial) (fun _ _ _ => trivial)
  change MachineClosed[⊤ ∧ □ ⊤, 𝒮ℱ a] at h
  simpa only [always_true, true_and] using h

instance IsLiveness.weakFairness (a : action σ) : IsLiveness[𝒲ℱ a] :=
  IsLiveness.of_entails (P := strong_fairness a) sf_implies_wf

end Lentil
