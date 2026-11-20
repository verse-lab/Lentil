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
def MachineClosed (S F : pred σ) : Prop := (𝒞 (S ∧ F)) =tl= (S)

/-- Inside `MachineClosed[S, F]`, write two Lentil temporal formulas, with the
safety part first and the additional requirement second. For example,
`MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒲ℱ a]` says that each finite prefix of a legal
execution can be extended to a legal execution satisfying weak fairness for `a`.
When both arguments are already Lean terms `S F : pred σ`, write `MachineClosed S F`. -/
scoped macro:max "MachineClosed[" s:tlfml ", " f:tlfml "]" : term =>
  `(Lentil.MachineClosed [tlfml| $s] [tlfml| $f])

/-- With unrestricted safety, machine closure requires a satisfying continuation
of every finite prefix, exactly the liveness condition on `P`
(Abadi and Lamport, *An Old-Fashioned Recipe for Real Time*, §4.3). -/
theorem machineClosed_true_iff_isLiveness {P : pred σ} :
    MachineClosed[⊤, P] ↔ IsLiveness P := by
  unfold MachineClosed
  rw [true_and]
  exact ⟨fun h => ⟨h⟩, fun h => h.closure_eq⟩

/-- An extension that meets `F` also meets every requirement entailed by `F`.
This specializes the weakening rule with premise `S ∧ F ⊢ G`
(Abadi and Lamport, *An Old-Fashioned Recipe for Real Time*, §2.3, Proposition 3). -/
theorem MachineClosed.mono_right {S F G : pred σ} (h : MachineClosed S F)
    (entails : (F) |-tl- (G)) : MachineClosed S G := by
  haveI : IsSafety S := h ▸ IsSafety.closure _
  refine (pred_eq_iff_iff _ _).mpr ⟨safetyClosure_least and_left, ?_⟩
  unfold MachineClosed at h
  simpa only [h] using safetyClosure_monotone (P := tl_and S F) (Q := tl_and S G)
    fun e i ⟨hs, hf⟩ => ⟨hs, entails e i hf⟩

/-- At the end of any legal prefix where `a` is enabled, some `a` step
extends that prefix to a legal behavior (Abadi and Lamport,
*An Old-Fashioned Recipe for Real Time*, §2.3). The prefix includes the state enabling `a`. -/
def IsSubactionOf (a : action σ) (S : pred σ) : Prop :=
  ∀ e i n, (e |=tl[i]= S) → enabled a (e (i + n)) →
    -- `e[i: i+n] = t[i: i+n]`
    ∃ t, e.take_from i (n + 1) = t.take_from i (n + 1) ∧
      (t |=tl[i]= S) ∧ (t |=tl[i + n]= ⟨a⟩)

/-- In `IsSubactionOf[a, S]`, write a Lean action term for `a` and a Lentil
temporal formula for `S`, as in `IsSubactionOf[a, ⌜init⌝ ∧ □ ⟨step⟩]`. -/
scoped macro:max "IsSubactionOf[" a:term ", " s:tlfml "]" : term =>
  `(Lentil.IsSubactionOf $a [tlfml| $s])

-- CHECK `⌜init⌝ ∧ □ ⟨step⟩` might be too specific; consider possible generalization
/-- In a state machine with a successor at every state, it suffices that an
enabled action has at least one successor that is also a legal step.
The subaction criterion requires `Enabled A ⇒ Enabled (A ∧ [N]ᵥ)` along legal behaviors
(Abadi and Lamport, *An Old-Fashioned Recipe for Real Time*, §2.3, before Proposition 1).
Here `compatible` checks every state, and `total` lets the chosen step extend to
an infinite execution. -/
theorem IsSubactionOf.of_step (init : σ → Prop) (step a : action σ)
    (total : ∀ s, ∃ t, step s t)
    (compatible : ∀ s, enabled a s → ∃ t, a s t ∧ step s t) :
    IsSubactionOf[a, ⌜init⌝ ∧ □ ⟨step⟩] := by
  classical
  intro e i n he hen
  obtain ⟨dest, taken, legal⟩ := compatible _ hen
  let advance (j : Nat) (s : σ) :=
    if j < i + n then e (j + 1) else if j = i + n then dest else (total s).choose
  let t : exec σ := Nat.rec (e 0) advance
  have keep (j : Nat) (hj : j ≤ i + n) : t j = e j := by
    cases j with
    | zero => rfl
    | succ j => exact ite_eq_left hj
  have atNext : t (i + n + 1) = dest := by simp [t, advance]
  refine ⟨t, exec.take_from_eq_iff.mpr (by grind), ⟨?_, ?_⟩, ?_⟩
  · simpa [state_pred, keep i (by omega)] using he.1
  · intro d
    have before : step (e (i + d)) (e (i + d + 1)) := he.2 d
    have after := (total (t (i + d))).choose_spec
    change step (t (i + d)) (advance (i + d) (t (i + d)))
    grind
  · simpa [exec.satisfies, action_pred, keep, atNext] using taken

section MachineClosureForFairness

-- CHECK The following scheduler might not work for cases like FLP. Is it possible to do
-- some generalization?
/-- One stage of the fairness construction. The states fixed so far are
`run.take_from i prefixLength`. The full execution `run` witnesses that this
prefix extends to an execution satisfying `S` at `i`. -/
private structure FairnessStage (S : pred σ) (i : Nat) where
  run : exec σ
  prefixLength : Nat
  legal : S run i

private def FairnessStage.prefix {S : pred σ} {i : Nat} (p : FairnessStage S i) : List σ :=
  p.run.take_from i p.prefixLength

-- CHECK The following code seems a bit messy, might need some tidy up
/-- If a legal continuation can reach an enabling state, extend the prefix
through a legal `a` step. Otherwise grow the prefix by one state. -/
private theorem FairnessStage.extendFor {S : pred σ} {i : Nat} (p : FairnessStage S i)
    {a : action σ} (sub : IsSubactionOf a S) :
    ∃ q : FairnessStage S i, p.prefixLength < q.prefixLength ∧
      q.run.take_from i p.prefixLength = p.prefix ∧
      ∀ t, S t i → t.take_from i q.prefixLength = q.prefix →
        (∃ d ≥ p.prefixLength, enabled a (t (i + d))) →
        ∃ d ≥ p.prefixLength, a (t (i + d)) (t (i + d + 1)) := by
  classical
  by_cases possible : ∃ w d, S w i ∧ w.take_from i p.prefixLength = p.prefix ∧
      p.prefixLength ≤ d ∧ enabled a (w (i + d))
  · obtain ⟨w, d, hw, agree, hd, hen⟩ := possible
    obtain ⟨t, keep, ht, taken⟩ := sub w i d hw hen
    refine ⟨⟨t, d + 2, ht⟩, by dsimp; omega, ?_, ?_⟩
    · exact (exec.take_from_eq_of_subinterval keep (Nat.le_refl _) (by omega)).symm.trans agree
    · intro z _ same _
      refine ⟨d, hd, ?_⟩
      have eq := exec.take_from_eq_iff.mp same
      change a (t (i + d)) (t (i + d + 1)) at taken
      grind
  · refine ⟨{ p with prefixLength := p.prefixLength + 1 }, Nat.lt_succ_self _, rfl, ?_⟩
    intro t ht same ⟨d, hd, hen⟩
    apply (possible ⟨t, d, ht, ?_, hd, hen⟩).elim
    exact exec.take_from_eq_of_subinterval same (Nat.le_refl _) (by simp)

/-- There is a schedule that revisits every action index arbitrarily late. -/
private theorem exists_fair_schedule {α : Type v} [Nonempty α]
    (countable : ∃ code : α → Nat, Function.Injective code) :
    ∃ schedule : Nat → α, ∀ j k, ∃ n ≥ k, schedule n = j := by
  obtain ⟨code, inj⟩ := countable
  obtain ⟨decode, decode_code⟩ := inj.exists_leftInverse
  -- Each block starting at 2^b visits the codes 0, ..., 2^b - 1.
  refine ⟨fun n => decode (n - 2 ^ n.log2), fun j k => ?_⟩
  let b := code j + k
  have bound : code j + k < 2 ^ b := Nat.lt_two_pow_self
  refine ⟨2 ^ b + code j, by omega, ?_⟩
  have block : (2 ^ b + code j).log2 = b := (Nat.log2_eq_iff (by omega)).mpr
    ⟨by omega, by rw [Nat.pow_succ]; omega⟩
  simpa [block] using decode_code j

/-- Countably many strong fairness requirements on subactions of a safety
property can be satisfied by the same extension of each legal prefix
(Abadi and Lamport, *An Old-Fashioned Recipe for Real Time*, §2.3, Proposition 1, SF case). -/
theorem machineClosed_countableSF {α : Type v} (S : pred σ) [IsSafety S] (a : α → action σ)
    (sub : ∀ j, IsSubactionOf (a j) S)
    (countable : ∃ code : α → Nat, Function.Injective code := by exact ⟨id, Function.injective_id⟩) :
    MachineClosed[S, ∀ j, 𝒮ℱ (a j)] := by
  classical
  refine (pred_eq_iff_iff _ _).mpr ⟨safetyClosure_least and_left, ?_⟩
  intro e i he k
  by_cases inhabited : Nonempty α
  case neg => exact ⟨e, rfl, he, fun j => (inhabited ⟨j⟩).elim⟩
  obtain ⟨schedule, revisit⟩ := exists_fair_schedule countable
  -- Once a stage takes its scheduled action, later stages preserve that step.
  let next (n : Nat) (p : FairnessStage S i) := (p.extendFor (sub (schedule n))).choose
  let stage : Nat → FairnessStage S i := Nat.rec ⟨e, k, he⟩ next
  have advance (n : Nat) := (FairnessStage.extendFor (stage n) (sub (schedule n))).choose_spec
  have grow (n : Nat) : (stage n).prefixLength < (stage (n + 1)).prefixLength := (advance n).1
  have mono {n m : Nat} (h : n ≤ m) : (stage n).prefixLength ≤ (stage m).prefixLength := by
    induction h <;> grind
  have size (n : Nat) : n ≤ (stage n).prefixLength := by
    induction n <;> grind
  have nested {n m : Nat} (h : n ≤ m) :
      (stage m).run.take_from i (stage n).prefixLength = (stage n).prefix := by
    induction h with
    | refl => rfl
    | step h ih =>
      exact (exec.take_from_eq_of_subinterval (advance _).2.1 (Nat.le_refl _)
        (Nat.add_le_add_left (mono h) i)).trans ih
  -- Each state at offset d has stabilized by stage i + d + 1.
  let t : exec σ := fun j => (stage (j + 1)).run j
  have agrees (n : Nat) : t.take_from i (stage n).prefixLength = (stage n).prefix := by
    apply exec.take_from_eq_iff.mpr
    rintro j ⟨hij, hj⟩
    have left := exec.take_from_eq_iff.mp (nested (Nat.le_max_right n (j + 1))) j
    have right := exec.take_from_eq_iff.mp (nested (Nat.le_max_left n (j + 1))) j
    change (stage (j + 1)).run j = (stage n).run j
    grind
  -- Every prefix of the limit has a legal witness, so safety gives S on the limit.
  have ht : S t i := by
    rw [← IsSafety.closure_eq (P := S)]
    intro b
    exact ⟨(stage b).run, exec.take_from_eq_of_subinterval (agrees b) (Nat.le_refl _)
      (Nat.add_le_add_left (size b) i), (stage b).legal⟩
  refine ⟨t, (agrees 0).symm, ht, ?_⟩
  intro j
  rw [sf_as_implies]
  intro enabledOften b
  obtain ⟨n, hn, hj⟩ := revisit j b
  have serve := (advance n).2.2 t ht (agrees (n + 1))
  rw [hj] at serve
  obtain ⟨d, hd⟩ := enabledOften (stage n).prefixLength
  obtain ⟨r, hr, taken⟩ := serve ⟨(stage n).prefixLength + d, by omega, by
    simpa [tl_enabled, state_pred, Nat.add_assoc] using hd⟩
  have hb : b ≤ r := Nat.le_trans hn (Nat.le_trans (size n) hr)
  refine ⟨r - b, ?_⟩
  simpa only [action_pred, Nat.add_assoc, Nat.add_sub_of_le hb] using taken

/-- Every legal prefix has one extension meeting both countable families of
weak and strong fairness obligations (Abadi and Lamport,
*An Old-Fashioned Recipe for Real Time*, §2.3, Proposition 1). The paper takes properties
to be invariant under stuttering. Here the hypotheses are `IsSafety S` and the subaction conditions.
The two index types may differ, and each must admit an injection into `Nat`.
For TLA fairness relative to `w`, use the action `fun s t => A s t ∧ w s ≠ w t`. -/
theorem machineClosed_countableFairness {α : Type v} {β : Type w} (S : pred σ) [IsSafety S]
    (weak : α → action σ) (strong : β → action σ)
    (hw : ∀ j, IsSubactionOf (weak j) S) (hs : ∀ j, IsSubactionOf (strong j) S)
    (countWeak : ∃ code : α → Nat, Function.Injective code := by exact ⟨id, Function.injective_id⟩)
    (countStrong : ∃ code : β → Nat, Function.Injective code := by exact ⟨id, Function.injective_id⟩) :
    MachineClosed[S, (∀ j, 𝒲ℱ (weak j)) ∧ (∀ j, 𝒮ℱ (strong j))] := by
  obtain ⟨encodeWeak, weakInj⟩ := countWeak
  obtain ⟨encodeStrong, strongInj⟩ := countStrong
  have countSum : ∃ code : α ⊕ β → Nat, Function.Injective code := by
    refine ⟨Sum.elim (fun j => 2 * encodeWeak j) (fun j => 2 * encodeStrong j + 1), ?_⟩
    intro x y eq
    cases x <;> cases y <;> simp_all [Function.Injective] <;> grind
  have closed := machineClosed_countableSF S (Sum.elim weak strong)
    (fun | .inl j => hw j | .inr j => hs j) countSum
  exact closed.mono_right fun e i fair =>
    ⟨fun j => sf_implies_wf e i (fair (.inl j)), fun j => fair (.inr j)⟩

/-- State-machine form of the countable WF/SF theorem. The Coq theorem `machine_closed`
assumes that `Next` has a successor at every state and each fairness action implies `Next`
(Wan et al., *Formal Proof of a Machine Closed Theorem in Coq*, §§3.3 and 4.2). -/
theorem machineClosed_countableFairness_of_total {α : Type v} {β : Type w}
    (init : σ → Prop) (step : action σ)
    (weak : α → action σ) (strong : β → action σ) (total : ∀ s, ∃ t, step s t)
    (weakSub : ∀ j s t, weak j s t → step s t)
    (strongSub : ∀ j s t, strong j s t → step s t)
    (countWeak : ∃ code : α → Nat, Function.Injective code := by exact ⟨id, Function.injective_id⟩)
    (countStrong : ∃ code : β → Nat, Function.Injective code := by exact ⟨id, Function.injective_id⟩) :
    MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, (∀ j, 𝒲ℱ (weak j)) ∧ (∀ j, 𝒮ℱ (strong j))] := by
  have sub (a : action σ) (h : ∀ s t, a s t → step s t) :
      IsSubactionOf[a, ⌜init⌝ ∧ □ ⟨step⟩] :=
    IsSubactionOf.of_step init step a total fun s ⟨t, ht⟩ => ⟨t, ht, h s t ht⟩
  exact machineClosed_countableFairness _ weak strong
    (fun j => sub _ (weakSub j)) (fun j => sub _ (strongSub j)) countWeak countStrong

/-- A single strongly fair action is machine closed when its steps are legal
and the machine can stutter in every state (Abadi and Lamport,
*An Old-Fashioned Recipe for Real Time*, §2.3, Proposition 1, single-action SF case).
For TLA's `SF_w(A)`, pass the nonstuttering action `fun s t => A s t ∧ w s ≠ w t` as `a`. -/
theorem machineClosed_singleSF (init : σ → Prop) (step a : action σ)
    (stutter : ∀ s, step s s) (sub : ∀ s t, a s t → step s t) :
    MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒮ℱ a] := by
  have ha := IsSubactionOf.of_step init step a (fun s => ⟨s, stutter s⟩)
    fun s ⟨t, ht⟩ => ⟨t, ht, sub s t ht⟩
  exact (machineClosed_countableSF _ (fun _ => a) fun _ => ha).mono_right
    fun _ _ fair => fair 0

/-- The single-action WF case follows from `machineClosed_singleSF` since strong fairness
implies weak fairness (Abadi and Lamport, *An Old-Fashioned Recipe for Real Time*, §2.3,
Proposition 1). -/
theorem machineClosed_singleWF (init : σ → Prop) (step a : action σ)
    (stutter : ∀ s, step s s) (sub : ∀ s t, a s t → step s t) :
    MachineClosed[⌜init⌝ ∧ □ ⟨step⟩, 𝒲ℱ a] :=
  (machineClosed_singleSF init step a stutter sub).mono_right sf_implies_wf

end MachineClosureForFairness

/-- With all initial states and steps allowed, every prefix has a strongly fair extension.
This liveness result is also reported for both SF and WF
(Wan et al., *Formal Proof of a Machine Closed Theorem in Coq*, §1). -/
instance IsLiveness.strongFairness (a : action σ) : IsLiveness[𝒮ℱ a] := by
  apply machineClosed_true_iff_isLiveness.mp
  have h := machineClosed_singleSF (fun _ => True) (fun _ _ => True) a
    (fun _ => trivial) (fun _ _ _ => trivial)
  change MachineClosed[⊤ ∧ □ ⊤, 𝒮ℱ a] at h
  simpa only [always_true, true_and] using h

/-- The strongly fair extension from `IsLiveness.strongFairness` also witnesses weak fairness. -/
instance IsLiveness.weakFairness (a : action σ) : IsLiveness[𝒲ℱ a] :=
  IsLiveness.of_entails (P := strong_fairness a) sf_implies_wf

end Lentil
