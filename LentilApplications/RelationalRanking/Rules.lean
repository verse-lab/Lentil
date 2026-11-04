module

public import Lentil
public import Batteries.Data.List.Basic
import Batteries.Data.List.Perm
import Batteries.Tactic.Init
import Lentil.Utils.MiscLemmas
public import LentilApplications.RelationalRanking.Util

@[expose] public section

/-! # Relational Ranking Technique for Proving Liveness Properties

    Let's validate the rules from [this paper](https://link.springer.com/chapter/10.1007/978-3-031-65627-9_13)! -/

namespace RelationalRanking

open Lentil Classical LentilLib Lean

section TheoremsFromMathlib

private theorem forall₂_length_eq {α : Type u} {β : Type v} {r : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ r xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem forall₂_getElem {α : Type u} {β : Type v} {r : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ r xs ys) :
    ∀ (i : Nat) (hi : i < xs.length) (hi' : i < ys.length), r xs[i] ys[i] := by
  induction h with
  | nil => intro i hi ; exact (Nat.not_lt_zero i hi).elim
  | cons h _ ih =>
    intro i ; cases i with
    | zero => intros ; exact h
    | succ i => intro hi hi' ; exact ih i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')

end TheoremsFromMathlib

/-! ## Characterization of Finite-Support Relations

    NOTE: We could also use `Finsupp` from Mathlib, but it is kind of "heavy-weight"
    for validating the rules. For example, a finite-support function is defined as a
    `structure` there, where the finite support condition is bundled with the
    function; here we want to separate the function and its condition, with the
    latter being proven separately. -/

/-- The domain of `p` can be enumerated by a list without repetitions. -/
def simple_finite {α : Type u} (p : α → Prop) :=
  ∃ (xs : List α), xs.Nodup ∧ ∀ a, p a ↔ a ∈ xs

-- `simple_finite` closes under `∨`
theorem simple_finite_or {α : Type u} {p q : α → Prop} (hp : simple_finite p) (hq : simple_finite q) :
  simple_finite (fun a => p a ∨ q a) := by
  rcases hp with ⟨xs, hxs, hp⟩ ; rcases hq with ⟨ys, hys, hq⟩
  exists xs ++ ys.filter (fun x => decide (x ∉ xs)) ; grind

/-- The size of the domain of a predicate with finite support. -/
noncomputable def domain_size {α : Type u} (p : α → Prop) (hf : simple_finite p) : Nat :=
  hf.choose.length

/-- The condition for `n` to be the size of the domain of `p`.
    The condition for `p` being finite will be given extrinsically. -/
def domain_size_spec {α : Type u} (p : α → Prop) (n : Nat) : Prop :=
  ∀ (xs : List α), xs.Nodup → (∀ a, p a ↔ a ∈ xs) → xs.length = n

-- an induction rule(?) for `domain_size_spec`
-- HMM this is natural, well
theorem domain_size_spec_induction {α : Type u} {q : Nat → Prop} {p : α → Prop} {n : Nat}
    (hf : simple_finite p) (hn : domain_size_spec p n) :
  (∀ (xs : List α), xs.Nodup → (∀ a, p a ↔ a ∈ xs) → q xs.length) → q n := by
  rcases hf with ⟨xs, hxs, hf⟩
  intro h ; rw [← hn xs hxs hf] ; exact h xs hxs hf

-- characterization of `domain_size`
theorem simple_finite_domain_size_spec {α : Type u} (p : α → Prop) (hf : simple_finite p) :
  domain_size_spec p (domain_size p hf) := by
  unfold domain_size domain_size_spec
  rcases Exists.choose_spec hf with ⟨hxs', hf'⟩
  intro xs hxs hx
  apply List.Perm.length_eq
  grind

/-- Lifting `simple_finite` onto a state predicate. -/
def simple_finite_record {σ : Type u} {α : Type v} (δ : α → σ → Prop) : σ → Prop :=
  fun s => simple_finite (δ · s)

-- showing `δ'` has finite domain if `δ` has finite domain
theorem simple_finite_record_implies {σ : Type u} {α : Type v} (δ δ' : α → σ → Prop) (s : σ) :
  (∀ x, δ' x s → δ x s) → simple_finite_record δ s → simple_finite_record δ' s := by
  intro h ⟨xs, hxs, hfin⟩
  exists xs.filter (fun x => decide (δ' x s))
  grind

/-! ### Comparing Finite-Support Relations

    Intuitively, we can treat a finite-support relation as the size of its domain,
    and we can compare two finite-support relations by comparing the sizes of their
    domains. An equivalent way of doing such comparison is by checking the
    validity of some formulas, like the `conserves` and `reduces` in the paper.

    We can represent `conserves` and `reduces` as both action predicates
    and temporal formulas (using `◯`), which are definitionally equal. -/

section relational_order

variable {σ : Type u} {α : Type v} (δ : α → σ → Prop)

def relational_ge (s s' : σ) : Prop := ∀ (x : α), δ x s' → δ x s

def relational_eq (s s' : σ) : Prop := ∀ (x : α), δ x s ↔ δ x s'

def relational_gt (s s' : σ) : Prop :=
  relational_ge δ s s' ∧ (∃ (x : α), δ x s ∧ ¬ δ x s')

notation s " ≥ᵣ" "{" δ "} " s' => relational_ge δ s s'
notation s " =ᵣ" "{" δ "} " s' => relational_eq δ s s'
notation s " >ᵣ" "{" δ "} " s' => relational_gt δ s s'

section relational_order_lemmas

omit δ
variable {δ : α → σ → Prop} {s s' : σ}

theorem relational_eq_then_ge : (s =ᵣ{δ} s') → (s ≥ᵣ{δ} s') := by
  simp [relational_eq, relational_ge] ; aesop

theorem relational_ge_not_gt_then_eq : (s ≥ᵣ{δ} s') → ¬ (s >ᵣ{δ} s') → (s =ᵣ{δ} s') := by
  simp [relational_gt, relational_eq, relational_ge] ; aesop

theorem relational_ge_implies_simple_finite_record :
  (s ≥ᵣ{δ} s') → simple_finite_record δ s → simple_finite_record δ s' :=
  simple_finite_record_implies (fun x _ => δ x s) (fun x _ => δ x s') s

end relational_order_lemmas

section relational_order_to_domain_size_order

omit δ
variable {δ : α → σ → Prop} {s s' : σ} {n n' : Nat}
  (hf : simple_finite_record δ s) (hf' : simple_finite_record δ s')
  (hn : domain_size_spec (δ · s) n) (hn' : domain_size_spec (δ · s') n')
include hf hf' hn hn'

-- NOTE: the inverse direction is not true in general; same below
theorem relational_gt_domain_size_gt : (s >ᵣ{δ} s') → n > n' := by
  apply domain_size_spec_induction hf hn ; clear hf hn ; intro xs hxs hf
  apply domain_size_spec_induction hf' hn' ; clear hf' hn' ; intro ys hys hf'
  simp [relational_ge, relational_gt]
  intro hge x hx hnx
  have hnodup : (x :: ys).Nodup := List.nodup_cons.mpr ⟨fun hin => hnx ((hf' x).mpr hin), hys⟩
  have hsubset : x :: ys ⊆ xs := by
    intro a ha ; rcases List.mem_cons.mp ha with rfl | ha
    · exact (hf a).mp hx
    · exact (hf a).mp (hge a ((hf' a).mpr ha))
  exact (List.subperm_of_subset hnodup hsubset).length_le

theorem relational_eq_domain_size_eq : (s =ᵣ{δ} s') → n = n' := by
  apply domain_size_spec_induction hf hn ; clear hf hn ; intro xs hxs hf
  apply domain_size_spec_induction hf' hn' ; clear hf' hn' ; intro ys hys hf'
  simp [relational_eq]
  intro h ; apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup hxs hys).mpr
  intro x ; rw [← hf, ← hf', h]

end relational_order_to_domain_size_order

/-- The domain of the relational ranking function `δ` does not get larger
    after one transition. -/
def conserves : pred σ := [tlfml| ∀ x, ((◯ ⌜ δ x ⌝) → ⌜ δ x ⌝) ]

/-- The domain of the relational ranking function `δ` does get smaller
    after one transition. -/
def reduces : pred σ := [tlfml| ∃ x, (⌜ δ x ⌝ ∧ ◯ ¬ ⌜ δ x ⌝) ]

end relational_order

/-! ## Lexicographic Order for Series of Finite-Support Relations

    Suppose we have a series `[p ℐ[0], p ℐ[1], ...]` of finite-support relations
    indexed by some list `ℐ`. By regarding this series as a list `l` of natural numbers,
    where for each `i`, `l[i]` is the domain size of `p ℐ[i]`, we can define
    the lexicographic order on the series `[p 𝒾 | 𝒾 ∈ ℐ ]` of finite-support relations
    as the order on lists of natural numbers (of a fixed length). -/

-- FIXME: here we might as well skip the intermediate `List Nat` representation,
-- and directly use the lexicographic order on the series of finite-support relations?

/-- The "domain-size vector" of the series `[p 𝒾 | 𝒾 ∈ ℐ ]` of finite-support relations. -/
noncomputable def domain_sizes_vec {α : Type u} {β : Type v} (p : β → α → Prop) (ℐ : List β)
    (hfin : ∀ x ∈ ℐ, simple_finite (p x)) : List Nat :=
  ℐ.attach.map fun ⟨x, hin⟩ => domain_size (p x) (hfin x hin)

/-- The condition for `l` to be the "domain-size vector" of the series `[p 𝒾 | 𝒾 ∈ ℐ ]`.
    The condition for each `p 𝒾` being finite will be given extrinsically. -/
def domain_sizes_vec_spec {α : Type u} {β : Type v} (p : β → α → Prop) : List Nat → List β → Prop :=
  List.Forall₂ (fun n i => domain_size_spec (p i) n)

-- characterization of `domain_sizes_vec`
theorem simple_finite_domain_sizes_vec_spec {α : Type u} {β : Type v} (p : β → α → Prop) (ℐ : List β)
    (hfin : ∀ x ∈ ℐ, simple_finite (p x)) :
  domain_sizes_vec_spec p (domain_sizes_vec p ℐ hfin) ℐ := by
  induction ℐ with
  | nil => exact .nil
  | cons i ℐ ih =>
    simp only [domain_sizes_vec, domain_sizes_vec_spec, List.attach_cons, List.map_cons, List.map_map]
    exact .cons (simple_finite_domain_size_spec _ _) (ih (fun x hx => hfin x (List.mem_cons_of_mem _ hx)))

section relational_lex_order

variable {σ : Type u} {α : Type v} {β : Type w} (δ : β → α → σ → Prop) (ψ r : β → pred σ) (ℐ : List β)

def relational_gt_lex (s s' : σ) : Prop :=
  ∃ (i : Fin ℐ.length), (s >ᵣ{δ ℐ[i]} s') ∧ (∀ i' < i, s =ᵣ{δ ℐ[i']} s')

def relational_eq_lex (s s' : σ) : Prop :=
  ∀ (i : Fin ℐ.length), s =ᵣ{δ ℐ[i]} s'

def relational_ge_lex (s s' : σ) : Prop :=
  relational_gt_lex δ ℐ s s' ∨ relational_eq_lex δ ℐ s s'

notation s " >ᵣₗ" "{" δ "," ℐ "} " s' => relational_gt_lex δ ℐ s s'
notation s " =ᵣₗ" "{" δ "," ℐ "} " s' => relational_eq_lex δ ℐ s s'
notation s " ≥ᵣₗ" "{" δ "," ℐ "} " s' => relational_ge_lex δ ℐ s s'

section relational_lex_order_lemmas

omit δ ℐ
variable {δ : β → α → σ → Prop} {ℐ : List β} {s s' : σ}

-- the `=ᵣ` part in `relational_gt_lex` can be weakened to `≥ᵣ`
theorem relational_gt_lex_alt : (s >ᵣₗ{δ, ℐ} s') ↔
  ∃ (i : Fin ℐ.length), (s >ᵣ{δ ℐ[i]} s') ∧ (∀ i' < i, s ≥ᵣ{δ ℐ[i']} s') := by
  simp [relational_gt_lex] ; constructor
  · intro ⟨i, hgt, heq⟩ ; exists i ; apply And.intro hgt
    intro i' hlt ; apply relational_eq_then_ge ; apply heq _ hlt
  · -- a more involved case
    intro ⟨⟨i, hlt⟩, hgt, hge⟩
    let p i_ := fun hlt_ => s >ᵣ{δ ℐ[Fin.mk i_ hlt_]} s'
    have htmp := LentilLib.Nat.find_min (p := fun i_ => ∃ h_, p i_ h_) i (Exists.intro hlt hgt)
    unfold p at htmp ; clear p
    dsimp at htmp ; rcases htmp with ⟨i', hle, ⟨hlt', hgt'⟩, hmin⟩ ; simp at hmin
    exists ⟨i', hlt'⟩ ; apply And.intro hgt'
    intro ⟨i'', hlt''⟩ hii'' ; simp at *
    specialize hge ⟨_, hlt''⟩ (by simp ; omega) ; simp at hge
    apply relational_ge_not_gt_then_eq hge (hmin _ hii'' hlt'')

theorem relational_gt_lex_nat_list_lex {l l' : List Nat}
    (hf : ∀ (i : Fin ℐ.length), simple_finite_record (δ ℐ[i]) s)
    (hf' : ∀ (i : Fin ℐ.length), simple_finite_record (δ ℐ[i]) s')    -- we might be able to remove this, but this makes things more convenient, so anyway
    (hl : domain_sizes_vec_spec (fun i => (δ i · s)) l ℐ)
    (hl' : domain_sizes_vec_spec (fun i => (δ i · s')) l' ℐ) :
  (s >ᵣₗ{δ, ℐ} s') → ListLex.List.lexLt Nat.lt_wfRel l' l := by
  rw [ListLex.List.lexLt_alt] ; simp +instances [ListLex.List.lexLt', Nat.lt_wfRel, relational_gt_lex]
  -- do some preparation first
  dsimp only [domain_sizes_vec_spec] at hl hl'
  have hll := forall₂_length_eq hl ; have hll' := forall₂_length_eq hl'
  have hlpw_ := fun i h2 => forall₂_getElem hl i (hll ▸ h2) h2
  have hlpw_' := fun i h2 => forall₂_getElem hl' i (hll' ▸ h2) h2
  intro ⟨x, hltx⟩ hgt heq ; simp at hgt ; exists x ; constructor
  · apply List.ext_get <;> simp [hll, hll']
    intro j hj _
    have hltj : j < ℐ.length := by omega
    symm ; apply relational_eq_domain_size_eq (hf ⟨j, hltj⟩) (hf' ⟨j, hltj⟩)
      (hlpw_ _ hltj) (hlpw_' _ hltj)
    exact heq ⟨j, hltj⟩ (by simpa using (show j < x by omega))
  · simp [hll, hll']
    exists hltx
    apply relational_gt_domain_size_gt (hf ⟨x, hltx⟩) (hf' ⟨x, hltx⟩) (hlpw_ _ hltx) (hlpw_' _ hltx)
    simp ; exact hgt

end relational_lex_order_lemmas

end relational_lex_order

/-! ## The Rules from the Paper

    Now we can validate the rules from the paper.
    We start by proving the most precise rule, and then proving the other
    rules as its special cases. -/

section rules_with_scheduler_and_parameter

variable {σ : Type u} {α : Type v} {β : Type w} {γ : Type u_1} (R : α → σ → Prop) (δ : β → α → σ → Prop)
  (p q ϕ : pred σ) (ψ r : γ → β → pred σ) (ℐ : List β)

def preempted (g : γ) (i : Fin ℐ.length) : pred σ :=
  [tlfml| ⋁ j ∈ (ℐ.take i), (ψ g j) ]

def required (g : γ) (i : Fin ℐ.length) : pred σ :=
  [tlfml| (ψ g ℐ[i]) ∧ ¬ (preempted ψ ℐ g i) ]

local macro "S1" : term => `([tlfml| (p ∧ (¬ ◇ q) ⇒ ϕ) ])
local macro "P2" : term => `([tlfml| (∀ g : γ, (⋀ i ∈ (List.finRange ℐ.length), ϕ ∧ (¬ ◇ q) ⇒
  ◯ ϕ ∧
  (¬ (preempted ψ ℐ g i) → (conserves (δ ℐ[i]))) ∧
  ((required ψ ℐ g i) ∧ (r g ℐ[i]) → (reduces (δ ℐ[i]))) ∧
  ((required ψ ℐ g i) ∧ ¬ (r g ℐ[i]) → ◯ (ψ g ℐ[i])))) ])
local macro "P3" : term => `([tlfml| ∀ g : γ, (⋀ i ∈ ℐ, ϕ ∧ (¬ ◇ q) ∧ (ψ g i) ⇒ ◇ (r g i)) ])
local macro "P4" : term => `([tlfml| (ϕ ∧ (¬ ◇ q) ⇒ ∃ g : γ, (⋁ i ∈ ℐ, (ψ g i))) ])
local macro "S5" : term => `([tlfml| (⋀ i ∈ ℐ, ϕ ⇒ ∀ x, (⌜ δ i x ⌝ → ⌜ R x ⌝)) ])
local macro "S6" : term => `([tlfml| (□ ⌜ simple_finite_record R ⌝) ])

private theorem preempted_downwards (g : γ) (i j : Fin ℐ.length) (hlt : j ≤ i) :
  (¬ (preempted ψ ℐ g i)) |-tl- (¬ (preempted ψ ℐ g j)) := by
  unfold preempted ; repeat rw [bigvee_exists_list]
  rcases (List.take_prefix_take_left hlt) with ⟨suf, h⟩ ; rw [← h] ; tunfold_simp ; aesop

-- a semantics-based proof saying that infinite descent is impossible
private theorem no_infinite_descent :
  ((□⋁ i ∈ List.finRange ℐ.length,
    (⋀ j ∈ List.take (i.val + 1) ℐ, (conserves (δ j))) 𝑈
      ((⋀ j ∈ List.take (i.val + 1) ℐ, (conserves (δ j))) ∧ (reduces (δ ℐ[i])))) ∧
    (□⋀ i ∈ ℐ, ⌜ simple_finite_record (δ i) ⌝)) |-tl- (⊥) := by
  intro e t ⟨h, hfin⟩
  /- As mentioned before, we can regard `δ ℐ[0] · s, δ ℐ[1] · s, ...` as a list
     of natural numbers, with `δ x · s` mapped to its domain size.
     It then suffices to show that this list cannot decrease infinitely w.r.t.
     lexicographic order. -/
  have materialize : ∀ m, ∃ (l : List Nat), domain_sizes_vec_spec (fun i => (δ i · (e (t + m)))) l ℐ := by
    /- NOTE: instead of directly applying `domain_sizes_vec`, we abstract
       the existence of such a list so that the obtained list does not depend
       on `hfin` -/
    intro m ; specialize hfin m ; rw [bigwedge_forall_list] at hfin
    exists domain_sizes_vec (fun i => (δ i · (e (t + m)))) ℐ
      (by clear h ; tunfold_simp ; apply hfin)
    apply simple_finite_domain_sizes_vec_spec
  -- induction on the domain-size list at the beginning
  have ⟨l0, hl0⟩ := materialize 0
  induction l0 using (ListLex.List.lexRecOn Nat.lt_wfRel) generalizing e t
  rename_i l0 ih
  -- now use `h` to know `l0` will eventually decrease
  have hu := always_weaken _ _ h ; rw [bigvee_exists_fintype_list] at hu
  rcases hu with ⟨⟨i, hlt⟩, hu⟩ ; simp at hlt hu
  rcases hu with ⟨n, ⟨⟨hcsvfinal, hred⟩, hcsv⟩⟩
  have hcsv' := (fun (j : Nat) (hj : j ≤ n) => match Nat.eq_or_lt_of_le hj with
    | Or.inl heq => heq.symm ▸ hcsvfinal
    | Or.inr hlt => hcsv j hlt)
  clear hcsv hcsvfinal ; have hcsv := hcsv' ; clear hcsv'
  -- making `hcsv` pairwise should be good
  have hcsv' : ∀ (j : Fin ℐ.length), j.val ≤ i → ∀ k ≤ n + 1, ∀ k' ≤ n + 1, k ≤ k' → ((e (t + k)) ≥ᵣ{δ ℐ[j]} (e (t + k'))) := by
    clear h hfin materialize hl0 ih hred l0
    intro ⟨j, hltj⟩ hji k hkn k' hkn' hkk' ; dsimp at hji
    induction k' using Nat.strongRecOn generalizing k hkn
    rename_i k' ih ; simp
    rcases Nat.eq_or_lt_of_le hkk' with hkk' | hkk' ; subst_vars ; exact (fun _ => id)  -- side goal
    rcases k' with _ | k' ; simp at hkk'
    specialize hcsv k' (by omega) ; specialize ih k' (by simp) _ hkn (by omega) (by omega)
    rw [bigwedge_forall_fintype_list] at hcsv
    specialize hcsv ⟨j, by simp ; omega⟩ ; simp at hcsv ih ⊢
    simp [conserves] at hcsv ; tunfold_simp
    intro x hx ; apply ih ; simpa [Nat.add_assoc] using hcsv x hx
  clear hcsv ; have hcsv := hcsv' ; clear hcsv'
  have hred' : (e t) >ᵣ{δ ℐ[i]} (e (t + (n + 1))) := by
    clear h hfin materialize hl0 ih l0
    apply And.intro (hcsv ⟨i, hlt⟩ (by simp) 0 (by simp) (n + 1) (by simp) (by simp))
    specialize hcsv ⟨i, hlt⟩ (by simp) 0 (by simp) n (by simp) (by simp)
    simp [relational_ge] at hcsv ; simp [reduces] at hred
    tunfold_simp ; simp [Nat.add_assoc] at hred ; aesop
  clear hred ; have hred := hred' ; clear hred'
  -- now, we apply the induction hypothesis on the list at time `n + 1`
  -- by first showing that the list indeed decreases w.r.t. lexicographic order
  have hrelgtlex : (e t) >ᵣₗ{δ, ℐ} (e (t + (n + 1))) := by
    rw [relational_gt_lex_alt]
    exists ⟨i, hlt⟩ ; apply And.intro hred
    intro i' hlt' ; apply hcsv (k := 0) <;> (try rfl) <;> (try simp)
    cases i' ; simp at hlt' ⊢ ; omega
  clear hcsv hred
  have ⟨ln, hln⟩ := materialize (n + 1)
  have hnatlexgt : ListLex.List.lexLt Nat.lt_wfRel ln l0 := by
    rw [bigwedge_forall_fintype_list] at hfin
    apply relational_gt_lex_nat_list_lex <;> (try apply hrelgtlex) <;> (try assumption)
    · simpa only [tl_forall, state_pred, Nat.add_zero] using hfin 0
    · clear h materialize hl0 hln hrelgtlex ih ; tunfold_simp ; apply hfin
  specialize ih ln (by
    rw [forall₂_length_eq hln, forall₂_length_eq hl0])
    hnatlexgt e (t + (n + 1))
    (by intro k ; simpa [Nat.add_assoc] using h (n + 1 + k))
    (by intro k ; simpa [Nat.add_assoc] using hfin (n + 1 + k))
    (by intro m ; simpa [Nat.add_assoc] using materialize (n + 1 + m))
    (by simpa using hln)
  exact ih

-- a lemma useful for proving `rule11`
private theorem rule11_aux (g : γ) :
  ((□⋀ i ∈ ℐ, (ψ g i) → ◇(r g i)) ∧
    (□⋀ x ∈ List.finRange ℐ.length,
          (¬(preempted ψ ℐ g x) → (conserves (δ ℐ[x]))) ∧
            ((required ψ ℐ g x) ∧ (r g ℐ[x]) → (reduces (δ ℐ[x]))) ∧ ((required ψ ℐ g x) ∧ ¬(r g ℐ[x]) → ◯(ψ g ℐ[x]))) ∧
    ⋁ i ∈ ℐ, (ψ g i)) |-tl-
  (⋁ i ∈ List.finRange ℐ.length,
      ((⋀ j ∈ List.take (i.val + 1) ℐ, (conserves (δ j))) 𝑈
        ((⋀ j ∈ List.take (i.val + 1) ℐ, (conserves (δ j))) ∧ (reduces (δ ℐ[i]))))) := by
  tstart hS3 hL2 hbigveeψ
  -- assume it is `ψ i` that happens initially
  rw [bigvee_exists_fintype_list] ; trcases hbigveeψ with ⟨⟨i, hlt⟩, hψi⟩
  /- NOTE: Here we strengthen the conclusion to make the proof easier.
     The idea is: if `ψ i` happens, then eventually there will be some `i' ≤ i`
     for which `ψ i'` will not be preempted until `r i'` eventually happens.
     We prove this by doing induction on `i`. -/
  tsuffices hthis : ∃ i' : Fin ℐ.length, ∃ _x : i'.val ≤ i, ((⋀ j ∈ List.take (i'.val + 1) ℐ, (conserves (δ j))) 𝑈
      ((⋀ j ∈ List.take (i'.val + 1) ℐ, (conserves (δ j))) ∧ (reduces (δ ℐ[i'])))) by
    trcases hthis with ⟨i', h1, h2⟩
    rw [bigvee_exists_list]
    texists i'
    tsplit_ands
    · tprove_pure ; apply List.finRange_fin_in
    · tassumption
  trevert hψi
  ttoggle_goal_under_always
  induction i using Nat.strongRecOn
  rename_i i ih
  ttoggle_goal_under_always ; tintro hψi
  -- simplify and split `hL2` first
  thave hL2back := hL2     -- backup, fed into `ih` later
  repeat trewrite [bigwedge_inner_and_split, always_and] at hL2
  trcases hL2 with ⟨hL2a, hL2b, hL2c⟩
  trewrite [always_bigwedge, bigwedge_forall_list] at hL2a hL2b hL2c
  let p (i j : Nat) := fun hltj => [tlfml| ⌞ j < i ⌟ ∧ ◇ (ψ g ℐ[Fin.mk j hltj]) ]
  -- prove some useful things first; they are only useful in this proof, so did not make lemmas
  thave hconserves : ∀ i : Fin ℐ.length, ((∀ j : Nat, ∀ hltj, ¬ (p i j hltj)) →
    (□¬(preempted ψ ℐ g i) ∧ □ (⋀ j ∈ List.take (i + 1) ℐ, (conserves (δ j))))) by
    tsimp only [p, Lentil.not_and_to_imp]
    trintro ⟨i, hlti⟩ hh ; clear ih ; tclear *- hh hL2a
    tapply modus_ponens_with_premise ; tsplit_ands
    · tsimp [preempted, bigvee_exists_fintype_list, Lentil.not_exists, always_forall]
      tsimp only [not_eventually] at hh
      trintro ⟨x, hltx⟩ ; dsimp only ; simp [Nat.lt_min] at hltx
      tspecialize hh x hltx.2 hltx.1
      tapply hh
    · tsimp [bigwedge_forall_fintype_list, always_forall]
      trintro hnotpre ⟨x, hltx⟩ ; dsimp ; simp [Nat.lt_min] at hltx ; rcases hltx with ⟨hltx1, hltx2⟩
      tspecialize hL2a (Fin.mk x hltx2) (List.finRange_fin_in _ _)
      tclear hh ; tmonotone
      tapply hL2a ; tclear hL2a
      apply preempted_downwards ; simp ; omega
  -- now do something simple: just case-analyze whether there will be smaller `j < i` that
  -- `ψ j` happens at future
  tby_cases hc : ∃ j : Nat, ∃ hltj, (p i j hltj)
  · -- first minimize the `j` of `hc` and then use `ih`
    tclear *- hS3 hL2back hconserves hc
    trcases hc with ⟨jtmp, hc⟩
    -- NOTE: If we do not specify `p` here, unification will unfold related definitions
    treplace hc := (Lentil.find_min (p := fun j_ => [tlfml| ∃ hltj, (p i j_ hltj)]) jtmp) hc
    tobtain ⟨j, hle, ⟨hltj, hp⟩, hmin⟩ := hc
    tdsimp [p] at hp ; trcases hp with ⟨hji, hψj⟩
    tpull_pure hle hji
    clear jtmp hle    -- we don't care about the original `jtmp`
    -- use `ih` and first simplify the goal a bit
    specialize ih _ hji ‹_›
    thave ih := ih ⟨hS3, hL2back⟩ ; clear ih ; tclear hL2back hS3
    tmap hψj using ih ; tclear ih
    -- FIXME: extracting pure things? manual only now
    tsimp only [pure_and_to_exists, ← Lentil.exists_and_left, eventually_exists] at hψj
    trcases hψj with ⟨i', (ih1 : i'.val ≤ j), ih⟩
    texists i', (by grind)
    -- use `hmin` with `hconserves`
    tsimp only [Lentil.not_exists] at hmin
    thave htmp : ∀ m, ∀ x, ¬(p i' m x) by
      tintro m hltm
      tsimp only [p, Lentil.not_and_to_imp] at hmin ⊢
      tintro hmi
      tspecialize hmin m ((by omega) : m < j) hltm ((by grind) : m < i)
      tapply hmin
    tspecialize hconserves (⟨i', by omega⟩ : Fin ℐ.length) htmp
    trcases hconserves with ⟨-, hconserves⟩ ; tclear htmp hmin
    -- Combine the eventual and until delays; conservation holds throughout the prefix.
    texit
    intro e t ⟨⟨n, m, hfinal, _⟩, hconserves⟩
    refine ⟨n + m, ?_, fun k _ => hconserves k⟩
    simpa only [Nat.add_assoc] using hfinal
  · -- if there is no such `j`, then we set `i'` to be `i`
    tsimp only [Lentil.not_exists] at hc
    tspecialize hconserves (⟨i, hlt⟩ : Fin ℐ.length) hc
    trcases hconserves with ⟨hnp, hconserves⟩
    tclear hc hL2back ; clear p ih
    texists ⟨i, hlt⟩ , (Nat.le_refl _) ; tdsimp only
    -- prepare
    tspecialize hL2c (⟨i, hlt⟩ : Fin _) (List.finRange_fin_in _ _)
    tspecialize hL2b (⟨i, hlt⟩ : Fin _) (List.finRange_fin_in _ _)
    tdsimp only [required] at hL2b hL2c
    -- simplify `hL2c`
    thave hL2c' : □((ψ g ℐ[Fin.mk i hlt]) ∧ ¬(r g ℐ[Fin.mk i hlt]) → ◯(ψ g ℐ[Fin.mk i hlt])) by
      tclear *- hL2c hnp
      tmonotone ; trintro ⟨h1, h2⟩ ; tapply hL2c ; tsplit_ands <;> tassumption
    -- use `until_induction`
    thave htmp := until_induction ⟨hψi, hL2c'⟩
    tclear hL2c hL2c'
    thave hFr := always_weaken hS3
    trewrite [bigwedge_forall_fintype_list] at hFr
    tspecialize hFr (Fin.mk i hlt) hψi
    trcases htmp with (htmp | htmp)
    on_goal 1=>
      -- side goal
      trewrite [always_and, ← not_eventually] at htmp
      treplace htmp := Lentil.and_right htmp
      tcontradiction
    tclear hL2a hFr hS3 hψi hc
    texit ; tunfold_simp ; grind

-- NOTE: sometimes for goals that can be solved without unfolding the temporal definitions,
-- we discharge them by `tnontemporal_simp` (and doing semantic reasoning)
theorem rule11 (hne : ℐ ≠ []) :
  (S1 ∧ P2 ∧ P3 ∧ P4 ∧ S5 ∧ S6) |-tl- (p ↝ q) := by
  unfold leads_to always_implies
  -- prove by contradiction
  rw [← not_not (p := [tlfml| (p → ◇q) ]), not_implies_to_and, ← Lentil.imp_false (a := [tlfml| (p ∧ ¬◇q) ]), not_eventually]
  -- eliminate the `□` in the conclusion by applying `always_monotone`;
  -- if we instead lift its negation to the premise, then it will result in `◇`,
  -- which makes the proof complicated (we need to use things like `always_and_eventually` everywhere!)
  tstart hS1 hP2 hP3 hS4 hS5 hS6
  tsimp only [← always_bigwedge] at hP2 hP3 hS5
  tsimp only [← always_forall] at hP2 hP3
  ttoggle_goal_under_always ; trintro ⟨hp, hNG⟩
  treplace hS1 := always_weaken hS1
  -- use `S1`; we can now get rid of `p`
  thave hFϕ : ϕ ∧ □¬q by tsplit_ands ; tapply hS1 ⟨hp, hNG⟩ ; tassumption
  tclear hNG hp hS1
  -- use `P2` to show that once `ϕ ∧ □¬q` holds, then `□ϕ` holds
  thave hFGϕ : □(ϕ ∧ □¬q) by
    tsimp only [bigwedge_forall_list] at hP2
    trewrite [always_induction] ; tconstructor
    · tassumption
    · tclear *- hP2 hS4
      tmonotone ; trintro ⟨h1, h2⟩
      tspecialize hS4 ⟨h1, h2⟩ ; trcases hS4 with ⟨g, -⟩
      tspecialize hP2 g (Fin.mk 0 (by rw [List.length_pos_iff] ; exact hne)) (List.finRange_fin_in _ _) ⟨h1, h2⟩
      trewrite [later_and]
      trewrite [always_unroll] at h2
      trcases hP2 with ⟨_, _⟩ ; trcases h2 with ⟨_, _⟩ ; tsplit_ands <;> tassumption
  tclear hFϕ
  -- simplify `P3`
  thave hP3' : □(∀ g : γ, (⋀ i ∈ ℐ, (ψ g i) → ◇ (r g i))) by
    tclear *- hP3 hFGϕ
    tmonotone
    tintro g ; tspecialize hP3 g
    trewrite [bigwedge_forall_fintype_list] at *
    tintro x h ; trcases hFGϕ with ⟨h1, h2⟩
    tapply hP3 x ⟨h1, h2, h⟩
  tclear hP3 ; trename hP3' => hP3
  -- simplify `P2`
  thave hP2' : □ ∀ g : γ, (⋀ x ∈ List.finRange ℐ.length,
      ((¬(preempted ψ ℐ g x) → (conserves (δ ℐ[x]))) ∧
          ((required ψ ℐ g x) ∧ (r g ℐ[x]) → (reduces (δ ℐ[x]))) ∧
          ((required ψ ℐ g x) ∧ ¬(r g ℐ[x]) → ◯(ψ g ℐ[x])))) by
    tclear *- hP2 hFGϕ
    tmonotone
    tsimp only [bigwedge_forall_list] at hP2 ⊢
    tintro g x hx ; tspecialize hP2 g x hx
    tspecialize hP2 hFGϕ ; tapply Lentil.and_right hP2
  tclear hP2 ; trename hP2' => hP2
  -- use `P4` to know `□ (∃ g, ⋁ i ∈ ℐ, (ψ i))`
  tmap hS4' := hFGϕ using hS4
  tclear hS4 ; trename hS4' => hS4
  -- now show the main thing: `δ` will infinitely often decrease!
  thave hDC : (□⋁ i ∈ (List.finRange ℐ.length),
    ((⋀ j ∈ (ℐ.take (i.val + 1)), (conserves (δ j))) 𝑈
      ((⋀ j ∈ (ℐ.take (i.val + 1)), (conserves (δ j))) ∧ (reduces (δ ℐ[i]))))) by
    tclear *- hP2 hP3 hS4
    ttoggle_goal_under_always
    treplace hS4 := always_weaken hS4
    trcases hS4 with ⟨g, hS4⟩
    tapply (rule11_aux δ ψ r ℐ g) ; tsplit_ands <;> (try tassumption) <;> tclear hS4
    · tmonotone ; tapply hP3 g
    · tmonotone ; tapply hP2 g
  tclear hP2 hP3 hS4
  -- use `S5` to know that after `ϕ` happens, all `δ ℐ[i]` will be finite-support
  thave hfinδ : □(⋀ i ∈ ℐ, ⌜ simple_finite_record (δ i) ⌝) by
    tmonotone
    trewrite [bigwedge_forall_fintype_list] at hS5 ⊢
    treplace hFGϕ := Lentil.and_left hFGϕ
    tintro x ; tspecialize hS5 x hFGϕ ; tclear hDC hFGϕ
    texit ; tfinite_window
    aesop (add unsafe apply simple_finite_record_implies)
  tclear hFGϕ hS5 hS6
  -- now, just show that infinite descent is impossible
  tapply (no_infinite_descent _ _) ⟨hDC, hfinδ⟩

end rules_with_scheduler_and_parameter

section rules_with_scheduler

variable {σ : Type u} {α : Type v} {β : Type w} (R : α → σ → Prop) (δ : β → α → σ → Prop)
  (p q ϕ : pred σ) (ψ r : β → pred σ) (ℐ : List β)

local macro "S1" : term => `([tlfml| (p ∧ (¬ ◇ q) ⇒ ϕ) ])
local macro "S2" : term => `([tlfml| (⋀ i ∈ ℐ, ϕ ∧ (¬ ◇ q) ⇒
  ◯ ϕ ∧
  (conserves (δ i)) ∧
  ((ψ i) ∧ (r i) → (reduces (δ i))) ∧
  ((ψ i) ∧ ¬ (r i) → ◯ (ψ i))) ])
local macro "S3" : term => `([tlfml| (⋀ i ∈ ℐ, ϕ ∧ (¬ ◇ q) ∧ (ψ i) ⇒ ◇ (r i)) ])
local macro "S4" : term => `([tlfml| (ϕ ∧ (¬ ◇ q) ⇒ ⋁ i ∈ ℐ, (ψ i)) ])
local macro "S5" : term => `([tlfml| (⋀ i ∈ ℐ, ϕ ⇒ ∀ x, (⌜ δ i x ⌝ → ⌜ R x ⌝)) ])
local macro "S6" : term => `([tlfml| (□ ⌜ simple_finite_record R ⌝) ])

local macro "L2" : term => `([tlfml| (⋀ i ∈ (List.finRange ℐ.length), ϕ ∧ (¬ ◇ q) ⇒
  ◯ ϕ ∧
  (¬ (preempted (fun _ => ψ) ℐ Unit.unit i) → (conserves (δ ℐ[i]))) ∧
  ((required (fun _ => ψ) ℐ Unit.unit i) ∧ (r ℐ[i]) → (reduces (δ ℐ[i]))) ∧
  ((required (fun _ => ψ) ℐ Unit.unit i) ∧ ¬ (r ℐ[i]) → ◯ (ψ ℐ[i]))) ])

theorem rule10 (hne : ℐ ≠ []) :
  (S1 ∧ L2 ∧ S3 ∧ S4 ∧ S5 ∧ S6) |-tl- (p ↝ q) := by
  refine pred_implies_trans ?_ (rule11 (γ := Unit) R δ p q ϕ (fun _ => ψ) (fun _ => r) _ hne)
  simp only [Lentil.forall_unit, Lentil.exists_unit]
  apply pred_implies_refl

theorem rule8 (hne : ℐ ≠ []) :
  (S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5 ∧ S6) |-tl- (p ↝ q) := by
  -- we just show that `S2` implies `L2`
  have hS2L2 : (S2) |-tl- (L2) := by
    unfold always_implies ; intro e t h
    rw [bigwedge_forall_fintype_list] at h
    rw [bigwedge_forall_list] ; intro x tmp ; specialize h x
    revert h ; apply always_monotone ; clear e t tmp
    dsimp [required] ; tnontemporal_simp ; aesop
  intro e t ⟨hS1, hS2, hS3, hS4, hS5, hS6⟩
  exact rule10 _ _ _ _ _ _ _ _ hne e t ⟨hS1, hS2L2 _ _ hS2, hS3, hS4, hS5, hS6⟩

end rules_with_scheduler

section rules_without_scheduler

variable {σ : Type u} {α : Type v} (R δ : α → σ → Prop) (p q r ϕ : pred σ)

local macro "C0" : term => `([tlfml| (□ ⌜ simple_finite_record R ⌝) ])
local macro "C1" : term => `([tlfml| (p ⇒ (q ∨ ϕ ∧ ∀ x, (⌜ δ x ⌝ → ⌜ R x ⌝))) ])
local macro "C2" : term => `([tlfml| (ϕ ⇒ (◯ q ∨ ◯ ϕ ∧ (conserves δ))) ])
local macro "C3" : term => `([tlfml| ((ϕ ∧ r) ⇒ (◯ q ∨ (reduces δ))) ])

local macro "D1" : term => `([tlfml| (p ⇒ (◇ q ∨ ϕ ∧ ∀ x, (⌜ δ x ⌝ → ⌜ R x ⌝))) ])
local macro "D2" : term => `([tlfml| (ϕ ⇒ (◇ q ∨ ◯ ϕ ∧ (conserves δ))) ])
local macro "D3" : term => `([tlfml| ((ϕ ∧ r) ⇒ (◇ q ∨ (reduces δ))) ])
local macro "D4" : term => `([tlfml| (ϕ ⇒ (◇ q ∨ ◇ r)) ])

-- HMM why the following does not work? have to directly declare macros as terms
-- local macro "C0" : tlfml => `(tlfml| (□ ⌜ simple_finite_record R ⌝) )

/-! NOTE: To prove the `rule7` below, the basic idea is to just apply `rule8`,
    since `rule7` is mostly a special case of having only a single component of `δ`.

    However, a direct application is not possible, since `rule8` depends on
    the relational lexicographic order, so it requires `S5` to make sure that
    each `δ ℐ[i]` component is _constantly_ finite-support; otherwise, there can
    be irregular cases where for some `i`, `j` where `i < j`, `δ ℐ[i]` reduces but
    `δ ℐ[j]` becomes infinite-support. While in `rule7`, we only have a single
    `δ`, so it suffices to make sure that `δ` is finite support when `ϕ` happens.

    To bridge this gap, we apply `rule8` with a different `R` and `ϕ`. -/

-- FIXME: How to make `grind` or `aesop` to effectively work on these kinds of goals?

theorem rule7 : (C0 ∧ D1 ∧ D2 ∧ D3 ∧ D4) |-tl- (p ↝ q) := by
  -- intuitively, `R'` "remembers" the domain of `δ` when it becomes finite-support
  let R' := fun a s => (if simple_finite_record δ s then R a s ∨ δ a s else R a s)
  tstart hC0 hD1 hD2 hD3 hD4
  -- rw [eventually_to_always, ← implies_to_or, ← not_eventually] at hD1 hD2 hD3 hD4
  tapply rule8 (β := Unit) R' (δ := fun _ => δ) p q
    (ϕ := [tlfml| ϕ ∧ ⌜ simple_finite_record δ ⌝ ])  -- extend `ϕ` with the invariant that `δ` is finite-support
    (ψ := fun _ => [tlfml| ⊤ ]) (r := fun _ => r) (ℐ := [()]) (by simp)
  unfold always_implies
  tdsimp only [bigwedge_list_cons, bigwedge_list_nil, bigvee_list_cons, bigvee_list_nil]
  tnormalize
  trewrite [eventually_to_always, ← implies_to_or, ← not_eventually] at hD1 hD2 hD3 hD4
  tsplit_ands <;> tmonotone
  · tclear *- hC0 hD1
    trintro ⟨h1, h2⟩ ; tobtain ⟨hϕ, hh⟩ := hD1 h1 h2
    tsplit_ands ; tassumption
    tclear *- hC0 hh
    texit ; tfinite_window
    aesop (add unsafe apply simple_finite_record_implies)
  · tclear *- hD2 hD3
    trintro ⟨hϕ, hf, hh⟩
    tobtain ⟨h1, h2⟩ := hD2 hϕ hh
    trewrite [later_and] ; tsplit_ands <;> try tassumption
    · tclear *- h2 hf
      unfold conserves
      texit ; tfinite_window
      aesop (add unsafe apply relational_ge_implies_simple_finite_record)
    · tintro hr ; tapply hD3 ; tsplit_ands <;> tassumption
  · tclear *- hD4
    trintro ⟨hϕ, hf, hh⟩ ; tapply hD4 hϕ hh
  · trintro ⟨hϕ, h⟩
    tclear *- h
    texit ; tfinite_window
    aesop
  · tclear *- hC0
    texit ; tfinite_window
    simp [R', simple_finite_record]
    split <;> (try apply id)
    next h' => intro h ; apply simple_finite_or <;> assumption

theorem rule6 : (C0 ∧ C1 ∧ C2 ∧ C3) |-tl- (□ ◇ r → (p ↝ q)) := by
  -- for this rule, we do simple propositional reasoning
  tnormalize
  tstart hC0 hC1 hC2 hC3 hr
  tapply rule7 R δ p q r ϕ
  unfold always_implies
  tsplit_ands <;> try tassumption
  · tclear *- hC1 hC2
    tmonotone
    tintro hp ; tspecialize hC1 hp
    trcases hC1 with (hq | h)
    · treplace hq := now_weaken_to_eventually hq
      tleft ; tassumption
    · tright ; tassumption
  · tclear *- hC2
    tmonotone
    tintro hϕ ; tspecialize hC2 hϕ
    trcases hC2 with (hq | h)
    · treplace hq := later_weaken_to_eventually hq
      tleft ; tassumption
    · tright ; tassumption
  · -- FIXME: repetitive
    tclear *- hC3
    tmonotone
    tintro hϕ ; tspecialize hC3 hϕ
    trcases hC3 with (hq | h)
    · treplace hq := later_weaken_to_eventually hq
      tleft ; tassumption
    · tright ; tassumption
  · tclear *- hr
    tmonotone
    tintro h ; tright ; tassumption

end rules_without_scheduler

end RelationalRanking
