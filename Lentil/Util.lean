import Lean

open Lean

def binderIdentToFunBinder (stx : TSyntax ``binderIdent) : MacroM (TSyntax ``Parser.Term.funBinder) :=
  match stx with
  | `(binderIdent| $x:ident) =>  `(Parser.Term.funBinder| $x:ident )
  | `(binderIdent| _ ) =>  `(Parser.Term.funBinder| _ )
  | _ => Macro.throwUnsupported

theorem List.mem_forall_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∀ x, x ∈ l → p x) ↔ ∀ (x : Fin l.length), p l[x] := by
  constructor
  · intro h x ; apply h ; simp
  · intro h x hin ; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩ ; subst_vars ; exact h ⟨_, hlt⟩

theorem List.mem_exists_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∃ x, x ∈ l ∧ p x) ↔ ∃ (x : Fin l.length), p l[x] := by
  constructor
  · intro ⟨x, hin, h⟩ ; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩ ; subst_vars ; exists ⟨_, hlt⟩
  · intro ⟨n, h⟩ ; exists l[n] ; simp ; try assumption

theorem List.finRange_fin_in (n : Nat) : ∀ (x : Fin n), x ∈ List.finRange n := by
  intro ⟨x, hlt⟩ ; rw [List.mem_iff_getElem] ; simp ; assumption

-- sometimes we depend on theorems that themselves or similar ones
-- are present in Mathlib, but to reduce dependencies, we prove them here

-- NOTE: usually, the unification is not strong enough to figure out `p`,
-- which would be supplied by the user in practice
theorem Nat.find_min {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, m < n' → ¬ p m := by
  induction n using Nat.strongRecOn
  rename_i n ih
  by_cases h' : ∃ m, m < n ∧ p m
  · rcases h' with ⟨m, hlt, h'⟩
    have ⟨n', hle, ha, hb⟩ := ih _ hlt h'
    exists n' ; apply And.intro (by omega) (And.intro ‹_› ‹_›)
  · simp at h' ; exists n ; simp_all

theorem Nat.find_min' {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, p m → n' ≤ m := by
  have ⟨n', hn', ha, hb⟩ := Nat.find_min _ h
  exists n' ; apply And.intro ‹_› (And.intro ‹_› _) ; intros ; apply Nat.le_of_not_lt ; intro hlt ; solve_by_elim

register_option lentil.pp.useDelab : Bool := {
  defValue := true
  descr := "Use Delab instead of Unexpander for delaboration. "
}

register_option lentil.pp.autoRenderSatisfies : Bool := {
  defValue := true
  descr := "Automatically render an application `p e` as `e |=tla= p` when `p` is a TLA formula. "
}

/-- Marking the non-temporal parts of TLA. -/
register_simp_attr tla_nontemporal_def

/-- Marking the TLA definitions. -/
register_simp_attr tlasimp_def

/-- Marking the theorems that can be simplify reasoning at the TLA level. -/
register_simp_attr tlasimp

/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tladual

initialize registerTraceClass `lentil.debug
