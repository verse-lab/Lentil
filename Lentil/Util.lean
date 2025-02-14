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

-- NOTE: the following part about induction on lists of natural numbers w.r.t. lexicographic order
-- is potentially in Lean (but not in the `main` branch), so here we just prove things
-- as we need

namespace NatListLex

section Main

universe u
variable {α : Type u} {n : Nat} (r : α → α → Prop) (rl : { l : List α // l.length = n } → { l : List α // l.length = n } → Prop)

/-- Given a list whose length is `n + 1`, return its head and tail
    and also an associated proof. -/
def List.succLengthInv (lo : { l : List α // l.length = n.succ }) :
  PSigma fun a => { l : List α // l.length = n ∧ lo.val = a :: l } :=
  match lo with
  | ⟨a :: l, h⟩ => ⟨a, ⟨l, And.intro (Nat.succ_inj'.mp h) rfl⟩⟩
  | ⟨[], h⟩ => by simp at h

/-- Just like `Prod.Lex`, but defined over the `(head, tail)` pairs
    of lists. -/
def List.consLex (l1 l2 : { l : List α // l.length = n.succ }) : Prop :=
  match List.succLengthInv l1, List.succLengthInv l2 with
  | ⟨x, ⟨l1, h1⟩⟩, ⟨y, ⟨l2, h2⟩⟩ => Prod.Lex r rl (x, ⟨l1, h1.1⟩) (y, ⟨l2, h2.1⟩)

-- adapted from `Prod.lexAccessible`
theorem consLexAccessible (aca : Acc r a) (acl : ∀ (b : { l : List α // l.length = n }), Acc rl b)
    (l : { l : List α // l.length = n }) :
  Acc (List.consLex r rl) (⟨a :: l.val, congrArg Nat.succ l.property⟩ : { l : List α // l.length = n.succ }) := by
  induction aca generalizing l with
  | intro xa _ iha =>
    induction (acl l) with
    | intro xl _ ihl =>
      apply Acc.intro
      intro ⟨l', hl'⟩ hlt
      rcases l' with _ | ⟨x', l'⟩ <;> simp at hl'
      simp [List.consLex] at hlt
      cases hlt with
      | left  _ _ h => simp [List.succLengthInv] at h ; apply iha _ h ⟨_, hl'⟩
      | right _ h   => simp [List.succLengthInv] at h ; apply ihl _ h

end Main

def List.cons_wfRel {α : Type u} {n : Nat} (h : WellFoundedRelation α)
  (hl : WellFoundedRelation { l : List α // l.length = n }) :
  WellFoundedRelation { l : List α // l.length = n.succ } where
  rel := List.consLex h.rel hl.rel
  wf := ⟨fun l =>
    match List.succLengthInv l with
    | ⟨a, ⟨l', hh⟩⟩ => (congrArg (Acc _) ((Subtype.eq (a1 := ⟨a :: l', _⟩) hh.2.symm))) ▸
      consLexAccessible _ _ (WellFounded.apply h.wf a) (WellFounded.apply hl.wf) ⟨l', hh.1⟩⟩

def List.natLexLt_wfRel (n : Nat) : WellFoundedRelation { l : List Nat // l.length = n } :=
  match n with
  | .zero => emptyWf
  | .succ n' => List.cons_wfRel Nat.lt_wfRel (List.natLexLt_wfRel n')

def List.natLexLt : List Nat → List Nat → Prop
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ natLexLt xs ys)
  | _, _ => False

/-- An equivalent way of expressing `List.natLexLt`. -/
def List.natLexLt' (l l' : List Nat) : Prop :=
  ∃ (i : Nat) (hlt : i < l.length) (hlt' : i < l'.length),
    l.take i = l'.take i ∧ l[i]'hlt < l'[i]'hlt'

theorem List.natLexLt_alt (l l' : List Nat) :
  List.natLexLt l l' ↔ List.natLexLt' l l' := by
  induction l generalizing l' with
  | nil => simp [List.natLexLt, List.natLexLt']
  | cons x l ih =>
    cases l' with
    | nil => simp [List.natLexLt, List.natLexLt']
    | cons y l' =>
      simp [List.natLexLt, List.natLexLt', ih] ; constructor
      · intro h ; cases h with
        | inl h => exists 0 ; simp ; assumption
        | inr h =>
          rcases h with ⟨heq, i, h⟩
          subst y ; exists (i + 1) ; simp ; exact h
      · intro ⟨i, htakeeq, h⟩
        cases i with
        | zero => simp at h ; apply Or.inl h
        | succ i =>
          simp at htakeeq h ; right ; apply And.intro htakeeq.1
          exists i ; apply And.intro htakeeq.2 h

-- the underlying `rel` of `List.natLexLt_wfRel` is `List.natLexLt`
theorem List.natLexLt_wfRel_rel (n : Nat) l l' :
  (List.natLexLt_wfRel n |>.rel l l') ↔ List.natLexLt l.val l'.val := by
  rcases l with ⟨l, hl⟩ ; rcases l' with ⟨l', hl'⟩
  induction n generalizing l l' with
  | zero => simp at hl hl' ; subst_vars ; simp [List.natLexLt_wfRel, emptyWf, List.natLexLt, emptyRelation]
  | succ n' ih =>
    rcases l with _ | ⟨x, l⟩ <;> simp at hl
    rcases l' with _ | ⟨y, l'⟩ <;> simp at hl'
    simp [List.natLexLt_wfRel, List.cons_wfRel, List.consLex, List.succLengthInv, List.natLexLt, Nat.lt_wfRel, Prod.lex_def, ih]

noncomputable def List.natLexRecOn
    {motive : List Nat → Sort u}
    (l : List Nat)
    (ind : ∀ l, (∀ l', l'.length = l.length → List.natLexLt l' l → motive l') → motive l) : motive l :=
  (List.natLexLt_wfRel l.length |>.wf.fix)
    (fun ⟨l', hl'⟩ (recc : ∀ (l_' : { l_ : List Nat // l_.length = l.length }), _ → motive l_') =>
      ind l' (fun l'' hl'' hlt =>
        recc ⟨l'', Eq.trans hl'' hl'⟩ ((List.natLexLt_wfRel_rel l.length ⟨l'', Eq.trans hl'' hl'⟩ ⟨l', hl'⟩ |>.mpr) hlt))) ⟨l, rfl⟩

end NatListLex

register_option lentil.pp.useDelab : Bool := {
  defValue := true
  descr := "Use Delab instead of Unexpander for delaboration. "
}

register_option lentil.pp.autoRenderSatisfies : Bool := {
  defValue := true
  descr := "Automatically render an application `p e` as `e |=tla= p` when `p` is a TLA formula. "
}

register_simp_attr tla_nontemporal_def  -- marking the non-temporal parts of TLA
register_simp_attr tlasimp_def
register_simp_attr tlasimp
register_simp_attr tladual      -- experimental
