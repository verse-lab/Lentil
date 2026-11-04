module

@[expose] public section

namespace LentilLib.ListLex

section Main

universe u
variable {α : Type u} {n : Nat} (r : α → α → Prop) (rl : { l : List α // l.length = n } → { l : List α // l.length = n } → Prop)

/-- Given a list whose length is `n + 1`, return its head and tail
    and also an associated proof. -/
def List.succLengthInv (lo : { l : List α // l.length = n.succ }) :
  PSigma fun a => { l : List α // l.length = n ∧ lo.val = a :: l } :=
  match lo with
  | ⟨a :: l, h⟩ => ⟨a, ⟨l, And.intro (Nat.succ_inj.mp h) rfl⟩⟩
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

/-- The auxiliary function for `List.lexLt_wfRel`. -/
@[implicit_reducible]
def List.cons_wfRel {α : Type u} {n : Nat} (h : WellFoundedRelation α)
  (hl : WellFoundedRelation { l : List α // l.length = n }) :
  WellFoundedRelation { l : List α // l.length = n.succ } where
  rel := List.consLex h.rel hl.rel
  wf := ⟨fun l =>
    match List.succLengthInv l with
    | ⟨a, ⟨l', hh⟩⟩ => (congrArg (Acc _) ((Subtype.ext (a1 := ⟨a :: l', _⟩) hh.2.symm))) ▸
      consLexAccessible _ _ (WellFounded.apply h.wf a) (WellFounded.apply hl.wf) ⟨l', hh.1⟩⟩

/-- Given `h : WellFoundedRelation α` and `n`, return the `WellFoundedRelation`
    (lexicographic order) on lists with length `n`. -/
@[implicit_reducible]
def List.lexLt_wfRel {α : Type u} (h : WellFoundedRelation α) (n : Nat) : WellFoundedRelation { l : List α // l.length = n } :=
  match n with
  | .zero => emptyWf
  | .succ n' => List.cons_wfRel h (List.lexLt_wfRel h n')

/-- The `<` operator for the lexicographic order on lists of a fixed length
    (although the length equality is not checked here). -/
def List.lexLt {α : Type u} (h : WellFoundedRelation α) : List α → List α → Prop
  | x :: xs, y :: ys => h.rel x y ∨ (x = y ∧ List.lexLt h xs ys)
  | _, _ => False

/-- An equivalent way of expressing `List.lexLt`. -/
def List.lexLt' {α : Type u} (h : WellFoundedRelation α) (l l' : List α) : Prop :=
  ∃ (i : Nat) (hlt : i < l.length) (hlt' : i < l'.length),
    l.take i = l'.take i ∧ h.rel (l[i]'hlt) (l'[i]'hlt')

/-- `List.lexLt` and `List.lexLt'` are equivalent. -/
theorem List.lexLt_alt {α : Type u} (h : WellFoundedRelation α) (l l' : List α) :
  List.lexLt h l l' ↔ List.lexLt' h l l' := by
  induction l generalizing l' with
  | nil => simp [List.lexLt, List.lexLt']
  | cons x l ih =>
    cases l' with
    | nil => simp [List.lexLt, List.lexLt']
    | cons y l' =>
      simp [List.lexLt, List.lexLt', ih] ; constructor
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

/-- The relation part of `List.lexLt_wfRel` is equivalent to `List.lexLt`.
    This makes the statement of the induction principle easier. -/
theorem List.lexLt_wfRel_rel {α : Type u} (h : WellFoundedRelation α) (n : Nat) l l' :
  (List.lexLt_wfRel h n |>.rel l l') ↔ List.lexLt h l.val l'.val := by
  rcases l with ⟨l, hl⟩ ; rcases l' with ⟨l', hl'⟩
  induction n generalizing l l' with
  | zero => simp at hl hl' ; subst_vars ; simp +instances [List.lexLt_wfRel, emptyWf, List.lexLt, emptyRelation]
  | succ n' ih =>
    rcases l with _ | ⟨x, l⟩ <;> simp at hl
    rcases l' with _ | ⟨y, l'⟩ <;> simp at hl'
    simp +instances [List.lexLt_wfRel, List.cons_wfRel, List.consLex, List.succLengthInv, List.lexLt, Prod.lex_def, ih]

/-- The induction principle of lists on the lexicographic order. -/
noncomputable def List.lexRecOn
    {α : Type u} {motive : List α → Sort v} (h : WellFoundedRelation α)
    (l : List α)
    (ind : ∀ l, (∀ l', l'.length = l.length → List.lexLt h l' l → motive l') → motive l) : motive l :=
  (List.lexLt_wfRel h l.length |>.wf.fix)
    (fun ⟨l', hl'⟩ (recc : ∀ (l_' : { l_ : List α // l_.length = l.length }), _ → motive l_') =>
      ind l' (fun l'' hl'' hlt =>
        recc ⟨l'', Eq.trans hl'' hl'⟩ ((List.lexLt_wfRel_rel h l.length ⟨l'', Eq.trans hl'' hl'⟩ ⟨l', hl'⟩ |>.mpr) hlt)))
    ⟨l, rfl⟩

end LentilLib.ListLex
