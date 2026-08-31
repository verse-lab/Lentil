import Lentil
import Lentil.ProofMode.Display

/- Tests for the `trcases` tactic.

   Initial scope: destructuring `tl_and` (via `⟨pat₁, pat₂⟩`) and `tl_exists`
   (via `⟨witness, pat⟩`), mutually nested. The pattern syntax reuses Lean's
   built-in `rcasesPat` category, restricted to ident / `_` / tuple shapes.

   Note: `tstart` flattens conjunctions in the premise (via
   `splitAndIntoParts`), so a single hypothesis with an `a ∧ b` pred cannot
   appear right after `tstart`. The and-destructure tests below construct
   one via `thave hab := <lem> h` first.
-/

namespace Lentil.ProofMode.Test.RCases

open Lentil Lentil.ProofMode

variable {σ : Type u} (a b c d e : pred σ)

/-! ## And destructure -/

-- Single level: `trcases hab with ⟨ha, hb⟩` on `hab : a ∧ b`.
example (lem : (a) |-tl- (a ∧ b)) : (a) |-tl- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨ha, hb⟩
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  tassumption

-- N-ary tuple on a right-associated chain: `⟨ha, hb, hc⟩` on `h : a ∧ b ∧ c`.
example (lem : (a) |-tl- (a ∧ b ∧ c)) : (a) |-tl- (c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha, hb, hc⟩
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  tassumption

-- Wildcard sub-pattern: `⟨_, hb⟩` names only the right half (the left half
-- still lands in the temporal context, just with a hygienic name).
example (lem : (a) |-tl- (a ∧ b)) : (a) |-tl- (b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨_, hb⟩
  tcheck_goal_form
  tassumption

/-! ## Exists destructure -/

-- Single level: `trcases hex with ⟨n, hp⟩` on `hex : ∃ n, P n`.
example (P : Nat → pred σ) :
    (∃ n : Nat, (P n)) |-tl- (∃ n : Nat, (P n)) := by
  tstart hex
  trcases hex with ⟨n, hp⟩
  guard_target =ₛ Entails [⟨"hp", P n⟩] [tlfml| ∃ n : Nat, (P n)]
  texists n
  tassumption

-- Existential destructuring also introduces proof-valued witnesses.
example (Q : Prop) (P : Q → pred σ) :
    (∃ hQ : Q, (P hQ)) |-tl- (⊤) := by
  tstart h
  trcases h with ⟨hQ, hp⟩
  guard_target =ₛ Entails [⟨"hp", P hQ⟩] [tlfml| ⊤]
  tprove_pure
  trivial

-- Chained exists with n-ary tuple: `⟨x, y, hp⟩` on `h : ∃ a, ∃ b, P a b`.
example (P : Nat → Nat → pred σ) :
    (∃ x : Nat, (∃ y : Nat, (P x y))) |-tl- (∃ x : Nat, (∃ y : Nat, (P x y))) := by
  tstart h
  trcases h with ⟨x, y, hp⟩
  guard_target =ₛ Entails [⟨"hp", P x y⟩] [tlfml| ∃ x : Nat, (∃ y : Nat, (P x y))]
  texists x, y
  tassumption

/-! ## Mixed nest -/

-- `trcases h with ⟨n, ⟨ha, hb⟩⟩` on `h : ∃ y, A y ∧ B y`.
example (PA PB : Nat → pred σ) :
    (∃ n : Nat, ((PA n) ∧ (PB n))) |-tl- (∃ n : Nat, (PA n)) := by
  tstart h
  trcases h with ⟨n, ⟨ha, hb⟩⟩
  guard_target =ₛ Entails [⟨"ha", PA n⟩, ⟨"hb", PB n⟩] [tlfml| ∃ n : Nat, (PA n)]
  texists n
  tassumption

/-! ## Witness destructure (delegates to Lean's `rcases`) -/

-- Destruct a `Fin n` witness into its underlying value + proof.
example (P : Fin 3 → pred σ) :
    (∃ i : Fin 3, (P i)) |-tl- (∃ i : Fin 3, (P i)) := by
  tstart h
  trcases h with ⟨⟨v, hlt⟩, hp⟩
  -- After the destructure: `v : Nat`, `hlt : v < 3` in the Lean ctx,
  -- and the temporal hyp is `hp : P ⟨v, hlt⟩`.
  guard_target =ₛ Entails [⟨"hp", P ⟨v, hlt⟩⟩] [tlfml| ∃ i : Fin 3, (P i)]
  texists ⟨v, hlt⟩
  tassumption

-- Destruct a `Subtype` (e.g. `{n : Nat // n > 0}`) witness.
example (P : {n : Nat // n > 0} → pred σ) :
    (∃ x : {n : Nat // n > 0}, (P x)) |-tl- (∃ x : {n : Nat // n > 0}, (P x)) := by
  tstart h
  trcases h with ⟨⟨n, hpos⟩, hp⟩
  -- `n : Nat`, `hpos : n > 0`, hyp `hp : P ⟨n, hpos⟩`.
  guard_target =ₛ Entails [⟨"hp", P ⟨n, hpos⟩⟩] [tlfml| ∃ x : {n : Nat // n > 0}, (P x)]
  texists ⟨n, hpos⟩
  tassumption

-- Witness slot can be wildcard `_` — Lean's `rcases` is invoked but with
-- nothing to destructure, so the witness lands anonymously.
example (P : Nat → pred σ) :
    (∃ n : Nat, (P n)) |-tl- (∃ n : Nat, (P n)) := by
  tstart h
  trcases h with ⟨_, hp⟩
  texit
  apply Lentil.exists_elim ; rfl

/-! ## Top-level rename -/

example : (a) |-tl- (a) := by
  tstart h
  trcases h with h'
  guard_target =ₛ Entails [⟨"h'", a⟩] a
  exact pred_implies_refl _

/-! ## Or destructure -/

-- Single level: `trcases hab with (ha | hb)` on `hab : a ∨ b` splits into
-- two subgoals.
example (lem : (a) |-tl- (a ∨ b)) : (a) |-tl- (a ∨ b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with (ha | hb)
  · guard_target =ₛ Entails [⟨"ha", a⟩] (Lentil.tl_or a b)
    tleft
    tassumption
  · guard_target =ₛ Entails [⟨"hb", b⟩] (Lentil.tl_or a b)
    tright
    tassumption

-- N-ary alternation on a right-associated chain: `(ha | hb | hc)` on
-- `h : a ∨ b ∨ c` produces three subgoals.
example (lem : (a) |-tl- (a ∨ b ∨ c)) : (a) |-tl- (a ∨ b ∨ c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (ha | hb | hc)
  · tleft
    tassumption
  · tright
    tleft
    tassumption
  · tright
    tright
    tassumption

-- Alternation nested inside a tuple: `⟨ha, hb | hc⟩` on `h : a ∧ (b ∨ c)`.
-- The conjunct `ha` is retained in both branches.
example (lem : (a) |-tl- (a ∧ (b ∨ c))) : (a) |-tl- (a) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha, hb | hc⟩
  · tassumption
  · tassumption

-- Alternation crossing a sibling: `⟨ha | hb, hc⟩` on `h : (a ∨ b) ∧ c`. The
-- split happens in the first slot, yet `hc` must reach both branches.
example (lem : (a) |-tl- ((a ∨ b) ∧ c)) : (a) |-tl- (c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha | hb, hc⟩
  · tassumption
  · tassumption

-- Deep nest: both tuple slots case-split. The explicit bullets pin the goal
-- count at exactly four.
example (lem : (a) |-tl- ((a ∨ b) ∧ (c ∨ d))) : (a) |-tl- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha | hb, hc | hd⟩
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial

-- Deeper nest: an outer or-split whose first branch is the deep nest above and
-- whose second branch is a plain hypothesis. Five bullets pin the goal count.
example (lem : (a) |-tl- (((a ∨ b) ∧ (c ∨ d)) ∨ e)) : (a) |-tl- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (⟨ha | hb, hc | hd⟩ | he)
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial
  · tprove_pure
    trivial

-- Mixed and/or/exists nest: an existential whose body is an `or` of an `and`.
-- Two bullets: the `and` branch and the plain branch.
example (A B C : Nat → pred σ)
    (lem : (a) |-tl- (∃ n : Nat, (((A n) ∧ (B n)) ∨ (C n)))) :
    (a) |-tl- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨n, (⟨ha, hb⟩ | hc)⟩
  · tprove_pure
    trivial
  · tprove_pure
    trivial

/-! ## Obtain and by-cases -/

example (lem : |-tl- (a ∧ b)) : (⊤) |-tl- (a) := by
  tstart
  thave h := lem
  tobtain ⟨ha, hb⟩ := h
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  tassumption

example (P : Nat → pred σ) (lem : |-tl- (∃ n : Nat, (P n))) :
    (⊤) |-tl- (∃ n : Nat, (P n)) := by
  tstart
  tobtain ⟨n, hp⟩ := lem
  texists n
  tassumption

example (Q : Prop) (P : Q → pred σ) (lem : |-tl- (∃ hQ : Q, (P hQ))) :
    (a) |-tl- (⊤) := by
  tstart ha
  tobtain ⟨hQ, hp⟩ := lem
  guard_target =ₛ Entails [⟨"ha", a⟩, ⟨"hp", P hQ⟩] [tlfml| ⊤]
  tprove_pure
  trivial

example : (⊤) |-tl- (a ∨ ¬ a) := by
  tstart
  tby_cases ha : a
  · tleft
    tassumption
  · tright
    tassumption

/-! ## Clear (`-`) -/

-- Top-level `-` clears the targeted hypothesis.
example : (a) |-tl- (⊤) := by
  tstart h
  trcases h with -
  guard_target =ₛ Entails [] (tl_true : pred σ)
  tprove_pure
  trivial

-- `-` in a tuple slot discards that conjunct after destructuring.
example (lem : (a) |-tl- (a ∧ b)) : (a) |-tl- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨ha, -⟩
  guard_target =ₛ Entails [⟨"ha", a⟩] a
  tassumption

-- Symmetric: discard the left conjunct, keep the right.
example (lem : (a) |-tl- (a ∧ b)) : (a) |-tl- (b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨-, hb⟩
  guard_target =ₛ Entails [⟨"hb", b⟩] b
  tassumption

-- `tobtain - := h` routes through `tlRcasesCore` and clears `h`.
example : (a) |-tl- (⊤) := by
  tstart h
  tobtain - := h
  guard_target =ₛ Entails [] (tl_true : pred σ)
  tprove_pure
  trivial

-- `-` inside an alternation discards the introduced hypothesis on that branch.
example (lem : (a) |-tl- (a ∨ b)) : (a) |-tl- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (ha | -)
  · guard_target =ₛ Entails [⟨"ha", a⟩] (tl_true : pred σ)
    tprove_pure
    trivial
  · -- the `b`-branch hypothesis was cleared
    guard_target =ₛ Entails [] (tl_true : pred σ)
    tprove_pure
    trivial

/-! ## Errors -/

-- Pred head is neither `tl_and` nor `tl_exists`.
/--
error: trcases: cannot destructure pred a with pattern ⟨ha, hb⟩
-/
#guard_msgs in
example : (a) |-tl- (a) := by
  tstart h
  trcases h with ⟨ha, hb⟩

-- Alternation on a pred that is not a `tl_or`.
/--
error: trcases: cannot case-split pred a with alternation (ha | hb)
-/
#guard_msgs in
example : (a) |-tl- (a) := by
  tstart h
  trcases h with (ha | hb)

-- Reference to a hypothesis not in the Entails list.
/--
error: trcases: hypothesis 'noSuchHyp' not found in the goal's Entails list
-/
#guard_msgs in
example (lem : (a) |-tl- (a ∧ b)) : (a) |-tl- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases noSuchHyp with ⟨_, _⟩

-- Clearing a numeric location removes only that occurrence when names collide.
example (lem : (a) |-tl- (b)) : (a) |-tl- (a) := by
  tstart h
  thave h := lem h
  trcases 1 with -
  guard_target =ₛ Entails [⟨"h", a⟩] a
  tassumption

-- A name location also resolves to one exact occurrence rather than clearing
-- every hypothesis with that name.
example (lem : (a) |-tl- (b)) : (a) |-tl- (b) := by
  tstart h
  thave h := lem h
  trcases h with -
  guard_target =ₛ Entails [⟨"h", b⟩] b
  tassumption

-- Anonymous `tobtain` hypotheses receive distinct internal names, so clearing
-- the newer one does not discard an older wildcard hypothesis.
example (lemA : |-tl- (a)) (lemB : |-tl- (b)) : (⊤) |-tl- (a) := by
  tstart
  tobtain _ := lemA
  tobtain - := lemB
  tassumption

end Lentil.ProofMode.Test.RCases
