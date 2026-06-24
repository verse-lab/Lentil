import Lentil
import Lentil.ProofMode.Display

/- Tests for the `trcases` tactic.

   Initial scope: destructuring `tla_and` (via `⟨pat₁, pat₂⟩`) and `texists`
   (via `⟨witness, pat⟩`), mutually nested. The pattern syntax reuses Lean's
   built-in `rcasesPat` category, restricted to ident / `_` / tuple shapes.

   Note: `tstart` flattens conjunctions in the premise (via
   `splitAndIntoParts`), so a single hypothesis with an `a ∧ b` pred cannot
   appear right after `tstart`. The and-destructure tests below construct
   one via `thave hab := <lem> h` first.
-/

namespace TLA.ProofMode.Test.RCases

open TLA TLA.ProofMode

variable {σ : Type u} (a b c d e : pred σ)

/-! ## And destructure -/

-- Single level: `trcases hab with ⟨ha, hb⟩` on `hab : a ∧ b`.
example (lem : (a) |-tla- (a ∧ b)) : (a) |-tla- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨ha, hb⟩
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  intro _ ⟨ha, _⟩ ; exact ha

-- N-ary tuple on a right-associated chain: `⟨ha, hb, hc⟩` on `h : a ∧ b ∧ c`.
example (lem : (a) |-tla- (a ∧ b ∧ c)) : (a) |-tla- (c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha, hb, hc⟩
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩, ⟨"hc", c⟩] c
  intro _ ⟨_, _, hc⟩ ; exact hc

-- Wildcard sub-pattern: `⟨_, hb⟩` names only the right half (the left half
-- still lands in the temporal context, just with a hygienic name).
example (lem : (a) |-tla- (a ∧ b)) : (a) |-tla- (b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨_, hb⟩
  tcheck_goal_form
  intro _ ⟨_, hb⟩ ; exact hb

/-! ## Exists destructure -/

-- Single level: `trcases hex with ⟨n, hp⟩` on `hex : ∃ n, P n`.
example (P : Nat → pred σ) :
    (∃ n : Nat, (P n)) |-tla- (∃ n : Nat, (P n)) := by
  tstart hex
  trcases hex with ⟨n, hp⟩
  tcheck_goal_form
  tcheck_goal Entails [⟨"hp", P n⟩] (TLA.texists P)
  intro e hp
  exact ⟨n, hp⟩

-- Existential destructuring also introduces proof-valued witnesses.
example (Q : Prop) (P : Q → pred σ) :
    (∃ hQ : Q, (P hQ)) |-tla- (⊤) := by
  tstart h
  trcases h with ⟨hQ, hp⟩
  tcheck_goal Entails [⟨"hp", P hQ⟩] [tlafml| ⊤]
  intro _ _
  trivial

-- Chained exists with n-ary tuple: `⟨x, y, hp⟩` on `h : ∃ a, ∃ b, P a b`.
example (P : Nat → Nat → pred σ) :
    (∃ x : Nat, (∃ y : Nat, (P x y))) |-tla- (∃ x : Nat, (∃ y : Nat, (P x y))) := by
  tstart h
  trcases h with ⟨x, y, hp⟩
  tcheck_goal_form
  tcheck_goal Entails [⟨"hp", P x y⟩] [tlafml| ∃ x : Nat, (∃ y : Nat, (P x y))]
  intro e hp
  exact ⟨x, y, hp⟩

/-! ## Mixed nest -/

-- `trcases h with ⟨n, ⟨ha, hb⟩⟩` on `h : ∃ y, A y ∧ B y`.
example (PA PB : Nat → pred σ) :
    (∃ n : Nat, ((PA n) ∧ (PB n))) |-tla- (∃ n : Nat, (PA n)) := by
  tstart h
  trcases h with ⟨n, ⟨ha, hb⟩⟩
  tcheck_goal_form
  tcheck_goal Entails [⟨"ha", PA n⟩, ⟨"hb", PB n⟩] [tlafml| ∃ n : Nat, (PA n)]
  intro e ⟨ha, _⟩
  exact ⟨n, ha⟩

/-! ## Witness destructure (delegates to Lean's `rcases`) -/

-- Destruct a `Fin n` witness into its underlying value + proof.
example (P : Fin 3 → pred σ) :
    (∃ i : Fin 3, (P i)) |-tla- (∃ i : Fin 3, (P i)) := by
  tstart h
  trcases h with ⟨⟨v, hlt⟩, hp⟩
  -- After the destructure: `v : Nat`, `hlt : v < 3` in the Lean ctx,
  -- and the temporal hyp is `hp : P ⟨v, hlt⟩`.
  tcheck_goal Entails [⟨"hp", P ⟨v, hlt⟩⟩] [tlafml| ∃ i : Fin 3, (P i)]
  intro e hp
  exact ⟨⟨v, hlt⟩, hp⟩

-- Destruct a `Subtype` (e.g. `{n : Nat // n > 0}`) witness.
example (P : {n : Nat // n > 0} → pred σ) :
    (∃ x : {n : Nat // n > 0}, (P x)) |-tla- (∃ x : {n : Nat // n > 0}, (P x)) := by
  tstart h
  trcases h with ⟨⟨n, hpos⟩, hp⟩
  -- `n : Nat`, `hpos : n > 0`, hyp `hp : P ⟨n, hpos⟩`.
  tcheck_goal Entails [⟨"hp", P ⟨n, hpos⟩⟩] [tlafml| ∃ x : {n : Nat // n > 0}, (P x)]
  intro e hp
  exact ⟨⟨n, hpos⟩, hp⟩

-- Witness slot can be wildcard `_` — Lean's `rcases` is invoked but with
-- nothing to destructure, so the witness lands anonymously.
example (P : Nat → pred σ) :
    (∃ n : Nat, (P n)) |-tla- (∃ n : Nat, (P n)) := by
  tstart h
  trcases h with ⟨_, hp⟩
  intro e hp
  -- The anonymous Nat witness is still in scope; we use Exists.intro to
  -- reuse it (any concrete Nat would do).
  exact ⟨_, hp⟩

/-! ## Top-level rename -/

example : (a) |-tla- (a) := by
  tstart h
  trcases h with h'
  tcheck_goal Entails [⟨"h'", a⟩] a
  exact pred_implies_refl _

/-! ## Or destructure -/

-- Single level: `trcases hab with (ha | hb)` on `hab : a ∨ b` splits into
-- two subgoals.
example (lem : (a) |-tla- (a ∨ b)) : (a) |-tla- (a ∨ b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with (ha | hb)
  · tcheck_goal_form
    tcheck_goal Entails [⟨"ha", a⟩] (TLA.tla_or a b)
    intro _ ha ; exact Or.inl ha
  · tcheck_goal_form
    tcheck_goal Entails [⟨"hb", b⟩] (TLA.tla_or a b)
    intro _ hb ; exact Or.inr hb

-- N-ary alternation on a right-associated chain: `(ha | hb | hc)` on
-- `h : a ∨ b ∨ c` produces three subgoals.
example (lem : (a) |-tla- (a ∨ b ∨ c)) : (a) |-tla- (a ∨ b ∨ c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (ha | hb | hc)
  · intro _ ha ; exact Or.inl ha
  · intro _ hb ; exact Or.inr (Or.inl hb)
  · intro _ hc ; exact Or.inr (Or.inr hc)

-- Alternation nested inside a tuple: `⟨ha, hb | hc⟩` on `h : a ∧ (b ∨ c)`.
-- The conjunct `ha` is retained in both branches.
example (lem : (a) |-tla- (a ∧ (b ∨ c))) : (a) |-tla- (a) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha, hb | hc⟩
  · intro _ ⟨ha, _⟩ ; exact ha
  · intro _ ⟨ha, _⟩ ; exact ha

-- Alternation crossing a sibling: `⟨ha | hb, hc⟩` on `h : (a ∨ b) ∧ c`. The
-- split happens in the first slot, yet `hc` must reach both branches.
example (lem : (a) |-tla- ((a ∨ b) ∧ c)) : (a) |-tla- (c) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha | hb, hc⟩
  · intro _ ⟨hc, _⟩ ; exact hc
  · intro _ ⟨hc, _⟩ ; exact hc

-- Deep nest: both tuple slots case-split. The explicit bullets pin the goal
-- count at exactly four.
example (lem : (a) |-tla- ((a ∨ b) ∧ (c ∨ d))) : (a) |-tla- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨ha | hb, hc | hd⟩
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro

-- Deeper nest: an outer or-split whose first branch is the deep nest above and
-- whose second branch is a plain hypothesis. Five bullets pin the goal count.
example (lem : (a) |-tla- (((a ∨ b) ∧ (c ∨ d)) ∨ e)) : (a) |-tla- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (⟨ha | hb, hc | hd⟩ | he)
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro

-- Mixed and/or/exists nest: an existential whose body is an `or` of an `and`.
-- Two bullets: the `and` branch and the plain branch.
example (A B C : Nat → pred σ)
    (lem : (a) |-tla- (∃ n : Nat, (((A n) ∧ (B n)) ∨ (C n)))) :
    (a) |-tla- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with ⟨n, (⟨ha, hb⟩ | hc)⟩
  · intro _ _ ; exact True.intro
  · intro _ _ ; exact True.intro

/-! ## Obtain and by-cases -/

example (lem : |-tla- (a ∧ b)) : (⊤) |-tla- (a) := by
  tstart
  thave h := lem
  tobtain ⟨ha, hb⟩ := h
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hb", b⟩] a
  tassumption

example (P : Nat → pred σ) (lem : |-tla- (∃ n : Nat, (P n))) :
    (⊤) |-tla- (∃ n : Nat, (P n)) := by
  tstart
  tobtain ⟨n, hp⟩ := lem
  intro e hp
  exact ⟨n, hp⟩

example (Q : Prop) (P : Q → pred σ) (lem : |-tla- (∃ hQ : Q, (P hQ))) :
    (a) |-tla- (⊤) := by
  tstart ha
  tobtain ⟨hQ, hp⟩ := lem
  tcheck_goal Entails [⟨"ha", a⟩, ⟨"hp", P hQ⟩] [tlafml| ⊤]
  intro _ _
  trivial

example : (⊤) |-tla- (a ∨ ¬ a) := by
  tstart
  tby_cases ha : a
  · intro _ ha ; exact Or.inl ha
  · intro _ ha ; exact Or.inr ha

/-! ## Clear (`-`) -/

-- Top-level `-` clears the targeted hypothesis.
example : (a) |-tla- (⊤) := by
  tstart h
  trcases h with -
  tcheck_goal Entails [] (tla_true : pred σ)
  intro _ _ ; exact True.intro

-- `-` in a tuple slot discards that conjunct after destructuring.
example (lem : (a) |-tla- (a ∧ b)) : (a) |-tla- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨ha, -⟩
  tcheck_goal Entails [⟨"ha", a⟩] a
  intro _ ha ; exact ha

-- Symmetric: discard the left conjunct, keep the right.
example (lem : (a) |-tla- (a ∧ b)) : (a) |-tla- (b) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases hab with ⟨-, hb⟩
  tcheck_goal Entails [⟨"hb", b⟩] b
  intro _ hb ; exact hb

-- `tobtain - := h` routes through `tlaRcasesCore` and clears `h`.
example : (a) |-tla- (tla_true) := by
  tstart h
  tobtain - := h
  tcheck_goal Entails [] (tla_true : pred σ)
  intro _ _ ; exact True.intro

-- `-` inside an alternation discards the introduced hypothesis on that branch.
example (lem : (a) |-tla- (a ∨ b)) : (a) |-tla- (⊤) := by
  tstart ha0
  thave h := lem ha0
  tclear ha0
  trcases h with (ha | -)
  · tcheck_goal Entails [⟨"ha", a⟩] (tla_true : pred σ)
    intro _ _ ; exact True.intro
  · -- the `b`-branch hypothesis was cleared
    tcheck_goal Entails [] (tla_true : pred σ)
    intro _ _ ; exact True.intro

/-! ## Errors -/

-- Pred head is neither `tla_and` nor `texists`.
/--
error: trcases: cannot destructure pred a with pattern ⟨ha, hb⟩
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tstart h
  trcases h with ⟨ha, hb⟩

-- Alternation on a pred that is not a `tla_or`.
/--
error: trcases: cannot case-split pred a with alternation (ha | hb)
-/
#guard_msgs in
example : (a) |-tla- (a) := by
  tstart h
  trcases h with (ha | hb)

-- Reference to a hypothesis not in the Entails list.
/--
error: trcases: hypothesis 'noSuchHyp' not found in the goal's Entails list
-/
#guard_msgs in
example (lem : (a) |-tla- (a ∧ b)) : (a) |-tla- (a) := by
  tstart ha0
  thave hab := lem ha0
  tclear ha0
  trcases noSuchHyp with ⟨_, _⟩

end TLA.ProofMode.Test.RCases
