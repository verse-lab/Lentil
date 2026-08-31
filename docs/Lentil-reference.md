# Lentil reference manual

A complete map of the notation, proof-mode tactics, and automation hooks defined
in the Lentil library.

For a condensed one-pager see [Lentil-cheatsheet.md](Lentil-cheatsheet.md).
Additional rules that apply to AI agents writing Lentil proofs are collected in
[Lentil-agent-appendix.md](Lentil-agent-appendix.md).

Usually the notation and tactics below are already in scope. Otherwise:

```lean
import Lentil
```

## Contents

- [Lentil reference manual](#lentil-reference-manual)
  - [Contents](#contents)
  - [Formula notation](#formula-notation)
    - [The underlying types](#the-underlying-types)
    - [Writing formulas](#writing-formulas)
  - [Term-level notation](#term-level-notation)
  - [Parser precedence rules](#parser-precedence-rules)
  - [Proof-mode mental model](#proof-mode-mental-model)
  - [Common locations](#common-locations)
  - [Entering, exiting, and checking proof mode](#entering-exiting-and-checking-proof-mode)
    - [`tnormalize`](#tnormalize)
    - [`tstart`](#tstart)
    - [`texit`](#texit)
    - [`tcheck_goal_form`](#tcheck_goal_form)
  - [Introducing and reverting binders](#introducing-and-reverting-binders)
    - [`tintro`](#tintro)
    - [`trintro`](#trintro)
    - [`trevert`](#trevert)
    - [`trevert_all`](#trevert_all)
  - [Context management](#context-management)
    - [`tassumption`](#tassumption)
    - [`tclear`](#tclear)
    - [`trename`](#trename)
    - [`tpull_pure`](#tpull_pure)
    - [`tcontradiction`](#tcontradiction)
  - [Goal construction](#goal-construction)
    - [`texists`](#texists)
    - [`tleft` and `tright`](#tleft-and-tright)
    - [`tsplit_ands`](#tsplit_ands)
    - [`tprove_pure`](#tprove_pure)
    - [`texfalso`](#texfalso)
    - [`tby_cases`](#tby_cases)
  - [Applying, deriving, and specializing facts](#applying-deriving-and-specializing-facts)
    - [`tspecialize`](#tspecialize)
    - [`thave`](#thave)
    - [`thave'`](#thave-1)
    - [`treplace`](#treplace)
    - [`tsuffices`](#tsuffices)
    - [`tapply`](#tapply)
    - [`tapply'`](#tapply-1)
    - [`tmap`](#tmap)
  - [Destructuring temporal hypotheses](#destructuring-temporal-hypotheses)
    - [`trcases`](#trcases)
    - [`tobtain`](#tobtain)
  - [Rewriting and simplification in proof mode](#rewriting-and-simplification-in-proof-mode)
    - [`trewrite`](#trewrite)
    - [`tsimp`](#tsimp)
    - [`tdsimp`](#tdsimp)
    - [`tunfold`](#tunfold)
  - [Temporal/modal automation](#temporalmodal-automation)
    - [`tmonotone`](#tmonotone)
    - [`ttoggle_goal_under_always`](#ttoggle_goal_under_always)
    - [`tadvance`](#tadvance)
    - [`tstep`](#tstep)
  - [Finite-window tactic](#finite-window-tactic)
    - [`tfinite_window`](#tfinite_window)
  - [Helpers outside proof mode](#helpers-outside-proof-mode)
  - [Common proof recipes](#common-proof-recipes)
    - [Prove from an assumption](#prove-from-an-assumption)
    - [Prove a conjunction](#prove-a-conjunction)
    - [Prove a disjunction](#prove-a-disjunction)
    - [Introduce a temporal implication](#introduce-a-temporal-implication)
    - [Destructure an introduced conjunction](#destructure-an-introduced-conjunction)
    - [Apply a theorem with temporal premises](#apply-a-theorem-with-temporal-premises)
    - [Keep a derived fact](#keep-a-derived-fact)
    - [Pull a pure fact to Lean](#pull-a-pure-fact-to-lean)
    - [Rewrite in a temporal hypothesis](#rewrite-in-a-temporal-hypothesis)
    - [Use monotonicity](#use-monotonicity)
  - [Troubleshooting](#troubleshooting)

## Formula notation

### The underlying types

Throughout, `σ` is the type of the *states* of the system being specified — for
a counter it might be `Nat`, for a protocol a structure of variables. Everything
else is built on it:

| Type | Definition | Meaning |
|---|---|---|
| `exec σ` | `Nat → σ` | An execution: the state at each time index. Executions are infinite. |
| `pred σ` | `exec σ → Nat → Prop` | A temporal formula, evaluated at one index of one execution. |
| `action σ` | `σ → σ → Prop` | A relation between the current state and the next one. |

So a formula is not a `Prop` but a `pred σ`, and the notations below are ways of
building one:

- `⌜ p ⌝` holds at index `i` when `p` holds of the state `e i`;
- `⟨ a ⟩` holds at index `i` when `a` relates `e i` and `e (i + 1)`;
- `□ p` holds at `i` when `p` holds at every `i + k`, and `◇ p` when it holds at
  some `i + k`;
- `|-tl- p` (validity) means `p` holds at *every* index of *every* execution.

### Writing formulas

Lentil defines a separate syntax category `tlfml`. Write a formula as a Lean
term with:

```lean
[tlfml| ... ]
```

In proofs you rarely need this wrapper, and it reads better without it: some
proof-mode tactics let you write temporal formulas directly.

Formula forms:

| Syntax | Expands to | Meaning |
|---|---|---|
| `[tlfml| t]` | `t` | Atomic fallback: any Lean term of type `Lentil.pred σ` can be an atom. |
| `⌜ p ⌝` | `Lentil.state_pred p` | State predicate, `p : σ → Prop`. |
| `⌞ P ⌟` | `Lentil.pure_pred P` | Pure Lean proposition, `P : Prop`. |
| `⟨ a ⟩` | `Lentil.action_pred a` | Action predicate, `a : σ → σ → Prop`. |
| `⊤` | `Lentil.tl_true` | True predicate. |
| `⊥` | `Lentil.tl_false` | False predicate. |
| `¬ p` | `Lentil.tl_not p` | Negation. |
| `□ p` | `Lentil.always p` | Always. |
| `◇ p` | `Lentil.eventually p` | Eventually. |
| `◯ p` | `Lentil.later p` | Next/later. |
| `Enabled a` | `Lentil.tl_enabled a` | Enabled action. |
| `p → q` | `Lentil.tl_implies p q` | Temporal implication. |
| `p ∧ q` | `Lentil.tl_and p q` | Conjunction. |
| `p ∨ q` | `Lentil.tl_or p q` | Disjunction. |
| `p 𝑈 q` | `Lentil.tl_until p q` | Until. |
| `p ↝ q` | `Lentil.leads_to p q` | Leads-to, defined as `□ (p → ◇ q)`. |
| `p ⇒ q` | `Lentil.always_implies p q` | Always-implies, defined as `□ (p → q)`. |
| `𝒲ℱ a` | `Lentil.weak_fairness a` | Weak fairness for action `a`. |
| `∀ x, p x` | `Lentil.tl_forall (fun x => p x)` | Temporal universal quantifier. |
| `∃ x, p x` | `Lentil.tl_exists (fun x => p x)` | Temporal existential quantifier. |
| `⋀ x ∈ xs, p x` | `Lentil.tl_bigwedge (fun x => p x) xs` | Big conjunction over a `Foldable`. |
| `⋁ x ∈ xs, p x` | `Lentil.tl_bigvee (fun x => p x) xs` | Big disjunction over a `Foldable`. |

Quantifiers support typed binders:

```lean
[tlfml| ∀ n : Nat, P n ∧ q]
[tlfml| ∃ n : Nat, P n]
```

Big operators use binder identifiers:

```lean
[tlfml| ⋀ i ∈ xs, P i]
[tlfml| ⋁ i ∈ xs, P i]
```

## Term-level notation

These notations produce Lean terms:

| Syntax | Expands to | Meaning |
|---|---|---|
| `(p) |-tl- (q)` | `Lentil.pred_implies p q` | Sequent/predicate implication. |
| `|-tl- p` | `Lentil.valid p` | Validity. |
| `(p) =tl= (q)` | `[tlfml| p] = [tlfml| q]` | Definitional equality between predicates. |
| `e |=tl= p` | `Lentil.exec.satisfies p e` | Execution `e` satisfies formula `p`. |

Examples:

```lean
example : (p ∧ q) |-tl- (p) := by
  tstart hp hq
  tassumption

example : (|-tl- (p → q)) = Lentil.valid [tlfml| p → q] := rfl
```

## Parser precedence rules

Facts pinned by `LentilTest/Notation.lean`:

- Lean applications are accepted as formula atoms: `P n ∧ q` parses as `(P n) ∧ q`.
- `Enabled A n ∧ p` parses as `(Enabled (A n)) ∧ p`.
- `𝒲ℱ A n ∧ p` parses as `(𝒲ℱ (A n)) ∧ p`.
- `∀` and `∃` scope over the whole following formula.
- Unary temporal operators bind more tightly than `𝑈`.
- `𝑈` binds more tightly than `∧` and `∨`.
- Temporal implication `→` is right-associative: `p → q → r` is `p → (q → r)`.
- `↝` and `⇒` bind more tightly than plain `→`.
- Parenthesize mixed implication-like expressions unless the intended parse is
  obvious.
- Both sides of `|-tl-` and of `=tl=` must be maximal-precedence formulas: a
  bracketed atom (`⌜ p ⌝`, `⌞ P ⌟`, `⟨ a ⟩`, `⊤`, `⊥`), a unary-modality
  application (`□ p`), or a parenthesized formula. A bare Lean term such as a
  variable `p` is not accepted, so write `(p ∧ q) |-tl- (r)`, not
  `(p ∧ q) |-tl- r`.
- `|-tl-` as validity binds tighter than a temporal `→`, so `|-tl- p → q` parses
  as `(|-tl- p) → q` at the Lean level. Write `|-tl- (p → q)`.

Examples:

```lean
[tlfml| p ∧ q 𝑈 r] = [tlfml| p ∧ (q 𝑈 r)]
[tlfml| p → q ∨ r] = [tlfml| p → (q ∨ r)]
[tlfml| p ⇒ q → r] = [tlfml| (p ⇒ q) → r]
```

## Proof-mode mental model

Proof mode represents a sequent as:

```lean
Lentil.ProofMode.Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
```

The pretty-printer displays it as:

```text
hp : p
hq : q
|-tl- r
```

Important:

- Temporal hypotheses are not Lean local hypotheses. They live in the `Entails` list.
- Ordinary Lean tactics do not see temporal hypotheses unless a tactic exits/rewrites proof mode.
- New temporal hypotheses are usually appended to the end of the list.
- Numeric temporal hypothesis indices are zero-based and refer to the current proof-mode list order.
- A Lean local can shadow a temporal hypothesis name. Tactics that accept bare terms check Lean locals first where relevant.

## Common locations

`temporalHypLoc` is either a hypothesis name or a numeric index:

```lean
trename hp => hp'
trename 0 => hHead
trcases hp with ⟨ha, hb⟩
trcases 0 with ⟨ha, hb⟩
tspecialize h hp
tspecialize 2 hp
```

Rewrite/simp-like tactics use Lean location syntax, but locations refer to proof-mode predicates:

```lean
trewrite [heq]              -- goal only
trewrite [heq] at hp        -- temporal hyp `hp` only
trewrite [← heq] at hp ⊢    -- hyp `hp` and goal
trewrite [heq] at *         -- each temporal hyp and the goal

tsimp [defs] at hp hq
tdsimp [wrap] at *
tunfold wrap at hp ⊢
```

## Entering, exiting, and checking proof mode

### `tnormalize`

```lean
tnormalize
```

Normalizes raw temporal goals using `[tlnormsimp]`. Useful before `tstart`, especially when a goal is `|-tl- (p → q)` and should become `(p) |-tl- (q)`.

### `tstart`

```lean
tstart h1 h2 ...
```

Enters proof mode from a raw `(p) |-tl- (q)` sequent. It splits the left side conjunction into named temporal hypotheses.

```lean
example : (p ∧ q) |-tl- (r) := by
  tstart hp hq
  -- hp : p
  -- hq : q
```

Rules and pitfalls:

- `tstart` requires exactly one name per flattened left-side conjunct.
- `tstart` from `(⊤) |-tl- (p)` takes no names.
- Names must be distinct.
- It only supports goals reducible to a single `|-tl-` sequent.

### `texit`

```lean
texit
```

Leaves proof mode by converting `Entails` back to a raw sequent. Empty context becomes `|-tl- (goal)`; one hypothesis becomes `(p) |-tl- (goal)`; multiple hypotheses become a conjunction.

### `tcheck_goal_form`

```lean
tcheck_goal_form
```

Test/debug tactic. Succeeds only if the current goal is a canonical literal `Entails [...] goal`.

To check exact temporal hypothesis names/order and definitional equality of
predicates, use Lean's own `guard_target`:

```lean
guard_target =ₛ Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
```

## Introducing and reverting binders

### `tintro`

```lean
tintro x1 x2 ...
```

Introduces from the proof-mode goal:

- `∀ x, p x`: introduces Lean local `x`.
- `⌞P⌟ → q`: introduces Lean proof `hP : P`.
- `p → q`: adds temporal hypothesis `h : p`.

Example:

```lean
tintro n hp hPure
```

### `trintro`

```lean
trintro pat1 pat2 ...
```

Like `tintro`, but accepts `rintro`/`rcases`-style patterns. For a temporal implication `p → q`, it adds `p` as a temporal hypothesis and immediately destructures it.

```lean
trintro ⟨hp, hq⟩
trintro (hp | hq)
trintro n ⟨hp, hq⟩
trintro -
```

Supported temporal patterns are identifiers, `_`, `-`, tuples `⟨...⟩`, and parenthesized alternations `(p | q | ...)`.

### `trevert`

```lean
trevert h1 h2 ...
```

Moves assumptions back into the proof-mode goal.

- Temporal hyp `hp : p` becomes goal `p → goal`.
- Lean proof `hP : P` becomes goal `⌞P⌟ → goal`.
- Non-Prop Lean local `n : Nat` becomes goal `∀ n, goal`.

Names are processed so the written order becomes the outer-to-inner goal order.

### `trevert_all`

```lean
trevert_all
```

Moves all temporal hypotheses back into the goal as a chain of temporal implications. It does not revert Lean locals.

## Context management

### `tassumption`

```lean
tassumption
```

Closes a proof-mode goal if the target predicate appears among temporal hypotheses by definitional equality. Outside proof mode, falls back to Lean `assumption`.

### `tclear`

```lean
tclear h1 h2 ...
tclear * - hKeep1 hKeep2 ...
```

Removes temporal hypotheses by name, or removes all except listed names.

Note: `tclear` accepts names, not numeric indices.

### `trename`

```lean
trename old => new
trename 0 => hHead
```

Renames a temporal hypothesis by name or index. Predicate and position are unchanged.

### `tpull_pure`

```lean
tpull_pure hP hQ
```

Moves pure temporal hypotheses `hP : ⌞P⌟` into Lean's local context as ordinary proofs `hP : P`, removing them from the temporal context.

### `tcontradiction`

```lean
tcontradiction
```

Closes any proof-mode goal when the temporal context contains:

- `⊥`, or
- both `p` and `¬ p`.

## Goal construction

### `texists`

```lean
texists w1, w2, ...
```

Provides witnesses for temporal existential goals, left to right.

```lean
texists 0
texists n, m
```

### `tleft` and `tright`

```lean
tleft
tright
```

For a disjunctive goal `p ∨ q`, reduce to the left or right disjunct.

### `tsplit_ands`

```lean
tsplit_ands
```

Splits a conjunctive proof-mode goal into separate goals.

### `tprove_pure`

```lean
tprove_pure
```

For a pure conclusion `⌞P⌟`, reduces the remaining proof obligation to the Lean proposition `P`.

### `texfalso`

```lean
texfalso
```

Changes the current proof-mode goal to `⊥`, the temporal counterpart of Lean's
`exfalso`. Useful when the remaining work is to derive a contradiction from the
temporal context; see also `tcontradiction`.

### `tby_cases`

```lean
tby_cases h : p
```

Splits into two proof-mode goals: one with `h : p`, one with `h : ¬ p`.

## Applying, deriving, and specializing facts

### `tspecialize`

```lean
tspecialize h arg1 arg2 ...
tspecialize 0 arg1 arg2 ...
```

Specializes a temporal hypothesis in place. Each argument is consumed according to the current shape of the selected hypothesis:

- `∀ x, p x`: argument is a Lean witness.
- `⌞P⌟ → q`: argument is a Lean proof of `P`.
- `p → q`: argument names existing proof-mode hypothesis/hypotheses.
- Multiple temporal premises can be passed as a flat tuple: `⟨hp, hq⟩`.

Examples:

```lean
tspecialize h 0
tspecialize h hPure
tspecialize h hp
tspecialize h ⟨hp, hq⟩
tspecialize h 0 hp
```

Pitfall: temporal implication arguments must be proof-mode hypothesis names, not arbitrary Lean terms.

### `thave`

Forms:

```lean
thave h : p by
  tac

thave h := t
thave := t
```

Adds a temporal hypothesis.

- `thave h : p by tac` proves `p` in the current proof-mode context using `tac`, then appends `h : p`.
- `thave h := t` adds the temporal theorem/fact obtained from `t`.
- `thave := t` uses the default proof-mode name `"this"`.

Examples:

```lean
thave hb : b by
  tapply lemAB
  tassumption

thave hb := lem ha
thave := lem
```

If `t` starts with a bare proof-mode hypothesis name, the hypothesis is duplicated and then specialized with the remaining arguments.

### `thave'`

```lean
thave' h := thm arg1 arg2 ...
thave' h := @thm arg1 arg2 ...
```

Restricted variant of `thave h := ...`:

- theorem head must be an identifier;
- arguments may be written as temporal formulas without `[tlfml| ... ]`;
- `@thm` exposes implicit theorem arguments.

Examples:

```lean
thave' h := lem (a ∧ b)
thave' h := @lem a (b ∧ c) ha
```

### `treplace`

```lean
treplace h := t
```

Replaces named temporal hypothesis `h` with the temporal fact obtained from `t`. Internally behaves like `thave`, `tclear`, then `trename`; the replacement is appended before being renamed back to `h`.

### `tsuffices`

```lean
tsuffices h : p by
  tac
```

Changes the main goal to proving `p`. In the `by` block, the original goal is available with an additional temporal hypothesis `h : p`.

Example:

```lean
tsuffices hbc : b ∧ c by
  trcases hbc with ⟨hb, hc⟩
  tassumption
```

### `tapply`

```lean
tapply t
```

Proves the current proof-mode goal using a temporal theorem or hypothesis. If the theorem has unsupplied temporal premises, they become new proof-mode goals.

Examples:

```lean
tapply lem
tapply lem hp
tapply lem hp hq
tapply h hp
tapply Lentil.or_elim
```

### `tapply'`

```lean
tapply' thm arg1 arg2 ...
tapply' @thm arg1 arg2 ...
```

Restricted variant of `tapply`:

- theorem head must be an identifier;
- arguments can be temporal formulas without wrappers;
- `@thm` exposes implicit theorem arguments.

Examples:

```lean
tapply' lem (p ∧ q)
tapply' lem (p ∧ q) ⟨hp, hq⟩
tapply' @wf1 _ a b
```

### `tmap`

```lean
tmap hnew := hsrc using rule
tmap hsrc using rule
```

Applies an implication `rule` underneath nesting of modalities that have
registered monotonicity, so the surrounding modal context of `hsrc` is preserved.

- The rule may prove `(p) |-tl- (q)`, `|-tl- (p ⇒ q)`, or `|-tl- (□ (p → q))`.
- A proof-mode hypothesis `hrule : p ⇒ q` or `hrule : □ (p → q)` is also accepted.
- The second form replaces `hsrc` in place, keeping its name (it moves to the end
  of the context), like `treplace`.

Example: from `hp : □ ◇ p` and `hpq : (p) |-tl- (q)`,

```lean
tmap hq := hp using hpq
```

adds `hq : □ ◇ q` while preserving the rest of the context.

Additional unary predicate operators can be registered with the `tmap_mono`
attribute (operators may have parameters before their predicate argument):

```lean
@[tmap_mono]
theorem op_monotone {p q : pred σ} :
    |-tl- ((p ⇒ q) → (op p → op q)) := by
  ...
```

The statement may also take the sequent form `(p ⇒ q) |-tl- (op p → op q)`.

## Destructuring temporal hypotheses

### `trcases`

```lean
trcases h with pat
trcases 0 with pat
```

Destructures a temporal hypothesis.

Supported patterns:

- `ident`: rename selected hyp to `ident`.
- `_`: keep/discard generated name without changing context.
- `-`: clear the selected hypothesis.
- `⟨p1, p2, ...⟩`: destructure conjunctions or existentials.
- `(p1 | p2 | ...)`: case-split disjunctions.
- Nested combinations, for example `⟨ha, hb | hc⟩`.

Examples:

```lean
trcases h with ⟨hp, hq⟩
trcases h with ⟨n, hp⟩
trcases h with (hp | hq)
trcases h with ⟨ha, -⟩
trcases 0 with ⟨hp, hq⟩
```

Pitfalls:

- Type ascriptions in patterns, such as `pat : ty`, are not supported.
- Empty and unary tuples are not supported. Drop brackets for a single pattern.

### `tobtain`

```lean
tobtain pat := t
```

Adds the temporal fact proved by `t` and immediately destructures it. If `t` is a bare proof-mode hypothesis, it destructures that hypothesis in place.

Examples:

```lean
tobtain ⟨hp, hq⟩ := h
tobtain (hp | hq) := Lentil.excluded_middle [tlfml| p]
```

## Rewriting and simplification in proof mode

### `trewrite`

```lean
trewrite [rules]
trewrite [rules] at hp
trewrite [← rule] at hp hq ⊢
trewrite [rules] at *
```

Runs Lean `rewrite` on selected proof-mode predicates. With no location, rewrites the goal predicate only. With `at *`, each temporal hypothesis and the goal are tried separately.

### `tsimp`

```lean
tsimp
tsimp [lemmas]
tsimp only [lemmas] at hp ⊢
```

Runs Lean `simp` through `conv` on selected proof-mode predicates.

### `tdsimp`

```lean
tdsimp
tdsimp [defs] at hp
tdsimp only [defs] at *
```

Runs Lean `dsimp` through `conv` on selected proof-mode predicates.

### `tunfold`

```lean
tunfold def1 def2 at hp ⊢
```

Unfolds definitions inside selected proof-mode predicates.

## Temporal/modal automation

### `tmonotone`

```lean
tmonotone
```

Peels a common monotone temporal prefix from every proof-mode hypothesis and the goal.

Supported prefixes:

- `◯` over multiple hypotheses.
- `□` over multiple hypotheses.
- `◇□` over multiple hypotheses.
- `◇` for a single temporal hypothesis.
- `□◇` for a single temporal hypothesis.

It also works outside proof mode by applying raw monotonicity theorems.

If a leading modality is hidden behind a definition tagged with `[tl_modality_unfold]`, the tactic may unfold that head for recognition. Built-in tagged wrappers are `Lentil.leads_to` (`↝`), `Lentil.always_implies` (`⇒`), and `Lentil.weak_fairness` (`𝒲ℱ`).

### `ttoggle_goal_under_always`

```lean
ttoggle_goal_under_always
```

Toggles one leading `□` on the current proof-mode goal when every temporal hypothesis has a leading `□` or a tagged wrapper exposing `□`.

Examples:

```lean
-- hp : □ p, goal □ q  becomes  goal q
ttoggle_goal_under_always

-- hp : □ p, goal q    becomes  goal □ q
ttoggle_goal_under_always
```

### `tadvance`

```lean
tadvance h
tadvance 0
```

Advances the current proof point to a selected eventuality: if `h : ◇ p`, the
tactic replaces `h` by `p`.

It requires that

- every other temporal hypothesis has a leading `□` (possibly hidden behind a
  definition tagged with `[tl_modality_unfold]`), and
- `PrefixClosed goal` can be synthesized. Built-in instances cover `◇ q`,
  `□ ◇ q`, and pure facts; for another prefix-closed goal, add a `PrefixClosed`
  instance.

### `tstep`

```lean
tstep
```

Advances a proof-mode sequent by one deterministic temporal step. The goal must
have a leading `◯`, which is peeled off.

Every temporal hypothesis must have a leading `□` or `◯`: a `□ p` stays `□ p`,
while a `◯ q` becomes `q`. In the resulting context the `□` hypotheses come
before the peeled `◯` ones.

## Finite-window tactic

### `tfinite_window`

```lean
tfinite_window
```

Reduces an obligation whose proof only needs a bounded execution prefix to an
ordinary Lean goal over finitely many states. It accepts validity goals
(`|-tl- (p)`), raw sequents (`(p) |-tl- (q)`), proof-mode `Entails` goals, and
predicate equalities (`(p) =tl= (q)`).

It computes one window for the whole obligation, introduces its states as `s`,
`s'`, `s''`, and so on, and leaves the resulting non-temporal proposition. For
example,

```lean
(⌜ inv ⌝ ∧ ⟨next⟩) |-tl- (◯ ⌜ inv ⌝)
```

becomes a goal of the shape

```lean
s s' : σ
⊢ inv s ∧ next s s' → inv s'
```

An equality `(p) =tl= (q)` becomes one pointwise `Iff` goal; it is not split
into two sequents.

Window sizes: a state predicate observes one state, an action predicate two, and
each `◯` shifts the required window by one.

What has to fit in a bounded prefix is the obligation as a whole, not every
formula in it — so a modality is allowed or rejected according to the direction
it is used in:

- an assumption `□ p` is fine: it supplies every copy of `p` that falls inside
  the window;
- a conclusion `◇ p` is fine: it may be proved by a witness inside the window;
- a conclusion `□ p` fails: no finite prefix establishes it;
- an assumption `◇ p` fails: it gives no uniformly bounded witness.

Support comes from `HasFiniteWindow` certificates and directional
`HasWindowApprox` instances; further predicate forms can be covered by adding
instances.

## Helpers outside proof mode

These are ordinary Lean tactics applied `at *`, meant for raw goals rather than
proof-mode ones. They unfold Lentil's definitions so that plain Lean tactics can
take over.

| Tactic | What it does |
|---|---|
| `tunfold_defs` | `dsimp only` with the `[tlsimp_def]` set: unfold the LTL definitions everywhere |
| `tunfold_defs'` | `tunfold_defs`, then also unfold the `[execsimp]` set (execution operations such as `exec.drop`) |
| `tunfold_simp` | as `tunfold_defs`, but a full `simp` rather than `dsimp only` |
| `tunfold_simp'` | `tunfold_simp`, then also `[execsimp]` |
| `tnontemporal_simp` | `simp` with the `[tl_nontemporal_def]` set: unfold only the non-temporal definitions, leaving `□`, `◇`, `◯`, and `𝑈` folded |

## Common proof recipes

### Prove from an assumption

```lean
example : (p) |-tl- (p) := by
  tstart hp
  tassumption
```

### Prove a conjunction

```lean
example : (p ∧ q) |-tl- (p ∧ q) := by
  tstart hp hq
  tsplit_ands <;> tassumption
```

### Prove a disjunction

```lean
example : (p) |-tl- (p ∨ q) := by
  tstart hp
  tleft
  tassumption
```

### Introduce a temporal implication

```lean
example : (p) |-tl- (q → p) := by
  tstart hp
  tintro hq
  tassumption
```

### Destructure an introduced conjunction

```lean
example : (p) |-tl- ((q ∧ r) → q) := by
  tstart hp
  trintro ⟨hq, hr⟩
  tassumption
```

### Apply a theorem with temporal premises

```lean
example (lem : (p ∧ q) |-tl- (r)) : (p ∧ q) |-tl- (r) := by
  tstart hp hq
  tapply lem ⟨hp, hq⟩
```

### Keep a derived fact

```lean
example (lem : (p) |-tl- (q)) : (p) |-tl- (q) := by
  tstart hp
  thave hq := lem hp
  tassumption
```

### Pull a pure fact to Lean

```lean
example (P : Prop) : (⌞P⌟ ∧ p) |-tl- (p) := by
  tstart hP hp
  tpull_pure hP
  tassumption
```

### Rewrite in a temporal hypothesis

```lean
example (heq : q = r) : (q) |-tl- (r) := by
  tstart hq
  trewrite [heq] at hq
  tassumption
```

### Use monotonicity

```lean
example (h : (p ∧ q) |-tl- (r)) : (□ p ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  exact h
```

## Troubleshooting

If a proof fails, check these first:

- Did you call `tstart` before proof-mode tactics such as `tintro`, `tapply`, or `tassumption`?
- Does `tstart` receive exactly one name per flattened conjunct on the sequent left side?
- Is a temporal hypothesis being used as if it were a Lean local? Use `tapply`, `thave`, `tspecialize`, `trcases`, or `tpull_pure`.
- Does `tspecialize` need a proof-mode hypothesis name rather than an arbitrary Lean term?
- Does a theorem head need the prime form `tapply'` or `thave'` so formula arguments can be written directly?
- Did a pure temporal hypothesis `⌞P⌟` need `tpull_pure` before ordinary Lean reasoning?
- Did `trewrite`, `tsimp`, `tdsimp`, or `tunfold` target the goal by default when you meant `at hp` or `at *`?
- Does `tmonotone` require all hypotheses and the goal to share the same supported leading modality?
- Does `ttoggle_goal_under_always` require every temporal hypothesis to have a leading `□`?
- Does `tfinite_window` fail because a `□` sits in the conclusion, or a `◇` among the assumptions? Those directions have no finite window.
