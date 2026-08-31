# Lentil cheat sheet

A one-page summary of Lentil's temporal-logic notation and proof-mode tactics:
what each tactic means and how to type it. For the full story (semantics, corner
cases, pitfalls) see [Lentil-reference.md](Lentil-reference.md).

```lean
import Lentil
```

## Formula notation

`σ` is the type of the system's states. An execution `exec σ = Nat → σ` is an
infinite sequence of states, and a temporal formula is a
`pred σ = exec σ → Nat → Prop` — a proposition about one execution at one time
index, not a bare `Prop`. An `action σ = σ → σ → Prop` relates a state to its
successor.

| Syntax | Meaning |
|---|---|
| `⌜ p ⌝` | state predicate, `p : σ → Prop` |
| `⌞ P ⌟` | pure Lean proposition, `P : Prop` |
| `⟨ a ⟩` | action predicate, `a : σ → σ → Prop` |
| `⊤` / `⊥` | true / false |
| `¬ p`, `p ∧ q`, `p ∨ q`, `p → q` | propositional connectives, on temporal formulas |
| `□ p` / `◇ p` / `◯ p` | always / eventually / next |
| `p 𝑈 q` | until |
| `p ↝ q` | leads-to, i.e. `□ (p → ◇ q)` |
| `p ⇒ q` | always-implies, i.e. `□ (p → q)` |
| `Enabled a` | action `a` is enabled |
| `𝒲ℱ a` | weak fairness for `a` |
| `∀ x, p x` / `∃ x, p x` | temporal quantifiers |
| `⋀ x ∈ xs, p x` / `⋁ x ∈ xs, p x` | big conjunction / disjunction |

Term level:

| Syntax | Meaning |
|---|---|
| `(p) \|-tl- (q)` | sequent: `p` entails `q` |
| `\|-tl- p` | `p` is valid |
| `(p) =tl= (q)` | the two formulas are equal predicates |
| `e \|=tl= p` | execution `e` satisfies `p` |

Precedence, shortest form: unary modalities bind tightest, then `𝑈`, then
`∧`/`∨`, then `↝`/`⇒`, then `→` (right-associative). Lean applications are atoms,
so `Enabled A n ∧ p` is `(Enabled (A n)) ∧ p`. Parenthesize when mixing
implication-like operators. Usually, both sides of `|-tl-` and `=tl=` must be
parenthesized: `(p ∧ q) |-tl- (r)`, never `(p ∧ q) |-tl- r`.

## Mental model of proof mode

The Lentil proof mode is for manipulating **Lentil entailments**.
A Lentil entailment can be thought as a special layout of temporal sequent.
It contains a **temporal proof context** that lists multiple **temporal hypotheses**, and a **temporal goal**:

```text
hp : p         -- temporal hypotheses
hq : q
|-tl- r        -- temporal goal
```

A temporal hypothesis is addressed by its name or by zero-based index.
Rewriting tactics use Lean's location syntax, resolved against proof-mode
predicates: `at hp`, `at hp ⊢`, `at *`. (`tclear` takes names only.)

Note:
- Temporal hypotheses are **not** Lean local hypotheses. Plain Lean tactics
  cannot see them; use the `t`-prefixed tactics instead.
- `tstart` enters proof mode from a raw `(p) |-tl- (q)` sequent, `texit` leaves it.
- Almost every tactic accepts temporal formulas written directly, so you rarely
  need the `[tlfml| ... ]` wrapper (see [here](Lentil-reference.md#writing-formulas) for details).

## Tactics

Each `t`-tactic is the temporal counterpart of the Lean tactic of the same name,
acting on the temporal context instead of Lean's. The rows below say only what
differs from that.

### Entering and leaving proof mode

| Tactic | What it does |
|---|---|
| `tnormalize` | normalize a raw goal, e.g. turn `\|-tl- (p → q)` into `(p) \|-tl- (q)` |
| `tstart h1 h2 ...` | enter proof mode; one name per conjunct on the left of `\|-tl-` |
| `texit` | leave proof mode, back to a raw sequent |

### Binders

| Tactic | What it does |
|---|---|
| `tintro x hp hP` | introduce from the goal: `∀ x, p` gives a Lean local and `⌞P⌟ → q` a Lean proof, while `p → q` gives a temporal hypothesis |
| `trintro ⟨hp, hq⟩` | like `tintro`, with `rcases`-style patterns |
| `trevert h1 h2` | inverse of `tintro`: temporal `hp : p` becomes goal `p → …`, a Lean proof `hP : P` becomes `⌞P⌟ → …`, a Lean local `n` becomes `∀ n, …` |
| `trevert_all` | revert every temporal hypothesis; Lean locals stay put, use `trevert` for those |

### Managing the context

| Tactic | What it does |
|---|---|
| `tassumption` | close the goal with a matching temporal hypothesis |
| `tclear h1 h2` / `tclear * - hKeep` | drop hypotheses / keep only the listed ones |
| `trename old => new` | rename a hypothesis by its location |
| `tpull_pure hP` | move `hP : ⌞P⌟` into Lean's context as `hP : P` |
| `tcontradiction` | close the goal from `⊥`, or from both `p` and `¬ p` |

### Building the goal

| Tactic | What it does |
|---|---|
| `texists w1, w2` | supply witnesses for temporal `∃` goals |
| `tleft` / `tright` | pick a disjunct of `p ∨ q` |
| `tsplit_ands` | split a conjunctive goal |
| `tprove_pure` | reduce a pure goal `⌞P⌟` to the Lean goal `P` |
| `tby_cases h : p` | split into `h : p` and `h : ¬ p` |
| `texfalso` | change the goal to `⊥` |

### Using facts

| Tactic | What it does |
|---|---|
| `tapply t` | close the goal with a theorem or hypothesis; missing temporal premises become new goals |
| `tapply' thm arg ...` | same, but `thm` is an identifier and arguments may be bare temporal formulas |
| `thave h : p by tac` | prove `p` here, then add `h : p` |
| `thave h := t` | add the fact denoted by `t` |
| `thave' h := thm arg ...` | same, with bare temporal formula arguments |
| `treplace h := t` | replace `h` with the fact from `t` |
| `tspecialize h a1 a2` | specialize a hypothesis in place; each argument is consumed according to its current shape, and a temporal premise must be a hypothesis *name*, not a term |
| `tsuffices h : p by tac` | reduce the goal to `p`; `tac` proves the old goal from `h : p` |
| `tmap hq := hp using rule` | apply an implication under `□`, `◇`, ... inside `hp` |

### Destructuring

| Tactic | What it does |
|---|---|
| `trcases h with pat` | destructure a hypothesis; patterns `ident`, `_`, `-`, `⟨..⟩`, `(.. \| ..)` |
| `tobtain pat := t` | add the fact from `t` and destructure it immediately |

### Rewriting and simplification

| Tactic | What it does |
|---|---|
| `trewrite [rules] at hp ⊢` | `rewrite` on selected proof-mode predicates |
| `tsimp [lemmas] at hp` | `simp` on selected proof-mode predicates |
| `tdsimp [defs] at *` | `dsimp` on selected proof-mode predicates |
| `tunfold d1 d2 at hp ⊢` | unfold definitions inside selected predicates |

With no location the goal is targeted; `at *` covers every hypothesis and the goal.

### Modal automation

| Tactic | What it does |
|---|---|
| `tmonotone` | strip a shared modal prefix (`◯`, `□`, `◇□`; `◇`, `□◇` for a single hypothesis) from hypotheses and goal |
| `ttoggle_goal_under_always` | add or remove one leading `□` on the goal when all hypotheses are `□`-prefixed |
| `tadvance h` | if `h : ◇ p`, move to that eventuality and replace `h` by `p`; every other hypothesis must be `□`-prefixed |
| `tstep` | peel a leading `◯` off the goal and take one step: hypotheses of the shape `□ p` stays, `◯ q` becomes `q` |
| `tfinite_window` | reduce a finite-window sequent to an ordinary Lean goal over finitely many states |

### Outside proof mode

Plain Lean tactics applied `at *`, for raw goals rather than proof-mode ones. Mostly useful for proving by exposing underlying semantics. 

| Tactic | What it does |
|---|---|
| `tunfold_defs` / `tunfold_defs'` | `dsimp only` unfolding the LTL definitions; the primed form also unfolds execution operations |
| `tunfold_simp` / `tunfold_simp'` | the same, as a full `simp` |
| `tnontemporal_simp` | `simp` unfolding only the non-temporal definitions, leaving `□`, `◇`, `◯`, `𝑈` folded |

## Small examples

```lean
-- from an assumption
example : (p) |-tl- (p) := by
  tstart hp
  tassumption

-- conjunction / disjunction
example : (p ∧ q) |-tl- (p ∧ q) := by
  tstart hp hq
  tsplit_ands <;> tassumption

example : (p) |-tl- (p ∨ q) := by
  tstart hp; tleft; tassumption

-- introduce and destructure
example : (p) |-tl- ((q ∧ r) → q) := by
  tstart hp
  trintro ⟨hq, hr⟩
  tassumption

-- apply a theorem with temporal premises
example (lem : (p ∧ q) |-tl- (r)) : (p ∧ q) |-tl- (r) := by
  tstart hp hq
  tapply lem ⟨hp, hq⟩

-- keep a derived fact
example (lem : (p) |-tl- (q)) : (p) |-tl- (q) := by
  tstart hp
  thave hq := lem hp
  tassumption

-- pure fact to Lean
example (P : Prop) : (⌞P⌟ ∧ p) |-tl- (p) := by
  tstart hP hp
  tpull_pure hP
  tassumption

-- monotonicity
example (h : (p ∧ q) |-tl- (r)) : (□ p ∧ □ q) |-tl- (□ r) := by
  tstart hp hq
  tmonotone
  exact h
```

## Gotchas

- `tstart` needs exactly one name per flattened left-side conjunct; from
  `(⊤) |-tl- (p)` it takes none.
- A temporal hypothesis cannot be passed to a plain Lean tactic; use `tapply`,
  `thave`, `tspecialize`, `trcases`, or `tpull_pure`.
- Use the primed `tapply'` / `thave'` when you want to write formula arguments
  without `[tlfml| ... ]`.
- `trcases` patterns take no type ascriptions, and no empty or unary tuples.
- `tmonotone` needs the *same* supported leading modality on every hypothesis and
  on the goal. 
