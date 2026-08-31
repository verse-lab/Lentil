# Lentil appendix for AI agents

This appendix collects the instructions and constraints that apply when an AI
agent writes Lentil proofs. It is **not** part of the user-facing documentation.

Read it together with:

- [Lentil-cheatsheet.md](Lentil-cheatsheet.md) — short summary of notation and tactics;
- [Lentil-reference.md](Lentil-reference.md) — full reference for notation, semantics, and tactic usage.

**NOTE**: When you are reading this because you are going to do a proof, please, stick with the constraints listed in the end of this document.

## Code-generation instructions

- Usually, you can directly use the notation and tactics documented in the
  reference. Otherwise, do

  ```lean
  import Lentil
  ```

- To keep good looking, you should **avoid** writing the `[tlfml| ... ]` wrapper
  in proofs. Use the appropriate tactics which allow you writing directly
  temporal formulas.
- Add parentheses around mixed implication-like expressions when generating code
  unless the intended parse is obvious.

## When a proof fails

Work through the [Troubleshooting checklist](Lentil-reference.md#troubleshooting)
in the reference before changing approach.

## Proof Constraints

- Stay in Lentil temporal proof mode unless a genuine blocker forces otherwise.
- **DO NOT** explicitly write `[tlfml| ... ]` when using temporal logic notation.
- If either of the two constraints above must be violated, stop and report before doing it.
- **DO NOT** use proof-mode internals or bottom-layer implementation lemmas directly.
- **DO NOT** hand-write low-level temporal constructors when proof-mode temporal notation can express the formula.
