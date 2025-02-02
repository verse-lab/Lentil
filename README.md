# TLA in Lean

> TLA+ is considered to be exhaustively-testable pseudocode, and its use likened to drawing blueprints for software systems; _TLA_ is an acronym for Temporal Logic of Actions. 
>
> (from [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA%2B))

Yet another formalization of TLA in Lean 4. The definitions are ported from the [`coq-tla`](https://github.com/tchajed/coq-tla) library, while the proofs are written using Lean's tactic language. 

Given the unprecedented enthusiasm with which people have been using Lean to formalize various concepts and port formalizations from other proof assistants (a trend that began with the release of Lean 3 and has only intensified since), we do not expect this project to become the most comprehensive or practical TLA formalization in Lean. Its current development principle is to ensure a minimum level of user-friendliness while including enough content to enable our development of other projects. 

## Usage

Add this project into your `lakefile.lean` (just like how you would do for other Lean4 projects), and then

```lean
import Lentil
```
