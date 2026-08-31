# Lentil

Lentil is a proof infrastructure for linear temporal logic in Lean 4. It formalizes the semantics of LTL, provides rules and a dedicated proof mode to conduct proofs in LTL as an object logic. 

## Getting Started

Add Lentil as a dependency. In `lakefile.lean`:

```lean
require lentil from git "https://github.com/verse-lab/Lentil" @ "main"
```

or in `lakefile.toml`:

```toml
[[require]]
name = "lentil"
git = "https://github.com/verse-lab/Lentil"
rev = "main"
```

and then

```lean
import Lentil
```

Lentil is built against the Lean version pinned in [`lean-toolchain`](lean-toolchain).

Refer to [this cheat sheet](docs/Lentil-cheatsheet.md) for a quick start, and the
[reference manual](docs/Lentil-reference.md) for the full notation and tactic
documentation. 

## Acknowledgments

The definitions of the embedding are initially ported from
[`coq-tla`](https://github.com/tchajed/coq-tla). 
The design of the proof mode is partly inspired by [Iris Proof Mode](https://iris-project.org/).

## License

See [LICENSE](LICENSE).
