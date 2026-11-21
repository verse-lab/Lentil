# Advice for Agents

Lentil is a Lean 4 library for linear temporal logic and its proof mode. Use the Lean version pinned in `lean-toolchain`.

## Repository layout

- `Lentil/` contains the library and proof mode.
- `LentilApplications/` contains applications, and `LentilTest/` contains tests.
- `docs/` contains the reference manual and cheat sheet.

## Working on changes

- Keep the diff focused. Follow nearby code and proof style, reuse existing lemmas and tactics, and preserve unrelated worktree changes.
- Use `lake env lean path/to/File.lean` or `lake build path/to/File.lean` for a focused check. **Run `lake test` before committing or handing off changes to Lean code or Lake configuration.** Report the checks you ran and any that remain open.

## Preserving ordinary Lean behavior on import

- Prefer `scoped` for new DSL entry points and helper commands. Open the scope where the syntax is used. Scope notation-specific delaborators together with their parsers so the printed notation can be parsed in the same context. See `𝒞` in `Lentil/MetaTheory/Safety.lean`.
- When an identifier should act as a keyword only inside `tlfml`, follow the `.nonReservedSymbol … true` pattern for `Enabled`, `𝒲ℱ`, and `𝒮ℱ` in `Lentil/Basic.lean`. Test both an ordinary Lean application and the temporal formula form.
- Keep proof-specific simplification rules and simprocs in named simp sets. Review globally registered instances and new transitive imports for effects on ordinary Lean syntax, instance search, and default `simp`. Files without a `module` header can still load registrations through private imports.
- Check import-sensitive changes in a small file with `import Lentil` and no scope opened. Compare affected ordinary Lean behavior against `import Lean`, and check both module and non-module clients when changing imports. Add parser regressions to `LentilTest/Notation.lean`.
