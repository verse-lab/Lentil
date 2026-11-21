# Advice for Agents

Lentil is a Lean 4 library for linear temporal logic and its proof mode. Use the Lean version pinned in `lean-toolchain`.

## Repository layout

- `Lentil/` contains the library and proof mode.
- `LentilApplications/` contains applications, and `LentilTest/` contains tests.
- `docs/` contains the reference manual and cheat sheet.

## Working on changes

- Keep the diff focused. Follow nearby code and proof style, reuse existing lemmas and tactics, and preserve unrelated worktree changes.
- Use `lake env lean path/to/File.lean` or `lake build path/to/File.lean` for a focused check. **Run `lake test` before committing or handing off changes to Lean code or Lake configuration.** Report the checks you ran and any that remain open.
