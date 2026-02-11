# AGENTS.md

## Important Instructions

- Use spaces only; never use tabs.
- Do not modify `lakefile.toml`.
- Do not use `python`, `cat`, `git checkout`, or `git reset`.
- When encountering the error `expected '{' or indented tactic sequence`, fix the indentation.
- Autonomously continue executing the tasks specified in `PLANS.md` until the maximum request limit is reached.
- Use the `lean-lsp` MCP server tools when applicable.
- Write all comments in English.
- Use `$...$` or `$$...$$` for LaTeX math formatting in Markdown.
- Always implement full proofs. Do not ask whether to proceed full proofs or introduce helper lemmas. If needed for full proofs, implement all of them.
- Do not explore shorter proof paths before the current proof is completed. Only after completion may you consider improved approaches.
- Before ending the session, run `lake build` to ensure the project builds successfully.

## Prohibitions

The following tokens are strictly prohibited to use in this project:

- `sorry`
- `admit`
- `axiom`
- `set_option`
- `unsafe`
- `System`
- `open System`
- `Lean.Elab`
- `Lean.Meta`
- `Lean.Compiler`
