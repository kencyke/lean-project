# AGENTS.md

## Working Principles

**Think before coding.**
- Read the target file and its importers before editing.
- State your assumptions about the goal, the existing lemmas, and the proof
  skeleton before typing tactics. Capture the goal with `lean_goal` rather
  than guessing the shape from the file context.
- Prefer `lean-lsp` MCP tools over shelling out: `lean_goal`,
  `lean_local_search`, `lean_leansearch`, `lean_loogle`. If you do not know
  whether a lemma exists, say so and search; do not invent plausible-looking
  names.
- When stuck on a goal, search closing lemmas with `lean_state_search` /
  `lean_hammer_premise`, then verify with `lean_multi_attempt` before
  editing.
- If Lean reports `expected '{' or indented tactic sequence`, fix indentation
  first — almost always a whitespace issue, not a tactic bug.
  **Why:** tactics that compile by accident can mask unsoundness; this
  project mandates a fully axiom-free codebase.

**Abstraction first.**
- Do not formalize only what the current task requires.
- Approach our goal with the kind of abstraction and generalization used by mathematicians and physicists.
- Prefer the most direct proof that closes the goal over the cleverest one.
  If `simp` / `linarith` / `aesop` suffices, do not unfold by hand.
  **Why:** every extra declaration is surface area to maintain and to keep
  axiom-free; speculative API decays faster than it earns interest.

**Goal-driven verification (Definition of Done).**
- A change is done only when `lake build` completes with no new errors or
  warnings on the edited modules and their downstream importers.
- After adding imports, run `lean_build` via MCP to restart the LSP;
  otherwise `lean_diagnostic_messages` suffices.
- Never report a task as successful until the above checks pass.
  **Why:** "looks right" is not a soundness gate; the kernel is, and
  downstream modules can still break even when the edited file type-checks
  in isolation.

## Editing Hygiene

- Spaces only, never tabs.
  **Why:** Mathlib style; mixed whitespace breaks `lake exe runLinter`.
- Never modify `lakefile.toml`, `lean-toolchain`, or `lake-manifest.json`.
  **Why:** the toolchain and manifest are pinned intentionally; accidental edits cascade into reproducibility failures.
- Write comments in English.

## Prohibited Tokens

The following tokens are strictly prohibited, grouped by reason.

- *Unsound or deferred proofs:* `sorry`, `admit`, `axiom`.
  **Why:** the project targets a fully axiom-free formalization; assumptions smuggled into structure fields count as axioms too.
- *Global configuration and unsafe code:* `set_option`, `unsafe`.
  **Why:** these mutate kernel or elaborator behavior project-wide, or bypass soundness.
- *Compiler and metaprogramming internals:* `System`, `open System`, `Lean.Elab`, `Lean.Meta`, `Lean.Compiler`.
  **Why:** this is a mathematics repository, not a tactic-library repository; depending on internals creates brittle code.

## Commit Style

`lefthook` + `commitlint` enforce this; the accepted vocabulary is:

- Conventional Commits: `feat` / `fix` / `chore` / `docs` / `refactor` / `test` / `perf`.
- Lowercase type, colon, imperative subject.
- One logical change per commit.

## Style Guidelines

The Mathlib contribute templates are authoritative; the bullets below distill what actually comes up during edits.

**Naming.**
- `lowerCamelCase` for terms and definitions (`gnsRepresentation`, `isPureState`).
- `UpperCamelCase` for types, structures, and propositions (`CStarAlgebra`, `IsState`).
- Theorem names use `_` as word separator (`norm_add_le`, `inner_self_nonneg`).
- Prefer the `_of_` pattern for implications (`continuous_of_lipschitz`); `iff` joins equivalences; `not_` prefixes negations.

**Layout.**
- 100-column line limit.
- 2-space indentation; `by` stays on the same line as the goal it opens unless the resulting line would exceed the limit.
- Hoist shared hypotheses into `variable` blocks; keep explicit/implicit arity consistent with sibling lemmas.
- Align `calc` steps on the relation; use `·` (centered dot) for focused goals, not `case _ =>`.

**Docstrings.**
- Every public declaration gets a `/-- ... -/` docstring whose first sentence is a self-contained summary.
- Module docs (`/-! # Title ... -/`) at the top of each file describe the content and any non-obvious conventions.

**References** (fetch when a rule above is ambiguous):

- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/doc.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/naming.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/style.md

## Source of Truth

`AGENTS.md` is the single source of truth; `CLAUDE.md` is a symlink to it. Edit only this file.
