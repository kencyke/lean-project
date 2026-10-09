# AGENTS.md

## Project Layout

- `Project/` — the `Project` Lean library and default build target. `Project/Example.lean` is a
  template placeholder.
- `Project.lean` — aggregate root importing every module under `Project/`. Regenerate with
  `lake exe mk_all` (shipped by Mathlib) whenever a module is added, renamed, or removed.

## Working Principles

**Think before coding.**
- Read the target file and its importers before editing.
- State the goal, the lemmas you expect to use, and the proof skeleton before writing tactics.
  Capture the goal with `lean_goal` instead of inferring it from surrounding code.
- Prefer `lean-lsp` MCP tools over shelling out: `lean_goal`, `lean_local_search`,
  `lean_leansearch`, `lean_loogle`. Never invent lemma names — if unsure, say so and search.
- When stuck, find candidate lemmas with `lean_hammer_premise` / `lean_leanfinder` and test them
  with `lean_multi_attempt` before editing.

**Abstraction first.**
- Build the general interface before the concrete model, even when the source literature treats
  only a special case. Introduce the abstract structure in the *first* commit, then instantiate.
- Do not weaken hypotheses to fit whatever fragment Mathlib has the most lemmas for. Follow the
  literature, even when that means building supporting API Mathlib lacks.

**Do not bridge what should be unified.**
- When Mathlib provides an object (a type copy, a topology, a structure), use it. Never
  reimplement it locally and paper over the mismatch with a conversion lemma, `Equiv`, or
  `Homeomorph`. If such a copy already exists, migrate to Mathlib's and delete it.
- Likewise for two local spellings of one notion (image vs preimage, bundled vs unbundled):
  pick one and state every result in it.
- A conversion lemma is acceptable only when both sides are outside your control — both already
  in Mathlib, or the local object carries structure Mathlib's cannot.
  **Why:** a bridge makes duplication permanent; every later lemma must pick a side, and a local
  copy of a Mathlib object can never be upstreamed.

**Prove what is provable; do not defer it.**
- Never add a `class` / `structure` field or `def … : Prop` hypothesis standing in for a theorem
  with a known proof — even when Mathlib lacks the supporting lemmas or proving it is out of
  scope for the current change.
- A hypothesis class is acceptable only for genuinely model-dependent inputs: false for some
  objects in the class, with no known universal proof.
  **Why:** deferred hypotheses become permanent and silently grow the trusted base.

**Match the code to the docs, not the docs to the code.**
- When a docstring claims more than the code establishes, raise the code: strengthen the
  statement, discharge the hypothesis, or generalise. Do not trim the docs to fit.
  **Why:** docs record the *intended* theorem; trimming them hides the gap instead of closing it.

**Definition of Done.**
- `lake build` succeeds. With `warningAsError = true`, any warning (including Mathlib style
  linters) fails the build; CI (`.github/workflows/lean_action_ci.yml`) runs the same build.
- After adding imports, run `lean_build` via MCP to restart the LSP; otherwise
  `lean_diagnostic_messages` suffices.
- Check headline results with `lean_verify`: only Lean's standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`) may appear.
- Never silence a failing tactic with `try` / `<;>`. Re-inspect with `lean_goal` and fix the
  actual mismatch.

## Plan Mode & Responses

- In plan mode, a question deserves an answer, not a plan: reply via AskUserQuestion and answer
  only what was asked.
- Lead with numbered steps, then brief notes. Do not narrate a plan in prose.
  **Why:** the reader has ADHD; a response that demands sustained attention does not get read.
- If a request cannot reasonably become an implementation plan, say why and offer viable
  alternatives or references instead of forcing one.

## Editing Hygiene

- Spaces only, never tabs (Mathlib style). Comments in English.
- Do not touch `lakefile.toml`, `lean-toolchain`, or `lake-manifest.json` unless the task is a
  toolchain/Mathlib bump. A bump keeps the Lean version consistent across `lean-toolchain`, the
  Mathlib `rev` in `lakefile.toml`, `.devcontainer/Dockerfile`, and `version` in
  `pyproject.toml`; merging a `lean-toolchain` change to `main` triggers
  `.github/workflows/release-lean.yml`, which tags a release.

## Prohibited Tokens

Strictly forbidden in Lean sources:

- `sorry`, `admit`, `axiom` — no axioms beyond Lean's standard three; assumptions smuggled into
  structure fields count as axioms too.
- `set_option`, `unsafe` — these alter kernel/elaborator behaviour or bypass soundness.
  Project-wide options belong in `[leanOptions]` of `lakefile.toml`.
- `System`, `open System`, `Lean.Elab`, `Lean.Meta`, `Lean.Compiler` — this is a mathematics
  repository, not a tactic library; depending on internals is brittle.

## Commit Style

Enforced by `lefthook.yml`: `commit-msg` runs `uv run cz check` (commitizen, configured in
`pyproject.toml`); `pre-commit` runs `gitleaks` on staged files.

- Conventional Commits with the project vocabulary `feat` / `fix` / `chore` / `docs` /
  `refactor` / `test` / `perf`. The stock `cz_conventional_commits` schema also accepts
  `build` / `ci` / `style` / `revert` / `bump`, but prefer the narrower list.
- Lowercase type, colon, imperative subject: `feat: add infinitude of primes`.
- One logical change per commit. Never commit secrets.

## Style Guidelines

The Mathlib contribute templates are authoritative; the bullets below distill what comes up most.

**Naming.**
- `lowerCamelCase` for terms and definitions (`Nat.factorial`, `Nat.minFac`);
  `UpperCamelCase` for types, structures, and propositions (`Nat.Prime`, `IsCompact`).
- Theorem names use `_` as separator (`norm_add_le`); `_of_` for implications
  (`continuous_of_lipschitz`), `_iff` for equivalences, `not_` for negations.

**`theorem` versus `lemma`.**
- `theorem` is reserved for the headline results a file exists to prove — the statements a
  textbook would call a theorem, typically those listed under "Main results" in the module doc.
  A file rarely needs more than a handful.
- Everything else (API lemmas, rewriting rules, `_iff`/`_of_` bookkeeping) is a `lemma`;
  anything used only inside the file is a `private lemma`.
  **Why:** `theorem` marks what a reader should look at first; overuse makes it meaningless.

**Layout.**
- 120-column limit by convention (`linter.style.longLine` is disabled in `lakefile.toml`).
- 2-space indentation; `by` stays on the goal's line unless that would exceed the limit.
- Hoist shared hypotheses into `variable` blocks; keep arity consistent with sibling lemmas.
- Align `calc` steps on the relation; use `·` for focused goals, not `case _ =>`.

**Docstrings.**
- Every public declaration gets a `/-- ... -/` docstring whose first sentence stands alone.
- Each file opens with a module doc (`/-! # Title ... -/`) describing content and conventions.

## Source of Truth

`AGENTS.md` is the single source of truth; `CLAUDE.md` is a symlink to it. Edit only this file.
