# lean-project

```bash
$ lake exe mk_all
No update necessary
$ lake build
ℹ [496/498] Replayed Project.Example
info: Project/Example.lean:29:0: import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
info: Project/Example.lean:29:0: `#`-commands, such as '#min_imports', are not allowed in 'Mathlib' [linter.hashCommand]
Build completed successfully (498 jobs).
```

## Initialization

1. Create a repository from this template.
2. Confirm github workflows in `.github/workflows/`.
3. Confirm lint settings in `package.json`, `.lefthook/`, and `lefthook.yml`.
4. Remove `Project.lean` and `Project/`.
5. Make your project files, then update `lakefile.toml`.
6. Bump lean version in `.devcontainer/Dockerfile`, `lakefile.toml`, and `lean-toolchain`.
7. Reomve `lake-manifest.json` and `.lake/`.
8. Execute `lake exe cache get`.

## Tools in development

### VSCode Extensions

- [ms-vscode-remote.remote-containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)

### MCP Servers

- https://github.com/oOo0oOo/lean-lsp-mcp

### Skills

- https://github.com/leanprover/skills
- https://github.com/cameronfreer/lean4-skills
- https://github.com/companion-inc/feynman
