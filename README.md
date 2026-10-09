# lean-project

```bash
$ lake exe mk_all
No update necessary
$ lake build
Build completed successfully (538 jobs).
```

## Getting Started

1. Create a new repository from this template.
2. Review the GitHub Actions workflows in `.github/workflows/`.
3. Review the lint settings in `pyproject.toml` and `lefthook.yml`.
4. Update the Lean version in `.devcontainer/Dockerfile`, `lakefile.toml`, `lean-toolchain`, and `pyproject.toml`.
5. Run **Dev Containers: Rebuild Container**. Alternatively, delete `lake-manifest.json` and `.lake/`, then run
   `lake exe cache get`.
6. Remove `Project.lean` and `Project/`, then add your own project files.
