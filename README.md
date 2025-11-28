# lean-project

```bash
$ lake build
Build completed successfully (579 jobs).
```

## How to use

1. Create a repository from this template.
2. Confirm lint settings in `package.json`, `.lefthook/`, and `lefthook.yml`.
3. Remove `Project.lean` and `Project/`.
4. Make your project files, then update `lakefile.toml`.
5. Bump lean version in `.devcontainer/Dockerfile`, `lakefile.toml`, and `lean-toolchain`.
6. Reomve `lake-manifest.json` and `.lake/`.
7. Execute `lake exe cache get`.

## Recommend to use

### VSCode Extensions

- [ms-vscode-remote.remote-containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
- [github.copilot-chat](https://marketplace.visualstudio.com/items?itemName=GitHub.copilot-chat)

### MCP Servers

- https://github.com/oOo0oOo/lean-lsp-mcp
