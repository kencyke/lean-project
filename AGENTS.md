# AGENTS.md

## Important Instructions

- Do not add files.
- Do not remove files.
- Do not modify `lakefile.toml`.
- Do not perform actions other than those explicitly instructed.
- Do not create `namespace` or `section` blocks unless specifically instructed.
- Minimize the use of `sorry` and `admit`, and strive to complete proofs.
- Do not use builtin `fetch` tool to read web pages. Alternatively, try to use the following tools:
   - Given a github repository, use tools in deepwiki mcp server.
   - Given a PDF file's URL, use `convert_to_markdown`.
   - Otherwise, use `read_url_content_as_markdown`.
- Use `$...$` or `$$...$$` for LaTeX math formatting in markdown.
- Use `conj` as complex conjugate when declaring `open ComplexConjugate` or `open scoped ComplexConjugate`.
- Use `simp` when referring `try 'simp' instead of 'simpa'`.
- Fix indentation when referring `expected '{' or indented tactic sequence`.
- Do not use tabs. Use spaces instead.
