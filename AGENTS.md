# AGENTS.md

## Agent Constraints

### Lean 4 Skill

When working on Lean 4 proofs, theorem statements, proof repair, diagnostics, or library
search, use the Lean 4 skill at:

`/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/skills/lean4/SKILL.md`

Prefer the workflows and helper scripts described there over ad-hoc approaches.

### Environment

The following environment variables are expected to be available in the shell:

- `LEAN4_PLUGIN_ROOT=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4`
- `LEAN4_SCRIPTS=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/lib/scripts`
- `LEAN4_REFS=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/skills/lean4/references`

### Lean Workflow

- Prefer using the Lean 4 skill for proof workflows, theorem search, and handling `sorry`s.
- Prefer helper scripts from `LEAN4_SCRIPTS` when the skill references them.
- Use absolute paths when invoking local Lean 4 skill resources.
- If Lean MCP is configured for this repository, use it as part of the Lean workflow for goals,
  diagnostics, and code actions.

### GitHub MCP Pull Requests

- Before calling `create_pull_request`, load the pull request template from the target
  repository's default branch.
- Check in this order: `.github/pull_request_template.md`, `pull_request_template.md`,
  `docs/pull_request_template.md`, then `.github/PULL_REQUEST_TEMPLATE/`.
- If no repository template exists, check for an organization or user default community health
  template.
- Pass the template contents as the `body` to `create_pull_request`.
- If the pull request already exists, use `update_pull_request` to set the `body`.
- If multiple templates exist and the correct one is unclear, ask the user which one to use.

## Project Constraints

For Mathlib project-specific contribution requirements, consult the official documents under:

`/home/raibunitsu/working_directory/leanprover-community.github.io/templates/contribute/`

Treat all relevant documents in that directory as authoritative rather than relying on duplicated
local summaries. At the time of writing, this directory contains:

- `index.md`: overall Mathlib contribution guide covering contribution scope, AI disclosure,
  branch-and-PR workflow, and review-queue lifecycle.
- `style.md`: Lean code style guide covering formatting, headers and imports, indentation,
  declaration layout, and related file-structure conventions.
- `naming.md`: naming guide for files, declarations, namespaces, symbol-derived names, and
  standard structural lemma names.
- `doc.md`: documentation guide covering file headers, module docstrings, declaration docstrings,
  Markdown/LaTeX usage, citations, and sectioning comments.
- `commit.md`: pull request title and description convention, including allowed types, scope
  format, subject/body rules, footers, and dependency listings.
- `git.md`: contributor git workflow covering fork/clone setup, remotes, branch management,
  pushing changes, and working with pull requests.
- `pr-review.md`: review guide describing review etiquette and the main checks for style,
  documentation, location, improvements, and library integration.
- `tags_and_branches.md`: branch, tag, and CI workflow guide for Lean, Batteries, and Mathlib,
  especially nightly-testing and breaking-change adaptation workflows.

If additional relevant contribution documents are added there later, treat them as part of the
project constraints as well.
