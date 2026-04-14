# Contributing to shannon-entropy

Thank you for your interest in contributing to shannon-entropy.

Please note that this project has a [Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold it.

## Reporting Issues

- **Bug reports and feature requests:** Use the [issue tracker](https://github.com/cboone/shannon-entropy/issues/new/choose)
- **Questions and ideas:** Use [GitHub Discussions](https://github.com/cboone/shannon-entropy/discussions)
- **Security vulnerabilities:** See [SECURITY.md](.github/SECURITY.md)

## Development Setup

### Requirements

- Lean 4 toolchain (version specified in `lean-toolchain`)
- Lake (bundled with Lean)
- markdownlint-cli2 (Homebrew: `brew install markdownlint-cli2`)
- cspell (Homebrew: `brew install cspell`)

### Getting Started

```bash
# Clone the repository
git clone https://github.com/cboone/shannon-entropy.git
cd shannon-entropy

# Bootstrap (downloads Mathlib artifacts and builds)
bin/bootstrap-worktree

# Run linter
make lint

# Run all checks (lint + lean-lint + build + test)
make check
```

## Code Style

- Run `make lint` before committing
- Follow the Lean conventions documented in `AGENTS.md`
- Add domain-specific terms to `cspell-words.txt` when needed

## Commit Messages

Use [Conventional Commits](https://www.conventionalcommits.org/) format:

```text
<type>: <description>
```

**Types:**

- `feat`: new feature
- `fix`: bug fix
- `docs`: documentation changes
- `refactor`: code refactoring (no functional change)
- `test`: adding or updating tests
- `build`: build system or dependency changes
- `ci`: CI configuration changes
- `chore`: maintenance tasks

**Examples:**

```text
feat: add mutual information definition
fix: correct simplex proof for edge case
docs: update module layout in README
refactor: simplify rational approximation lemma
test: add entropy examples for uniform distributions
chore: update Mathlib to v4.30
```

## Pull Request Process

1. Fork the repository
1. Create a feature branch
1. Make your changes
1. Ensure tests pass: `make check`
1. Ensure linting passes: `make lint`
1. Submit a pull request

### Branch Naming

Use descriptive branch names with a type prefix:

- `feature/*`: new features
- `fix/*`: bug fixes
- `docs/*`: documentation changes
- `refactor/*`: code refactoring
- `test/*`: test additions or fixes
