MATHLIB_BUILD_DIR := .lake/packages/mathlib/.lake/build/lib/lean

build: _check-mathlib-cache ## Build the Shannon library
	lake build Shannon

build-all: _check-mathlib-cache ## Build everything (Shannon + dependencies)
	lake build

bootstrap: ## Bootstrap worktree (lake update, cache get, build)
	bin/bootstrap-worktree

_check-mathlib-cache:
	@if [ ! -d "$(MATHLIB_BUILD_DIR)" ] || [ -z "$$(ls $(MATHLIB_BUILD_DIR)/Mathlib*.olean 2>/dev/null)" ]; then \
		echo "Error: Mathlib prebuilt artifacts not found." >&2; \
		echo "Run 'make bootstrap' or 'bin/bootstrap-worktree' first." >&2; \
		exit 1; \
	fi

lint: lint-markdown lint-spelling ## Run all linters

lint-markdown: ## Lint Markdown files
	markdownlint-cli2 "**/*.md"

lint-spelling: ## Check spelling with cspell
	cspell --no-progress "**/*.md"

check: lint build ## Lint, then build

clean: ## Remove Lake build artifacts
	lake clean

help: ## Show this help
	@grep -E '^[a-zA-Z0-9_-]+:.*##' $(MAKEFILE_LIST) | \
		awk -F ':.*## ' '{printf "  \033[36m%-20s\033[0m %s\n", $$1, $$2}'

.PHONY: build build-all bootstrap clean lint lint-markdown lint-spelling check help _check-mathlib-cache
