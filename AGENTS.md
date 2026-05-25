# Repository Guidelines

## Project Structure & Module Organization
The active implementation lives in `tersus/`, a Stack-based Haskell package. Core language, parser, proof, and utility modules are under `tersus/src/`; the CLI entry point is `tersus/app/Main.hs`; and regression tests are in `tersus/test/TestTersus.hs`. The `python/` directory contains older parser and proof prototypes plus `python/tests.py`. The `stack/tersus/` tree is a starter snapshot, not the main development target.

## Build, Test, and Development Commands
Work from `tersus/` unless you are touching the Python prototype.

- `stack build`: compile the Haskell package and surface warnings.
- `stack run`: start the simple parser CLI in `app/Main.hs`.
- `stack test`: run the custom Haskell test harness in `test/TestTersus.hs`.
- `ghci` then `:load Proof`: quick interactive workflow noted in `tersus/README.md`.
- `python python/tests.py`: run legacy Python prototype checks from the repository root.

## Coding Style & Naming Conventions
Follow the existing style in `tersus/src`: 4-space indentation, explicit type signatures for top-level helpers when useful, and `CamelCase` for data constructors and module names. Use `camelCase` for functions such as `parseStatementBlock` and `evalReturningBlock`. Keep parser and proof code split by concern instead of growing monolithic files. For Python prototypes, keep PEP 8 spacing and `snake_case` only when extending those files; preserve existing naming if you are making a minimal fix.

## Testing Guidelines
Add or update Haskell tests in `tersus/test/TestTersus.hs` alongside the affected parser, evaluator, or validator behavior. Existing tests group cases with names like `testParseEval` and `testValidationFail`; follow that pattern and make failures readable. Run `stack test` before opening a PR. If you change prototype-only Python code, run `python python/tests.py` as a secondary check.

Note: the current Haskell test harness is custom and debugging-oriented. It prints `Pass`/`Fail` per case, but `stack test` may still exit successfully even when individual cases report `Fail`, so read the test output rather than trusting the process exit code alone.

## Commit & Pull Request Guidelines
Recent history uses short, direct subjects such as `Minor cleanup` and feature-focused summaries. Prefer concise imperative commits that describe behavior, not process; avoid `Checkpoint` for reviewable work. PRs should include a brief problem statement, the chosen approach, and exact verification commands. Link related issues when available and include example Tersus snippets when grammar or proof behavior changes.

## Contributor Notes
Keep experimental work isolated from the production Haskell package. If a change affects both `python/` and `tersus/`, document which implementation is authoritative in the PR.
