# Repository Guidelines

## Language Evolution and Compatibility
Tersus is in alpha. Breaking changes to syntax, semantics, APIs, and internal
representations are fully allowed when they improve the language or implementation.
Do not preserve compatibility through aliases, legacy paths, or extra complexity
unless the task explicitly requires it. Update affected library code, examples,
tests, documentation, and bootstrap artifacts as appropriate, and explain the
resulting behavior and migration when a change is user-visible.

## Project Structure & Module Organization
The active implementation lives in `tersus/`, a Stack-based Haskell package. Core language, parser, proof, and utility modules are under `tersus/src/` (the shared definitions are split by concern: `Types` is the core type language, `Syntax` is the AST and proof terms, and `Solver` is the proof solver state; the checker is `TypeCheck` over the lower `TypeCheckCore` monad, unification and builtin typing); the CLI entry point is `tersus/app/Main.hs`; the traits `Sequence`, `Growable`, `Clone`, `Copy`, `Drop` and `Deref` that every program that mentions any of them has is in `tersus/lib/prelude.tersus`, and the list that native code is made of in `tersus/lib/lists.tersus`, and the Box that native code is made of in `tersus/lib/box.tersus`, and the struct `String` that a string literal is a value of in `tersus/lib/string.tersus` (all embedded by `PreludeSource`); and regression tests are in `tersus/test/` (`TestTersus.hs` runs the groups, which live in `TestBasics`, `TestValidation`, `TestProofs`, `TestControl`, `TestData`, `TestPipeline`, `TestNative`, `TestOwnership`, `TestTraits`, `TestArrays`, `TestBox`, `TestDeref`, `TestPointers`, `TestBorrow`, `TestCopies`, `TestGenerics`, `TestSequence`, `TestStrings`, `TestBytes`, `TestConnectives`, `TestMirData`, `TestMirReader`, `TestMirEmit`, `TestBootstrap` and `TestParity`, with the shared harness in `TestHarness`).

## Build, Test, and Development Commands
Work from `tersus/`.

- `stack build`: compile the Haskell package and surface warnings.
- `stack run -- check <file>` / `stack run -- run <file>`: validate, or validate, compile to native code and run (needs clang), a `.tersus` program via the CLI; `stack run -- eval <file>` runs the validated MIR with the reference interpreter instead (what `testNative` compares native code with) in `app/Main.hs` (logic in `src/Cli.hs`). `stack run -- mir --data <file>` prints the MIR that native code is made from as data (`MirData`; the input of the emitter that step 31 writes in Tersus), `stack run -- llvm <file>` prints the LLVM IR of a validated program (written by the emitter in Tersus, `examples/emit.tersus`, which is built with clang on first use from the seed `bootstrap/emitter.ll` and cached; `Bootstrap`) and `stack run -- build <file> -o <output>` compiles it with clang (which `testNative` also needs to run the executables; it passes without). `testNative` also runs some programs under `valgrind` when it is installed; the heap model of `testOwnership` needs neither.
- `stack test`: run the custom Haskell test harness in `test/TestTersus.hs`, which runs each group in a process of its own; `stack test --test-arguments='-j 1'` runs the groups one at a time, and `stack test --test-arguments='testBorrow testCopies'` runs only those groups.
- `ghci` then `:load Pipeline`: quick interactive workflow noted in `tersus/README.md`.

## Coding Style & Naming Conventions
Follow the existing style in `tersus/src`: 4-space indentation, explicit type signatures for top-level helpers when useful, and `CamelCase` for data constructors and module names. Use `camelCase` for functions such as `parseStatementBlock` and `evalReturningBlock`. Keep parser and proof code split by concern instead of growing monolithic files.

## Testing Guidelines
Add or update Haskell tests in the matching module under `tersus/test/` (and list a new group in `TestTersus.hs`) alongside the affected parser, evaluator, or validator behavior. Existing tests group cases with names like `testParseEval` and `testValidationFail`; follow that pattern and make failures readable. Run `stack test` before opening a PR.

Note: the Haskell test harness is custom. It prints `[PASS]`/`[FAIL]` per case and a final `Summary: N passed, M failed` line, and exits non-zero if any case fails, so the process exit code is reliable. It runs each group in a process of its own, several at a time (at most one process per group, and no more than the machine has processors), and prints a `[TIME] <group> <s>s` line per group so a slow group is easy to find; a group that dies without reporting a result is counted and printed as `[CRASH]`. Because the groups are separate processes, a test must not depend on another group having run, and anything global (a locale, `XDG_CACHE_HOME`, a fixed temporary file name) is per group rather than per run. Example programs in `tersus/examples/` are loaded and checked by `testExamples`, so a new or edited example needs a matching expectation in `tersus/test/TestPipeline.hs`.

## Documentation Guidelines
Keep `tersus/LANGUAGE.md` in sync with user-visible syntax (including comments), builtins, validation statements, rewrite rules, contracts, and known language limitations. Keep `tersus/examples/README.md` in sync with the programs in `tersus/examples/`. Update the interpreter-flow section in `tersus/README.md` when parser, concrete evaluation, validation, scope, function-call, or CLI behavior changes. Include small Tersus snippets when documenting grammar or proof behavior.

## Commit & Pull Request Guidelines
Recent history uses short, direct subjects such as `Minor cleanup` and feature-focused summaries. Prefer concise imperative commits that describe behavior, not process; avoid `Checkpoint` for reviewable work. PRs should include a brief problem statement, the chosen approach, and exact verification commands. Link related issues when available and include example Tersus snippets when grammar or proof behavior changes.

## Contributor Notes
Keep experimental work isolated from the production Haskell package.
