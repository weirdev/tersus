# Repository Guidelines

## Language Evolution and Compatibility
Tersus is in alpha. Breaking changes to syntax, semantics, APIs, and internal
representations are fully allowed when they improve the language or implementation.
Do not preserve compatibility through aliases, legacy paths, or extra complexity
unless the task explicitly requires it. Update affected library code, examples,
tests, documentation, and bootstrap artifacts as appropriate, and explain the
resulting behavior and migration when a change is user-visible.

## Project Structure & Module Organization
The active implementation lives in `tersus/`, a Stack-based Haskell package.

- `tersus/src/`: core language, parser, type checker, MIR, proof, and utility
  modules (the shared definitions are split by concern: `Types` is the core
  type language, `Syntax` is the AST and proof terms, and `Solver` is the
  proof solver state; `TypeCheckCore` holds the checking monad, unification
  and builtin typing, and `TypeCheck` holds declaration, expression and
  proof inference). The CLI entry point is `tersus/app/Main.hs` (logic in
  `src/Cli.hs`).
- `tersus/lib/` (Tersus sources the Haskell implementation depends on):
  - `eq.tersus`: the trait `Eq` that `=` and `!=` call, and its impls for lists, arrays and Boxes, put in front of every program that does not
    declare a trait `Eq` (`Pipeline.libraries`). Embedded by `PreludeSource`.
  - `clone.tersus`: the trait `Clone` that `clone(x)` and `x.clone()` call, and its impls for lists, arrays and Boxes, put in front of every program that does not
    declare a trait `Clone` (`Pipeline.libraries`). Embedded by `PreludeSource`.
  - `prelude.tersus`: the traits `Sequence`, `Growable`, `Copy`, `Drop`
    and `Deref`, put in front of a program that mentions any of them and does
    not declare it (`Pipeline.libraries`). Embedded by `PreludeSource`.
  - `lists.tersus`: the list that native code is made of (`StdList`), and
    `box.tersus`: the Box that native code is made of (`StdBox`). Both embedded
    by `PreludeSource` and lowered with the lists library.
  - `string.tersus`: the struct `String` that a string literal is a value of,
    embedded by `PreludeSource` and put after the prelude for a program that
    writes a string literal or mentions `String`.
  - `stdlib.tersus`: the standard library written in Tersus. Embedded by
    `PreludeSource` and parsed by `StdLibDefs`, which is where the builtins it
    declares get their contracts; it is not put in front of user programs.
  - `validation.tersus`: the validator written in Tersus, run by
    `SelfHostedMir`/`SelfHostedProof` alongside the Haskell validator, which
    remains the production path. It is not embedded by `PreludeSource`; tests
    and hosts read it from `lib/` directly.
- `tersus/examples/`: example programs, all loaded and checked by
  `testExamples` (see Testing Guidelines). `examples/emit.tersus` is the LLVM
  emitter written in Tersus, and `examples/mir_reader.tersus` /
  `examples/mir_verify.tersus` are the MIR reader and MIR checker written in
  Tersus.
- `tersus/bootstrap/emitter.sha256`: the SHA-256 pin of the seed IR the Tersus
  emitter is bootstrapped from; the seed itself is a GitHub release asset
  (see Build, Test, and Development Commands).
- `tersus/dev/parity/`: the `parity` executable, a development harness outside
  the production library and CLI.
- `tersus/test/`: regression tests. `TestTersus.hs` runs the test groups; the
  groups live in `TestBasics`, `TestValidation`, `TestProofs`, `TestControl`,
  `TestData`, `TestPipeline`, `TestNative`, `TestOwnership`, `TestTraits`,
  `TestArrays`, `TestBox`, `TestDeref`, `TestPointers`, `TestBorrow`,
  `TestCopies`, `TestEq`, `TestGenerics`, `TestSequence`, `TestStrings`, `TestBytes`,
  `TestConnectives`, `TestMirData`, `TestMirReader`, `TestMirVerify`,
  `TestMirEmit` and `TestBootstrap`, with the shared harness in `TestHarness`.

## Build, Test, and Development Commands
Work from `tersus/`.

- `stack build`: compile the Haskell package and surface warnings. CI
  (`.github/workflows/ci.yml`) runs `stack build --test --no-run-tests` and
  then `stack test`, both from `tersus/`.
- The package builds two executables, `parity` and `tersus-exe`, and a bare
  `stack run` runs the first of them (`parity`), so always name the CLI:
  `stack run tersus-exe -- <command> <file>`. Commands (`src/Cli.hs`):
  - `check <file>`: parse and validate a program.
  - `run <file> [args]`: validate, compile to native code and run (needs
    clang), passing any extra arguments to the program.
  - `eval <file> [args]`: run the validated MIR with the reference interpreter
    instead (what `testNative` compares native code with); no compiler needed.
  - `mir <file>`: print the validated MIR; `mir --data <file>` prints the MIR
    that native code is made from as data (`MirData`; the input of the emitter
    written in Tersus).
  - `owned <file>`: print the MIR that native code is made from, with moves,
    copies and frees.
  - `llvm <file>`: print the LLVM IR of a validated program (written by the
    emitter in Tersus, `examples/emit.tersus`, which is built with clang on
    first use from the seed (a release asset pinned by
    `bootstrap/emitter.sha256`, fetched and verified on first use; a seed at
    `$TERSUS_SEED_FILE` or `bootstrap/emitter.ll` is used instead when
    present) and cached; `Bootstrap`).
  - `build <file> -o <output>`: compile a validated program to an executable
    with clang (which `testNative` also needs to run the executables; it
    passes without).
  - `assumptions <file>`: print what the program takes on trust (`assume`,
    `Block::assume`, `extern fn` and `axiom`), which the validator does not
    prove.
  - Use `-` as the file to read the program from standard input.
  `testNative` also runs some programs under `valgrind` when it is installed;
  the heap model of `testOwnership` needs neither.
- If a change alters what the emitter in Tersus produces (a change to
  `examples/emit.tersus` or to what it is built from), regenerate the seed
  into a temporary file only when that succeeds:
  `stack run tersus-exe -- llvm examples/emit.tersus > emitter.ll.new`,
  then `sha256sum emitter.ll.new`, upload it as the `emitter.ll` asset of a
  new GitHub release tagged `bootstrap-<first 12 digits of that digest>`,
  put the digest in `bootstrap/emitter.sha256`, and let `TestBootstrap`
  check the stage 0 / stage 1 fixpoint. Do not redirect straight into a seed
  file the running compiler is using: the shell truncates it before the
  compiler runs.
- `stack test`: run the custom Haskell test harness in `test/TestTersus.hs`,
  which runs each group in a process of its own;
  `stack test --test-arguments='-j 1'` runs the groups one at a time, and
  `stack test --test-arguments='testBorrow testCopies'` runs only those groups.
- `ghci` then `:load Pipeline`: quick interactive workflow noted in
  `tersus/README.md`.

## Coding Style & Naming Conventions
Follow the existing style in `tersus/src`: 4-space indentation, explicit type signatures for top-level helpers when useful, and `CamelCase` for data constructors and module names. Use `camelCase` for functions such as `parseStatementBlock` and `evalReturningBlock`. Keep parser and proof code split by concern instead of growing monolithic files.

`tersus.cabal` is generated from `package.yaml` by hpack: edit `package.yaml`
and let Stack regenerate the `.cabal` file; do not hand-edit it. A new file
under `lib/` that the build depends on also needs an `extra-source-files`
entry in `package.yaml`, and a `PreludeSource` embedding if Haskell code has
to read it at compile time.

## Testing Guidelines
Add or update Haskell tests in the matching module under `tersus/test/` (and list a new group in `TestTersus.hs`) alongside the affected parser, evaluator, or validator behavior. Existing tests group cases with names like `testParseEval` and `testValidationFail`; follow that pattern and make failures readable. Run `stack test` before opening a PR.

Note: the Haskell test harness is custom. It prints `[PASS]`/`[FAIL]` per case and a final `Summary: N passed, M failed` line, and exits non-zero if any case fails, so the process exit code is reliable. It runs each group in a process of its own, several at a time (at most one process per group, and no more than the machine has processors), and prints a `[TIME] <group> <s>s` line per group so a slow group is easy to find; a group that dies without reporting a result is counted and printed as `[CRASH]`. Because the groups are separate processes, a test must not depend on another group having run, and anything global (a locale, `XDG_CACHE_HOME`, a fixed temporary file name) is per group rather than per run. Example programs in `tersus/examples/` are loaded and checked by `testExamples`, so a new or edited example needs a matching expectation in `tersus/test/TestPipeline.hs`.

## Documentation Guidelines
Keep `tersus/LANGUAGE.md` in sync with user-visible syntax (including comments), builtins, validation statements, rewrite rules, contracts, and known language limitations. Keep `tersus/examples/README.md` in sync with the programs in `tersus/examples/`. Update the interpreter-flow section in `tersus/README.md` when parser, concrete evaluation, validation, scope, function-call, or CLI behavior changes. Include small Tersus snippets when documenting grammar or proof behavior.

The design and status documents in `tersus/` are part of the documentation:
update whichever of `MIR.md`, `DATA_MODEL.md`, `POINTERS.md`, `DROPS.md`,
`REFERENCES.md`, `ALLOCATORS.md`, `STEP31.md` and `REPLACING_HASKELL.md`
describes the area a change touches, including its Status section when what
is built changes, and the roadmap in `tersus/README.md` when a step's state
changes.

## Commit & Pull Request Guidelines
Recent history uses short, direct subjects such as `Minor cleanup` and feature-focused summaries. Prefer concise imperative commits that describe behavior, not process; avoid `Checkpoint` for reviewable work. PRs should include a brief problem statement, the chosen approach, and exact verification commands. Link related issues when available and include example Tersus snippets when grammar or proof behavior changes.

## Contributor Notes
Keep experimental and development-only work out of the production Haskell
library and the `tersus-exe` CLI; put it under `tersus/dev/` (as the `parity`
harness is) or in examples, and wire it into `package.yaml` as its own
executable or test target rather than into the library.
