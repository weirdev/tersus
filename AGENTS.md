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
  Packages and modules are in `src/Modules.hs` (package discovery, the module
  graph and the loader, canonical names), `src/Interface.hs` (what a checked
  module exposes to its importers), `src/ModuleResolve.hs` (rewriting a file's
  references to canonical names through its imports), `src/LibPackage.hs` (the
  compiler libraries compiled once as a synthetic `tersuslib` package, one
  module per lib file, from the `PreludeSource` texts) and `src/Link.hs`
  (merging the lowered modules into one program and pruning what the entry
  program does not reach); `src/ElaborateRequest.hs` is the elaborator's request and response
  for one module (the compiler elaborates every program and module through it,
  with the Haskell `respond`; `AST_DATA.md`); `src/Pipeline.hs` compiles each module with the
  implicit libraries its own text calls for (`Compile.librariesFor`, consumed
  via synthesised implicit imports on both the single-file and package paths,
  the package path in `src/PackageCompile.hs`) and links the package.
- `tersus/lib/` (Tersus sources the Haskell implementation depends on). The
  first seven are the compiler libraries: each is compiled as one module of the
  synthetic `tersuslib` package (`src/LibPackage.hs`) from its `PreludeSource`
  text, selected per module by `Compile.librariesFor` and consumed via
  synthesised implicit imports on both the single-file and package paths:
  - `types.tersus`: the structs `List` and `Box` that a list and a Box are
    values of, imported for every program that does not declare `List` or
    `Box`. Embedded by `PreludeSource`.
  - `eq.tersus`: the trait `Eq` that `=` and `!=` call, and its impls for lists, arrays and Boxes, imported for every program that does not
    declare a trait `Eq`. Embedded by `PreludeSource`.
  - `clone.tersus`: the trait `Clone` that `clone(x)` and `x.clone()` call, and its impls for lists, arrays and Boxes, imported for every program that does not
    declare a trait `Clone`. Embedded by `PreludeSource`.
  - `prelude.tersus`: the traits `Sequence`, `Growable`, `Copy`, `Drop`,
    `Deref` and `Hash` (with `hashCombine`), imported for a program that
    mentions any of them (or `hashCombine`) and declares none of them;
    declaring any prelude trait suppresses the prelude and with it `string`,
    `map` and `set`. It imports `clone`. Embedded by `PreludeSource`.
  - `string.tersus`: the struct `String` that a string literal is a value of,
    imported for a program that writes a string literal or mentions `String`.
    It imports `prelude`, `eq` and `clone`. Embedded by `PreludeSource`.
  - `map.tersus`: the struct `HashMap` (and its `Entry`), imported for a
    program that mentions `HashMap` (a `HashSet` pulls it in too). It imports
    `prelude`, `eq` and `clone`. Embedded by `PreludeSource`.
  - `set.tersus`: the struct `HashSet`, made of a map, imported for a program
    that mentions `HashSet`. It imports `map`, `prelude`, `eq` and `clone`.
    Embedded by `PreludeSource`.
  - `lists.tersus` and `box.tersus`: native-only List/Box helper modules of
    the same synthetic `tersuslib` package. They import the types and traits
    they use; `types.tersus` alone owns the structs and layout invariants.
    `LibPackage` checks and lowers them separately, and `MirHousekeeping`
    links them and erases their ghosts. Native code of the validator is made
    with them, so they are built unvalidated, and the validator, once built,
    validates them (with a List and a Box as the structs they are) before it is
    used (`ValidatorNative.validatorExecutable`).
    `MirLists` links only the helper units native lowering needs, after user
    validation. Their bodies and Drop impls are never implicit user imports.
  - `stdlib.tersus`: the standard library written in Tersus. Embedded by
    `PreludeSource` and parsed by `StdLibDefs`, which is where the builtins it
    declares get their contracts; it is not linked into user programs.
  - `validation/`: the validator package. Fourteen declarative sibling files
    separate the data model, relations, differences, context/linear reasoning, sequence facts,
    goal proofs, state/joins, evaluation/execution, saturation and control flow.
    They remain one root module. `driver.tersus` is the sole entry and imports
    each provider explicitly; reference queries call the same unpruned linked
    program without running the driver. `PreludeSource.validationPackageFiles`
    embeds all files and the package marker. `ValidatorNative` requires the
    full validator source and physical List/Box proofs before use.
  - `mir/`, `data/`, `parser/` and `ast_reader/`: the compiler's own programs,
    four packages beside `validation/` with their own `package.tersus`
    markers. `testHostValidation` validates the AST reader and the MIR reader,
    checker, eraser and emitter, and says what running them with no input does.
    `mir/emit/emit.tersus` is the LLVM emitter written in Tersus, and
    `mir/mir_reader/mir_reader.tersus` / `mir/mir_verify/mir_verify.tersus` /
    `mir/mir_erase/mir_erase.tersus` are the MIR reader, the MIR checker and
    the ghost erasure. The host runs the checker and the erasure on the MIR as
    data (`MirHousekeeping`); they are the production path.
    `mir/ownership/` holds the ownership and reference-write passes; the
    emitter's executable runs them when its input starts with `pass ownership`
    or `pass expand`. The emitter's declaration-only `types.tersus`,
    `values.tersus`, `operations.tersus`, `functions.tersus` and
    `helpers.tersus` files are siblings of `emit.tersus` in one `mir::emit`
    module; only `emit.tersus` runs. `data/` holds the shared token, type and
    AST codecs and the reader of AST data (`data::reader`, which the AST
    reader runs and an elaborator written in Tersus will), `parser/parser.tersus` is the native parser and
    `ast_reader/ast_reader.tersus` the AST reader (`AST_DATA.md`). All are
    embedded by `PreludeSource` (`mirPackageFiles`, `dataPackageFiles`,
    `parserPackageFiles`, `astReaderPackageFiles`) and listed in
    `package.yaml`.
- `tersus/examples/`: example programs, all loaded and checked by
  `testExamples` (see Testing Guidelines).
- `tersus/bootstrap/emitter.sha256`: the SHA-256 pin of the seed IR the Tersus
  emitter is bootstrapped from; the seed itself is a GitHub release asset
  (see Build, Test, and Development Commands).
- `tersus/bootstrap/parser.sha256`: the SHA-256 pin of the native parser LLVM
  seed; `TERSUS_PARSER_SEED_FILE` supplies verified local bytes before release.
- `tersus/test/`: regression tests. `TestTersus.hs` runs the test groups; the
  groups live in `TestBasics`, `TestValidation`, `TestProofs`, `TestControl`,
  `TestData`, `TestPipeline`, `TestNative`, `TestOwnership`, `TestTraits`,
  `TestArrays`, `TestBox`, `TestDeref`, `TestPointers`, `TestBorrow`,
  `TestCopies`, `TestEq`, `TestGenerics`, `TestSequence`, `TestStrings`, `TestBytes`,
  `TestConnectives`, `TestMirData`, `TestMirReader`, `TestMirVerify`,
  `TestMirEmit`, `TestBootstrap`, `TestParity`, `TestAstData` and `TestDifferential`
  (the differential harness of `test/Differential.hs`, also run on an elaborator
  executable by `stack run frontend-diff`), with the shared harness in `TestHarness`.

## Build, Test, and Development Commands
Work from `tersus/`.

- `stack build`: compile the Haskell package and surface warnings. CI
  (`.github/workflows/ci.yml`) runs `stack build --test --no-run-tests` and
  then `stack test`, both from `tersus/`.
- The package builds the executable `tersus-exe`:
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
    emitter in Tersus, `lib/mir/emit/emit.tersus`, which is built with clang on
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
  `lib/mir/emit/emit.tersus` or to what it is built from), regenerate the seed
  into a temporary file only when that succeeds:
  `stack run emitter-seed -- emit /tmp/emitter.ll.new` (it checks that stage 0
  and stage 1 own and emit the emitter alike; after a change to what the
  ownership passes in `lib/mir/ownership/` write, run
  `stack run emitter-seed -- advance` first, pin its output, and `emit` from it,
  which must give the same bytes; `STEP31.md`),
  then `sha256sum /tmp/emitter.ll.new`, upload it as the `emitter.ll` asset of a
  new GitHub release tagged `bootstrap-<first 12 digits of that digest>`,
  put the digest in `bootstrap/emitter.sha256`, and let `TestBootstrap`
  check the stage 0 / stage 1 fixpoint. Do not write straight into a seed
  file the running compiler is using.
- Production parsing uses native P1. Bootstrap readers (`StdLibDefs`,
  `LibParsed`, `Compile`, default `Modules`) use the pinned native P0 leaf;
  there is no Haskell grammar or fallback. Building Haskell needs no clang
  or network; the first language parse needs clang and verified parser/emitter
  seeds. The parser seed override is `TERSUS_PARSER_SEED_FILE` (the emitter's
  remains `TERSUS_SEED_FILE`). `AST_DATA.md` describes seed regeneration through
  the exact prepared parser package and its P0/P1/P2 fixpoint.
- `stack test`: run the custom Haskell test harness in `test/TestTersus.hs`,
  which runs each registered group in a process of its own with `-N1`;
  `stack test --test-arguments='-j 1'` runs the groups one at a time, and
  `stack test --test-arguments='testBorrow testCopies'` runs only those groups.
  `testNative`, `testMirEmit`, `testMirVerify`, `testMirSelfHosted`,
  `testAstData`, `testParser` and `testAstReader` each register four batches named
  `<original>:1/4` through `<original>:4/4`. The AST/parser corpora partition
  samples without splitting package declaration contexts; all emitter
  helper files share one prepared-parser comparison.
  Selecting an original name selects all its batches; shard filters intersect
  the full-suite assignment. Self-hosted batches share one shard and its full
  validated-program cache; Native memory-limit cases stay ordered in one batch.
  `testBootstrap` remains one private cold group. Parser bootstrap registers
  `testParserBootstrap:1/2` for the genuine cold/refusal/reuse checks and
  `testParserBootstrap:2/2` for repair and fixpoint checks from independent
  private copies of the runner's ordinary tool cache. Ordinary preparation
  is counted in the latter group and never credited to the cold pair.
  CI reserves one runner for each of these three bootstrap groups; the
  remaining groups use three runners, with four worker processes per runner.
  The required aggregate check still requires every shard to pass.
  `testHostValidation`, which validates the compiler's own programs (the MIR
  reader, checker and eraser, and the emitter), runs only when named, since it
  takes far longer than the rest of the suite (`TestTersus.optInGroups`).
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
library and the `tersus-exe` CLI; put it under `tersus/dev/` or in examples, and wire it into `package.yaml` as its own
executable or test target rather than into the library.
