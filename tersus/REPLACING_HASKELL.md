# Replacing Haskell with Tersus

The goal is a native Tersus compiler and test suite with no Haskell dependency.
The LLVM emitter was the first compiler stage to move (`STEP31.md`). This
survey separates completed replacements from the next work; the numbers below
are measured on GitHub master `a9e12e6cc8aa0337e1a44b6fff570e58ada5732b`
(2026-11-05), not the earlier `751dcc9` snapshot.

## Survey baseline

At `a9e12e6`, `tersus/src/` had 45 Haskell files and 21,816 lines. The table
records that baseline; ownership is now a Tersus pass, `MirOwnership.hs` is
deleted, and its operand-role helpers for move checking are in `MirMoves`.

| Area | Main modules |
|---|---|
| Elaboration | `TypeCheck` (1,790), `TypeCheckCore` (1,663), `Types`, `Syntax`, `Solver` |
| MIR and passes | `MirLower` (1,247), `MirMoves` (719), `Mir` (698), `MirLists` (515), `MirMono` (276); the former 1,196-line ownership transform is deleted |
| Parser and data bridges | `AstData`, `DataCodec`, `ParsedFile`, `TersusParser`, `SourceParse`, `FileParserProtocol`, `ParserSeed`, `MirData` |
| Validation host | `SelfHostedMir` (3,090), `ValidatorNative` (349) |
| Packages and linking | `Modules` (1,362), `ModuleResolve` (535), `Link` (347), `Interface` (269), `PackageCompile` (268), `LibPackage` (164) |
| Runtime and host | `MirEval` (802), `MirHousekeeping`, `Native`, `Seed`, `Bootstrap`, `PreludeSource`, `LlvmRuntime`, `Pipeline`, `Cli`, utilities |

At the same baseline, `test/*.hs` had 17,682 lines and the CLI entry had 81.
They are separate from the source count. Reproduce current counts from
`tersus/` with `wc -l src/*.hs test/*.hs app/Main.hs`.

## Implemented replacements

- **LLVM emission:** `lib/mir/emit/` is the production emitter.
  `LlvmEmit.hs` is deleted. Bootstrap uses the release asset pinned by
  `bootstrap/emitter.sha256`.
- **Validation:** the `lib/validation/` package is the only production validator.
  `SelfHostedMir` encodes its input and `ValidatorNative` builds and runs it;
  an unmodelled program is refused, not sent to a Haskell fallback.
  The old proof engine, validator and `SelfHostedProof` are deleted. The
  bridge remains: replacing a validator is not the same as deleting its host.
- **Builtin contracts:** `lib/stdlib.tersus` supplies them through
  `StdLibDefs`. `StdLib.hs` still contains 207 lines of primitive signatures
  and metadata; this is not an 839-line pending contract rewrite.
- **MIR checking and ghost erasure:** `mir_verify` and `mir_erase` are
  production Tersus tools hosted by `MirHousekeeping`. `MirVerify.hs` and
  `MirGhost.hs` are deleted. The host restores metadata omitted by their
  runtime data views. The MIR executor runs only the recursive erasure of the
  List/Box library during tool construction. Cold tool builds (E1, checker,
  eraser, P1 and the unchecked validator) run concurrently; their prepared
  owned-MIR inputs are cached per compiler snapshot, entry and flags, and each
  executable's identity is the actual prepared bytes.
- **Parsing:** `lib/parser/` supplies native P1. `Parse.hs` and the
  Haskell-parser selector are deleted. P0 is the pinned native parser seed;
  the explicit interpreted selector executes the Tersus parser, not a
  different grammar. `AST_DATA.md` describes the P0/P1/P2 evidence.
- **Ownership and reference-write expansion:** `lib/mir/ownership/`
  contains both transformations, and the emitter executable dispatches their
  native requests. `MirHousekeeping` keeps the monomorphization adapter and
  `MirOwnershipData` preserves omitted metadata. The replacement is implemented;
  performance optimization and final verification are still in progress.
- **AST data:** `AstData` and `lib/ast_reader/` exchange parsed syntax
  and complete elaborated occurrence types, contracts and builtin metadata.
  Parsed data is a production boundary; elaboration itself remains Haskell.

The validator keeps changing independently. PR #169 is on the survey base;
its loop-state anchors and closure reuse reduce work unrelated to a loop's
writes. PR #167 (test cleanup) and PR #168 (CI speed) landed after it; the
ownership replacement is built on `de36319b1d370cd17dcf5cca2188b2424d143268`.
Baseline counts above describe `a9e12e6`, not a current test total or
performance result.

## Validator package migration

The validator core and native driver are one ordinary package under
`lib/validation/`, with `driver.tersus` as the entry for native construction
and reference queries. Both preserve bare core type and function identities.
Reference queries call named functions without executing the driver main;
the unpruned linked program retains every helper and its proof metadata.

The core declarations are split into fourteen sibling providers, all in that
same root module:

- `model.tersus`: data declarations and their Clone/Copy implementations.
- `relations.tersus`: equality/order facts, congruence closure and representatives.
- `differences.tersus`: difference constraints, constants and overflow-safe arithmetic.
- `context.tersus` and `linear.tersus`: context closure/analysis and linear entailment.
- `sequenceFacts.tersus`: finite and quantified facts about sequence reads.
- `validation.tersus`: goal entailment, proof-step checking and proof-flow queries.
- `state.tersus` and `joins.tersus`: values, boolean facts, branch joins and read/write splits.
- `evaluation.tersus` and `execution.tersus`: concrete/builtin facts and execution steps.
- `saturation.tersus`: quantified instances, frames and bounded proof search.
- `loopInference.tersus` and `flow.tersus`: loop candidates and execution-flow validation.

Every file imports the providers it uses explicitly. `driver.tersus` is still
the sole executable entry and imports the moved types and helper functions
from their actual owners. `JoinedFact`, its implementations, private bounded
`commonFacts` and its regular wrapper stay together in `joins.tersus`. Data
and Clone/Copy declarations retain their original relative order in
`model.tersus`: a derived clone needs its field types' clone implementations
already available when it is checked. No file-name ordering dependency or
compiler change is introduced. The package remains one build unit: the cycles between reasoning and execution
helpers do not become cross-module dependencies. Declarations, function
bodies, contracts and the driver wire protocol are unchanged; generated
source-coordinate names and declaration-placement metadata reflect the new
files. The fixed full-metadata regression is updated only after comparing
those differences with the landed baseline.

The entry module cannot be imported by a reachable dependency without a
cycle, so it uses the existing compiler-owned home interface. Private bounded
helpers stay inside that entry unit; bounded exports from ordinary imported
modules remain unsupported. Top-level functions after a main return are
lowered once at their declaration position, rather than consuming their
expression types once while skipping and again while lowering. Linked ghost
environments are completed with the existing `Compile.completeSpecEnvs`
contract, including private instantiated library functions. Existing local
bindings win over global function names; completing twice changes nothing.

Preparation uses the package's path/content manifest and the existing native
input, producer, runtime, flags and target keys. The checked validator still
requires uncached proofs of the full linked core/driver source and physical
native List/Box storage. No algorithm, wire format or bootstrap trust gate
changes with the move.

## Ownership replacement

`insertOwnership` and `expandRefWrites` now run in Tersus through the shared
MIR reader/writer and the emitter executable. The operand-role helpers move
checking needs are in `MirMoves`. The old Haskell transformation, kept for a
while as a frozen test oracle, is deleted with the comparisons against it.

The native order is a correctness constraint:

```
validate -> eraseGhosts -> expandRefWrites -> lowerLists
         -> monomorphize -> ownership -> verifyProgram -> emitter
```

The host's `insertOwnership` calls `MirMono.monomorphize` before invoking the
Tersus ownership pass. The reference-write entry point runs earlier; moving
monomorphization itself remains separate work. Reference-write expansion
rebuilds logical fields and sequences before list operations become helper
calls, while generic function bodies still contain symbolic types and sizes.
Assignments through reference-typed roots remain reference writes for the
emitter and retained Haskell adapters.

The data contract must follow those phases:

- Before list lowering, preserve symbolic `Type`/`Size` values, type arguments,
  function parameter metadata and declarations. The shared codec retains
  `TNamed`'s original base and argument tokens; do not replace them with a
  rendered-name-only representation.
- Ownership runs on the monomorphized program and needs `borrowed`,
  `mutBorrowed`, `from`, source local names, all type declarations and the
  concrete Drop/Clone functions. Removing an apparently uncalled implementation
  can change ownership or the code emitted for a clone/drop.
- `MirData` v1 is a runtime view, not a lossless replacement for `Program`:
  it omits `progGenerics`, `progInvariants`, function specifications and ghosts.
  A host adapter must keep untouched metadata on the original program and
  restore any ghost identities across statement expansion/block splitting.
  Do not use `forNative` as the new pipeline result. Only the existing
  normalization/erasure stages may discard metadata according to their contract.
- `monomorphize` has a no-generic fast path that returns the original program,
  including its proof metadata. Do not assume every ownership input has empty
  specifications merely because it crossed that call.

Bootstrap for this replacement combines ownership with the emitter executable.
The pinned stage-0 emitter seed runs `pass expand` and `pass ownership` on the
sources the host builds for itself (the emitter, checker, eraser, parser and
validator), so their prepared inputs need no stage 1 and are made concurrently;
stage 1 emits the tools and owns and emits user programs. The bootstrap
fixpoint makes stage 0 and stage 1 own the emitter alike. Ownership has no
interpreted cold path or Haskell fallback. `dev/emitter-seed` has `advance`
and `emit`; `emit` checks independent stage-0/stage-1 ownership and emission.
Publishing a PR requires a production-emitted seed that reproduces itself, its
release asset and pin, and the full test evidence below.

Gate: the independent heap model against the executor and native/reference
parity for the corpus and the reference-write fixtures; interpreted/native
parity of the ownership tool on MIR fixtures; metadata and malformed-input
checks; the complete suite and opt-in host validation; and independent
stage-0/stage-1 ownership and emitter/parser bootstrap fixpoints. Cold bootstrap
must also stay within the agreed performance budget against the same-host base.

## Next work, in priority order

### 1. Native monomorphization

Replace `MirMono.monomorphize` after the ownership gates pass. Its baseline is
276 lines, but it needs a data
contract for generic type templates and type/size substitution, reachable
instances, and implicit Drop instantiation. `monomorphizeForValidation` preserves
contracts and serves `SelfHostedMir`; moving the native path does not authorize
stripping that validation metadata or deleting the validation path.

### 2. Elaboration and the package frontend

Move `TypeCheck`/`TypeCheckCore` over the elaborated AST bridge, including
interfaces, builtin typing, trait resolution and diagnostics. The parser is done;
this is not a second parser rewrite. Keep occurrence typing and declaration
ordering explicit (`AST_DATA.md`).

Package loading and linking are also compiler work, not incidental CLI glue:
`Modules`, `ModuleResolve`, `Interface`, `LibPackage`, `PackageCompile` and `Link`
resolve canonical names, compile interfaces and library units, reject collisions,
and retain reachable implementations. Include them in the eventual frontend
replacement instead of leaving them out of the roadmap.

#### Feasibility spike: findings

`dev/frontend-spike/` holds the feasibility spike for this item. It is not
part of the compiler and is replaced by the real elaborator package when that
lands. `elaborate/` is an elaborator written in Tersus (1,152 lines in five
files, 73 functions) for a slice of the language: Int, Bool, functions,
structs without parameters, `if`, `while`, blocks, calls, contracts and
`forall`, with single-file semantics (a struct is declared before its use;
package modules predeclare theirs, which the slice does not model). It reads
a program's `tersus-ast 1 parsed` data and writes the `tersus-ast 1
elaborated` data `TypeCheck.elaborateWith` would, or refuses. Anything
outside the slice, including a builtin used by name and a function named like
one, is refused as "not modelled". The `frontend-spike` executable builds it,
validates it, and compares it with the Haskell elaborator. Measured on master
`3cc441a`, on one shared 96-CPU devserver:

- **Agreement.** On every program measured, the two agree. 40 accepted
  programs give byte-identical data, which `readElaborated` and
  `MirLower.lowerModuleWith` accept: 8 from `examples/`, 26 from
  `examples/rejected/` (refused later, by the validator) and 6 from
  `dev/frontend-spike/corpus/`. So do 4 generated programs of 10 to 800
  functions (`synth.py`). 21 programs are refused by both with the same
  message: 20 in the corpus and `rejected/struct_field_type.tersus`. The other
  94 example programs are outside the slice (lists, strings, enums, traits,
  generics, builtins), and `rejected/for_assigns_counter.tersus` does not parse.
- **The data contract.** For the slice, elaboration changes nothing in the
  statement tree except `shrinks e` (to `Counting` or `Parts`, a record of the
  same shape). The elaborated data is the parsed records unchanged, then the
  occurrence types, last first, then the root. Elaboration that inserts
  calls (unsizing, clones, trait methods) changes the tree, so the real
  elaborator has to write a fresh arena in the writer's order.
- **Native time.** Medians of 7 runs, against the Haskell elaborator built
  with `-O1` elaborating and writing the data in-process. "Through the host"
  pipes the request in and reads the reply back as a Haskell `String`, as a
  host adapter would; "alone" reads the request from a file and discards the
  reply.

  | Program | Haskell | Tersus through the host | Tersus alone |
  |---|---|---|---|
  | 40 small programs, in total | 25-26 ms | 46 ms | 34 ms |
  | 10 functions | 22 ms | 9-10 ms | 7 ms |
  | 50 functions | 124-128 ms | 49-56 ms | 32-33 ms |
  | 200 functions | 618-634 ms | 195-230 ms | 130 ms |
  | 800 functions | 2.64 s | 0.81-0.82 s | 0.55-0.57 s |

  For a small program, starting the process (0.85 ms with empty input) is
  nearly all of the cost, so one run is about 1.8 times Haskell's; one
  elaborator process per package rather than per module spreads that cost.
  From 50 functions up the spike takes 0.3 to 0.45 of Haskell's time through
  the host and 0.2 to 0.26 alone; reading the reply back as a `String` is most
  of the difference.
- **Proof cost.** The production validator proves the spike with no
  `assume`, axiom or fuel-bounded recursion: 30 s with no verdicts in the
  cache (`validate --cold`), for 198 functions including the library code the
  spike instantiates (`HashMap<String, Int>`, `HashMap<Int, Int>`, lists of
  structs). The validator checks one function at a time. 35 of the 73
  functions are declared `~`, like the AST writer and the ownership passes:
  they walk the tree recursively. For comparison, on the same host
  `tersus-exe check lib/mir/mir_verify/mir_verify.tersus` (1,827 lines) was
  still validating after an hour, and the AST reader's 535-line `nodeAt` alone
  is known to take over two hours. The cost follows the size and branching of
  a function more than the length of the program: the spike keeps every
  function small, threads one state struct by value
  (`St { ty: t, ..st }`) instead of `&mut` fields, and guards every index.
  A full elaborator written the same way should stay within the budget, but
  one large dispatch function could cost hours, as `nodeAt` shows.
- **Seed shape.** The spike's LLVM IR, emitted twice, is byte-identical
  (2.4 MB, SHA-256 `096baa55...`), and an executable built from that IR alone
  gives the same results. The F0/F1 self-elaboration fixpoint has to wait
  until the elaborator covers its own source (lists, strings, maps, imports),
  which is after the core and trait work.

So elaboration in Tersus is feasible on all four counts: identical data, less
time than Haskell once a process is started, a proof without assumptions in
seconds, and seed IR that is emitted reproducibly. Things found on the way:
a list literal holds only constants, so a list of strings is built with
`push`; `rewrite` is a keyword; and when a package file fails to parse,
`Modules.parseModuleFiles` reports the error the file gives without its
package's declarations ("a string literal needs the library String"), which
can hide the real error.

Reproduce from `tersus/`, with the seeds available:

```sh
stack run frontend-spike -- build /tmp/elaborate
stack run frontend-spike -- compare --runs 7 /tmp/elaborate examples/*.tersus examples/rejected/*.tersus dev/frontend-spike/corpus/*.tersus
python3 dev/frontend-spike/synth.py /tmp/synth
stack run frontend-spike -- compare --runs 7 /tmp/elaborate /tmp/synth/*.tersus
stack run frontend-spike -- validate --cold
```

### Deferred or coordinated work

Draft [PR #157](https://github.com/weirdev/tersus/pull/157) changes collection
proof frames and overlaps moves, ownership and late list lowering. It remains
open at this survey. Do not adopt its unlanded invariants or change its branch.
Leave `MirLists`, `MirMoves` and `MirLower` replacements until that design settles;
check fresh master before implementing each.

`SelfHostedMir` is large but still tracks active validator changes. Preserve it
until a Tersus frontend can supply the validator's complete input. Retire
`MirEval` rather than port it: it is the reference executor and cold-bootstrap
runner until native replacements can build themselves without it.

## Final host and test replacement

A Tersus entry point must load files and packages, run the compiler stages,
invoke clang and manage bootstrap/cache failures. Primitive OS/runtime symbols
stay outside the language where required; `LlvmRuntime`'s remaining C surface is
a separate runtime task, not an ownership rewrite.

Port test groups alongside their replacements. Until the host is replaced,
keep the Haskell harness and independent native/heap-model checks. Done means:
no `.hs` files remain, the compiler builds itself from pinned seeds without GHC,
and the complete ported test suite passes. Check that state by enumerating the
repository, not by assuming a deleted module implies its callers are gone.
