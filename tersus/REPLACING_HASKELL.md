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
  gives the same results. The F0/F1 self-elaboration fixpoint had to wait
  until the elaborator covered its own source; it holds now ("The frontend
  seed" below).

So elaboration in Tersus is feasible on all four counts: identical data, less
time than Haskell once a process is started, a proof without assumptions in
seconds, and seed IR that is emitted reproducibly. Things found on the way:
a list literal holds only constants, so a list of strings is built with
`push`; `rewrite` is a keyword; and when a package file fails to parse,
`Modules.parseModuleFiles` reports the error the file gives without its
package's declarations ("a string literal needs the library String"), which
can hide the real error.

Reproduced from `tersus/` at the spike's commit (the flip removed `dev/frontend-spike`):

```sh
stack run frontend-spike -- build /tmp/elaborate
stack run frontend-spike -- compare --runs 7 /tmp/elaborate examples/*.tersus examples/rejected/*.tersus dev/frontend-spike/corpus/*.tersus
python3 dev/frontend-spike/synth.py /tmp/synth
stack run frontend-spike -- compare --runs 7 /tmp/elaborate /tmp/synth/*.tersus
stack run frontend-spike -- validate --cold
```

#### Data contracts and the differential harness

Built: what an elaborator written in Tersus needs from the host and gives back
is data (`AST_DATA.md`). A module interface is `tersus-ast 1 interface`
(`InterfaceData`, read in Tersus by `data::reader`), the builtins the checker
knows are the table `lib/data/builtins.ast` (`BuiltinTable`, made from
`BuiltinRegistry` and checked against it), and an elaboration is a
`tersus-elaborate 1` request answered by a `tersus-elaborated 1` response
(`ElaborateRequest`). Until the flip the compiler elaborated every program and
module through that request in process, with the Haskell `respond`, and
`test/Differential.hs` recorded the requests it made over the corpus and
compared another elaborator's responses with `respond`'s: agreement, a refusal
in other words, disagreement, not modelled (`testDifferential`; the
`frontend-diff` tool for an executable). A test holds the lowering to taking exactly the expression types the
elaboration gives (one more or one fewer is refused), and a test that expects a refusal in the checker's words
no longer passes when the validator refuses instead (`TestHarness`).

The checker accepts two top-level functions of one name and a function named
like a builtin (duplicate definitions were left to the validator,
`e35b571`); the validator written in Tersus refuses both as something it does
not model yet ("two functions with one name", "a function named like a
builtin"), and the tests say so. An elaborator written in Tersus has to accept
them too, or the differential reports a disagreement, until they become the
checker's errors.

#### Elaborator core

Built: `lib/elaborate/` is the elaborator written in Tersus, a port of
`TypeCheck`/`TypeCheckCore` function by function, so that it numbers fresh
type variables and words refusals as the Haskell checker does. It reads a
`tersus-elaborate 1` request (which carries the builtin table, so the
elaborator types builtins from data) and writes the `tersus-elaborated 1`
response. Types live in an arena of the checker's state; the output is the
request's parsed arena with the new records appended, renumbered into the order
`AstData` writes (`data::arena`, which the parser writes through too).

It covers the whole checker: types and their instances, finiteness,
unification and coercion, statements, functions and gathered signatures,
generic calls, termination, contracts and proof terms, the builtins of
addresses and permissions, references (places, borrows, `writes(...)`
footprints, `from` origins and aliases), `clone` and the Copy and Clone
markers, traits and impls (method resolution, `Type::f`, `Trait::f(x)`, `Eq`
behind `=`, Deref look-through and the functions that check an impl against
its trait), functions with bounds (made for each list of types a call gives
them, placed before the statement that called them; one another package's
module defines is checked in what that module sees, its defining context, and
the sizes its bounds name are in the instance's name and body), and the modules of
packages and of the compiler libraries: a module predeclares its own types,
a library module sees a generic constructor's owner as a type, and the
elaborator gives back the interface the module exposes
(as the Haskell `Interface.extractInterface` and `extractLibInterface` did). It answers
`unmodelled` only for data it cannot read and for a builtin whose type only
the program's declarations give, which no request carries. Until the flip, `testElaborate` built the
elaborator from the embedded sources (`PreludeSource.elaboratePackageFiles`)
and ran the differential over every single-file corpus program and every
`testTypeCheck` source (with the clone, equality and list libraries in front
of it), the example package, the compiler libraries and four small packages
that try the edges of predeclaration and interfaces: every request agreed,
interfaces included, and `frontend-diff compare` covered the compiler's own
packages. `testElaborateMutant`, run only when named, checks that a mutant whose
unification lets Int and Bool stand for each other is caught. The
differential runs the elaborator with the largest stack the system allows,
as the validator is run: it recurses over the nesting of expressions.

The elaborator is validated (`testHostValidation`) by the unmodified
validator, with no `assume`, axiom or fuel: all 1,026 functions of its
program, with the libraries it links, validate (`tersus-exe check
lib/elaborate/elaborate.tersus`). The host validates one function at a time,
so a check with no verdicts cached takes hours, as for the AST reader. The
elaborator's own functions are `~`: they walk the program recursively, as
the AST writer and the ownership passes do, and a function that terminates
cannot call one that may not. What the validator needs, the code gives
locally: a list is read through `nth`, `firstText` and the like, which answer
-1 or nothing where the data has no such element; a record is cast only after
its variant is checked; and a search loop carries `i <= size` for the slice
that follows it. The validator's cost follows the size and branching of a
function, so the dispatchers are split: `data::reader` reads a record with
the reader of a group of at most five tags (found by its tag's number in a
table made once per block), `data::arena` renumbers through groups of node
kinds, and the elaborator's large functions (`checkStatement`,
`extractInterface`, `checkImpl`, `templateCall` and others) are made of
smaller ones.

Cost: the compiler elaborating and lowering a unit with the elaborator
written in Tersus (`frontend-diff pipeline`, one CPU, best of three) took
1.15 times as long as it does on master with the Haskell elaborator, over the
six compiler packages together (119.5 s against 103.7 s; 1.03 to 1.33 times
for each), and 0.05 to 0.37 s longer for a small program, whose whole build
(`tersus-exe build`, validation and native code included) takes 3.6 to 108 s. The elaborator's state is one struct, and what the compiler does
with it decides most of the cost:
- A state built as `St { f: e, ..st }`, where `e` reads `st`, copies every
  other field of the state before `e` runs; such an `e` is computed into a
  local first.
- A method called on a field of the state, `st.ctors.lookup(k, noCtor())`,
  copies the field (the whole map) when an argument needs a call to compute;
  the elaborator calls `HashMap::lookup(&st.ctors, k, noCtor())` instead.
- `zonk` of a type that is already resolved, and `withTy` of the type the
  state already has, leave the state as it is.

A request carries an interface for the module and again in the defining
context of every module that depends on it; the host writes each interface
once, and the elaborator parses a block whose records it has already read
once (it keeps the blocks it has read by their text) and reads a defining
context's interface where the module's own copy of it already is, so that a
template the module imported is the one its defining context owns.

`holdsGhost` and `holdsRef` keep what they found for a named type until a
type, a linear type or a drop is declared. On the host's side, the request
and the response are put together and read as lines rather than as one text
split again, the writer reads back only the type and size records it wrote,
and numbers are read digit by digit rather than with `reads` (which also took
forms such as `0x1F` and `(5)` that no writer of the data writes).

#### The frontend seed

Built: the elaborator written in Tersus bootstraps from a pinned seed, as the
emitter and the parser do. F0 is the elaborator built with clang from seed IR
(`bootstrap/frontend.sha256`, the `frontend.ll` asset of release
`bootstrap-25421a0b113f`; `TERSUS_FRONTEND_SEED_FILE` or an ignored
`bootstrap/frontend.ll` supplies local bytes, verified against the same pin).
F1 is the elaborator as it is now, its modules and the compiler libraries
elaborated by F0 and the rest of the build done by the host as for its other
programs (`ElaboratorNative.frontendStage`); F2 is the same elaborated by F1.
A stage is kept in the cache under the program its executable is made of, with
the IR it was built from, so the fixpoint is F2 being F1.

`testFrontendBootstrap` checks that the pin records the elaborator's sources as
they are, that F1 (and F2, when it is another executable) answers every request
of the elaborator's own build and of the compiler libraries as F0 does, that F2
is F1, that the host's programs (the emitter, the MIR checker and eraser, the
parser, the AST reader and the validator) elaborated by F1 are the ones F0
gives, that a missing or corrupt seed is refused and an elaborator that fails
refuses the module, and that the seed and the stages are kept. CI runs it on a
runner of its own. `stack run frontend-seed -- emit` makes the same fixpoint
check and writes F1's IR.

#### The flip

Built: the compiler type-checks with the elaborator written in Tersus, and
`TypeCheck`, `TypeCheckCore` and the checker half of `Interface` are gone. The
data the rest of the compiler reads (templates, import environments) is in
`Elaboration`. Building F1 takes several minutes (owning its MIR is most of
it), longer than master's whole cold bootstrap, so the compiler runs F0 while
the pin's second word, a fingerprint of what the seed was made from (the
`lib/elaborate` and `lib/data` files, the builtin table and the protocol
headers), matches the sources (`ElaboratorTool.sourceElaborator`), and builds
F1 only when it does not; `testFrontendBootstrap` fails on a mismatch, so a
change to the elaborator comes with a new seed. The compiler's own code (its
tools, the compiler libraries, the List and Box helper units and the stages)
is always elaborated by F0 (`bootstrapElaborator`), as P0 reads the compiler's
own sources. A failure of the elaborator executable refuses the module. Before
the switch, the elaborator was brought up to the Haskell checker on imported
templates: one is checked in a state seeded from its provider's interfaces, the
sizes its bounds name are part of the instance, and a caller's impl meets its
bounds in the context that defines it. The differential agreed on every
request of the corpus, the examples and the probes, and the `testPhase2Packages`
packages (168, 180 and 90 requests) on its last run.

Cost, against master on the same host: the full suite takes 1.15 times as long
(1,053 s against 917 s of wall time on seven shards; 1.11 times the summed group
time), most of it in the package tests, whose compiles now start an elaborator
process for each module. From an empty cache, `tersus-exe run
examples/basics.tersus` takes 1.10 times as long (257 s against 235 s, the mean
of three alternating pairs on eight pinned CPUs, 1.06 to 1.12 times each): F0's
build is the largest of the three seeds, so the first parse builds it beside the
parser and emitter seeds, before the parse runs.

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
