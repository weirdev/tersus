# Replacing all Haskell with a fully Tersus native implementation

The aim: the compiler is a Tersus program compiled to native code, and no
Haskell remains in the repository. Step 31 (`STEP31.md`) did the first part:
the lowering from the MIR to LLVM IR is `examples/mir/emit/emit.tersus`, built from
the seed `bootstrap/emitter.ll` in two stages, and `LlvmEmit` is deleted.
This is the plan for the rest, in the order to do it. Each target names the
Haskell it deletes, why it comes where it does, and what blocks it.

## Where things stand (measured 2026-10-30, at `751dcc9`)

The Haskell package `tersus/` is 61 `.hs` files, about 24,900 lines:

| Part | Lines | Modules |
|---|---|---|
| Frontend | 4,454 | `Parse` (1,377), `TypeCheck` (2,241), `StdLib` (839) |
| Proof and validation | 3,997 | `ProofEngine` (1,363), `MirValidate` (812), `Ghost` (642), `MirVerify` (438), `MirGhost` (245), `ProofState`, `ProofHelpers`, `Linear` |
| MIR and its passes | 4,116 | `Mir` (626), `MirLower` (867), `MirOwnership` (501), `MirData` (469), `MirLists` (450), `MirMoves` (426), `MirMono` (213), `MirEval` (572) |
| Core types and utilities | 1,084 | `TersusTypes` (713), `Pretty` (209), `PreludeSource` (78), `Utils` (71), `Hash` (17) |
| Self-hosted bridges | 977 | `SelfHostedMir` (782), `SelfHostedProof` (196) |
| Native and bootstrap glue | 793 | `LlvmRuntime` (605), `Bootstrap` (134), `Native` (57) |
| Pipeline and CLI | 371 | `Pipeline` (181), `Cli` (192), plus `app/Main.hs` (56) |
| Tests | 8,399 | 25 files under `test/`, plus `dev/parity/Parity.hs` (101) |

Already in Tersus: the emitter (`examples/mir/emit/emit.tersus`, 3,698 lines), a
reader and writer of the MIR as data (`examples/mir/mir_reader/mir_reader.tersus`) and a
checker of it (`examples/mir/mir_verify/mir_verify.tersus`), the
libraries every program gets (`lib/prelude.tersus`, `lib/lists.tersus`,
`lib/box.tersus`, `lib/string.tersus`), and a validator that is not yet the
production one (`lib/validation.tersus`, 2,884 lines). The superseded
Python prototype and the `stack/tersus/` starter snapshot are deleted
(the second in PR #95), so everything below is the real remainder.

Dependencies are boot libraries only (`base`, `containers`, `directory`,
`filepath`, `parsec`, `process`, `template-haskell`), which is what makes
replacing the Haskell thinkable at all: nothing here needs a Haskell
library that Tersus would have to grow first.

## The targets, in order

### 1. Make the Tersus validator the production validator (deletes ~4,000 lines)

`ProofEngine`, `Ghost`, `MirValidate`, `MirVerify`, `MirGhost`,
`ProofState`, `ProofHelpers` and `Linear` go, replaced by
`lib/validation.tersus`. This comes first because it is the only target
whose Tersus implementation is already substantially written, and because
it deletes the largest single chunk.

What exists: `SelfHostedProof` interns Haskell proof terms and answers
supported relation and `Within` queries from a Tersus proof context;
`SelfHostedMir` translates a subset of typed MIR (copies, boxing, plain
structs, pure binary operations, list and array literals and operations,
assertions, jumps and branches, loops by their declared invariant,
direct calls with simple contracts) for the Tersus checker;
`dev/parity` runs the two validators against each other. Both bridges
return `Nothing` on anything unsupported, and unsupported facts are
omitted, so a bridge can never invent a proof. `Pipeline.compileSource`
still calls the Haskell `validateProgram`; the bridges are for
comparison only. Their source-container view excludes the standard List/Box
address/block layout declarations and invariants; those belong to the native
container-library validator, not to the logical list and Box proof model.
User declarations and invariants remain subject to the bridge's capability
checks. Qualified Box storage selectors remain distinct from payload fields
in the proof bridge.

What blocks the flip, in the bridges' own terms: enums; `extern fn`;
`Addr*`/`Block*` operations, `TBlock` and `TWord`; loop invariants the
Haskell validator infers (such as a counter against the size of the list
it pushes to) rather than reads from the source; and joining states at a
merge instead of walking each path through the join separately.

Gate: `Pipeline` may call the Tersus validator when `dev/parity` and the
differential checks in `TestPipeline` agree on every example and every
test program, with the Haskell validator kept for one release as the
oracle behind a flag. Then the Haskell proof modules and both bridges
are deleted together (the bridges exist only to feed a Haskell host).

Status (2026-10-31, PR #94): the flip is made. `Pipeline` validates only
through `lib/validation.tersus`, fed by `SelfHostedMir`; the Haskell
validator, `SelfHostedProof` and `dev/parity` are deleted, and a program
the bridge does not model is refused, never passed.

Since then the three things master had gained have been modeled. For
equality, a relation used as a value is the comparison application
itself, a struct local is its constructor applied to its fields, a
branch derives the relation from any comparison term equal to the
branched one, and two relation applications are one boolean when their
arguments match, both fail, or each gives the other. References are the
version of their place: the bridge finds each reference local's borrow
statically, gives a written root a new term (a construction with one
field replaced, or a `set`), rebinds the borrows of a root after it
changes, and gives update parameters fresh post-call terms with `old()`
read from an entry snapshot; returned references are the argument's
place. `testBorrow` passes outright.

A `forall` over list elements is no longer assumed only for one fresh
index. The bridge records it as one fact the checker instantiates:
two lists elementwise equal (function -30, the offset on either side),
elements different from a value (-31), elements equal to a value (-32),
and elements shifted from another list's (-33). The checker
instantiates a fact inside its range and at its end point, by a case
split on the index, reading through a push where the list was built by
one, and it proves a `get` of a list of known size from its elements.
With that, the list and string `Eq` impls prove, and `String::concat`,
`String::slice` and `String::find` check.

Generic code is checked as the copies a call decides: the bridge is
given the monomorphised program (`MirMono`'s copies with their
contracts kept), with the templates beside the copies as the sources
of contracts that name a function nothing calls. A call written in a
proof carries its contract with it (the callee's requires are an
obligation wherever the clause is used, its ensures are assumed of
the application's term), and a function declared `~` may not be
called in a proof at all. The function that checks an impl against
its trait is checked as written, or a weaker impl would pass. With
that, `HashMap` and `HashSet` check: their tests pass, including the
spread past four entries. The checker's arithmetic no longer traps
the compiled validator on values like the least integer: a linear
combination whose bound is not representable is dropped rather than
computed, and a size is known never negative. The validator's own
self-check (`testMir` on `lib/validation.tersus`) has not finished in
this environment; it is still unverified.

The validator itself uses `HashMap` and `HashSet`, so every validation
runs those libraries interpreted. Since the rebase the solver has been
sped up without changing its verdicts (equality and difference
searches work on class representatives, one context analysis serves
every goal asked of a context at a branch, and the interpreter skips
its reference bookkeeping at calls when the program makes no
reference), and a joined term keeps the bounds both branches give it,
including one that follows from a branch value (`0 <= 0 - n` from
`n < 0`), which the `String::fromInt` shape needs.

The validator no longer runs interpreted in production: it is compiled
to native code once (with `lib/validation_driver.tersus` as its main
program, which reads the bridge's encoded functions from standard
input) and kept in the cache directory under a name made of the
sources it is made of (`ValidatorNative`); `Pipeline` runs that
program for every validation. It is compiled without being validated,
as a bootstrap program is, and the interpreted validator remains only
where the validator is itself the program under test
(`TestPipeline`'s checks of `lib/validation.tersus`).

Concrete evaluation is in the validator: a term whose parts are all
known is recorded as the constant it evaluates to (arithmetic,
`size` and `get` of literal, pushed and made lists), as the Haskell
engine's constant values did, and loop invariants are inferred from
what the entry state proves, in the families the reference infers.

Addresses, permissions and uninitialised slots are modeled in the
bridge: each `Addr`, `Block` and `Uninit` operation is an application
with the contract `StdLib` gives it (what it needs is checked, what it
promises is assumed), a write or an emptied slot is a `set` on the
block's ghost arrays, whose size is the block's capacity, and an
operation that makes a new address or permission is tagged so two are
never one term. A `forall` that cannot be stated as one of the
checker's range facts is checked but not assumed, and what a checked
`forall` assumed of its index is forgotten after it: assuming the
guards of an instance that cannot exist made every later goal pass.
An `extern fn` is assumed at its calls to keep its contract, the
narrowing conversions give a value in their type's range, and a loop
test of several parts joined by `&&` (a call among them) or `||` is
checked as written; after `||` the body knows only what every test
gives, as LANGUAGE.md says. The solver canonicalises terms before
linear arithmetic and splits a get of a written list on the written
index. With that the pointer and connective tests pass.

`String::fromInt` is still too slow to check: the literal it returns
for the least integer puts twenty element facts in the entry context of
the whole function, and every goal at its loops works over them. Every
program that mentions `String` checks the whole library, so this blocks
the string tests and the string cases of `TestEq`. Ordering the
integer constants as a chain instead of pair by pair removes most of
the cost of a long literal, but it changes one verdict of
`testInferredInvariants` and is not in yet.

Open soundness bug, older than the pointer work: a `for` loop whose
body sets an element of a literal list, in a function that requires
its bound to be positive, leaves a contradictory context after the
loop (`affirm 1 = 2` validates after `for i in 0..n { out = set(out,
0, 7); }` with `affirm n > 0` required); the same loop written with
`while` is refused as it should be. `testInferredInvariants` 18 fails
from it, and 16 fails to prove a get through a pushing loop.

### 2. Write the standard library as Tersus text (deletes `StdLib`, 839 lines)

`StdLib.hs` defines the builtins in Haskell; its own TODO says to write
the standard library as text to be parsed. `lib/*.tersus` and
`PreludeSource` already prove the pattern of embedding Tersus source and
parsing it in front of a program. Doing this early removes builtin
definitions that the Tersus parser (target 6) would otherwise meet as
special cases, and shrinks the surface the proof bridges must intern.

Blocked by: builtins that read the world (`readByte`, the file and
argument readers) have no proof representation yet; the Tersus proof
context skips them (`SelfHostedProof` declines a goal that mentions
one). Those stay as named primitives the validator knows by contract,
as today.

### 3. MIR housekeeping in Tersus (deleted `MirVerify` 438, `MirGhost` 245; `MirData` stays until target 6)

The MIR-as-data format is already defined twice in Tersus (the reader in
`examples/mir/emit/emit.tersus` and `examples/mir/mir_reader/mir_reader.tersus`), and
`TestMirData`, `TestMirReader` and `TestMirEmit` are ready-made oracles:
a Tersus writer of the format must round-trip every example, and a
Tersus well-formedness check must accept and refuse the same programs
as `MirVerify`. Erasing ghosts (`MirGhost`) is a small pass over the
same types. Mostly transcription; do it while the format is fresh from
target 1's bridge work.

Status (2026-10-31): done. The writer and the reader were already
Tersus; the check is `examples/mir/mir_verify/mir_verify.tersus` and the erasure is
`examples/mir/mir_erase/mir_erase.tersus`. For the erasure the data gained a
version 2 (`MirData.writeProgramWithGhosts`, printed by `tersus mir
--ghost-data` from a validated program before its ghosts are
erased): the only records it adds are `ghost` and `dissolve L`, with
the types `block` and `uninit` that version 1 already wrote, since a
ghost statement's contents and a function's specification do not
survive erasure and are not written. The eraser takes the permissions
out, makes each `Uninit<T>` a `T`, refuses the `Block::cast`s whose
slots do not lay out alike, and writes version 1.

The host has moved: `MirHousekeeping` runs the two Tersus programs on
the MIR as data (cached native executables built from the seed, as
the emitter is built, with the MIR executor as fallback) wherever the
pipeline checked or erased a program, and `MirVerify.hs` and
`MirGhost.hs` are deleted. The bridge keeps the Haskell signatures
and verdicts, and puts back the parts of a program the data form
does not carry (function specifications, generics, invariants and
ghost statements). `TestMirVerify` and `TestMirErase` now compare the
Tersus programs against the bridge. `MirData`'s reader and writer
stay until the data form itself goes (target 6).

### 4. The MIR passes in Tersus (deletes `MirLower` 867, `MirOwnership` 501, `MirLists` 450, `MirMoves` 426, `MirMono` 213, and `Mir` 626)

These feed the one part that is already native, the emitter, and every
step can be checked by diffing `tersus mir --data` output against the
Haskell pass it replaces, exactly as the emitter was checked against
`LlvmEmit`. `STEP31.md` already names `MirOwnership` and `MirMono` as
the next to move. The order inside the target follows the pipeline:
`MirLower`, then moves and ownership, then list and Box lowering, then
monomorphization.

Blocked by: the passes take the elaborated AST, which is Haskell data.
Either they wait for target 6, or the elaborated AST gets a
serialization as data, like the MIR's, that both sides read and write.
The second is the better course: it keeps this target independent, and
the serialization is deleted when the frontend lands.

Status (2026-11-01): the bridge is implemented. `AstData` reads and writes
parsed syntax and the complete `Elaborated` wrapper (including ordered
expression-occurrence types); `examples/ast_reader/ast_reader.tersus` defines the
syntax as typed arena payloads and reads/writes the same versioned records.
It reuses the MIR `Type` and `Size`, preserves contracts and builtin
metadata, and includes no solver or Iota state. The bridge is developmental:
the elaborated bridge is developmental; parsed AST data now carries the production native parser output. See `AST_DATA.md`
for its checked APIs, format, explicit type/size limits and corpus tests.

### 5. Retire `MirEval` (572 lines) instead of porting it

`eval` is the reference interpreter that native code is tested against
(`testNative`); a native compiler runs programs itself, so the
interpreter is deleted, not rewritten. It comes late in the list for
one reason: inside the Haskell host it is also the runner
(`runNamedFunction`) that executes the self-hosted validator and the
emitter. It can only go when the host does (target 7). Until then its
test role is irreplaceable, so nothing about it changes.

### 6. The frontend in Tersus (deletes `TypeCheck` 2,241 and `Parse` 1,377, the largest files left)

The aim is still to replace the frontend, but its data bridge is now in
place: `examples/ast_reader/ast_reader.tersus` defines the syntax of `Syntax` and the
needed `Types` values as Tersus structs/enums, and exchanges parsed or
elaborated syntax with `AstData` (`AST_DATA.md`). It is not a source parser
or type checker.

The parser was a set of Parsec combinators and is now a hand-written Tersus
reader over bytes that produces the AST as data. The remaining frontend work
is elaboration over that AST. Error messages are part of the target: tests
name the stage that refused a program and often its reason, so a Tersus checker
must preserve those verdicts or change them deliberately with the tests.

Status (2026-11-03): the parser grammar is native-only. `Parse.hs` and the
`TERSUS_PARSER=haskell` oracle are deleted. `TersusParser` supplies P1 ASTs to
production source and package entry points; `ParsedFile` holds the shared data
records, and `Syntax` owns `Elaborated`. The elaborator remains Haskell.

A pinned parser LLVM seed provides P0 below the compiler. It verifies
`bootstrap/parser.sha256`, links the existing runtime and builds with clang.
P0 reads the standard library, sequential implicit-library contexts, current
prepared parser source and embedded MIR package. The unchanged checker and
lowering produce owned MIR; the existing emitter seed builds E1, which emits
P1. `Compile` and the default `Modules` loaders are explicit P0 bootstrap
consumers, so producing P1 never enters a P1 cache lock recursively.
`SourceParse` shares the lazy library AST/declaration cache, source probe and
selection with production. `Compile.lowerSourceParts` retains the
library/source split and prepared-prefix cache.

The first language parse now requires clang and verified native P0 even for
`TERSUS_PARSER=interpreted`. Haskell package compilation remains clang- and
network-free. Failed seed verification, native builds, processes or protocols
are explicit tool errors, with no alternate grammar.

`testParser` compares P0/P1 over the full source/rejection corpus and generated
cases. File state, imports, all ten declaration fields, shadowing and refusal
state remain covered; the language tests keep independent literal ASTs and
verdicts through native fragment helpers. Current GHC predicates are generated
into P1 and tested at their Unicode boundaries. P0 keeps its asset's baked
classifier version, so Unicode-version-sensitive identifier tests target P1;
the ASCII bootstrap corpus must still be accepted by P0.

The parser fixpoint uses the same prepared current source in P0 and P1. Its
ASTs, final declarations, checked/lowered MIR and E1-emitted IR must agree,
with P2 behavior checked too. Historical seed LLVM need not equal current LLVM.
Cold-process, concurrent-process, cache-reuse and corrupt/missing-seed controls
cover the bootstrap. `AST_DATA.md` documents provenance and seed regeneration.

### 7. The host glue, and a bootstrap with no GHC (deletes `Cli`, `Pipeline`, `Bootstrap`, `PreludeSource`, `LlvmRuntime`, `Native`, `Hash`, `Utils`, `Pretty`, `app/Main.hs`; ~1,600 lines)

The endgame: a Tersus `main` that reads files and arguments (the
language already has both, step 20 of the roadmap), runs the pipeline
of targets 1-6, writes the MIR as data to its own emitter, and invokes
clang. `LlvmRuntime`'s C becomes a standalone runtime file shipped with
the compiler (or finishes moving into Tersus per step 30); the
Template-Haskell embedding in `PreludeSource` is replaced by reading
the library files at run time; `Bootstrap`'s stage 0/stage 1 caching
becomes a build script. Done means: the emitter fixpoint
(stage 1 writes the same IR for the emitter as stage 0) holds, and
`grep` for GHC in the build finds nothing.

### 8. The tests, alongside (deletes `test/`, 8,399 lines, and `dev/parity`)

Not product code, but no target above can be deleted safely while the
only tests are Haskell: the Haskell modules a target deletes are the
ones its tests import. Port each test group to a Tersus or script
runner as its subsystem flips (`TestPipeline` with target 1,
`TestMir*` with targets 3-4, the frontend groups with target 6), and
keep the Haskell harness running the unported groups until target 7.
`TestNative`-style checks (build with clang, run, compare with the
reference) need target 7's process surface, so they port last; until
then `eval` (target 5) is their oracle.

## What "done" is

- `find . -name '*.hs'` in the repository finds nothing.
- The compiler that builds the compiler is the stage-1 emitter and the
  Tersus pipeline of targets 1-7, from the seed in
  `bootstrap/emitter.ll`.
- The full test suite, ported, passes with no GHC installed.
