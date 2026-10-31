# Replacing all Haskell with a fully Tersus native implementation

The aim: the compiler is a Tersus program compiled to native code, and no
Haskell remains in the repository. Step 31 (`STEP31.md`) did the first part:
the lowering from the MIR to LLVM IR is `examples/emit.tersus`, built from
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

Already in Tersus: the emitter (`examples/emit.tersus`, 3,698 lines), a
reader and writer of the MIR as data (`examples/mir_reader.tersus`) and a
checker of it (`examples/mir_verify.tersus`), the
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
comparison only.

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
the bridge does not model is refused, never passed. The bridge still
refuses three things master gained after the branch started, so the
corpus that uses them fails with "does not model yet" until they are
modeled. The plan for each, in the order to do them:

1. Equality as the trait `Eq` (`lib/eq.tersus`). `=` on anything but a
   word is now a call of an `eq` impl, which the bridge already models
   as a call with a contract (`return = (self = other)`). What is
   missing is proving the impls: the old engine's equality by parts
   (a disequality by refuting the equality, two lists equal by their
   sizes and a `forall` over their elements, two constructions equal
   by their fields, and `c = (a rel b)` from the relation), and the
   facts it added at branches and locals (a struct is its constructor
   applied to its fields; a value that tested as none of the other
   variants is the last one). These are entailment rules in
   `validation.tersus` plus constructed-value facts the bridge emits
   from the types it already reads.
2. References (REFERENCES.md, stages 1 to 5). A reference is the
   version of its place, as in the old validator, so no new proof
   terms are needed, only bookkeeping in the bridge: `&place` binds the
   reference local to the place's term (a field read or a `get`, with
   the index bound checked as `get` checks it); `*r` is a copy;
   `AssignRef root steps v` gives the root a new term (the whole value,
   a construction with one field replaced, or a `set`, so the invariant
   and the bound are checked as a construction and a `set` are); after
   any new version of a root, the reference locals borrowing it are
   rebound. The borrow of each reference local is found statically
   per function and the function is refused when two borrows of one
   local disagree. A call with update parameters gets a fresh term per
   updated argument, the callee's promise read with the parameter as
   that term and `old(p)` as the argument's term, and the root rebound;
   the callee is checked with `old(p)` as the entry term. Loops treat
   the roots that `AssignRef` and update calls write as assigned.
   Returned references (`from`) and holders follow from the same
   rebinding once the callee's `from` list says which argument's place
   the result is.
3. `Hash`, `HashMap` and `HashSet` (`lib/prelude.tersus`,
   `lib/map.tersus`, `lib/set.tersus`). Nothing new reaches the MIR:
   bounded impls are templates the checker instantiates. What the
   libraries need from the validator is arithmetic it does not have
   yet: `x % n` for a positive `n` in `0..n` (and the identity
   `x = n * (x / n) + x % n` that `hashCombine` rests on), and the
   list-of-lists frame facts of `bucketPut`. These go in with the
   division-family linear arithmetic gap that already fails several
   test cases.

The validator itself now uses `HashMap` and `HashSet`, so every
validation runs those libraries interpreted, and is several times
slower than it was before the rebase; and its own self-check needs
item 3. Performance comes before the three items, since each test run
is gated on it.

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

### 3. MIR housekeeping in Tersus (deletes `MirData` 469, `MirVerify` 438, `MirGhost` 245)

The MIR-as-data format is already defined twice in Tersus (the reader in
`examples/emit.tersus` and `examples/mir_reader.tersus`), and
`TestMirData`, `TestMirReader` and `TestMirEmit` are ready-made oracles:
a Tersus writer of the format must round-trip every example, and a
Tersus well-formedness check must accept and refuse the same programs
as `MirVerify`. Erasing ghosts (`MirGhost`) is a small pass over the
same types. Mostly transcription; do it while the format is fresh from
target 1's bridge work.

Status (2026-10-31): done, in the sense that every piece of the
housekeeping now has a Tersus program checked against the Haskell it
mirrors. The writer and the reader were already Tersus; the check is
`examples/mir_verify.tersus` (`TestMirVerify` compares its verdict with
`verifyProgram` on every example and test program, and on mutated
programs it must refuse), and the erasure is
`examples/mir_erase.tersus`. For the erasure the data gained a
version 2 (`MirData.writeProgramWithGhosts`, printed by `tersus mir
--ghost-data` from a validated program before its ghosts are
erased): the only records it adds are `ghost` and `dissolve L`, with
the types `block` and `uninit` that version 1 already wrote, since a
ghost statement's contents and a function's specification do not
survive erasure and are not written. The eraser takes the permissions
out, makes each `Uninit<T>` a `T`, refuses the `Block::cast`s whose
slots are not the same size, and writes version 1; `TestMirErase`
compares its output word for word with `withoutUninit (eraseGhosts
p)` on every example and test program, interpreted and natively.
What remains is the host's move, not more Tersus: the pipeline still
runs the Haskell check and erasure, and `MirData` still writes what
the emitter reads. When the host runs the two Tersus programs on the
data instead (as it already runs the emitter), `MirVerify` and
`MirGhost` can be deleted; `MirData`'s reader and writer stay until
the data form itself goes (target 6).

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

### 5. Retire `MirEval` (572 lines) instead of porting it

`eval` is the reference interpreter that native code is tested against
(`testNative`); a native compiler runs programs itself, so the
interpreter is deleted, not rewritten. It comes late in the list for
one reason: inside the Haskell host it is also the runner
(`runNamedFunction`) that executes the self-hosted validator and the
emitter. It can only go when the host does (target 7). Until then its
test role is irreplaceable, so nothing about it changes.

### 6. The frontend in Tersus (deletes `TypeCheck` 2,241 and `Parse` 1,377, the largest files left)

Nothing can be deleted end to end until source text can enter a Tersus
program, so this gates the finish even though it is the hardest part.
Parser first: `Parse` is Parsec combinators, which have no Tersus
analogue, so the Tersus parser is a hand-written reader over bytes in
the manner of `examples/mir_reader.tersus`, producing the AST of
`TersusTypes` re-declared as Tersus structs and enums. Then the
elaborator on that AST. Error-message parity is part of the target:
tests name the stage that refused a program and, for many programs, the
message, so the Tersus checker must refuse the same programs with the
same words, or the tests change deliberately with the messages.

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
