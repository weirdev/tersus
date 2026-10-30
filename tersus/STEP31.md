# Step 31: the lowering from the MIR to LLVM IR written in Tersus

The plan for step 31 of the roadmap in `README.md`. The aim is `LlvmEmit` (`src/LlvmEmit.hs`) written in Tersus, as the first
part of the compiler that compiles itself. The front end (parser, checker, validator, lowering, ownership, monomorphization)
stays in Haskell.

## What gets rewritten

- `LlvmEmit.hs` is 1,282 lines with 95 top-level functions. It runs in a state-plus-error monad (`G`) with about 190 binds,
  and does about 15 map lookups.
- It takes the **owned MIR** (after list lowering, monomorphization and `insertOwnership`), where the ghost statements and the
  contracts are already stripped. The Tersus emitter needs only the types, functions, locals, blocks, statements and
  constants. `MirOwnership` and `MirVerify` stay in Haskell.
- Small helpers to port with it: `renderType` (descriptor symbol names embed it), `slotsOf`, `ownerOf`, `needsDrop`, the
  escaping of names.
- Scale: `examples/hello.tersus` is 742 lines of owned MIR and 1,610 lines (60 KB) of IR, mostly from the string and list
  libraries. The Tersus emitter will be 3 to 4 thousand lines: no monads (the state is threaded by hand) and every index and
  loop needs a contract.

## What was measured, and what is missing from the language

- **Validation time grew with the square of the number of functions (fixed in slice 1).** A program of N functions of about
  15 lines each (a loop with an invariant and a few `is` tests on an enum), `check` on an `-O1` build:

  | functions | before | after |
  |---|---|---|
  | 10 | 0.4 s | 0.4 s |
  | 50 | 3 s | 1.9 s |
  | 200 | 33 s | 8 s |

  The cause was a fact `$f = f` for every function of the program in the global facts of every proof, which each query then
  searched and the cache rebuilt for each function. A function is now known by its iota (`ProofState.fnIota`), and the fact is
  added only for the functions a function names (`Mir.functionsNamed`, `ProofState.withFunctions`). The time is linear in the
  functions now (about 0.04 s for one of this size); what is left is the cost of one proof, which re-interns the standard
  library's facts for every query (`ProofEngine.proofContextFromCache`, `builtinsByClass`), a further gain if one is needed.
- Conditions had no `&&`, `||` or `and` (a probe failed to parse all three): added in slice 3.
- There is no mutual recursion (a function sees only the functions defined before it): the emit functions form a bottom-up
  order.
- There are no generic enums (step 22), so no `Option` or `Result`: the emitter state holds an error flag and a message.
- A map is not needed at first. The serializer can number the types and functions, and locals and blocks are numbered
  already, so a lookup is a list index.
- Done and not a blocker: strings, `Byte`, standard input and output, arguments, files.

## Slices

Each slice is a PR, and nothing changes the default `build` until slice 8 adds a flag (and slice 9 makes it the default).

1. **Validator scaling.** Done: see above. A 3,000-line program validates in about 8 seconds.
2. **The MIR as data.** Done for Haskell: `tersus mir --data` prints a stable line-oriented format (`src/MirData.hs`, described in
   MIR.md), with a reader and writer and a test that `read . print = id` for every example and every `TestNative` program
   (`test/TestMirData.hs`), and `LlvmEmit.emitOwned` gives the same IR for the program read back from the data as for the original, so nothing the emitter needs is left out. `llvm`, `build` and `run` still go straight from the owned MIR to `emitOwned`; the data is only on that path when the emitter in Tersus is (slice 8). The boundary is the owned MIR without the validator's part (ghost statements, contracts, structs with sizes
   and their invariants), in the order of the maps it was in, which is the order the emitter walks.
3. **Gaps found on the way.** Done: the connectives `&&`, `||` and `!` (lazy, lowered to the tests they stand for, so the validator knows the
   left test when it checks the right one; an `||` keeps only what both tests give), and in `lib/string.tersus` `String::fromInt`,
   `slice`, `find` and `startsWith` (equality of strings was there). Found while doing it: after an `||` the validator cannot use "this
   test or that one", which a loop condition with `||` has to live with.
4. **The MIR types and the reader in Tersus.** Done: `examples/mir_reader.tersus` (about 1,200 lines, 69 functions) has the types of the MIR as enums and structs,
   a tokenizer, a parser for each of them and a writer. It reads what `tersus mir --data` prints from the standard input and writes it
   again; `TestMirReader` builds it once and checks that the output is the input for every example, every program of the native tests and
   the reader's own data (22,000 lines, 440 KB), and that the texts that are not the data of a program are refused. It validates in 6 seconds,
   and the executable reads 20 KB (`hello`) in 0.2 s and the 440 KB in 5 s, which is linear but slow for a native program: a token is copied
   by every `get` of the list of tokens and a string literal is built for every word it is compared with, which the emitter should avoid
   (borrow, and compare once). Found while writing it:
   - Recursion over a tree whose children are in a list (`TFn { args: List<Type>, ... }`) cannot be shown to end: `shrinks` knows a field,
     not an element of a list. The writer's functions are `~`; the parsers, which recurse on an index in the line, are not
     (`shrinks size(ts) - pos`). A parser that needs a position in the line and gives one after it is the shape that works: it asks for
     `0 <= pos < size(ts)`, promises `pos < return.pos <= size(ts)`, and a failure is `ok: false` with the position at the end of the line.
   - An empty list `[]` as the argument of a generic function (`failed([], ts)`) is a `List<Int>` natively whatever the result is used for.
     The checker accepts it and the verifier of the native code refuses it (`is ill typed`); a function that returns the empty list
     gives it its type. Documented in LANGUAGE.md, not fixed: the type is not kept in the expression.
   - A list literal cannot hold string literals or structs, so the tables of words are built with `push`.
   - After a join of two branches the validator does not keep a bound on an index that each branch set (`p = t.pos` in one, `p = 3` in the
     other); an `affirm p >= 0;` at the end of each branch keeps it.
   - `match` as a statement can `return` from an arm, and an `if x is A { ... } else { (x as B) }` cannot show the else is `B`, so a
     two-variant enum is taken apart with `match`.
5. **Emitter part 1.** Done: `examples/emit.tersus` (a program is one file, so it has the reader of `mir_reader.tersus` between two marker lines that
   `TestMirEmit` checks are the same text in both) with `renderType`, `slotsOf`, `ownerOf`, `needsDrop`, `canonical`, `llvmType`, `escaped`, `closeTypes`,
   `typeDescriptors`, `declarations` and `entryPoint`, written as the Haskell is. It writes what `LlvmEmit.emitOutline` writes (the declarations, the descriptors
   of the types of the locals and what they contain, and the entry point), and `TestMirEmit` compares the two for every example and every program of the native
   tests, with the Haskell as the oracle. Found while doing it:
   - There is no mutual recursion, so `slotsOf` and `needsDrop`, which the Haskell writes as a function over types and one over declarations, are one function that
     looks the declaration up and calls itself on the types of its fields.
   - A cast is proved by the `is` test just before it in the same function, not by a helper that says it (`isSizedArray(t)` and then `t as Type::TArray` is refused), so the
     tests that guard a cast are made where it is, in helpers that give what was cast (`sizedArray(t)` gives `ok`, the length and the element type).
   - A chain of `concat` costs more than the rest of the program: `concat` promises the size and the bytes of its result, and the facts of ten of them in a function were
     27 of the 48 seconds to validate the emitter. `impl String { fn then }` (a `concat` that promises nothing) brought the program to 16 seconds. The emitter makes text
     from many pieces, so it uses `then`; a `String` method that is added in a program of its own works.
   - Output is a `List<String>` of lines that the caller prints at the end (the descriptors come before the code that decides which are needed), not a string that is
     appended to: a `push` is cheap, and a `concat` of the whole output would copy it every time.
6. **Emitter part 2.** Done: `examples/emit.tersus bodies` writes the code of each function whose locals and statements are words (Int, Byte, Bool, a function):
   operands, constants, `sharedType`, arithmetic with the checks for an overflow (`checked`, `binary` for `/` and `%`), the operations of the runtime that give a number,
   `store`, the terminators (`goto`, `switch`, `call` of a function and of a function value, `return`, with the entry's `%returned`) and `call`. A function that has
   anything else gives `; unsupported` (slice 7 adds it). `LlvmEmit.emitBody` (new, the lines of the blocks of a function with its globals, temps and types; `emitFunction`
   puts the header and prologue around it) is the oracle, and `TestMirEmit` compares the two for every function of every example and native-test program that makes only
   words (`wordOnly`: the test fails if the emitter gives `unsupported` for one, or if fewer than 100 were compared). Found while doing it, all of them about the time it
   takes, since the first version needed more than 200 seconds for the data of `mir_reader.tersus` (22,000 lines):
   - **The runtime walked the type at every drop and copy.** `words` and `needs_drop` in `LlvmRuntime` recomputed from the descriptor each time (65% of the time of a
     program that moves enums around). The descriptor now has `{ kind, aux, words, drops }`, worked out by `LlvmEmit.typeDescriptors` once. All native code gains by
     it: the emitter takes 3.6 seconds for that data and the reader 0.6, from more than 200 and 5.
   - **A field read from a struct that is used again afterwards is a copy**, so the state of the emission is never in a struct with the value (a `Named { g, name }` would copy the
     lines so far for each instruction). A function gives the state and leaves the text of its value in `last`.
   - **`get(functions, i)` copies the function and all its blocks**, so the calls look up the signatures taken once (`Sig`, `Ctx`), and the names of the types and whether each
     owns something are in the `Ctx` too (`declIndex`, `needsDropIn`).
   - **Names that are in two files clash**: the reader's `operandAt` and `isWord` are not available as the names of the emitter's own functions, which are `operandValue` and so on.
7. **Emitter part 3.** Done: `examples/emit.tersus` writes all of the IR, byte-identical to `LlvmEmit.emitOwned` for every example and every `TestNative` program (the
   emitter's own data too: 44,000 lines of MIR, 10 seconds). It has now the values held inline (`assignAggregate`, `constantAggregate`, `writeConstant`, `operandAddress`,
   `dataBase`, the constructors and their offsets), the arrays and lists (`fillElements`, `arrayRead`, `elementAddress`), Boxes, `cloneInto`, `dropSlot`, the calls and
   returns of values held inline, and the function around its blocks (`emitFunction`: the header, the frame, the parameters, `%returned`). `TestMirEmit` runs it with no
   argument against `emitOwned`, and with `outline` and `bodies` against the parts, for all of them, and fails if the emitter does not give the functions that the Haskell
   gives. Found while doing it:
   - **A local variable with the name of a generic function breaks the native build** (`done = n * 2;` in a function, with `fn done<T>` in the program: `Ownership failed: In
     main: bb0 names the function done, which is not there`). The program is accepted by the checker and the validator. The emitter avoids the names (`finish`, `pieces`);
     not fixed.
   - **The constructors are a table**, in the order of `Mir.constructor` (structs first, then the variants of the enums, so the first with a name is what it finds), and so is
     the words of each type, since walking the declarations for each field (and copying them to do it) was most of the time.
   - Mutual recursion is missing again: `operandValue` for a value moved from a local that holds an aggregate calls `operandAddress`, which has to come first, and the order of
     the functions follows what each needs.
8. **Wire-in and bootstrap.** Done: `tersus --tersus-emitter build|llvm|run <file>` had the IR written by `examples/emit.tersus` instead of `LlvmEmit` (the flag came before the
   command, since the arguments after the file of `run` are the program's), with the two stages in `Bootstrap`:
   - **Stage 0** was the emitter built (`stageZero`) from the IR that `LlvmEmit` writes for `emit.tersus`, built the first time (about 35 seconds) and kept in the cache
     directory of the user (`$XDG_CACHE_HOME/tersus`, or `~/.cache/tersus`; with no fallback to a shared directory such as `/tmp`, where another user could plant a program
     under its name, so the flag fails when the directory cannot be made).
   - **Stage 1** was the emitter built (`stageOne`) from the IR that stage 0 writes for the emitter's own MIR.
   `TestBootstrap` was the fixpoint: stage 0 writes for the emitter the IR it was built from, stage 1 writes for the emitter and for every example and native-test program the
   text that `llvmSource` gives (so the IR is the same at both stages, and stage 1 is stage 0 again). Found while doing it:
   - **The cache was not keyed by the Haskell emitter.** If `LlvmEmit` changed the IR, the cached stage 0 was still the emitter built from the old IR.
   - `testBootstrap` is among the longest groups (two builds with clang -O2, and the front end runs on the emitter and on every program; the programs are done in parallel,
     about five minutes unoptimized).
9. **The Tersus emitter is the default.** Done: `build`, `llvm` and `run` use it, and `--haskell-emitter` (before the command) has `LlvmEmit` write the IR, which needs no clang
   to print it. What it needs to stand on its own is a seed in the repository, since the Haskell emitter is no longer what builds it:
   - **`bootstrap/emitter.ll` is the seed**: the IR (8.7 MB of text, 600 KB compressed) that the emitter wrote for its own source. It is embedded in the compiler
     (`PreludeSource.seedSource`; its hash is made when that is compiled). A release binary was the other way, and was not taken: it is for one platform, it cannot be read in a
     diff, and what is run is whatever was uploaded; the IR is portable, can be checked (the fixpoint), and needs only the clang that `build` needs anyway. A release is for
     when the front end is also in Tersus, and the seed would have to be all of the compiler.
   - **The seed does not have to be the latest emitter.** Stage 0 is the seed built; stage 1 is the emitter as it is now, which stage 0 compiles (`stageOne`), and it is stage 1
     that compiles programs, so a change to `emit.tersus` takes effect with no new seed. The seed only has to be able to read the data (`tersus-mir 1`), compile the emitter
     as it is now (the language it is written in), and call the runtime as it is (`LlvmRuntime`). When one of those changes in a way it cannot follow, stage 0 fails or the
     fixpoint test does, and the seed is made again with `tersus llvm examples/emit.tersus > bootstrap/emitter.ll` (from a build that works).
   - **Two programs are in the cache**, `seed-<hash>` and `emitter-<hash>`: the hash of the first is of the seed and the runtime, and that of the second adds the emitter and
     the library every program has. The first `build`, `run` or `llvm` takes about a minute and a half (two builds); the next ones are as fast as before.
   - **`TestBootstrap`** is the fixpoint again: stage 0 and stage 1 write the same IR for the emitter (so the emitter built from either is the same program), and stage 1
     writes the IR of every example and native-test program. It checks the cache keeps both.
   - `llvm` needs clang now (to build the emitter once). Since `LlvmEmit` was deleted (slice 10), the tests go through the emitter in Tersus: `TestNative` builds and
     runs its IR against the executor, which is slower than the Haskell oracle was.
10. **The Tersus emitter is the only emitter.** Done: `LlvmEmit.hs` and the `--haskell-emitter` flag are deleted. The tests stand without the oracle: `TestNative`
    builds and runs the IR of the emitter in Tersus against the MIR executor, `TestMirEmit` runs every mode of it on every example and native-test program and checks
    that the data of a program and of the program read back from it make the same IR, and `TestBootstrap` checks the stage 0/stage 1 fixpoint. The seed
    `bootstrap/emitter.ll` is unchanged: it still compiles the emitter as it is now.

Slices 5 to 7 are the bulk of the work. Slice 1 is the one that may change the plan.

## Decisions

1. **Port style**: a faithful, byte-identical port (same evaluation order and temp numbering), so that the Haskell emitter is
   the oracle. Tidying comes after.
2. **`LlvmEmit.hs` was kept** as the oracle of the tests (and `--haskell-emitter`) while the Tersus emitter became the default in slice 9, with a checked-in seed
   (`bootstrap/emitter.ll`). It is deleted in slice 10: the tests now stand on the emitter in Tersus, and the seed alone builds it.
3. **Where the Tersus emitter lives at run time**: built lazily on first use from the seed and cached under a hash of what it is made of, so that
   `stack build` still does not need clang.
