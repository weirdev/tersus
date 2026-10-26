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

Each slice is a PR, and nothing changes the default `build` until slice 8.

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
5. **Emitter part 1.** Types, slot sizes, descriptors, declarations and the entry point, compared with Haskell on their own.
6. **Emitter part 2.** Operands, constants, word rvalues, arithmetic with overflow checks, terminators and calls.
7. **Emitter part 3.** Aggregates, arrays, Box, clone and drop, then function assembly. From here the test is that the IR is
   byte-identical to `LlvmEmit` for every example and every `TestNative` program.
8. **Wire-in and bootstrap.** `build` can use the Tersus emitter behind a flag. Stage 0 is the emitter built from the
   Haskell-emitted IR; stage 1 is the emitter compiled by stage 0. The fixpoint test: stage 1 gives identical IR for the
   emitter and for the examples.

Slices 5 to 7 are the bulk of the work. Slice 1 is the one that may change the plan.

## Decisions

1. **Port style**: a faithful, byte-identical port (same evaluation order and temp numbering), so that the Haskell emitter is
   the oracle. Tidying comes after.
2. **`LlvmEmit.hs` is kept** for now as the bootstrap path and the oracle. Deleting it needs a checked-in seed (the IR of the
   emitter, 1 to 2 MB, regenerated on every change); that decision waits for steps 30 and 31 to settle.
3. **Where the Tersus emitter lives at run time**: built lazily on first use and cached under a hash of its source, so that
   `stack build` still does not need clang.
