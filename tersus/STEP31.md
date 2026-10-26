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

- **Validation time grows faster than linearly with the number of functions.** A program of N functions of about 15 lines
  each (a loop with an invariant and a few `is` tests on an enum), `check`:

  | functions | `-O0` build | `-O1` build |
  |---|---|---|
  | 10 | 0.9 s | 0.4 s |
  | 50 | 6 s | 3 s |
  | 200 | 61 s | 33 s |

  Going from 50 to 200 functions (4 times) takes 11 times as long. The cause is not known; the first guess is that each
  function's proof state carries the contracts of every earlier function.
- Conditions have no `&&`, `||` or `and` (a probe failed to parse all three): a compound condition is nested `if`s.
- There is no mutual recursion (a function sees only the functions defined before it): the emit functions form a bottom-up
  order.
- There are no generic enums (step 22), so no `Option` or `Result`: the emitter state holds an error flag and a message.
- A map is not needed at first. The serializer can number the types and functions, and locals and blocks are numbered
  already, so a lookup is a list index.
- Done and not a blocker: strings, `Byte`, standard input and output, arguments, files.

## Slices

Each slice is a PR, and nothing changes the default `build` until slice 8.

1. **Validator scaling.** Profile and fix it, or learn what size of program is practical (otherwise the emitter is split
   into several programs of fewer than about 50 functions). This gates the rest.
2. **The MIR as data.** `tersus mir --data` prints a stable line-oriented format, with a Haskell reader and writer and a test
   that `read . print = id` for every example.
3. **Gaps found on the way.** Probably boolean connectives, decimal printing of an `Int`, string search and compare helpers.
4. **The MIR types and the reader in Tersus.** It parses the format from standard input and prints it again; the test is that
   the output equals the input.
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
