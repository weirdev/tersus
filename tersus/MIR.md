# Tersus MIR (design)

Status: steps 1 and 2 are implemented (`Mir.hs`, `MirLower.hs`, the checker written in Tersus run by `MirHousekeeping`, the validator package `lib/validation/` with its bridge `SelfHostedMir`, `MirEval.hs`; `tersus eval` validates and runs the MIR, `tersus run` validates, compiles and runs the native code, and `tersus mir` prints it) and the lowering to LLVM IR is written in Tersus (`lib/mir/emit/emit.tersus`, `tersus llvm` and `tersus build`; see Native code). The later steps are listed under Phases so the data model is shaped for them.

```
step 1:   source -> AST -> validation -> MIR -> execution of the MIR
today:    source -> AST (checked) -> MIR -> validation -> execution of the MIR
eventual: source -> AST -> MIR -> validation -> lowering to LLVM IR -> compilation -> execution
```

The MIR is to Tersus what Rust's MIR is to Rust: a typed control-flow graph that has no `if`, `while`, `match`, `for` or nested expressions left, only blocks of simple statements ending in a jump. The AST is what the programmer wrote and the validator reasons about; the MIR is what the machine will do.

## What the MIR has to represent

Facts about Tersus that decide the shape (from `Parse` and the semantics of the language):

- **Values are immutable and unaliased.** `push`/`set` return new lists; there is no heap to model, so a place is just a local. No projections, no borrows, no storage markers.
- **`match` and `for` are already desugared by the parser** into `if` chains over `Is` tests and `while` loops, so the MIR needs neither.
- **Functions are first-class but do not capture.** A body sees its parameters, the standard library and the top-level functions, so a nested `fn` lifts to a top-level MIR function with no environment.
- **Scopes decide which variable an assignment means** (`x = ...` updates the nearest enclosing `x`, else defines a new one in the current scope). `let` always declares a fresh binding; `TypeCheckScope` separates its identity from shadowed bindings before checking reference provenance. Lowering resolves bindings once; the MIR has numbered locals and no lexical scopes.
- **Partial operations have contracts the validator discharged** (`get` in range, `/` and `%` by non-zero, `first`/`last` of a non-empty list, `Cast`). The MIR keeps them as ordinary operations with documented preconditions, as `unreachable` would be in LLVM; the interpreter still checks them and reports an error, which turns any validator bug into a test failure instead of a wrong answer.
- **Proof-only constructs** (`affirm`, `define`, `rewrite`, `axiom`, `proof`, invariants, `shrinks`, contracts) have no run-time meaning. The validator reads them from the MIR (see Specifications and Validation); the executor ignores them.

## Data model

```haskell
module Mir where

newtype Local   = Local Int     -- _0 is the return slot, _1.._n the parameters, the rest variables and temporaries
newtype BlockId = BlockId Int   -- bb0 is the entry

data Program = Program
    { progTypes     :: Map Name TypeDecl    -- struct and enum declarations, for layout and for field lookup
    , progFunctions :: Map Name Function    -- every function, nested ones lifted (outer::inner, numbered on a clash)
    , progMain      :: Function             -- the top-level statements; no parameters
    , progGenerics  :: Map Name ([Variable], [(Variable, Type)])   -- the structs with sizes and types: their parameters and fields (completeInstances declares the instances)
    , progInvariants :: Map Name [ValidationStatement]   -- what every value of a struct meets, by the name of the struct: the validator proves it at every MakeData and assumes it for every value of the type
    }

data TypeDecl = StructDecl [(Variable, Type)] | EnumDecl [(Name, [(Variable, Type)])]   -- a struct is a one-variant enum underneath, as in the checker

data Function = Function
    { fnName    :: Name
    , fnParams  :: [Local]                  -- _1.._n
    , fnReturns :: Maybe Type               -- Nothing only for main without a `return`
    , fnLocals  :: Map Local LocalDecl      -- including _0 and the parameters
    , fnBlocks  :: Map BlockId BasicBlock   -- entry is bb0
    , fnSpec    :: FunctionSpec             -- inert for execution
    }

data LocalDecl = LocalDecl
    { localType :: Type                     -- the checker's types: TInt, TBool, TList, TArray (with its size), TFn, TNamed, TVariant
    , localName :: Maybe Variable           -- the source name, for messages and for the validator later; Nothing for temporaries
    }

data BasicBlock = BasicBlock
    { blockStatements :: [Statement]
    , blockTerminator :: Terminator
    }

data Statement
    = Assign Local Rvalue                   -- the only place is a local
    | Ghost GhostStatement                  -- affirm, define, rewrite, axiom, proof: skipped by execution

data Rvalue
    = Use Operand
    | BinaryOp BinOp Operand Operand
    | ListOp ListOp [Operand]
    | MakeList [Operand]                    -- a list built from elements
    | MakeBox Operand                       -- a value held in a Box: the same value (a Box has the value of what it holds)
    | Unbox Operand                         -- the value that a Box holds, taken out of it
    | Unsize Operand                        -- a Box of an array of a size, as a Box of an array of any size: the same value
    | MakeData Name [(Variable, Operand)]   -- a struct or an enum variant (named Enum::Variant), fields in declaration order
    | ReadField Operand Name Variable       -- field of a value known to be that constructor (Field, Project and Cast fused)
    | IsVariant Operand Name
    | AsVariant Operand Name                -- the same value, known to be that variant (`value as Enum::Variant`); gives the local the variant's type

data BinOp  = Add | Sub | Mul | Div | Mod | Compare Rel      -- Div and Mod need a divisor /= 0; Compare Eq and NotEq are of two words (anything else is compared by its Eq, which the checker calls)
data ListOp = Length | First | Last | Get | Push | Set | NewArray
                                                            -- First and Last need a non-empty list, Get and Set an index in range;
                                                            -- they work on a list or an array (TArray), Push only on a list;
                                                            -- NewArray n x makes an array of n copies of x (n a constant, the size of the type)

data Operand = Copy Local | Const Constant
data Constant
    = CInt Integer | CBool Bool | CList [Constant] | CArray [Constant] | CData Name [(Variable, Constant)]
    | CFn Name                              -- a function of the program as a value

data Terminator
    = Goto BlockId
    | SwitchBool Operand BlockId BlockId    -- if true then else; the test of every `if` and `while`
    | Call Operand [Operand] Local BlockId  -- callee, arguments, the local that gets the result, the block that follows
    | Return                                -- the value is in _0
    | Unreachable                           -- falling off the end of a function whose paths all returned
```

Choices and why:

- **Mutable locals, not SSA**, like Rust's MIR. A loop variable is one local assigned in the body; SSA and phi nodes can be built later for LLVM (`mem2reg` does it anyway).
- **A builtin used as a value** (`+` passed where a `fn(Int, Int) -> Int` is wanted) is lifted to a small function of the program (`builtin::add`) whose body applies it, so a function value is always a `CFn` of a function in `progFunctions` and the executor has one kind of callee.
- **Call is a terminator**, like Rust's `Call`: it ends a block, so a validator over the graph has a place to put the callee's contract. A builtin application is an `Rvalue`, which cannot fail except by a broken contract.
- **Operands are locals or constants.** `a * b + get(l, i)` lowers to temporaries, so every statement does one thing and the later passes see no trees.
- **Its own operator set**, not `BuiltinFunct`: `Within` is proof-only and does not belong in something that runs. `Ctor`, `Field`, `Project`, `Is` and `Cast` become `MakeData`, `ReadField`, `IsVariant` and `AsVariant` (a cast keeps the value, which the executor does not check, but the local that gets it has the variant's type, so the types stay honest and the verifier can tell a refinement the validator proved from a mistake), which name the constructor (this is why locals are typed: a `Field Nothing f` in the AST says nothing about which struct, and a layout needs it).
- **Types on every local.** The AST erases types after checking, so lowering recomputes the type of each temporary bottom-up from the declared types of locals and parameters, the signatures of functions, the field types of structs and the builtins' result types (about 40 lines, and total on a program that checked). It does not change `TypeCheck`.
- **No panic or assert terminator for now.** Rust's MIR has `Assert` for overflow and bounds; here the validator proves those, so the MIR would either have to repeat them or drop them. Dropping them (as above) is the current semantics of an unchecked cast. Revisit when integers become bounded (see Open issues).

### Specifications (kept, inert)

```haskell
data FunctionSpec = FunctionSpec
    { specRequires    :: [ValidationStatement]   -- the input contract
    , specEnsures     :: [ValidationStatement]   -- the output contract
    , specTermination :: Maybe Termination       -- after `elaborate`: Counting, Parts or MayDiverge
    , specLoops       :: Map BlockId LoopSpec    -- by loop header
    , specEnv         :: Env                     -- the parameters, and the functions at the top defined before this one
    }
data LoopSpec = LoopSpec { loopInvariant :: [ValidationStatement], loopTermination :: Maybe Termination, loopEnv :: Env }
data Statement = Assign Local Rvalue | Ghost Env GhostStatement
data GhostStatement = GhostValidation ValidationStatement | GhostAxiom ... | GhostProof ... | GhostFunction Name Variable Bool
type Env = Map Variable Operand               -- a local (Copy), or a function (Const (CFn name))
```

They are written with the names of the source (`ATerm "n"`), so each carries an `Env`: what the names stand for at that point of the program. A `localName` could not say it, since two scopes can use one name for two locals. The validator reads a name through the `Env` of the statement, the loop or the function. `GhostFunction name source topLevel` marks where a function is defined, which is where the validator checks its body and learns what it promises.

## A lowering, by example

```tersus
fn count(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] {
    i = 0;
    while i < n [{ affirm i <= n; }] shrinks n - i {
        i = i + 1;
    };
    return i;
};
return count(3);
```

```
fn count(_1: Int) -> Int {                     // _1 = n
    requires { affirm n >= 0 }   ensures { affirm return = n }
    let _2: Int;                               // i
    let _3: Bool;
    bb0: { _2 = const 0; goto bb1 }
    bb1: {                                     // loop header: invariant { affirm i <= n }, shrinks n - i
        _3 = Compare Lt (_2, _1);
        switch _3 [true: bb2, false: bb3]
    }
    bb2: { _2 = Add(_2, const 1); goto bb1 }
    bb3: { _0 = Use _2; return }
}
fn main() -> Int {
    let _1: Int;
    bb0: { call count(const 3) -> _1, bb1 }
    bb1: { _0 = Use _1; return }
}
```

`if` is a `SwitchBool` into two blocks that meet at a join block (or that both `Return`); `else if` nests; a `return` is an assignment to `_0` and `Return`, and statements after it are not lowered (nothing can reach them).

`IfExpr` uses these same guarded blocks, with each selected branch assigning a fresh typed result local before joining. A scoped `BlockExpr` evaluates its statements and moves or copies its final expression into a result local outside the scope. Composable `match` retains scoped subject and pattern bindings until this lowering; `if let` uses the same `Is` and checked projections in its success branch. No eager value-select operation or new MIR opcode is used. Expression lists reuse typed `Push` construction in source order, while constant lists retain `MakeList`/constant semantics.

## Canonical names and linking (packages)

A program compiled from a package (LANGUAGE.md, Modules) reaches the MIR as one `Program`, exactly as a single-file program does; there is no module field in the MIR and no emitter, runtime or `MirData` change. What differs is the names. A declaration of the entry module keeps the bare name it has in a single-file program, so existing programs produce identical MIR. A declaration of any other module is renamed before lowering to its canonical name `package$module$file$Local` (the file segment is the file's stem, present even when the single-file collapse lets source spell it at module level): `modules$geo$shapes$Point` is the `Point` of `geo/shapes.tersus` in package `modules`, and an impl function of it is `<modules$geo$shapes$Point as Eq>::eq`. `$` cannot be written in a Tersus name, so a canonical name cannot collide with a name a program writes, and an import alias is purely a source spelling: it never changes a symbol. An `extern fn` is named `extern <C name>` in the MIR, in C's namespace, not its module's.

Each module is lowered separately (`MirLower.lowerModuleWith`, seeded with stub functions and type declarations from the interfaces of its direct imports, `Interface`), and `Link.linkPrograms` merges the units: type, generic-struct and invariant maps and the function map are keyed by canonical name, `progMain` is the entry module's, and the `GhostFunction` statements of the dependency units are prepended to the entry `progMain`, so the validator learns an imported function at a definition before the entry program that calls it. The same name defined by two units with different definitions is a link error naming both modules. Two copies of the same unit (a compiler-library unit selected by several modules) are deduplicated by unit identity; a definition identical to the one already linked merges, as does an `extern fn` whose signature and contract agree (compared by signature, not body). Compiler-library units keep their bare names (`String`, `HashMap`, `<String>::concat` and the like), so a user declaration colliding with a library name is such a link error. `Link.pruneProgram` then keeps only what the entry program reaches: functions and types named from `progMain` through calls (including function values), fields, locals and returns, the functions a kept contract names, and the drop and trait-impl functions of kept types. That is what a selective import links: visibility is limited at the import site, and linking is limited by reachability. Monomorphization (`MirMono`), validation, ghost erasure and the later passes run once on the linked program, unchanged.

The native helper sources are parsed and compiled lazily against the imported
interfaces, outside the user-library compilation result. Parsing a helper
seeds declarations only from its import closure, not from the other files in
snapshot order. Compiler-only generic constructor owners do not enter user
import environments. No second loader or mutable cache is used.

The native storage modules use the existing compiler-owned bare-name unit
contract: they may declare their own checked impls for imported compiler
types. Ordinary package impl coherence is unchanged. Moving these Drop impls
into `types` would pull native bodies into user imports and form a cycle
through `prelude`/`clone` back to `types`; replacing the `types` unit with a
body-extended copy would violate its unit identity. Separate `lists` and `box`
units instead carry the declarations seeded from the authoritative type
interface. Exact declarations merge; a helper function from a different
origin does not. `MirLists` transforms only the validated user program and
links the needed erased helper units afterwards, leaving helper bodies in
physical form. Native declaration completion removes permission fields from
both concrete instances and generic templates before linking. This also
normalizes the imported declaration seeds carried by permission-free bootstrap
tools, whose runtime erasure is deliberately skipped; it does not change the
checked helper bodies or their pre-erasure layout proofs. The stdlib builtin-contract extraction and
`lib/validation/validation.tersus` are not part of this migration.

## Executing it

`MirEval.runProgram :: Program -> Result (Maybe MirValue) String` (and `runProgramOutput`, which also gives the bytes that `ListOp WriteByte` wrote, as characters from 0 to 255: the evaluator is a result that also collects them). A frame is the function's locals (a `Map`) and a current block; the loop is: run the statements, then follow the terminator; `Call` evaluates the callee operand (a `CFn name` is looked up in `progFunctions`) and recurses in Haskell. `MirValue` is `MInt | MBool | MList | MData | MFn Name`, so no value carries an AST. Run-time errors are `Division by zero`, `Get index out of range` and the like, which the validator is meant to make unreachable.

The validator does not run the MIR: a caller knows a callee by its contracts. There is no other evaluator: the AST is not executed.

## Changes to the flow

- `Cli.runSource`: parse, type check, **lower, validate the MIR, run the MIR** (step 1 validated the AST and then lowered it). A lowering error is an internal error (a program that type checks always lowers) and is reported as `Lowering failed: ...`.
- A new command `tersus mir <file>` prints the MIR of a validated program (like `rustc --emit=mir`). It is how a lowering is read and tested.
- `tersus check` parses, lowers and validates, as `run` and `eval` do before they run.

## Tests

- **Examples and programs**: every program in `examples/` is validated and run on the MIR and must give the value documented in the tests, and the small programs of `testMirRun` give the values written next to them (including the errors, `Division by zero` and `Integer overflow`).
- **Structure**: lowering a loop makes a back edge to its header, an `if` meets at one join, an early `return` in a branch leaves no edge to the join, a nested `fn` becomes a top-level function, shadowing and block-local variables get separate locals, a function passed as a value is a `CFn`.
- **Rendering**: `renderProgram` output for small programs (the one above, an `if`, a list/struct program), so a change to lowering shows as a diff.
- **Well-formedness** (`MirVerify.verifyProgram`, which every lowering goes through and which fails the lowering): every `BlockId` a terminator names exists, every `Local` used is declared, only `Return`/`Unreachable` end a path, every local's type is known (no `TVar`).

## Phases

1. **This step**: the model, the renderer, lowering, the executor, the flow change, the tests and docs above.
2. **Done**: validation moved onto the MIR (first `MirValidate.hs`, now the validator written in Tersus, see Validation), and the AST evaluator and the AST validator (`Proof.hs`) are gone.
3. **In progress**: LLVM lowering (`lib/mir/emit/emit.tersus`, see Native code): steps 1 to 4 (`Int`, `Bool`, control flow, calls, lists, structs, enums, function values and memory management) are done. What is left (borrowing a value to a function that only reads it, deep recursion, contracts as hints to LLVM, cheaper ownership, and valgrind in CI) is in the roadmap of `README.md`, item 17.

## Arithmetic and traps

`Int` is a 64-bit signed integer (see LANGUAGE.md, Integers), and **`Add`, `Sub`, `Mul` and `Div` trap when the result does not fit**: the program stops with `Integer overflow`, as in native code built from LLVM's `llvm.sadd.with.overflow` and the like followed by a branch to a trap. The validator reasons about unbounded integers, so what it proves holds for the runs that do not trap. The MIR has no operation that wraps.

So an operation of the MIR either gives a value or traps. Two kinds of trap:

- **Overflow** is always checked, in the executor and in native code, because nothing proves it cannot happen.
- **A broken contract** (a divisor of 0, an index out of range, `first` of an empty list) cannot happen in a validated program. The executor still checks and reports it, so that a validator bug is a failure and not a wrong answer. Native code omits these checks (they are `unreachable` to LLVM).

`Unreachable` is the end of a function whose every path returned and is never executed. The validator rejects a function with a path that reaches it.

## Native code

The emitter written in Tersus (`lib/mir/emit/emit.tersus`, `Bootstrap`) lowers the owned MIR to LLVM IR as text; `tersus build` compiles it, with the C runtime of `LlvmRuntime` (embedded in the compiler; both are written to uniquely named files in the temporary directory, which are removed afterwards), with clang.

- **Locals are stack slots.** Each local is an `alloca` in the entry block, and a statement loads its operands and stores its result, so the blocks need no phis; `-O2` runs `mem2reg`, which builds them. A block is a label `bbN`, `Goto` and `SwitchBool` are `br`, `Return` loads `_0` and returns it, and `Unreachable` is `unreachable`. `Ghost` statements and the `FunctionSpec` are dropped.
- **Names.** A function of the program is `@"fn.<name>"` (internal, quoted, since a lifted function is named `outer::inner`), the statements of `main` are `@tersus_main` (names of the program may use any letter, so a name is written as its UTF-8 bytes, with every one that is not printable ASCII as `\hh`, and the file stays ASCII), and the C-level `main` calls that and prints the result by the descriptor of its type (`tersus_print`). A program can finish without returning on some path (`if c { return 1; };`), where `tersus run` prints nothing, so when `main` returns a value its function returns the value with a flag that says whether `_0` was assigned (kept in a slot that every assignment of `_0` sets), and the C-level `main` prints only then.
- **Types.** `Int` is `i64`, `Bool` is `i1`, and a list is a `ptr` to a heap object `{ rc, len, cap, elements }`: 24 bytes of header, then one 8-byte slot per element (an `Int`, a `Bool` as 0 or 1, or the `ptr` of an inner list), so that one runtime function serves every element type. `rc` is not used (see Ownership). A struct or an enum value is not a value of the heap but its words, held inline (see Data), and a `Box<T>` is a `ptr` to room on the heap for the words of the `T` it holds, so a type that contains itself holds its recursion in a pointer. A function value is the address of the function (`ptr @"fn.<name>"`), since functions capture nothing, and a call of a local is a call through that address with the parameter and result types of its `TFn`.
- **Lists.** `Length`, `First`, `Last` and `Get` are loads (`First` and `Last` of an empty list, and `Get` out of range, are assumed not to happen). `MakeList` and a constant list call `tersus_list_new` and store the elements, each time the statement runs, so that a constant is a value owned like any other when memory is managed in step 4. `Push` and `Set` call the runtime, which changes the list it is given (growing it by doubling when it is full, and freeing the element `Set` replaces); the list is the caller's to change because of what the ownership pass decided (see Ownership).
- **Arrays.** An array (`TArray element size`) is held inline: its elements are 8-byte words one after another in the slot of the local that has it (`alloca [N x i64]`), and an element that is an array is its words, in line, so `Array<Array<Int, 3>, 2>` is six words. The value of an array operand is the address of its first word. Assigning one is a `memcpy` into the slot of the destination (nothing when it is the same local), `NewArray` stores the element `N` times (a `memset` for a zero, a loop otherwise), `Set` copies the array if it is another local and stores the element (so `a = set(a, i, x)` is a store into the slot), and `Get` of a row copies the row. A literal (`CArray`) is a private constant global of the words, which is read and never written. A function gives an array as the address of the caller's words and copies it into its own slot at the start, so it cannot change the caller's, and an array result is written into room the caller gives as the first parameter (`sret`), which the caller makes the slot of the local that gets it; the entry function of a program that returns an array is given room by the C-level `main`, which prints from it. The runtime describes an array by a descriptor of kind 5, with its count and the descriptor of its elements, to compare and print it. An array is not a value of the heap, and the frame holds it for the life of the function; one of plain elements (Int, Bool, arrays of those) owns nothing, so the ownership pass never clones, moves or drops it, and one whose elements own something (lists, `Box`es, structs with them) is moved, cloned and dropped like a struct (`needsDrop`): `array(n, x)` clones `x` into each slot (`fillElements`) and `set` drops the element it replaces (`dropElement`) (an `alloca` is only in the entry block, so a loop does not grow the stack). An array can also be a field of a struct or an enum and an element of a list: a field is laid out by the words of its type, a list has a stride of the words of its element (`tersus_list_new_words`, `tersus_list_push_words`, `tersus_list_set_words`), and the runtime walks them by the descriptor of each type (`words`, and a slot is the word it holds, or for a value held inline the address of its words) to clone, free, compare and print.
- **Data.** A struct is held inline as the words of its fields in declaration order, with no tag, and an enum as a word that says the variant (its position in the enum) and then the fields of that variant, in the room of the widest variant: `slotsOf` gives the words of a type, a field or an element that is held inline is its words in line, and the value of one wherever a value is wanted is the address of its first word. `MakeData` writes the tag and the fields into the slot of the local that gets it, `ReadField` is a load at the offset of the field (from the slot of the local, or from the address that a `Box` holds, since a Box is looked into), `IsVariant` compares the tag, and `AsVariant` copies the words (a `Box` that is cast is taken out of its room, which is freed). A variant's fields are those of the variant, so reading a field of another variant is the undefined behaviour the validator keeps out. A constant `CData` is built in room of its own (made at the start of the function, so a loop does not grow the frame) each time it is wanted, since it can hold a list. A value held inline is given to a function as the address of the words, which the function copies, and a function that returns one writes it into room that the caller gives (`sret`); when the local that gets the result owns something, the room is one of the function's own and the local is given the value after what it held is freed. Native code has no `Box` of its own (see A list in native code): `MakeBox` and `Unbox` reach the emitters only for a Box of an array, which is a `List`, and move the elements of an inline array into memory at an address (`tersus_addr_alloc`) or out of it (`tersus_addr_free`).
- **Structs with types.** A struct that has parameters is a struct of its own for each list of types and sizes it is given: the type carries them structurally (`TNamed "Vec" [ArgType ..., ArgSize ...]` for `Vec<List<Int>, 3>`, and with a `TParam` or a size parameter in a function that has them), so the instance is declared from `progGenerics` by `completeInstances` and a copy of a function renames it by substituting the types and the sizes in the arguments (`substitute`). The rendered name of an instance (`Vec<List<Int>, 3>`, with a ' marking a type parameter) is written only where a name is needed (the keys of `progTypes`, a constructor, a message), and is never read back. `MirMono` finds the type of a parameter that is a struct by matching the arguments of the instance with those of the argument.
- **Type parameters.** A function with type parameters (`fnTypeParams`) has locals whose types can be `TParam`; the validator and the executor run it as it is (values have no types there), and `MirVerify` takes a `TParam` for any type. `MirMono` makes a copy for each list of types (and sizes) that a call gives: it finds the types by matching the types of the parameters of the callee with the types of the arguments, and its result with the local that gets it (`typeArguments`), defaulting to `Int`, and replaces `TParam` in the types of the copy (`substitute`). So the ownership pass and the native code see only concrete types, and know whether a value owns something.
- **Box payload borrows.** Native lowering distinguishes a handle from a payload using the reference target and follows slot-zero addresses, never consuming `Unbox`. The verifier reads a native container slot's exact type from its declared `addr` field rather than reconstructing it from the instance name; a native Box handle is not implicitly unwrapped after a slot step.
- **Lent parameters.** A function lists the parameters it only reads in `fnBorrowed`, and in a type of a function value they are `TRef` (`fn(&List<Int>) -> Int`); the locals have the type without the `&`. The ownership pass does not move or clone an argument for a lent parameter (it is read, and a constant that owns something is made into a local first), never frees a lent parameter, and clones one that the function takes (`_0 = _1`, an argument for a parameter that is not lent). Natively a lent parameter held inline has no room of its own, the parameter is the address of the caller's words, and the result room of a call whose argument is the local that gets it is one of the function's own, since the callee does not copy what it reads.
- **Size parameters.** A function with size parameters (`fnSizeParams`) takes them as its last parameters, and its locals have types such as `Array<Int, n>`. The validator and the executor run it as it is. For native code `MirMono.monomorphize` (run first by `insertOwnership`) makes a copy of it for each list of constants that a call gives (`dot<3>`), with those parameters removed, the operands that read them the constants and the types' sizes replaced, and redirects the calls; the specifications and ghost statements are dropped, since they name the functions that are no longer there and only the validator reads them. A program with no function of the kind is left alone.
- **Structs with sizes.** A struct with sizes is declared in `progGenerics` and is a struct of its own, named by its sizes (`Packet<4>`), in `progTypes` for each one the program mentions (`completeInstances`); in a function with sizes the name has a size parameter in it (`Packet<n>`), and `MirMono` gives the copy for 4 the name `Packet<4>` in every type, constructor and constant, then declares what the copies mention and drops the declarations that name a size parameter. The names are printed without the sizes (`Packet { ... }`), and `MirEval` takes the struct for its name without them, so the executor can run a function with sizes as it is.
- **A Box of an array.** To the validator and the executor, `size`, `get`, `first`, `last` and `set` on a `Box<Array<T, N>>` or `Box<Array<T, ?>>` are the `ListOp`s of an array, and `ListOp NewBoxed n x` (`Array::boxed(n, x)`) and `Unsize` are the same value as the array they stand for, which is why the validator gives `NewBoxed` the contract of `NewArray` and treats `Unsize` like `MakeBox`. Native code has no Box of an array: `MirLists` makes each one a `List<T>` with as many elements as room, so those operations are those of a list, `NewBoxed` is a call of `listFilled`, `NewEmptyBoxed` one of `listNew` and `Unsize` the list as it is (see A list in native code). `ListOp Pop` takes the last element out of a list (before `MirLists` it is a list operation; after, a call of `listPop`). `ListOp NewEmptyBoxed` (`Array::empty()`) is the Box of an array of no elements: a null address and the count 0, so nothing is allocated.
- **Bytes.** `TByte` is a type of the MIR (the checker's `Byte`): one word, held, copied and printed as an `Int`, and `ListOp ToByte [x]` and `ListOp FromByte [b]` (`toByte(x)` and `toInt(b)`) are the same value as their operand, `ToByte` with the contract that it is from 0 to 255. The validator adds `0 <= x < 256` to every local of type `TByte` (`withTypeFacts`, as it adds the size of an array), which is sound because only `ToByte` makes one and it asks for the range; `MirVerify` accepts a constant `CInt` from 0 to 255 where a `TByte` is wanted. Native code treats `TByte` as `TInt` everywhere (`llvmType`, `loadAt`, `storeAt`, `toWord`) with a descriptor of its own of the same kind.
- **Output.** `ListOp WriteByte [b]` (`writeByte(b)`) writes the `Byte` `b` to the standard output and gives `b`: it is an operation on a Byte and not on a list, in `ListOp` because the validator gives every `ListOp` the contract of the builtin it stands for (`rvalueCall`), which for this one is `return = b`. The evaluator (`runProgramOutput`) collects the bytes and the emitter calls `tersus_writeByte` of the C runtime, which is `putchar`. `String::print` of `lib/string.tersus` is a loop of it. Nothing in the MIR is an effect otherwise: a call that is made for what it does is an `Assign` to a local that nothing reads.
- **Arguments.** `ListOp ArgCount []` and `ListOp ArgByte [i, j]` give the arguments of the program: `MirEval.runProgramIn` takes them as the bytes of each (as characters from 0 to 255), and the emitter gives `@main` its `argc` and `argv` (`tersus_init` keeps them) and calls `tersus_argCount` and `tersus_argByte`. Like `ReadByte` they are in `readsWorldOp`, so `Mir.readersOfInput` counts a function that has one as a reader, which the validator does not treat as a function of its arguments.
- **Files.** `ListOp PathByte`, `FileLoad`, `FileByte`, `StoreByte` and `FileStore` are the five operations that `String::readFile`, `fileSize` and `writeFile` of `lib/string.tersus` are made of: a path buffer, the file that was loaded last and the file being built, which the runtime keeps in C (`tersus_pathByte` and the others, over `fopen`) and `MirEval` keeps in its state `S` (with the files written so far, which `Outcome` gives and `Cli.runSourceFiles` returns for the CLI to write). The files a program can read in the interpreter are a function of the path (`RunEnv.envFile`: the real files for the CLI, a list in the tests). They are in `readsWorldOp`, like `ReadByte`.
- **Addresses and permissions** (POINTERS.md). `TAddr T` and `TBlock T` are types of the MIR. `ListOp AddrNull`, `AddrOffset`, `AddrCast`, `AddrToInt`, `AddrFromInt`, `AddrAlloc`, `AddrGet`, `AddrWrite`, `AddrTake`, `AddrDropValue`, `AddrDropRange`, `AddrResize` and `AddrFree` are the operations on memory, given the permission as their last operand, which only the validator reads; the `Block` operations (`BlockNew`, `BlockTaken`, `BlockResized`, `BlockSplitLo`, `BlockSplitHi`, `BlockJoin`, `BlockAssume`, `BlockCast`, `Mir.ghostOp`) make a permission. A form that gives two things is two operations and a tuple (`Addr::alloc(n)` is `AddrAlloc` and `BlockNew`). The validator gives each the contract of its builtin (`StdLib`), and `AddrAlloc`, `AddrResize` and `BlockAssume` are in `readsWorldOp`, since each gives a new allocation. `MirMoves` checks that every permission is used exactly once, and `MirGhost.eraseGhosts` then takes the permissions out (their locals, parameters, fields and operands, and the `Block` operations), so the program that runs has the address operations without their last operand, and `AddrWrite`, `AddrDropValue` and `AddrDropRange` give `0`. `MirEval` keeps a heap (an address is a number), and native code an `i64`, with `tersus_addr_alloc`, `tersus_addr_resize`, `tersus_addr_free` and `tersus_drop_slots` of the runtime.
- **Layout and fixed-width integers.** `TWord signed bits` is `I8`, `I16`, `I32`, `U16` or `U32`; `ListOp (Narrow signed bits) [x]` (`I32::from(x)` and the others) is `x` with the contract that it is in range, and `FromByte` (`toInt`) widens one. The validator knows the range of every local of such a type, as of a `Byte`. Native code lays values out as C does (`Mir.layoutOf`, `Mir.fieldOffsets`): a number is an `i64` in a register and its own width in memory, a `Bool` and a `Byte` one byte, a struct its fields at aligned offsets, an enum a `U32` tag and its variant; `slotsOf` is the 8-byte words of room a value takes in a frame.
- **Standard error.** `ListOp WriteError [b]` (`writeError(b)`) is `WriteByte` on the standard error: the evaluator keeps a second stream (`Written`, `runProgramStreams`), and the emitter calls `tersus_writeError` of the C runtime (`fputc` to `stderr`).
- **Input.** `ListOp ReadByte []` (`readByte()`) is the next byte of the standard input, or -1: an operation with no operand, which the validator gives the contract of the builtin (`return >= -1` and `return < 256`) and nothing else. The evaluator (`runProgramWith`) is a function of the input that is left, so it reads the stream as the program asks (`E` threads it with the output), and the emitter calls `tersus_readByte`, which is `getchar`. `String::read` and `String::readLine` of `lib/string.tersus` are loops of it with a limit. The validator does not treat a call of a function that reads (`Mir.readersOfInput`: one with a `ReadByte`, or that names one that has, as a callee or as a value) as a function of its arguments: `applyCall` leaves out the fact `result = f(args)` and the result evaluated from known arguments (`fnReads`), since two calls would otherwise be the same value, and a proof may not call it.
- **A list in native code.** After validation `MirLists` replaces list operations with calls of `lib/lists.tersus` and completes the `List<T>` structs (an address, then the count and the room, with the permission to the memory erased): `ListOp Length` is a `ReadField` of `len`, `ListOp Get`, `First` and `Last` stay `ListOp`s whose operand is the `List` (the struct's first field is the address of the elements, which `arrayPtr` reads), `Push` and `Set` are `Call`s of `listPush` and `listSet`, and `MakeList` and a `CList` constant are a `Call` of `listNew` and one of `listPush` for each element. The ownership pass, monomorphization and the emitter use named struct types; the runtime prints and compares a struct named `List` as a list (`tagged` 2 in its `Variants`). A `TBox t` whose `t` is not an array becomes the struct `Box<t>` of `lib/box.tersus` the same way: `MakeBox` and `Unbox` are `Call`s of `boxNew` and `boxUnbox`, and a `ReadField`, `IsVariant` or `AsVariant` of a Box is one of the `Box`, which the emitters read through the address that is its only word, as through a Box (`tagged` 3, printed, compared and copied as the value it holds, and freed by its drop). A `List` is freed by its drop (`impl<T> Drop for List<T>` in the library), as a `Box` is. A `Box` of an array, of a size or of any, becomes a `List<T>` too, with as many elements as room: `NewBoxed` is a `Call` of `listFilled`, `NewEmptyBoxed` one of `listNew`, `Unsize` a `Use`, and `MakeBox` of an inline array and `Unbox` of a Box of an array stay, which the emitters make of the list (the elements are moved into memory of their own, or out of it and the memory freed).
- **Descriptors.** The runtime prints values by the descriptor of their type: a constant global `@"type.List<Int>"` of `{ kind, aux }` for each type the program uses (and each type inside it, so a type that contains itself is there once): `aux` is the descriptor of the elements of a list, or the variants of a struct or an enum (each with its name, written `Enum::Variant`, and the names and descriptors of its fields). Equality (`Compare Eq` and `NotEq`, structural) and the printing of the result are then written once, in C, and print a value as `renderMirValue` does. A value of a variant (`TVariant`) has the descriptor of its enum. Step 4 adds how to free a value of the type.
- **Memory** is managed by ownership, decided on the MIR (see Ownership): nothing is counted at run time, and a value is freed when its owner lets go of it.
- **Arithmetic.** `Add`, `Sub` and `Mul` are `llvm.s{add,sub,mul}.with.overflow.i64` followed by a branch to the function's `overflow` block, which calls `tersus_overflow` (the message `Evaluation failed: Integer overflow` and exit status 1 of `tersus run`). `Div` rounds down, where `sdiv` truncates, so it subtracts 1 from the quotient when the remainder is not 0 and has the other sign than the divisor, and the one quotient that does not fit (the smallest `Int` divided by -1) goes to the overflow block. `Mod` takes the sign of the divisor, with `srem` by 1 in place of -1, which `srem` leaves undefined for the smallest `Int`, and the result 0 that follows.
- **Contracts are not checked.** A divisor that is not 0, an index in range, a list that is not empty are what validation proved, and the operations assume them as `unreachable` would (`sdiv` by 0 is undefined in LLVM). A bug in the validator is undefined behaviour in native code, where `tersus run` reports it. Overflow is the one trap, since nothing proves it cannot happen.
- **Tests.** `TestNative` builds programs and compares what the executable prints, and its exit status, with `tersus eval` (every example, structs, enums and lists and their operations, divisions of every sign, loops, recursion, and each overflow; calls of function values are lowered without validation, since the validator cannot follow them yet); the builds pass without clang.

## Moves

The checker resolves source `clone(x)` calls to the type's `Clone` implementation. A clone left as a builtin over a type parameter becomes the MIR rvalue `CopyOf`. The validator and reference executor treat `CopyOf` as `Use` over the same immutable value; native code calls an available `Clone` implementation or copies the fields structurally. Inside a type's own `Clone` implementation, structural copying avoids a recursive call to that same implementation. `MirMoves.checkMoves` runs during lowering, before validation, and rejects uses of moved values:

- **Places.** A place is a local with the fields (`SField`), the elements of a list (`SElem`) and the tag (`STag`) followed from it. The state along each path is the set of places that may have been moved out, with where and by which variable, and the places that a local is a *view* of on every path (a local that is a view on one path and not on another is taken for a value of its own, so a loop that rebuilds `bytes = push(bytes, x)` after `bytes = self.bytes` is not a second move of `self.bytes`). The blocks are walked to a fixed point, joining by union of the moves and intersection of the views, and the errors are collected from the last walk.
- **Views.** `d = x.f`, `d = get(l, i)` (or `first`, `last`), `d = x as V`, `d = Box::unbox(b)`, and the hidden locals of a `for` (`$list ...`) and a `match` (`$match`) make `d` a view of the place they read, when its type is not Copy. Reading a view moves nothing. Taking one (a `Consume` operand: a call argument that is not lent, a field of a struct made, `push`, `return`) moves the place it is a view of, which is an error for an element of a list and for a part of a parameter that is lent.
- **What an operand does** is `MirMoves.roles`, except that `ListOp NewArray` and `NewBoxed` take their element (n copies of it are made), `Unbox` and a cast read, and the value in `_0` is taken by `Return`.
- **Copy** (`isCopyType`) is Int, Byte, Bool, functions, an array of Copy, and a struct or enum that `CopyDef` named (with Copy fields for an instance of a struct with parameters). It is never moved.
- **Positions.** Lowering writes `GhostPosition line column` (from the parser's `Mark`) before the statements it comes from and at the start of every block, so each error has a line; `stripPositions` takes them out, and no other pass sees one.

`lib/lists.tersus` and `lib/box.tersus` are compiler-owned module units,
lowered with the same move and loan checks as other modules. Imported
signature stubs remain present during those checks, then leave the unit.

## Ownership

The production transformations are `insertOwnership` and `expandRefWrites` in
`lib/mir/ownership/`, hosted by `MirHousekeeping`. The order is ghost
erasure, reference-write expansion, list lowering, Haskell `MirMono`
monomorphization, Tersus ownership, verification, then emission. The
operand-role classification move checking uses is in `MirMoves`; the heap
model of `TestOwnership` has its own drop classification.

The host retains metadata outside the runtime data: generic struct templates,
struct invariants, function specifications and full ghost statements. For each
pass, `MirOwnershipData` replaces ghosts with globally unique numbered markers,
and MIR v2 carries them as `ghost N`. The returned marker must occur exactly
once in its original function, including after block splitting. Missing,
duplicate, unrecognized or unnumbered markers are errors, as are changed
original local declarations, function headers, type declarations or function
sets. Original block IDs are retained so loop specifications keep valid
references. Uncalled Drop/Clone implementations are not pruned at this boundary.
`forNative` still removes proof metadata only for emitter data.

The emitter executable includes the ownership request dispatcher. The pinned
stage-0 seed runs reference-write expansion and ownership on every program the
host builds for itself (the emitter, checker, eraser, parser and validator) and
emits the emitter to build stage 1. Stage 1 emits the other tools and runs the
passes for user programs. Ownership has no interpreted cold path;
only the recursive erasure of the List/Box library runs the eraser interpreted
while the tools are built. Build or
pass failures return `Error`; there is no Haskell ownership pass to fall back to.
`TestOwnership` runs the owned MIR of the corpus, made in the order native code
is made in, on the independent heap model against the executor;
`TestMirOwnership` does so for the programs that make references and have no
arrays or blocks, with the passes run before list lowering, and testNative runs
them natively (reference-write fixes included). `TestMirOwnership` also covers transport,
symbolic pre-mono inputs and protocol refusals; `testOwnershipMetadata` isolates
pure metadata checks. `testOwnershipInterpreted` runs the emitter's source in the
interpreter on MIR fixtures and requires the owned MIR the native tool writes, or
a clean run on the heap model. The heap-model MIR fixtures are also owned by the
production emitter, built with the runtime's memory checks and run under
valgrind; their callees take a reference parameter by value there, because the
native MIR checker gives a lent parameter the type of its referent. Two of them
(a view lent to a callee that writes its source, a borrowed view whose source is
replaced) are patterns the move checker now refuses in source, which a test
asserts. Lowered fixtures name a list or a Box as its declared struct, and paired
controls require the same ownership from the older `list`/`box` tokens.
An update parameter (`fn f(xs: &mut List<Int>)`) is a borrowed value local in
MIR, so `*xs = v` expands to an assignment of `xs`; native code stores over the
caller's place, so the pass frees what it held first, as for a reference write.

Native code frees what a program makes and changes lists in place, so `MirHousekeeping.insertOwnership` (run by `emitProgram`, after validation, and printed by `tersus owned`) rewrites the MIR to say who owns every value that has something to free: a list, a `Box`, and a struct, an enum or an array that holds one (`needsDrop`). A value that owns nothing (a number, and a struct, an enum or an array of them) is plain, and is copied where it is wanted. The result still means the same thing: `MirEval` runs it and gives the same answers, with `Move` as a `Copy`, `CopyOf` as a `Use`, and `Drop` as nothing.

**The invariant** is that what a value owns (a list or a `Box`, which are on the heap) has exactly one owner: a local, a word of another value (a field, or an element of a list), or a temporary on its way somewhere. So the heap is a forest, a value is freed with what is in it, a copy is a deep copy that shares nothing, and `push` and `set` may change the list they are given when it is theirs. A struct or an enum that holds one is held inline and owns it through its words, so it is moved, copied and dropped like a list: a `Move` copies the words to where they go and clears them where they were, `CopyOf` is a deep copy, and a `Drop` frees what the words own. Where a value is wanted by two the program has to say so (`clone`, see Moves), and the pass makes that copy where `CopyOf` is; it still clones a part of a value that is read and then not used before the whole changes (a view that cannot look at the value in place), which a program cannot see.

**What an operand does** decides what happens to the local it names:

| The operand | The local |
|---|---|
| reads the value: `size`, `==`, `is`, the list of a `get` | nothing |
| takes it: `y = x`, the list and the element of `push`/`set`, a field of a list or struct that is made, an argument of a call, `_0` | `Move x` when it is not used again (`x` is left holding nothing), and otherwise a `CopyOf` of it |

A local is dropped before an assignment or call overwrites a value it still owns, and remaining owned values are dropped at return. Ownership tracks whole values and partial fields across control-flow joins and uses flags where cleanup is conditional. A parameter declared with `&` or `&mut` borrows its referent; a consuming argument transfers the value it owns. If the caller still needs an owning value, it supplies a clone.

**A part of a value** (`get`, `first`, `last`, a field) is part of what contains it:

- A field of a value that is not used again is taken out of it (`TakeField`; what is left of the value is freed with it). This is what makes a `match` on a tree not copy the tree: the fields are taken from the scrutinee one by one. The check is by field: a field is taken when neither it nor the whole value is used later (the tag, read by `is`, does not count).
- A temporary used only by reads can `Peek` when its source and the source's loan/view origins stay live and undisturbed through those uses. Assignments, consumes, reference writes and call arguments are checked through their loan origins, not just the local named in the syntax. A temporary used as the root of a `Borrow` is copied instead of peeked, because that borrow can outlive its last direct use. Cross-block peeks and the hidden `$list` local of a `for` additionally require a chain to an unchanged read-only lent parameter; mutable parameters do not qualify. A cast is forwarded to subsequent reads so they read the original value directly.
- Otherwise it is a `CopyOf` of the part, made where the part is read.

**Borrowed places stay live through the reference's last use.** The ownership pass carries loan origins across the control-flow graph, including reborrows, reference copies and calls with `from` results. A read through a reference keeps its owner or top-level field live, so an earlier read cannot take that field out. A call that replaces an owner while reading a reference to it writes into a temporary and drops the old owner only after the call returns. Reassigning a reference replaces its old origins; joins keep the possible origins from each path.

**Box payload borrows use the existing place and slot representations.** Before native storage lowering, `&b` has type `&Box<T>` and `&*b` has type `&T`; both refer to the same logical Box place because the interpreter and source validator treat a Box as its contents. The verifier recognizes a named source Box's matching ghost `blk` declaration when its requested reference target is exactly the payload, normalizing only one level. Erased native handles have no such declaration and require explicit slot steps. `MirLists` uses that target type to distinguish them and appends the existing slot-zero index step only for the payload borrow. Native code follows the Box address without taking its value or freeing its room. Stable `clone(Box::unbox(place))` calls to lent Clone implementations borrow non-array payloads, while a terminal Box field is lent as a Box. Sized boxed arrays retain whole-array materialization because their native List storage has element slots rather than one inline-array slot. The child's Clone returns an owned value, which is moved into fresh Box storage; the temporary loan keeps the original owner live through the call and does not own the result. Consuming `Unbox` is unchanged.

**What this costs.** Borrowed parameters avoid copies of their referents. Last-use moves and undisturbed peeks also avoid copies; a clone or a view that must survive a mutation needs independent storage.

**How it is checked.** `TestOwnership` runs the owned MIR on a model of the heap that fails on a value used after it is moved from or freed, freed twice, looked at after it changed, changed in place while another place holds it, or left on the heap when the program ends, and compares the answer with the executor's. It runs every example and every program of the native tests, and the model is shown to catch the mistakes it exists for (MIR written by hand with each). `TestNative` builds every program with `-DTERSUS_CHECK`, which makes the runtime record each block (a block that is freed twice or left at the end is an error, and one that is freed is filled with 0xDD and kept so that a use of it reads that), and runs some of them under valgrind as well. When this was written, a generator of random programs over lists, nested lists, structs and enums (a script that is not in the repository) found no difference on the model or natively.

## The MIR as data

The MIR package imports `data::codec::codec` for `Token`, `Parsed`, `Size`,
`Type`, tokenization, escaping, decimal numbers and size/type read/write helpers.
AST consumers import that same module; the MIR record schema and program
readers/writers stay in `lib/mir`. `mir::support::support` imports those
codec types and the reader's declarations. It owns the shared declaration
lookup and variant ownership, array classification, primitive layout results,
Tersus type/name rendering and LLVM name escaping. Its result records and
Clone impls live there, not in the consumers. It is an ordinary package module,
not an implicit compiler library; the reader does not depend on it.

The emitter, verifier and eraser keep their full layouts local. The emitter
uses zero-sized `Block` and unwraps `Uninit`; the verifier retains its legacy
24-byte List and Box-of-array layout; the eraser combines those rules before
removing permissions. Their field layouts call those local rules.

`tersus mir --data <file>` prints the MIR that native code is made from (the owned MIR of the Ownership section) as text that a program can read, and `MirData` reads and writes it (`readProgram (writeProgram p) = Ok (forNative p)`, for every example and every program of the native tests: `TestMirData`). It is what the lowering to LLVM IR written in Tersus is given (`STEP31.md`), and the emitter gives the same IR for the program read back from the data as for the program (`TestMirEmit`), so the data is all that the code made needs. Only what the emitter uses is in it: the ghost statements, the contracts and loop invariants, the structs with sizes and the invariants of structs are left out (`forNative`), since the validator is done with them and monomorphization has made their copies.

The shared MIR record declarations and parsers are in `lib/mir/reader/reader.tersus`; the normalizing writer is in `lib/mir/writer/writer.tersus`. `lib/mir/mir_reader/mir_reader.tersus` imports both and reads/writes version 1. The writer also exports `printProgramWithGhosts` for version 2, retaining numbered ghost IDs, and `printProgramAsRead`, which the eraser writes version 1 with: a list or a Box read from the `list` or `box` token of older data is written with that token again (`printTypeWith` of `data::codec::codec`), where the other entries write every list and Box as its named struct. `tersus mir --data p.tersus | tersus run lib/mir/mir_reader/mir_reader.tersus` prints the data again, byte for byte (`TestMirReader` does it natively for every example, every program of the native tests, and for the reader's own data, and has it refuse the texts that are not the data of a program). It reads the file that the writer of `MirData` makes: the types, then the functions, then `main`, a record to a line, and it stops at the first empty line. `lib/mir/emit/emit.tersus` is the lowering to LLVM IR written with that reader; it writes all of the IR of the program (`TestMirEmit`), and with the arguments `outline` and `bodies` the declarations with the descriptors and the entry point, and the code of each function.

The first line is `tersus-mir 1`. Every other line is a record of words and numbers separated by one space, with names in quotes (the UTF-8 bytes of the name; printable ASCII as it is, and the others, `"` and `\` as `\xHH`), so the text is ASCII and a reader needs only a line, its words and its numbers. The order of the records is that of the maps they were in, which the emitter keeps: the types (`struct` and `enum`) by name, the functions by name, then `main`. A function is its `function` (or `main`) line, a `local` line for each local, a `block` line for each block followed by its statements and the line of its terminator, and `end`:

```
enum "Shape" 3 "Shape::Circle" 1 "radius" int "Shape::Rect" 2 "width" int "height" int "Shape::Empty" 0
function "double" params 1 1 returns some int sizeparams 0 typeparams 0 borrowed 0
local 0 none int
local 1 some "n" int
block 0
assign 0 binary add copy 1 copy 1
return
end
```

A type is `int`, `byte`, `bool`, `list T`, `array T SIZE`, `box T`, `fn N T... T`, `named "n" N ARG...` (each ARG `size SIZE` or `type T`), `variant "n"`, `var N`, `forall N "n"... N "n"... T`, `param "n"` or `ref T`, and a size is `c N`, `any`, `p "n"` or `v N`. An operand is `copy L`, `move L` or `const C`, and a constant `int N`, `bool true`, `list N C...`, `array N C...`, `data "n" N ("f" C)...` or `fn "n"`. A statement is `assign L RVALUE`, `peek L RVALUE` or `drop L`, and a terminator `goto B`, `switch O B B`, `call O N O... L B`, `return` or `unreachable`. An rvalue is `use O`, `binary OP O O` (`add sub mul div mod eq noteq lt lteq gt gteq`), `listop OP N O...` (the names of the `ListOp`s, as `get`, `newArray` and `writeByte`), `makelist N O...`, `makebox O`, `unbox O`, `unsize O`, `makedata "n" N ("f" O)...`, `readfield O "n" "f"`, `isvariant O "n"`, `asvariant O "n"`, `clone O` or `takefield L "n" "f"`.

## The mir package

`lib/mir/` is a package (package name `mir`) whose four entry programs share one MIR reader. The round-trip reader, the eraser and the ownership passes share the declarations-only `writer` module; its `printProgramWithGhosts` preserves ghost IDs in MIR v2. The emitter imports the ownership request dispatcher as well as its LLVM lowering files. The checker, eraser and emitter also import `support` for phase-neutral metadata. Only the selected entry file runs; sibling files and the ownership module contain declarations. Full layouts stay local. The eraser writes with the shared writer too (`printProgramAsRead` keeps the `list` and `box` tokens of older data).

| Entry | What it does | With no input |
| --- | --- | --- |
| `mir/mir_reader/mir_reader.tersus` | The MIR as data, read and written by a program (step 31, `STEP31.md`): the types of the MIR as enums and structs, a tokenizer, a parser for each of them in the style of the emitter to come (a `Parsed<T>` of the value, the index after it and whether it could be read; every index proved in range) and a writer. It reads the MIR as data from the standard input (the host feeds it what `tersus mir --data` prints, and programs before their ghosts are erased too) and writes the same text; it is made to read its own data too (the largest input, 22,000 lines) | returns `1` with no input (it says on the standard error that the input is not the MIR as data) |
| `mir/mir_verify/mir_verify.tersus` | The MIR as data, checked by a program (REPLACING_HASKELL.md target 3): the shared reader of the package, then the MIR well-formedness and type checks the host runs on every program (through `MirHousekeeping`) (every block a jump names is there, every local and function used is declared, and the types of statements, switches and calls), with its own phase-specific full layout rules and the shared primitive layout helpers. It reads the MIR as data from the standard input (the host feeds it what `tersus mir --data` prints, and programs before their ghosts are erased too) and writes `OK` for a well formed program; for one that is not it says why on the standard error and returns `1`. What erases ghosts is not checked: the data has none left to erase | returns `1` with no input (it says on the standard error that the input is not the MIR as data) |
| `mir/mir_erase/mir_erase.tersus` | The ghosts of a program, erased by a program (REPLACING_HASKELL.md target 3): the shared reader of the package read as version 2 of the data (`tersus mir --ghost-data`: the types `block T` and `uninit T`, the statements `ghost` and `dissolve L`), then the ghost erasure the host runs on every program (through `MirHousekeeping`): the permissions out, each `Uninit<T>` made a `T`, and the refusal of the `Block::cast`s whose slots do not lay out alike. It reads the program before its ghosts are erased from the standard input and writes it as version 1 of the data, as `tersus mir --data` writes it | returns `1` with no input (it says on the standard error that the input is not the MIR as data) |
| `mir/emit/emit.tersus` | The lowering from the MIR to LLVM IR written in Tersus (step 31, `STEP31.md`), first part: it reads `tersus mir --data` from the standard input (with the shared reader of the package) and writes all of the IR of the program for every example and program of the native tests; for the argument `outline` the declarations of the runtime, the descriptors of the types and the entry point, and for `bodies` the code of each function. It is the compiler's only emitter: `build`, `run` and `llvm` use it (built on first use, see `Bootstrap`), and the IR it wrote for itself is the seed `bootstrap/emitter.ll`. Written as the Haskell emitter it replaced was, with its local `String::then` for the long strings it builds (a `concat` that promises nothing, which keeps the time to validate down) | returns `1` with no input |

```
stack run tersus-exe -- eval lib/mir/mir_reader/mir_reader.tersus   # with MIR data on stdin, writes it again
stack run tersus-exe -- check lib/mir/emit/emit.tersus              # prints OK
```

| File | Contents |
| --- | --- |
| `mir/reader/reader.tersus` | The MIR record types and parsers; imports the common token and type codec (`programAt` for version 1, `ghostProgramAt` for version 2 with `ghost`/`dissolve`). It declares only, and runs nothing |
| `mir/support/support.tersus` | Shared declaration lookup, variant ownership, array classification, primitive layout results, type/name rendering and LLVM escaping. Owns its result records and Clone impls; reuses the codec's `catStrings` for text construction. Imports the codec and reader; full layouts and wire writers are not shared |
| `mir/writer/writer.tersus` | Shared normalizing writer. `printProgram` writes MIR v1; `printProgramWithGhosts` writes MIR v2 with `ghost N` identities; `printProgramAsRead` writes MIR v1 with the `list` and `box` tokens of older data kept (the eraser's output). Structural type/size arguments and function metadata are retained |
| `mir/ownership/ownership.tersus` | Declarations-only request dispatcher imported by the emitter. `pass ownership` or `pass expand` followed by MIR v2 produces MIR v2. `isOwnershipRequest` and `runOwnership` dispatch to the algorithms in `rewrite` and `refwrites`; `common`, `analysis` and `drops` provide their shared data and analyses. The host retains the Haskell monomorphization adapter and metadata sidecars |
| `mir/mir_reader/mir_reader.tersus` | The round-trip entry: imports the shared reader and writer |
| `mir/emit/emit.tersus` | Emitter entry and program assembly. It writes LLVM IR for MIR v1, or dispatches `pass ownership` and `pass expand` requests over MIR v2 to the ownership module. The pinned emitter seed includes both passes |
| `mir/emit/types.tersus` | Emitter model, layouts, symbols, type closure and cached context; owns the module-local `String.then` |
| `mir/emit/values.tersus` | Generation state, memory primitives, constants, operands and reference places |
| `mir/emit/operations.tersus` | Arithmetic, array/address operations, rvalues, aggregate construction and statements |
| `mir/emit/functions.tersus` | Calls, terminators, blocks, function signatures and frames |
| `mir/emit/helpers.tersus` | Generated drop, clone and print functions |
| `mir/mir_verify/mir_verify.tersus` | The checker the host runs on every program: imports the reader |
| `mir/mir_erase/mir_erase.tersus` | The ghost erasure the host runs on every program: imports the reader and reads it with `ghostProgramAt` |

## Verification

`MirVerify.verifyProgram` checks a MIR for its shape (every block a jump names exists, every local and function used is declared, every local has a known type) and its types: each operation is applied to operands of the types it takes and gives the type of the local it is assigned to (`Add` takes two `Int`, `Get` takes a list of the result's type and an `Int`, `ReadField` reads a field that the constructor has, from a value of that constructor's type or one of its variants, a call has the callee's arity and parameter types, `SwitchBool` tests a `Bool`). Lowering gives the locals the types `elaborate` worked out, and native code built on a wrong type is a wrong program, so every lowering goes through the verifier, and so should every pass over the MIR.

## Validation

The validator is written in Tersus (`lib/validation/`, one root module with explicit sibling-file imports and `driver.tersus` as its only entry, compiled to native code by `ValidatorNative`), and `SelfHostedMir` translates the MIR into its data: each function is a list of `ExecutionBlock`s whose steps run over numbered terms, and `validateExecution` walks them with one state per path (the term each local holds and the facts known). Values never change, so an assignment gives the local a new term and a fact stays true for the rest of the path.

- **Reuse.** A verdict on a function is kept for the rest of the process under the data the bridge makes of it (its blocks, its contracts and the contracts of what it calls, the invariants of the types it makes and the rules it uses), so a verdict is reused only where it would be the same; `testValidationCache` checks hits and cached/uncached parity. See [README.md, Interpreter flow](README.md#interpreter-flow).
- **Container proofs.** Validation keeps the logical List/Box model: list facts come from operation contracts, and a Box has the value of its payload (the bridge leaves the library's physical `List` and Box structs out of what it reads, `SelfHostedMir.sourceContainerView`). The native library itself, `lib/lists.tersus` and `lib/box.tersus`, is validated with its physical layouts instead (`SelfHostedMir.encodeLibrary`): a List and a Box are the structs they are, with their invariants, an operation of the logical list or Box is refused there, and its generic functions are checked as written, for any type. Native code of the validator is made with the library, so the validator is built first without validation and then validates the library before it is used (`ValidatorNative.validatorExecutable`). A Box's own `addr` and `blk` are field functions of their own in the logical view only, so a payload field of the same name says nothing of them.
- **Statements.** An operation records what it establishes and checks what it needs (the contracts of the builtins, `StdLib`), as an application of the builtin to the terms of its operands. `Use` of a local gives the destination the same term. A `Call` terminator checks the callee's input contract and assumes its output contract (only the contract: the callee's body is neither run nor read for facts). `Ghost` statements read their names through their `Env`.
- **Edges.** A `SwitchBool` adds the truth of its condition to each edge's state, and the relation the condition compares (`a < b`; negated on the false edge). A constant condition has one edge.
- **Joins.** Where a boolean branch meets again the states are joined by `mergeStates` (a fresh term for a local that differs, the facts both paths establish rewritten to the joined terms, and the bounds both paths give a joined term); other branches are walked path by path.
- **Loops.** A header with a `LoopSpec` is checked by its invariant: the invariant on entry, the locals the loop assigns replaced by fresh terms with the invariant and the condition assumed, the region (the header and every block that can get back to it) walked once, and every edge back to the header must establish the invariant again and shrink the variant; an edge out of the region is walked after the loop. A condition of several tests joined by `&&` or `||` is checked as written. Invariants are inferred from what the entry state proves, each kept only where the loop preserves it.
- **Returns and functions.** `Return` checks the output contract on its path. Each function is checked on its own, from its input contract and the contracts of what it calls; a generic function is checked as the copies a call decides. A function that calls itself, alone or in a cycle, must say why it ends.

## Notes on the implementation

- A condition (of an `if` or a `while`) made of `&&`, `||` and `!` is lowered to a test for each part that is evaluated, each a `SwitchBool` to the next test or to the block of the whole condition (`MirLower.lowerCondition`); a Bool wanted as a value (`ok = a && b;`) is the same tests ending in two blocks that assign `true` and `false` to a temporary, so the tests of a chain know the ones before them (`i >= 0 && i < size(l) && get(l, i) = 0`). A `LoopSpec` therefore says which block is the first of the body (`loopBody`) and the validator starts an iteration (the variant is bounded below and kept) when that block is entered, once the ways in have met, and not on the true edge of a single test.

- Lowering takes each local's type from the expression types `elaborate` hands over with the program, so `x = []; x = push(x, 1)` gives `x` the type `List<Int>`. A type no use decided (a list that is only created) is `Int`.
- A function defined at the top of the program is found by name from the functions after it and from itself. In the scope that defines it, a function is a name that stands for the lifted function and is called by name, unless the program assigns that name elsewhere (`f = size;`): then it is a local that holds the function, assigned like any variable (so the nearest binding changes), and a call of it is a call of a local. The bodies of the functions at the top still find the original by name.
- A program has one return type, that of its first `return` (the checker rejects a later one of another type), so `_0` has one type.
- Falling off the end of `main` is a `Return` (a program may end without a value); falling off the end of any other function is `Unreachable`, which fails with `Function did not return a value`.
- Blocks nothing jumps to are dropped and the rest are numbered in the order a walk from the entry reaches them, so the printed MIR reads from the top.
- `Pipeline` runs the stages (parse, `elaborate`, lower, validate) and checks the program's types once: the lowering takes the result of `elaborate` (`lowerElaborated`) and the validator the MIR (`validateProgram`).
- A statement after a `return` is not lowered, so it is not validated either: nothing can run it, and a proof about it would be about no run.

## Open issues

- **Top-level `return` with no value** (`main` without one) leaves `_0` unassigned and `fnReturns = Nothing`.
- **Recursive types** (`Tree`) need a pointer in a native layout; the MIR only names them.
- **Mutual recursion** is ordinary in the MIR: `progFunctions` holds every function before validation, and the validator works out the call cycles from it.
