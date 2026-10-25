# Tersus MIR (design)

Status: steps 1 and 2 are implemented (`Mir.hs`, `MirLower.hs`, `MirVerify.hs`, `MirValidate.hs`, `MirEval.hs`; `tersus run` validates and runs the MIR and `tersus mir` prints it) and the lowering to LLVM IR has begun (`LlvmEmit.hs`, `tersus llvm` and `tersus build`; see Native code). The later steps are listed under Phases so the data model is shaped for them.

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
- **Functions are first-class but do not capture.** A body sees its parameters, the standard library and the top-level functions defined before it, so a nested `fn` lifts to a top-level MIR function with no environment.
- **Scopes decide which variable an assignment means** (`x = ...` updates the nearest enclosing `x`, else defines a new one in the current scope). Lowering resolves that once; the MIR has numbered locals and no scopes.
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

data BinOp  = Add | Sub | Mul | Div | Mod | Compare Rel      -- Div and Mod need a divisor /= 0; Compare Eq is structural
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

## Executing it

`MirEval.runProgram :: Program -> Result (Maybe MirValue) String`. A frame is the function's locals (a `Map`) and a current block; the loop is: run the statements, then follow the terminator; `Call` evaluates the callee operand (a `CFn name` is looked up in `progFunctions`) and recurses in Haskell. `MirValue` is `MInt | MBool | MList | MData | MFn Name`, so no value carries an AST. Run-time errors are `Division by zero`, `Get index out of range` and the like, which the validator is meant to make unreachable.

The validator does not run the MIR: a caller knows a callee by its contracts. There is no other evaluator: the AST is not executed.

## Changes to the flow

- `Cli.runSource`: parse, type check, **lower, validate the MIR, run the MIR** (step 1 validated the AST and then lowered it). A lowering error is an internal error (a program that type checks always lowers) and is reported as `Lowering failed: ...`.
- A new command `tersus mir <file>` prints the MIR of a validated program (like `rustc --emit=mir`). It is how a lowering is read and tested.
- `tersus check` parses, lowers and validates, as `run` does before it runs.

## Tests

- **Examples and programs**: every program in `examples/` is validated and run on the MIR and must give the value documented in the tests, and the small programs of `testMirRun` give the values written next to them (including the errors, `Division by zero` and `Integer overflow`).
- **Structure**: lowering a loop makes a back edge to its header, an `if` meets at one join, an early `return` in a branch leaves no edge to the join, a nested `fn` becomes a top-level function, shadowing and block-local variables get separate locals, a function passed as a value is a `CFn`.
- **Rendering**: `renderProgram` output for small programs (the one above, an `if`, a list/struct program), so a change to lowering shows as a diff.
- **Well-formedness** (`MirVerify.verifyProgram`, which every lowering goes through and which fails the lowering): every `BlockId` a terminator names exists, every `Local` used is declared, only `Return`/`Unreachable` end a path, every local's type is known (no `TVar`).

## Phases

1. **This step**: the model, the renderer, lowering, the executor, the flow change, the tests and docs above.
2. **Done**: validation moved onto the MIR (`MirValidate.hs`, `Ghost.hs`, `ProofState.hs`; see Validation), and the AST evaluator and the AST validator (`Proof.hs`) are gone.
3. **In progress**: LLVM lowering (`LlvmEmit.hs`, see Native code): steps 1 to 4 (`Int`, `Bool`, control flow, calls, lists, structs, enums, function values and memory management) are done. What is left (borrowing a value to a function that only reads it, deep recursion, contracts as hints to LLVM, cheaper ownership, and valgrind in CI) is in the roadmap of `README.md`, item 17.

## Arithmetic and traps

`Int` is a 64-bit signed integer (see LANGUAGE.md, Integers), and **`Add`, `Sub`, `Mul` and `Div` trap when the result does not fit**: the program stops with `Integer overflow`, as in native code built from LLVM's `llvm.sadd.with.overflow` and the like followed by a branch to a trap. The validator reasons about unbounded integers, so what it proves holds for the runs that do not trap. The MIR has no operation that wraps.

So an operation of the MIR either gives a value or traps. Two kinds of trap:

- **Overflow** is always checked, in the executor and in native code, because nothing proves it cannot happen.
- **A broken contract** (a divisor of 0, an index out of range, `first` of an empty list) cannot happen in a validated program. The executor still checks and reports it, so that a validator bug is a failure and not a wrong answer. Native code omits these checks (they are `unreachable` to LLVM).

`Unreachable` is the end of a function whose every path returned and is never executed. The validator rejects a function with a path that reaches it.

## Native code

`LlvmEmit.emitProgram` lowers a validated `Program` to LLVM IR as text; `tersus build` compiles it, with the C runtime of `LlvmRuntime` (embedded in the compiler; both are written to uniquely named files in the temporary directory, which are removed afterwards), with clang.

- **Locals are stack slots.** Each local is an `alloca` in the entry block, and a statement loads its operands and stores its result, so the blocks need no phis; `-O2` runs `mem2reg`, which builds them. A block is a label `bbN`, `Goto` and `SwitchBool` are `br`, `Return` loads `_0` and returns it, and `Unreachable` is `unreachable`. `Ghost` statements and the `FunctionSpec` are dropped.
- **Names.** A function of the program is `@"fn.<name>"` (internal, quoted, since a lifted function is named `outer::inner`), the statements of `main` are `@tersus_main` (names of the program may use any letter, so a name is written as its UTF-8 bytes, with every one that is not printable ASCII as `\hh`, and the file stays ASCII), and the C-level `main` calls that and prints the result by the descriptor of its type (`tersus_print`). A program can finish without returning on some path (`if c { return 1; };`), where `tersus run` prints nothing, so when `main` returns a value its function returns the value with a flag that says whether `_0` was assigned (kept in a slot that every assignment of `_0` sets), and the C-level `main` prints only then.
- **Types.** `Int` is `i64`, `Bool` is `i1`, and a list is a `ptr` to a heap object `{ rc, len, cap, elements }`: 24 bytes of header, then one 8-byte slot per element (an `Int`, a `Bool` as 0 or 1, or the `ptr` of an inner list), so that one runtime function serves every element type. `rc` is not used (see Ownership). A struct or an enum value is not a value of the heap but its words, held inline (see Data), and a `Box<T>` is a `ptr` to room on the heap for the words of the `T` it holds, so a type that contains itself holds its recursion in a pointer. A function value is the address of the function (`ptr @"fn.<name>"`), since functions capture nothing, and a call of a local is a call through that address with the parameter and result types of its `TFn`.
- **Lists.** `Length`, `First`, `Last` and `Get` are loads (`First` and `Last` of an empty list, and `Get` out of range, are assumed not to happen). `MakeList` and a constant list call `tersus_list_new` and store the elements, each time the statement runs, so that a constant is a value owned like any other when memory is managed in step 4. `Push` and `Set` call the runtime, which changes the list it is given (growing it by doubling when it is full, and freeing the element `Set` replaces); the list is the caller's to change because of what MirOwnership decided (see Ownership).
- **Arrays.** An array (`TArray element size`) is held inline: its elements are 8-byte words one after another in the slot of the local that has it (`alloca [N x i64]`), and an element that is an array is its words, in line, so `Array<Array<Int, 3>, 2>` is six words. The value of an array operand is the address of its first word. Assigning one is a `memcpy` into the slot of the destination (nothing when it is the same local), `NewArray` stores the element `N` times (a `memset` for a zero, a loop otherwise), `Set` copies the array if it is another local and stores the element (so `a = set(a, i, x)` is a store into the slot), and `Get` of a row copies the row. A literal (`CArray`) is a private constant global of the words, which is read and never written. A function gives an array as the address of the caller's words and copies it into its own slot at the start, so it cannot change the caller's, and an array result is written into room the caller gives as the first parameter (`sret`), which the caller makes the slot of the local that gets it; the entry function of a program that returns an array is given room by the C-level `main`, which prints from it. The runtime describes an array by a descriptor of kind 5, with its count and the descriptor of its elements, to compare and print it. An array is not a value of the heap, and the frame holds it for the life of the function; one of plain elements (Int, Bool, arrays of those) owns nothing, so MirOwnership never clones, moves or drops it, and one whose elements own something (lists, `Box`es, structs with them) is moved, cloned and dropped like a struct (`needsDrop`): `array(n, x)` clones `x` into each slot (`fillElements`) and `set` drops the element it replaces (`dropElement`) (an `alloca` is only in the entry block, so a loop does not grow the stack). An array can also be a field of a struct or an enum and an element of a list: a field is laid out by the words of its type, a list has a stride of the words of its element (`tersus_list_new_words`, `tersus_list_push_words`, `tersus_list_set_words`), and the runtime walks them by the descriptor of each type (`words`, and a slot is the word it holds, or for a value held inline the address of its words) to clone, free, compare and print.
- **Data.** A struct is held inline as the words of its fields in declaration order, with no tag, and an enum as a word that says the variant (its position in the enum) and then the fields of that variant, in the room of the widest variant: `slotsOf` gives the words of a type, a field or an element that is held inline is its words in line, and the value of one wherever a value is wanted is the address of its first word. `MakeData` writes the tag and the fields into the slot of the local that gets it, `ReadField` is a load at the offset of the field (from the slot of the local, or from the pointer that a `Box` holds, since a `Box` is looked into), `IsVariant` compares the tag, and `AsVariant` copies the words (a `Box` that is cast is taken out of its room, which is freed). A variant's fields are those of the variant, so reading a field of another variant is the undefined behaviour the validator keeps out. A constant `CData` is built in room of its own (made at the start of the function, so a loop does not grow the frame) each time it is wanted, since it can hold a list. A value held inline is given to a function as the address of the words, which the function copies, and a function that returns one writes it into room that the caller gives (`sret`); when the local that gets the result owns something, the room is one of the function's own and the local is given the value after what it held is freed. `MakeBox` takes room on the heap (`tersus_box_new`) and moves the words into it (a word is stored, the words of a value held inline are copied), and `Unbox` moves them out and frees the room (`tersus_box_free`).
- **Structs with types.** The name of a struct that has parameters carries the types as well as the sizes (`Vec<List<Int>, 3>`, and `Vec<'T, n>` in a function that has the type T and the size n; a ' marks a type parameter, and `typeText` and `readType` write and read a type), so the instance is declared from `progGenerics` by `completeInstances` and a copy of a function renames it by substituting the types and the sizes (`substitute`). `MirMono` finds the type of a parameter that is a struct by matching the arguments of the instance with those of the argument.
- **Type parameters.** A function with type parameters (`fnTypeParams`) has locals whose types can be `TParam`; the validator and the executor run it as it is (values have no types there), and `MirVerify` takes a `TParam` for any type. `MirMono` makes a copy for each list of types (and sizes) that a call gives: it finds the types by matching the types of the parameters of the callee with the types of the arguments, and its result with the local that gets it (`typeArguments`), defaulting to `Int`, and replaces `TParam` in the types of the copy (`substitute`). So `MirOwnership` and the native code see only concrete types, and know whether a value owns something.
- **Lent parameters.** A function lists the parameters it only reads in `fnBorrowed`, and in a type of a function value they are `TRef` (`fn(&List<Int>) -> Int`); the locals have the type without the `&`. `MirOwnership` does not move or clone an argument for a lent parameter (it is read, and a constant that owns something is made into a local first), never frees a lent parameter, and clones one that the function takes (`_0 = _1`, an argument for a parameter that is not lent). Natively a lent parameter held inline has no room of its own, the parameter is the address of the caller's words, and the result room of a call whose argument is the local that gets it is one of the function's own, since the callee does not copy what it reads.
- **Size parameters.** A function with size parameters (`fnSizeParams`) takes them as its last parameters, and its locals have types such as `Array<Int, n>`. The validator and the executor run it as it is. For native code `MirMono.monomorphize` (run first by `insertOwnership`) makes a copy of it for each list of constants that a call gives (`dot<3>`), with those parameters removed, the operands that read them the constants and the types' sizes replaced, and redirects the calls; the specifications and ghost statements are dropped, since they name the functions that are no longer there and only the validator reads them. A program with no function of the kind is left alone.
- **Structs with sizes.** A struct with sizes is declared in `progGenerics` and is a struct of its own, named by its sizes (`Packet<4>`), in `progTypes` for each one the program mentions (`completeInstances`); in a function with sizes the name has a size parameter in it (`Packet<n>`), and `MirMono` gives the copy for 4 the name `Packet<4>` in every type, constructor and constant, then declares what the copies mention and drops the declarations that name a size parameter. The names are printed without the sizes (`Packet { ... }`), and `MirEval` takes the struct for its name without them, so the executor can run a function with sizes as it is.
- **A Box of an array.** `size`, `get`, `first`, `last` and `set` on a `Box<Array<T, N>>` or `Box<Array<T, ?>>` are the `ListOp`s of an array: the elements are read through the address that the Box holds in its first word (`arrayPtr`), and the length is the constant of the type or, for a Box of an array of no size, the word after the address. `Set` writes the element where it is and gives the Box back (the operand is moved, so nothing else has it). A `Box<Array<T, ?>>` (`isFat`) is two words held inline, as a struct is: the address of room on the heap and the number of elements, with kind 7 in the runtime (`tersus_drop` frees the room, `tersus_clone` makes room and copies, equality and printing go by the length). `ListOp NewBoxed n x` (`Array::boxed(n, x)`) takes room for `n` elements and fills it (the loop of `NewArray`, with a count that is a value), and `Unsize` stores the address of a `Box<Array<T, N>>` and the constant `N`; both are the same value to the validator and the executor as the array they stand for, which is why the validator gives `NewBoxed` the contract of `NewArray` and treats `Unsize` like `MakeBox`.
- **Descriptors.** The runtime prints and compares values by the descriptor of their type: a constant global `@"type.List<Int>"` of `{ kind, aux }` for each type the program uses (and each type inside it, so a type that contains itself is there once): `aux` is the descriptor of the elements of a list, or the variants of a struct or an enum (each with its name, written `Enum::Variant`, and the names and descriptors of its fields). Equality (`Compare Eq` and `NotEq`, structural) and the printing of the result are then written once, in C, and print a value as `renderMirValue` does. A value of a variant (`TVariant`) has the descriptor of its enum. Step 4 adds how to free a value of the type.
- **Memory** is managed by ownership, decided on the MIR (see Ownership): nothing is counted at run time, and a value is freed when its owner lets go of it.
- **Arithmetic.** `Add`, `Sub` and `Mul` are `llvm.s{add,sub,mul}.with.overflow.i64` followed by a branch to the function's `overflow` block, which calls `tersus_overflow` (the message `Evaluation failed: Integer overflow` and exit status 1 of `tersus run`). `Div` rounds down, where `sdiv` truncates, so it subtracts 1 from the quotient when the remainder is not 0 and has the other sign than the divisor, and the one quotient that does not fit (the smallest `Int` divided by -1) goes to the overflow block. `Mod` takes the sign of the divisor, with `srem` by 1 in place of -1, which `srem` leaves undefined for the smallest `Int`, and the result 0 that follows.
- **Contracts are not checked.** A divisor that is not 0, an index in range, a list that is not empty are what validation proved, and the operations assume them as `unreachable` would (`sdiv` by 0 is undefined in LLVM). A bug in the validator is undefined behaviour in native code, where `tersus run` reports it. Overflow is the one trap, since nothing proves it cannot happen.
- **Tests.** `TestNative` builds programs and compares what the executable prints, and its exit status, with `tersus run` (every example, structs, enums and lists and their operations, divisions of every sign, loops, recursion, and each overflow; calls of function values are lowered without validation, since the validator cannot follow them yet); the builds pass without clang.

## Ownership

Native code frees what a program makes and changes lists in place, so `MirOwnership.insertOwnership` (run by `emitProgram`, after validation, and printed by `tersus owned`) rewrites the MIR to say who owns every value that has something to free: a list, a `Box`, and a struct, an enum or an array that holds one (`needsDrop`). A value that owns nothing (a number, and a struct, an enum or an array of them) is plain, and is copied where it is wanted. The result still means the same thing: `MirEval` runs it and gives the same answers, with `Move` as a `Copy`, `Clone` as a `Use`, and `Drop` as nothing.

**The invariant** is that what a value owns (a list or a `Box`, which are on the heap) has exactly one owner: a local, a word of another value (a field, or an element of a list), or a temporary on its way somewhere. So the heap is a forest, a value is freed with what is in it, a copy is a deep copy that shares nothing, and `push` and `set` may change the list they are given when it is theirs. A struct or an enum that holds one is held inline and owns it through its words, so it is moved, copied and dropped like a list: a `Move` copies the words to where they go and clears them where they were, `Clone` is a deep copy, and a `Drop` frees what the words own. The language is unchanged: where a value is wanted by two, one gets a copy, which is what `push` did before.

**What an operand does** decides what happens to the local it names:

| The operand | The local |
|---|---|
| reads the value: `size`, `==`, `is`, the list of a `get` | nothing |
| takes it: `y = x`, the list and the element of `push`/`set`, a field of a list or struct that is made, an argument of a call, `_0` | `Move x` when it is not used again (`x` is left holding nothing), and otherwise a `Clone` of it |

A local that is given a value frees the one it held (assigning null does nothing), and `Drop` frees all that a function owns when it returns. A local that holds nothing is a null pointer (or, for a value held inline, cleared words, which a drop frees nothing of), and the pass needs no analysis of which locals might have been moved from. Every parameter is owned by the function, which frees it unless it moved it, and a function returns what it owns, so a call looks the same whichever function it is, including one reached through a function value. Two arguments that are the same local are a copy for all but the last.

**A part of a value** (`get`, `first`, `last`, a field) is part of what contains it:

- A field of a value that is not used again is taken out of it (`TakeField`; what is left of the value is freed with it). This is what makes a `match` on a tree not copy the tree: the fields are taken from the scrutinee one by one. The check is by field: a field is taken when neither it nor the whole value is used later (the tag, read by `is`, does not count).
- A temporary that is only read, by statements that follow it in its block, with nothing in between that takes, changes or gives away what it was read from, `Peek`s: it holds the pointer and owns nothing, so it costs nothing and is not freed. `(x as V).f` and `size(get(rows, i))` are like this. A cast is first forwarded to the reads that follow it, so that they read the value itself.
- Otherwise it is a `Clone` of the part, made where the part is read.

**What this costs.** A call with an argument that is used afterwards copies the argument (every parameter is owned, so there is no way to lend a value yet), and a part that is kept (`row = get(rows, i)`) copies the part. `out = push(out, x)` in a loop, `set` in a loop, and a recursion that takes a value apart copy nothing. A list that is built by pushing costs time and memory in proportion to its length (50,000 pushes took 38 seconds and 9.8 GB when each copied the list, and 5 million take 40 ms in a process limited to 200 MB).

**How it is checked.** `TestOwnership` runs the owned MIR on a model of the heap that fails on a value used after it is moved from or freed, freed twice, looked at after it changed, changed in place while another place holds it, or left on the heap when the program ends, and compares the answer with the executor's. It runs every example and every program of the native tests, and the model is shown to catch the mistakes it exists for (MIR written by hand with each). `TestNative` builds every program with `-DTERSUS_CHECK`, which makes the runtime record each block (a block that is freed twice or left at the end is an error, and one that is freed is filled with 0xDD and kept so that a use of it reads that), and runs some of them under valgrind as well. When this was written, a generator of random programs over lists, nested lists, structs and enums (a script that is not in the repository) found no difference on the model or natively.

## Verification

`MirVerify.verifyProgram` checks a MIR for its shape (every block a jump names exists, every local and function used is declared, every local has a known type) and its types: each operation is applied to operands of the types it takes and gives the type of the local it is assigned to (`Add` takes two `Int`, `Get` takes a list of the result's type and an `Int`, `ReadField` reads a field that the constructor has, from a value of that constructor's type or one of its variants, a call has the callee's arity and parameter types, `SwitchBool` tests a `Bool`). Lowering gives the locals their types by replaying the checker, which is a second copy of its rules, and native code built on a wrong type is a wrong program, so every lowering goes through the verifier, and so should every pass over the MIR.

## Validation

`MirValidate.validateProgram` walks the control-flow graph of each function with one state per path (`ProofState.PState`: which iota each local holds, the facts, the rules, and the solver of the facts). Values never change, so an assignment gives the local a new iota and a fact stays true for the rest of the path.

- **Statements.** `Assign` of an operation is a call of the builtin it stands for (`rvalueCall`): the arguments are the iotas of the operand locals, so the builtin's input contract is checked against what the path knows and its output facts are about the locals themselves. `Use` of a local gives the destination the same iota. A `Call` terminator does the same with the callee's contract (`Ghost.applyCall`) (only the contract: the callee's body is neither run nor read for facts). `Ghost` statements read their names through their `Env`.
- **Edges.** A `SwitchBool` adds the truth of its condition to each edge's state, and the relation the condition compares (`a < b`; negated on the false edge). A constant condition has one edge.
- **Joins.** The blocks are walked in reverse postorder, so every forward edge into a block has been walked when it is reached. The states that meet are joined by `mergeStates` (a fresh iota for a local that differs, each fact kept if every path establishes it, a path with contradictory facts ignored); the facts the next statements ask for (`affirm`s, invariants, the output contract about the value being returned) are tried as well.
- **Loops.** A header with a `LoopSpec` is entered once (`enterLoop`): its termination clause and the invariant on entry are checked, the locals the loop assigns get fresh iotas, and the loop's blocks (the natural loop: the header and every block that reaches a back edge) are walked as a region with the invariant assumed. An edge back to the header must establish the invariant and the variant; an edge out of the region is an edge of the walk that contained the loop. Nested loops are regions of regions. Invariants are inferred by walking the region with candidates assumed and dropping those not preserved.
- **Returns and functions.** `Return` checks the output contract on its path. A function is validated where `GhostFunction` defines it, from the facts that hold everywhere (the standard library and the functions at the top), with its input contract assumed; what it promises is what the join of its returns says of the parameters (as they were on entry) and the result. A function at the top can call itself with its output contract assumed. A function can be called only after its definition, because it is known only after the marker.
- **Not in the MIR.** A statement after a `return` is not lowered, and a function that is never defined by a reachable statement is not checked.

## Notes on the implementation

- Lowering takes the types by replaying the checker over the program (`TypeCheck.TC`, exported for the purpose), so `x = []; x = push(x, 1)` gives `x` the type `List<Int>`. A type no use decided (a list that is only created) is `Int`.
- A function defined at the top of the program is found by name from the functions after it and from itself. In the scope that defines it, a function is a name that stands for the lifted function and is called by name, unless the program assigns that name elsewhere (`f = size;`): then it is a local that holds the function, assigned like any variable (so the nearest binding changes), and a call of it is a call of a local. The bodies of the functions at the top still find the original by name.
- A program has one return type, that of its first `return` (the checker rejects a later one of another type), so `_0` has one type.
- Falling off the end of `main` is a `Return` (a program may end without a value); falling off the end of any other function is `Unreachable`, which fails with `Function did not return a value`.
- Blocks nothing jumps to are dropped and the rest are numbered in the order a walk from the entry reaches them, so the printed MIR reads from the top.
- `Pipeline` runs the stages (parse, `elaborate`, lower, validate) and checks the program's types once: the lowering takes the result of `elaborate` (`lowerElaborated`) and the validator the MIR (`validateProgram`).
- A statement after a `return` is not lowered, so it is not validated either: nothing can run it, and a proof about it would be about no run.

## Open issues

- **Top-level `return` with no value** (`main` without one) leaves `_0` unassigned and `fnReturns = Nothing`.
- **Recursive types** (`Tree`) need a pointer in a native layout; the MIR only names them.
- **Mutual recursion** does not exist in the language yet, so `progFunctions` needs no forward references.
