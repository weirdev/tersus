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
    { localType :: Type                     -- the checker's types: TInt, TBool, TList, TFn, TNamed, TVariant
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
    | MakeData Name [(Variable, Operand)]   -- a struct or an enum variant (named Enum::Variant), fields in declaration order
    | ReadField Operand Name Variable       -- field of a value known to be that constructor (Field, Project and Cast fused)
    | IsVariant Operand Name
    | AsVariant Operand Name                -- the same value, known to be that variant (`value as Enum::Variant`); gives the local the variant's type

data BinOp  = Add | Sub | Mul | Div | Mod | Compare Rel      -- Div and Mod need a divisor /= 0; Compare Eq is structural
data ListOp = Length | First | Last | Get | Push | Set       -- First and Last need a non-empty list, Get and Set an index in range

data Operand = Copy Local | Const Constant
data Constant
    = CInt Integer | CBool Bool | CList [Constant] | CData Name [(Variable, Constant)]
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

`MirEval.callWithFuel` runs one function on a budget of steps (a statement or a jump each): the validator uses it to learn the result of a call with known arguments. There is no other evaluator: the AST is not executed.

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
3. **In progress**: LLVM lowering (`LlvmEmit.hs`, see Native code): steps 1 and 2 (`Int`, `Bool`, control flow, calls, and lists) are done; structs and enums, function values, and memory management follow.

## Arithmetic and traps

`Int` is a 64-bit signed integer (see LANGUAGE.md, Integers), and **`Add`, `Sub`, `Mul` and `Div` trap when the result does not fit**: the program stops with `Integer overflow`, as in native code built from LLVM's `llvm.sadd.with.overflow` and the like followed by a branch to a trap. The validator reasons about unbounded integers, so what it proves holds for the runs that do not trap. The MIR has no operation that wraps.

So an operation of the MIR either gives a value or traps. Two kinds of trap:

- **Overflow** is always checked, in the executor and in native code, because nothing proves it cannot happen.
- **A broken contract** (a divisor of 0, an index out of range, `first` of an empty list) cannot happen in a validated program. The executor still checks and reports it, so that a validator bug is a failure and not a wrong answer. Native code omits these checks (they are `unreachable` to LLVM).

`Unreachable` is the end of a function whose every path returned and is never executed. The validator rejects a function with a path that reaches it.

## Native code

`LlvmEmit.emitProgram` lowers a validated `Program` to LLVM IR as text; `tersus build` compiles it, with the C runtime of `LlvmRuntime` (embedded in the compiler; both are written to uniquely named files in the temporary directory, which are removed afterwards), with clang.

- **Locals are stack slots.** Each local is an `alloca` in the entry block, and a statement loads its operands and stores its result, so the blocks need no phis; `-O2` runs `mem2reg`, which builds them. A block is a label `bbN`, `Goto` and `SwitchBool` are `br`, `Return` loads `_0` and returns it, and `Unreachable` is `unreachable`. `Ghost` statements and the `FunctionSpec` are dropped.
- **Names.** A function of the program is `@"fn.<name>"` (internal, quoted, since a lifted function is named `outer::inner`), the statements of `main` are `@tersus_main`, and the C-level `main` calls that and prints the result by the descriptor of its type (`tersus_print`). A program can finish without returning on some path (`if c { return 1; };`), where `tersus run` prints nothing, so when `main` returns a value its function returns the value with a flag that says whether `_0` was assigned (kept in a slot that every assignment of `_0` sets), and the C-level `main` prints only then.
- **Types.** `Int` is `i64`, `Bool` is `i1`, and a list is a `ptr` to a heap object `{ rc, len, cap, elements }`: 24 bytes of header, then one 8-byte slot per element (an `Int`, a `Bool` as 0 or 1, or the `ptr` of an inner list), so that one runtime function serves every element type. `rc` is the reference count of step 4 and unused until then. Structs, enums and function values are refused for now (`Native code does not support Node yet`). The plan for data: a pointer to `{ rc, tag, fields }` with each field a slot, a variant's tag being its position in the declaration; a function value is a bare function pointer (functions capture nothing).
- **Lists.** `Length`, `First`, `Last` and `Get` are loads (`First` and `Last` of an empty list, and `Get` out of range, are assumed not to happen). `MakeList` and a constant list call `tersus_list_new` and store the elements, each time the statement runs, so that a constant is a value owned like any other when memory is managed in step 4. `Push` and `Set` call the runtime, which copies the list (a list is a value, so the argument keeps its elements) and leaks the old one for now. The type of a list the code needs is the type of the local it is for, since a constant `[]` does not say what it holds.
- **Descriptors.** The runtime prints and compares values by the descriptor of their type: a constant global `@"type.List<Int>"` of `{ kind, element descriptor }` for each type the program uses, so that equality (`Compare Eq` and `NotEq` of lists, structural) and the printing of the result are written once, in C. Step 3 adds the fields and variants of data to it, and step 4 how to free a value of the type.
- **Memory** is leaked until step 4: reference counts, the last use of a local moving it, and `push`/`set` updating in place when a list is not shared.
- **Arithmetic.** `Add`, `Sub` and `Mul` are `llvm.s{add,sub,mul}.with.overflow.i64` followed by a branch to the function's `overflow` block, which calls `tersus_overflow` (the message `Evaluation failed: Integer overflow` and exit status 1 of `tersus run`). `Div` rounds down, where `sdiv` truncates, so it subtracts 1 from the quotient when the remainder is not 0 and has the other sign than the divisor, and the one quotient that does not fit (the smallest `Int` divided by -1) goes to the overflow block. `Mod` takes the sign of the divisor, with `srem` by 1 in place of -1, which `srem` leaves undefined for the smallest `Int`, and the result 0 that follows.
- **Contracts are not checked.** A divisor that is not 0, an index in range, a list that is not empty are what validation proved, and the operations assume them as `unreachable` would (`sdiv` by 0 is undefined in LLVM). A bug in the validator is undefined behaviour in native code, where `tersus run` reports it. Overflow is the one trap, since nothing proves it cannot happen.
- **Tests.** `TestNative` builds programs and compares what the executable prints, and its exit status, with `tersus run` (the examples that use only supported types, lists and their operations, divisions of every sign, loops, recursion, and each overflow); the builds pass without clang.

## Verification

`MirVerify.verifyProgram` checks a MIR for its shape (every block a jump names exists, every local and function used is declared, every local has a known type) and its types: each operation is applied to operands of the types it takes and gives the type of the local it is assigned to (`Add` takes two `Int`, `Get` takes a list of the result's type and an `Int`, `ReadField` reads a field that the constructor has, from a value of that constructor's type or one of its variants, a call has the callee's arity and parameter types, `SwitchBool` tests a `Bool`). Lowering gives the locals their types by replaying the checker, which is a second copy of its rules, and native code built on a wrong type is a wrong program, so every lowering goes through the verifier, and so should every pass over the MIR.

## Validation

`MirValidate.validateProgram` walks the control-flow graph of each function with one state per path (`ProofState.PState`: which iota each local holds, the facts, the rules, and the solver of the facts). Values never change, so an assignment gives the local a new iota and a fact stays true for the rest of the path.

- **Statements.** `Assign` of an operation is a call of the builtin it stands for (`rvalueCall`): the arguments are the iotas of the operand locals, so the builtin's input contract is checked against what the path knows and its output facts are about the locals themselves. `Use` of a local gives the destination the same iota. A `Call` terminator does the same with the callee's contract (`Ghost.applyCall`), and when the arguments are known the callee is run on a budget (`MirEval.callWithFuel`) for its result. `Ghost` statements read their names through their `Env`.
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
