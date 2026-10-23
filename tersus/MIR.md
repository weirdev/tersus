# Tersus MIR (design)

Status: step 1 is implemented (`Mir.hs`, `MirLower.hs`, `MirEval.hs`; `tersus run` runs the MIR and `tersus mir` prints it). The later steps are listed under Phases so the data model is shaped for them.

```
today:    source -> AST -> validation -> concrete evaluation of the AST
step 1:   source -> AST -> validation -> MIR -> execution of the MIR
eventual: source -> AST -> MIR -> validation -> lowering to LLVM IR -> compilation -> execution
```

The MIR is to Tersus what Rust's MIR is to Rust: a typed control-flow graph that has no `if`, `while`, `match`, `for` or nested expressions left, only blocks of simple statements ending in a jump. The AST is what the programmer wrote and the validator reasons about; the MIR is what the machine will do.

## What the MIR has to represent

Facts about Tersus that decide the shape (all from the current `Proof.evaluate` and `Parse`):

- **Values are immutable and unaliased.** `push`/`set` return new lists; there is no heap to model, so a place is just a local. No projections, no borrows, no storage markers.
- **`match` and `for` are already desugared by the parser** into `if` chains over `Is` tests and `while` loops, so the MIR needs neither.
- **Functions are first-class but do not capture.** A body sees its parameters, the standard library and the top-level functions defined before it, so a nested `fn` lifts to a top-level MIR function with no environment.
- **Scopes decide which variable an assignment means** (`x = ...` updates the nearest enclosing `x`, else defines a new one in the current scope). Lowering resolves that once; the MIR has numbered locals and no scopes.
- **Partial operations have contracts the validator discharged** (`get` in range, `/` and `%` by non-zero, `first`/`last` of a non-empty list, `Cast`). The MIR keeps them as ordinary operations with documented preconditions, as `unreachable` would be in LLVM; the interpreter still checks them and reports an error, which turns any validator bug into a test failure instead of a wrong answer.
- **Proof-only constructs** (`affirm`, `define`, `rewrite`, `axiom`, `proof`, invariants, `shrinks`, contracts) have no run-time meaning. The eventual flow validates the MIR, so the model has somewhere to keep them (see Specifications); the executor ignores them.

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
- **Its own operator set**, not `BuiltinFunct`: `Within` is proof-only and `Cast` is the identity, and neither belongs in something that runs. `Ctor`, `Field`, `Project` and `Is` become `MakeData`, `ReadField` and `IsVariant`, which name the constructor (this is why locals are typed: a `Field Nothing f` in the AST says nothing about which struct, and a layout needs it).
- **Types on every local.** The AST erases types after checking, so lowering recomputes the type of each temporary bottom-up from the declared types of locals and parameters, the signatures of functions, the field types of structs and the builtins' result types (about 40 lines, and total on a program that checked). It does not change `TypeCheck`.
- **No panic or assert terminator for now.** Rust's MIR has `Assert` for overflow and bounds; here the validator proves those, so the MIR would either have to repeat them or drop them. Dropping them (as above) is the current semantics of an unchecked cast. Revisit when integers become bounded (see Open issues).

### Specifications (kept, inert)

```haskell
data FunctionSpec = FunctionSpec
    { specRequires    :: [ValidationStatement]   -- the input contract
    , specEnsures     :: [ValidationStatement]   -- the output contract
    , specTermination :: Maybe Termination       -- after `elaborate`: Counting, Parts or MayDiverge
    , specLoops       :: Map BlockId LoopSpec    -- by loop header
    }
data LoopSpec = LoopSpec { loopInvariant :: [ValidationStatement], loopTermination :: Maybe Termination }
data GhostStatement = GhostValidation ValidationStatement | GhostAxiom ... | GhostProof ...
```

They still mention source variable names (`ATerm "n"`), which `localName` resolves at a program point. Nothing reads them in step 1 except the pretty-printer and a test that lowering keeps them. The point of keeping them is that the model need not change when validation moves onto the MIR.

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

`MirEval.runProgram :: Program -> Result (Maybe MirValue) String`. A frame is the function's locals (a `Map`) and a current block; the loop is: run the statements, then follow the terminator; `Call` evaluates the callee operand (a `CFn name` is looked up in `progFunctions`) and recurses in Haskell. `MirValue` is `MInt | MBool | MList | MData | MFn Name`, so no value carries an AST. Run-time errors are the ones the AST evaluator has (`Division by zero`, `Get index out of range`, ...), which the validator is meant to make unreachable.

The AST evaluator (`Proof.evaluate`) stays: the validator uses it to learn the result of a call with known arguments (with its fuel budget), and it is the oracle the MIR executor is tested against.

## Changes to the flow

- `Cli.runSource`: parse, `validate`, **lower, run the MIR** (was: evaluate the AST). A lowering error is an internal error (a validated program always lowers) and is reported as `Lowering failed: ...`.
- A new command `tersus mir <file>` prints the MIR of a validated program (like `rustc --emit=mir`). It is how a lowering is read and tested.
- `tersus check` is unchanged.

## Tests

- **Differential**: every program in `examples/` and every test program that runs is executed by the AST evaluator and by lower-then-run, and the two return values must be equal (rendered the same).
- **Structure**: lowering a loop makes a back edge to its header, an `if` meets at one join, an early `return` in a branch leaves no edge to the join, a nested `fn` becomes a top-level function, shadowing and block-local variables get separate locals, a function passed as a value is a `CFn`.
- **Rendering**: `renderProgram` output for small programs (the one above, an `if`, a list/struct program), so a change to lowering shows as a diff.
- **Well-formedness** (`Mir.checkProgram`, which every lowering goes through and which fails the lowering): every `BlockId` a terminator names exists, every `Local` used is declared, only `Return`/`Unreachable` end a path, every local's type is known (no `TVar`).

## Phases

1. **This step**: the model, the renderer, lowering, the executor, the flow change, the tests and docs above.
2. Validation moves onto the MIR: the validator walks blocks instead of statement lists (the `if` join becomes a real join in the graph, the loop `LoopEnd` marker becomes the back edge to the header, nested-call contracts become the `Call` terminators). This is the large step and changes `Proof.hs`.
3. LLVM lowering: layouts for lists, structs and enums from `progTypes` and the local types; a bounded integer policy; memory management for values that are copied by `push`/`set`.

## Notes on the implementation

- Lowering takes the types by replaying the checker over the program (`TypeCheck.TC`, exported for the purpose), so `x = []; x = push(x, 1)` gives `x` the type `List<Int>`. A type no use decided (a list that is only created) is `Int`.
- A function defined at the top of the program is found by name from the functions after it and from itself (as the evaluator does through its global context); any other function is a name in its scope that stands for the lifted function.
- Falling off the end of `main` is a `Return` (a program may end without a value); falling off the end of any other function is `Unreachable`, which fails with `Function did not return a value` as the evaluator does.
- Blocks nothing jumps to are dropped and the rest are numbered in the order a walk from the entry reaches them, so the printed MIR reads from the top.
- `Proof.evaluate` stays for the validator; `checkExample` in the tests runs every example on both and compares the results, and `testMirRun` does so for a set of small programs including the ones that fail.

## Open issues

- **Integers are unbounded** (`Integer`) in both evaluators. Native code needs a width and an overflow story (proved away by the validator, or checked, or wrapping). The MIR does not decide this; `Add` and the others stay abstract until it is decided.
- **Top-level `return` with no value** (`main` without one) leaves `_0` unassigned and `fnReturns = Nothing`.
- **Recursive types** (`Tree`) need a pointer in a native layout; the MIR only names them.
- **Mutual recursion** does not exist in the language yet, so `progFunctions` needs no forward references.
