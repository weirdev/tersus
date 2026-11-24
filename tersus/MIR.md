# Tersus MIR (design)

Status: steps 1 and 2 are implemented (`Mir.hs`, the lowering in the elaborator written in Tersus (`lib/elaborate/lower*.tersus`), the checker written in Tersus run by `MirHousekeeping`, the validator package `lib/validation/` with its bridge `SelfHostedMir`, `MirEval.hs`; `tersus eval` validates and runs the MIR, `tersus run` validates, compiles and runs the native code, and `tersus mir` prints it) and the lowering to LLVM IR is written in Tersus (`lib/mir/emit/emit.tersus`, `tersus llvm` and `tersus build`; see Native code). The later steps are listed under Phases so the data model is shaped for them.

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
- **Scopes decide which variable an assignment means** (`x = ...` updates the nearest enclosing `x`, else defines a new one in the current scope). `let` always declares a fresh binding; the elaborator (`localScopes`) separates its identity from shadowed bindings before checking reference provenance. Lowering resolves bindings once; the MIR has numbered locals and no lexical scopes.
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

Each module is lowered separately (by the elaborator, seeded with stub functions and type declarations from the interfaces of its direct imports, `Interface`), and `Link.linkPrograms` merges the units: type, generic-struct and invariant maps and the function map are keyed by canonical name, `progMain` is the entry module's, and the `GhostFunction` statements of the dependency units are prepended to the entry `progMain`, so the validator learns an imported function at a definition before the entry program that calls it. The same name defined by two units with different definitions is a link error naming both modules. Two copies of the same unit (a compiler-library unit selected by several modules) are deduplicated by unit identity; a definition identical to the one already linked merges, as does an `extern fn` whose signature and contract agree (compared by signature, not body). Compiler-library units keep their bare names (`String`, `HashMap`, `<String>::concat` and the like), so a user declaration colliding with a library name is such a link error. `Link.pruneProgram` then keeps only what the entry program reaches: functions and types named from `progMain` through calls (including function values), fields, locals and returns, the functions a kept contract names, the functions a ghost expression reaches through a conditional's branches, a block expression's statements and result, and an ascribed expression (an ascription's type is not an expression), and the drop and trait-impl functions of kept types. That is what a selective import links: visibility is limited at the import site, and linking is limited by reachability. The copy step (below) runs at the end of linking, and monomorphization (`MirMono`), validation, ghost erasure and the later passes run once on the linked program, unchanged.

## The native linking host

`Link.hs` sends the merge, environment-completion and pruning requests to
`lib/mir/link/` through the pinned emitter seed, avoiding a bootstrap cycle
through stage 1. `pass link` is followed by `merge N` and N units, each
`unit "package" none LINES` or `unit "package" some "module" LINES` followed
by that many MIR3 lines, or by `prune` or `environments` and one MIR3 program.
The answer is raw complete MIR3, or `1` with a refusal on stderr. The same
emitter retains `pass mono`; there is no second carrier or metadata sidecar.

The linker preserves the root main's entire original specification and loop
environments while completing its ghosts. Dependency ghosts follow numeric
block order. The host still runs `makeCopies (completeInstances ...)` after
the merge, with the existing `Validation failed: ` error prefix. Pruning uses
local processed-name sets to visit immutable function/type edge sources once,
without changing reachability, implementation discovery or metadata scrubbing.

## The copy step (functions with bounds)

The elaborator checks the body of a function with bounds once, against its bounds alone (LANGUAGE.md, Bounded types), and hands it back with its type parameters as parameters: a `BoundedDef` after the module's statements, with its expression types after the module's (AST_DATA.md). A call names the copy it needs (`total[List<Int>]`, the types rendered as an instance writes them, then the sizes its bounds name), and an `Instance` record says what each such name stands for: the function with bounds and its type and size arguments, which may name the type parameters of the function with bounds that makes the call (`count['T]`), and the copy's signature. A call through a bound is a call of `<$param T as Tr>::g`, and an `Instance` with no function gives its signature (the trait function's, with `Self` the parameter and the trait's parameters the bound's types; one of the prelude's `Sequence` or `Growable` that a builtin has is marked `$builtin`).

The lowering lowers a `BoundedDef` like any function with type parameters and records it in `progBounded` (the sizes its bounds name, its parameters bounded by `Copy`, and the functions lifted out of its body); an `Instance` is a stub of its signature while the program is lowered, which calls and proof terms name, recorded in `progInstances`. The check of moves covers the generic body once: a value of a type parameter is moved unless a bound makes the parameter `Copy`, and a call through a bound lends and gives `from` as the trait function's signature says. The stubs are not part of the unit.

`MirCopies.makeCopies` runs where a whole program first exists: at the end of `Link.linkPrograms`, and of `Lowering.finishProgram` for a program lowered on its own. From the roots (`main` and every function that is not a function with bounds or lifted out of one) it follows the copies the program names, keyed by function, types and bounded sizes, and makes each from the generic MIR: the types and the bounded sizes are put in (a bounded size stays a parameter, which the callers give, and a read of it is the constant), the struct instances it builds are named for its types, its references (call heads, function constants, proof terms) are renamed to the copies they name and those are made in turn, and its lifted functions are copied with it. The check of a bounded trait impl's function against its trait is made with each copy of the function. A call through a bound is made what the type gives, as the elaborator writes it for the type: `clone(x)` and `x.clone()` of a value of a type parameter (a copy, `CopyOf`, in the body) copy a word, an address, a function and a reference as they are, whatever impls of a trait named `Clone` the program has, and clone any other type as `Clone::clone` does; `Clone::clone` is the type's `Clone` impl (a tuple is copied as it is, and a Box of an array of no size is the library's `cloneBoxedArray` when the program has it); `Eq::eq` of words a comparison (`BinaryOp (Compare Eq)`), of a Box of an array of no size `eqBoxedArrays`; a `$builtin` sequence function of a list, an array or a Box of an array the prelude's impl of it, through its check function like any impl (but `size` and `get` the impl's functions, the builtins that the trait's contracts of those impls name); anything else the check function of the type's impl of the trait, `Tr for O::g`, which has the trait's contracts and whose body calls the impl's function (a copy of it when the impl has bounds, its types worked out from the call's operands and destination; an impl's function with no check function is an internal error), so a copy knows of the call only what the trait promises; the contracts of a check function name the check functions of the same impl, and the validator takes a check function as its impl's function, one value with two contracts, the impl's contract given only outside the body of a copy (`SelfHostedMir.validatorSymbol`), given the sizes the arguments' types decide for its size parameters; a sequence function that no impl gives is the builtin, and so are those of a Box of an array of a size, which the prelude's impl (for one of no size) does not cover. A local of a copy whose type in the body is a type parameter the copy fills, or reaches one through a reference or a Box (`T`, `&T`, `&mut T`, `Box<T>`), is opaque to the copy's proofs: the copy step marks it in the copy's environment (`$opaque <n>`, `MirCopies.opaqueKey`, dropped when ghosts are erased) and the validator gives it no facts of its type (`typeSteps`, whose facts reach into a part of a type only through a reference or a Box), so a copy proves no more of such a value than the generic body does. A copy for a bigger type than the same function's copy that needs it is refused (`f calls itself with the types ...`), and so is a copy with an array too big for a frame, its words counted as the elaborator counts them for an array of a type it knows (`typeWords`: a list four, a Box two; `f cannot be made as f[...] for this call: ...`); a refusal is the program's, `Validation failed:` as the elaborator's. Two gaps are older than the copy step and kept by it: native code holds a Box of an array of a size in more words than `typeWords` counts for it, so an array of them near the limit runs in the reference interpreter and is refused by the ownership pass of native lowering; and the element `replace` takes out of a list is a copy (`CopyOf`), which native code makes with the type's `Clone` impl and the reference interpreter makes as it is, so with an impl that does not give the same value the two disagree in concrete code (a copy of a function with bounds calls the impl in both). A copy is not validated, but it is marked `~` (`MirCopies.divergingCopies`) when it calls a function that may not end, which a call through a bound can be (an impl's function written `~`, or a closure's), or a copy so marked, so the validator refuses a caller that has to end. Each copy is defined (its `GhostFunction` marker) where `main` starts, so a program linked from units and the same program lowered whole have the same MIR, and both tables are emptied, so nothing after the step sees them. A program with none is returned as it is.

The functions with bounds are kept beside their copies (those of the compiler's libraries where the program uses them: a copy of one is made, or a body kept generic names it generically; `makeCopiesWith`), generic, for the validator, which checks each of them once in place of its copies (`MirCopies.finish`), and are dropped once it has (`withoutGeneric`, before the ghosts are erased): a generic body is marked `$generic` in its environment and keeps its marker where it was defined, and its copies (and their lifted functions) are marked `$covered`, which `SelfHostedMir.encodeMono` skips; both marks go with the ghosts. In a generic body a call through a bound, `<$param T as Tr>::g`, is a call of the trait's stub `Tr for $Self::g`, which the elaborator writes for each function of each trait (`traitStub`, `lib/elaborate/traits.tersus`): a function with bounds on `Self` (and the trait's types, and the traits whose functions the contracts call) with the trait's contract, whose body is the call through the bound; the validator takes every stub of one trait function as one function, `<$Self as Tr>::g` (as it takes a check function as its impl's), and never checks a stub. A reference to a copy whose types are not known names the generic callee, and one whose types are known the copy, which the step makes whether or not anything else calls it. A bounded trait impl's check function is such a body too, so an impl is checked against its trait once, for every type. What a copy calls through a bound meets the stub's contract: an impl's check function is checked against the trait, a comparison and a copy of words and `eqBoxedArrays` give what the library's `Eq` and `Clone` promise, `cloneBoxedArray` promises its result is its argument, and the builtins a copy calls for the library's `Sequence` on a Box of an array of a size are checked once, in the prelude, by functions generic in the element and the size whose bodies are the builtins and whose contracts are the trait's (`sizedBoxedSize`, `sizedBoxedGet`, `sizedBoxedSet`). A generic body's proofs name the functions there are, as a copy's do (`proofsNamed`), so its environment has no names of copies or bounds. This holds only while a program cannot declare a trait of the library's name or impl the library's traits for the types the language gives them for. A variadic function is validated generically too (`MirCopies.variadicBody`): its pack is a list of its arguments (`List<..T>`), a read of it at a number a `get`, a loop over it (`PackLoop`) a loop whose `LoopSpec` holds the bounds of its index, `lo <= i <= max(lo, hi)` (worked out before the loop, so a range that may be empty needs no guard), with the invariant the program wrote on it, if any, and whose measure is `max(lo, hi) - i`, a forward the call of the generic callee with the elements `<$packslice>` gives (`0 <= lo <= hi <= size(xs)` in, the slice out), and a function that calls itself with none is measured by `size(args)`; a read of the pack in a validation statement or a loop invariant is checked in range (an invariant's read by an invariant of its own), a `forall`'s for every index it ranges over, and so are the reads of its contracts, by a function of their own the validator checks beside the body (`f$contract`, `MirCopies.packContracts`): an input contract's under the input contract before it, an output contract's under the input contract and the output contract before it, with the result a parameter. Lowering gives a loop over the pack the `LoopSpec` of the invariant the program wrote, which each copy drops as it unrolls the loop (`MirPacks.expandPack`). Generic bodies and stubs are generic functions nothing concrete calls, so `MirMono` drops them before native code.

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

### Copies of variadic functions

A variadic function (LANGUAGE.md, "Variadic functions") is a function with bounds whose type parameters include a pack `..T`, and its last parameter (before its sizes) is the pack, a local of type `..T`. Its generic body uses the pack only through MIR it already has: `size(args)` is `ListOp Length [args]`, `get(args, k)` at a number `ReadField args "$pack" "k"` (and a borrow of it `Borrow args [RefField "$pack" "k"]`), at any other index `ListOp Get [args, i]`. So the check of moves needs one rule of its own, that `size(args)` reads no element of the pack (it is a number in each copy), and otherwise none: an element at a number is a field of the pack, a place of its own that a pack taken by value can give away once and a lent pack cannot; an element at another index is a list element, which is read and not moved; an element's type `..T#k` or `..T@n` is `Copy` when a bound makes `..T` `Copy`. A loop over the pack (`PackLoop`) is lowered as a counting loop with the `LoopSpec` of its written invariant (none when it has none), its element read at the index (a range loop names none and reads none), or, for a loop that takes the elements, a fresh value after the pack is moved into a temporary before the loop; `BoundedFn.boundedPackLoops` records its blocks and locals for the copy step.

A copy of it is named and keyed by the fixed types and then one type per argument (`total[Int, Bool]`, `total[]`), so the growth refusal counts the arguments' types. `MirPacks.expandPack` makes it from the generic MIR before the types are put in: the pack parameter becomes one parameter per argument, `args 0` ... of types `..T#0` ..., lent when the pack is; each loop over the pack, outermost first, becomes a copy of its body blocks and locals for each index, the index read as the number, the element as the parameter at it, and the loop's element type bound to that argument's type in the blocks and locals of the iteration; a local assigned once from a constant, arithmetic on such or `size(args)` is known, a `SwitchBool` on a known Bool is a jump, and blocks nothing reaches go, so a branch the copy does not take never names a copy or an obligation; then `size(args)` is the number and `get(args, k)` the parameter at `k` (a local only it assigns is renamed to the parameter), and a `get` out of range in a block the copy runs ends the block with the ghost assertion `k < N` (and the assumption `0 = 1`, so nothing after it is checked), which the validator refuses unless the path is ruled out; blocks nothing reaches any more then go. An element read at an index that is not a number has a type of its own, `..T@n`, which is bound to the type of the argument its index comes to, in the blocks and locals of that iteration and of the iterations inside it. A local is folded, or renamed to a parameter, only when it is assigned once and never borrowed. A function defined in the body of a loop over the pack is defined where the loop starts, and one defined only in blocks that go is defined at the start of the copy. A name a define in the body of a loop over the pack gives is a name of its own in each iteration (`m in iteration 1`), since the validator keeps one definition of a name; it is read as that name where the body's define comes first (earlier in the block, or in a block every path through the body reaches it by), the invariants and measures of loops in the body included. A name defined from an element the copy has no argument for stands for that index: a proof that reads it is the fact that the index is in range, as `get(args, k)` written in it is. A local of the type of an element no argument gives (the element of an iteration past the pack, or of a loop that never runs) is taken out of the environments that name it, and a copy that still uses one is an internal error. Lowering writes a ghost `define $pack read at LINE:COL = 0` before each read of the pack and each validation statement that names it (as it emits each statement, `lowerbuild.tersus` `packReadMark`; the `PackLoop` records are made by `lower.tersus` `lowerPackLoop`), which names the place in the message of an index out of range, and the copy step takes them all out. Contracts and the validator's statements get the same, with the index of an unrolled loop, which their environment gives, read as its number: `size(args)` the number, `get(args, k)` the parameter's name, a statement with an index out of range the failing fact, a `define` and the arguments of a rewrite rule the same, and an `affirm` or `assume` of a `forall i in lo..hi` whose body indexes the pack at an index made of `i` one fact per index (a call through the bound of an element read at an index that is not a number, `<$param ..T@n as Tr>::f`, given that element, is the one of `..T#k`). Environments name the parameters instead of the pack. Copies of functions without a pack are made as before, so their MIR is unchanged.

A call that forwards the pack (LANGUAGE.md, "Variadic functions", Forwarding) is an ordinary `Call` in the generic MIR: the pack local, then the bounds of the part forwarded, `g['..T](x, args, lo, hi)`, of a stub whose signature has the parameters `rest`, `rest lo` and `rest hi` (lent when the callee's pack is), so the move check reads the pack, or moves it for a callee that takes its pack by value (an element outside bounds written as numbers, which are the bounds of every copy, is not given to the call: its moves before the call or by another argument of it, and its loans, do not count). `MirPacks.spreadForwards` makes it, in each copy after the elements are resolved, a call with the parameters from `lo` to `hi - 1` in their place, named `g['..T] spread lo hi`; `MirCopies.build` gives that name the forwarded reference's type arguments with `..T#lo ... ..T#hi-1` in place of `..T`, so the callee's copy is named by the arguments' types, the one a direct call with those types names. Bounds out of range in a block the copy runs end the block with the ghost assertion `0 <= lo`, `lo <= hi` or `hi <= N` (named for the slice and its line, which lowering, the Haskell one and the one written in Tersus alike, marks at the end of a block whose call forwards the pack) and the assumption `0 = 1`. The growth check is the one of every copy: a recursion through a shrinking slice makes copies of fewer and fewer arguments, each a function of its own, and one that forwards a longer pack is refused.

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
- **Size parameters.** A function with size parameters (`fnSizeParams`) takes them as its last parameters, and its locals have types such as `Array<Int, n>`. The validator and the executor run it as it is. For native code `MirHousekeeping.monomorphizeWith` (run first by `insertOwnership`) makes a copy of it for each list of constants that a call gives (`dot<3>`), with those parameters removed, the operands that read them the constants and the types' sizes replaced, and redirects the calls; the specifications and ghost statements are dropped, since they name the functions that are no longer there and only the validator reads them. A program with no function of the kind is left alone.
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
- **A list in native code.** After validation `MirLists` replaces list operations with calls of `lib/lists.tersus` and completes the `List<T>` structs (an address, then the count and the room, with the permission to the memory erased): `ListOp Length` is a `ReadField` of `len`, `ListOp Get`, `First` and `Last` stay `ListOp`s whose operand is the `List` (the struct's first field is the address of the elements, which `arrayPtr` reads), `Push` and `Set` are `Call`s of `listPush` and `listSet`, and `MakeList` and a `CList` constant are a `Call` of `listNew` and one of `listPush` for each element, except that a non-empty constant list of Ints, Bools or Bytes (the bytes of a string literal) is a `MakeBox` of the `CArray` of its elements, the form `Box::new(#[…])` has, which the emitter makes a private constant global copied into memory of its own: one `tersus_addr_alloc` and one `memcpy`, with as much room as elements, so each run gets a list of its own and the first push grows it. The constant array is written with elements as wide as its type holds them (8 bytes for an Int, 1 for a Bool or a Byte). The ownership pass, monomorphization and the emitter use named struct types; the runtime prints and compares a struct named `List` as a list (`tagged` 2 in its `Variants`). A `TBox t` whose `t` is not an array becomes the struct `Box<t>` of `lib/box.tersus` the same way: `MakeBox` and `Unbox` are `Call`s of `boxNew` and `boxUnbox`, and a `ReadField`, `IsVariant` or `AsVariant` of a Box is one of the `Box`, which the emitters read through the address that is its only word, as through a Box (`tagged` 3, printed, compared and copied as the value it holds, and freed by its drop). A `List` is freed by its drop (`impl<T> Drop for List<T>` in the library), as a `Box` is. A `Box` of an array, of a size or of any, becomes a `List<T>` too, with as many elements as room: `NewBoxed` is a `Call` of `listFilled`, `NewEmptyBoxed` one of `listNew`, `Unsize` a `Use`, and `MakeBox` of an inline array and `Unbox` of a Box of an array stay, which the emitters make of the list (the elements are moved into memory of their own, or out of it and the memory freed).
- **Descriptors.** The runtime prints values by the descriptor of their type: a constant global `@"type.List<Int>"` of `{ kind, aux }` for each type the program uses (and each type inside it, so a type that contains itself is there once): `aux` is the descriptor of the elements of a list, or the variants of a struct or an enum (each with its name, written `Enum::Variant`, and the names and descriptors of its fields). Equality (`Compare Eq` and `NotEq`, structural) and the printing of the result are then written once, in C, and print a value as `renderMirValue` does. A value of a variant (`TVariant`) has the descriptor of its enum. Step 4 adds how to free a value of the type.
- **Memory** is managed by ownership, decided on the MIR (see Ownership): nothing is counted at run time, and a value is freed when its owner lets go of it.
- **Arithmetic.** `Add`, `Sub` and `Mul` are `llvm.s{add,sub,mul}.with.overflow.i64` followed by a branch to the function's `overflow` block, which calls `tersus_overflow` (the message `Evaluation failed: Integer overflow` and exit status 1 of `tersus run`). `Div` rounds down, where `sdiv` truncates, so it subtracts 1 from the quotient when the remainder is not 0 and has the other sign than the divisor, and the one quotient that does not fit (the smallest `Int` divided by -1) goes to the overflow block. `Mod` takes the sign of the divisor, with `srem` by 1 in place of -1, which `srem` leaves undefined for the smallest `Int`, and the result 0 that follows.
- **Contracts are not checked.** A divisor that is not 0, an index in range, a list that is not empty are what validation proved, and the operations assume them as `unreachable` would (`sdiv` by 0 is undefined in LLVM). A bug in the validator is undefined behaviour in native code, where `tersus run` reports it. Overflow is the one trap, since nothing proves it cannot happen.
- **Tests.** `TestNative` builds programs and compares what the executable prints, and its exit status, with `tersus eval` (including indirect calls through plain or contracted function types); the builds pass without clang.

## Native monomorphization

`lib/mir/mono/` specializes generic functions over the complete MIR3 codec.
It keeps canonical declaration and selector keys distinct from ordinary
function-argument rendering, substitutes types and sizes, follows reachable
calls and instantiates implicit Drop functions. Final-name collisions follow
the Haskell structural-key precedence.

Without a generic function, the pass preserves the complete original program.
Otherwise it removes function specifications and ghosts, completes erased
instances and drops symbolic declarations; program invariants and the remaining
generic, bounded and instance metadata survive. The validation specialization
path in `MirMono` retains its contracts, ghosts and cached named-type map.

The emitter's `pass mono` entry reads strict, EOF-exact MIR3. The published
matching seed runs this pass during cold builds; linking and pruning use
the native `Link` transport. `TestMirMono` compares canonical raw bytes on raw and
pre-native-stage inputs, and the current host-validator group proves the pass.

## Moves

The checker resolves source `clone(x)` calls to the type's `Clone` implementation. A clone left as a builtin over a type parameter becomes the MIR rvalue `CopyOf`; only the native list and Box helpers leave one, since a program clones a value of a type parameter only under a `Clone` bound, and the function is then made for each type. The validator and reference executor treat `CopyOf` as `Use` over the same immutable value; native code calls an available `Clone` implementation or copies the fields structurally. Inside a type's own `Clone` implementation, structural copying avoids a recursive call to that same implementation. `MirMoves.checkMoves` runs during lowering, before validation, and rejects uses of moved values:

- **Places.** A place is a local with the fields (`SField`), the elements of a list (`SElem`) and the tag (`STag`) followed from it. The state along each path is the set of places that may have been moved out, with where and by which variable, and the places that a local is a *view* of on every path (a local that is a view on one path and not on another is taken for a value of its own, so a loop that rebuilds `bytes = push(bytes, x)` after `bytes = self.bytes` is not a second move of `self.bytes`). The blocks are walked to a fixed point in rounds, joining by union of the moves and of the loans and intersection of the views; a round runs only the blocks whose state the round before changed, and a join keeps the record of the move that reached it in the earliest round. The errors are collected from the last walk.
- **Views.** `d = x.f`, `d = get(l, i)` (or `first`, `last`), `d = x as V`, `d = Box::unbox(b)`, and the hidden locals of a `for` (`$list ...`) and a `match` (`$match`) make `d` a view of the place they read, when its type is not Copy. Reading a view moves nothing. Taking one (a `Consume` operand: a call argument that is not lent, a field of a struct made, `push`, `return`) moves the place it is a view of, which is an error for an element of a list and for a part of a parameter that is lent.
- **What one operation lends, it does not move.** A call reads a lent argument, and what an argument that is a reference or holds references is to, until it returns, so a place it is lent (a view the lent argument is of on some path, or a loan's place) must not overlap a place it takes (a `Consume` argument that is not Copy, or the place that argument is a view of): `f(s, &s.xs)`, `f(&s, s.xs)` and `f(s, s.xs)` with a lent second parameter are errors (`s.xs is lent to this call, and s, which holds it, is moved by it too`). A view through a reference (`(*r).xs`) is of the place the reference is to, and a call result under `from` borrows the place the argument for that parameter is, or is a view of. An assignment is checked the same way against the loans of the references its rvalue uses, so `W { s: s, r: &s.xs }` is an error too. A loan of a reference whose last use is the call or the assignment is still live while it runs, which the liveness after the call or assignment does not say.
- **What one call updates, it does not read.** The places a lent argument that is not lent for updating is a view of (followed through references) must not overlap the place an argument lent for updating is to: `f(&mut s.xs, s.xs)` is an error (`s.xs is lent to this call and lent to it for updating too`). A Copy part read out of a value is a local of its own, not a view, so `f(&mut s.n, s.n)` is accepted; a view of an element keeps a known index, so `f(&mut get(xs, 0), get(xs, 1))` is too.
- **Holders.** A value that holds references (a struct made with them, or a call result under `from`) has loans, but its places are its own: a borrow of it, or of one of its fields, is a loan of that place, and carries the places that the references it reaches are to (all of them for the holder, those of the field for a field that can hold references, or all of them when that field's loans are not followed on their own, none for a field that cannot), so they stay frozen while the borrow is live. A reference read out of a field, directly or through a view of the holder or a reference to it, is to what that field is to, or to everything the holder borrows when its fields are not followed one by one (a Box, an enum, a call result whose type is not a struct of references, a list). Only the loan of a reference is followed to the place it is to.
- **Writes through references.** Lowering writes `*p = v` as an `AssignRef` rooted at `p` itself when `p` is a reference or an update parameter, or was made by borrowing a place of one (`p = &mut *q`), and rooted at the owner when `p` borrows a place of an owner (`q = &mut x; *q = v` is `x := v`). Lowering resolves `p` only through the borrow it was last given on every path to the write: a local given anything else (a read-out, a call result, another reference), or given a borrow in one branch or in a loop's body only, is written through as itself. So an `AssignRef` to a reference or an update parameter is a write through that local, and only one to an owner may go through one of the `&mut` locals that borrow it (`MirMoves.ownerRoot`): those count as used by it, and their loans do not stand against it. A write or read through a reference while a live reborrow of it overlaps the place is an error, whatever made the reference. A reborrow of a reference held in a part of a value (`&mut *w.r`, `&*get(rs, 0)`) is made of that reference read out into a local of its own; the MIR checker refuses a value that is not a reference written where a part holds one.
- **Every rvalue has a loan rule.** `assign` lists all `Rvalue` and `ListOp` constructors with no catch-all; `-Werror=incomplete-patterns` makes adding a constructor without a rule a build error. Moves, copies and part read-outs carry the source's loans; aggregate construction and replacements combine operands' loans. `Addr::write` adds the value's loans to the permission, `Addr::get` and `Addr::take` read loans out, and operations returning a permission preserve its loans. Allocating, assuming or minting an empty permission starts with no loans. `TakeField` and `Peek` are ownership-pass operations and are refused at this stage when the destination may hold a reference. A source-level reference assignment stores the value's loans at the target. Call results without `from` gather the eligible arguments' loans; a result with reference-bearing permission slots also gathers them even when `from` names the origins of its ordinary references. The fallback does not infer an exact pointee. An unsourced reference-bearing result is refused unless it comes from a generic callee or a copy of one. Return refuses loans of callee-local storage.
- **Shared paths.** `stShared` holds the locals whose value may hold an update reference, or be storage, reached through a shared reference or a parameter lent to be read (one in `fnBorrowed` but not `fnMutBorrowed`; the value a drop is given is its own). `sharedTransfer` decides it for every `Rvalue` and `ListOp`, with no catch-all: a part read out (a field, `*`, `Unbox`, `get`, `first`, `last`, `Uninit::get`/`take`, `Addr::get`/`take`) is shared when its source is such a parameter, a shared reference or shared; a cast, the value a `match` or a `for` reads, and a value made of others (a struct, a list, a Box, `push`, `set`, what `pop` leaves, `Uninit::new`, `Addr::write`, a permission given back) when an operand it reads and that is not Copy is (one it moves is refused instead, below); a clone only when its type may hold an update reference; a borrow, a number, an address and new memory never. A Copy value holds no update reference and is never shared. Joins union it, a new value of the local clears it, and a store through a reference adds it to the places written. Source lowering emits only `Use` stores, and a shared value cannot be moved into one. A write through what is shared (an `AssignRef` rooted at it), a borrow of it for updating and lending it for updating to a call are refused (`p may be reached through a shared reference or a parameter lent to be read (&T), so nothing can be changed through it: it cannot be written through`), and so is a move of a shared value that no other move rule refuses. Only the root is checked: what a place was borrowed from was checked when the borrow was made, and in source-lowered MIR cannot become shared while the borrow is live. For a hand-built `AssignRef … CopyOf`, the affected owners are marked but the reference used to write them is not; the source-lowered guarantee does not cover that form. A call's result is not shared: the callee's own check keeps what it reached through a shared path out of its result, and in a generic body a value of a type parameter holds no update reference a clone or copy could duplicate, since `Clone` and `Copy` bounds refuse a type that holds one. A shared update reference keeps its update loan.
- **Function boundaries.** A place is the caller's (`callersPlace`) when its root is a parameter that is a reference or lent, a reference with no loan made in the function, or the symbolic root a parameter's held references are to (`incomingRoot`, which travels with loans but is no local, so it conflicts with no move of the value that holds it). An `AssignRef` of a value whose type may hold a reference is refused when any place it may write (each place the reference may be to) is the caller's. A call stores nothing when its callee's body is move-checked at the call's types (in this module, or in the module that defines an imported function); a call of a generic function whatever its type arguments (deliberately conservative: the check does not match a generic callee's parameter types against its arguments), of a copy of one with bounds or a pack whose type arguments may hold a reference, of a bound's impl (`<$param T as ...>`) or of an unknown function value (`storingCallee`) stores, into every holder an argument reaches through update references (the root an update argument is to, and the roots the loans of an update argument's referent or of an argument given by value lead to, through types that may hold an update reference; `boundaryHolders`), every place an argument lends or is a reference to and every place what an argument holds is to (`referenceBounds`), except the holder itself and the place of the argument it is reached through. A holder of the caller's is refused; one of the function's own takes the places into its loans and every reference field's, and becomes a child of the arguments they come from. A call whose callee stores nothing leaves the caller's holders' loans as they were. A bound call of the library prelude's own `Sequence` or `Growable` functions (`size`, `get`, `getRef`, `set`, `push`) is recorded as a `$builtin` instance with no type arguments, so it falls under the copy rule and stores nothing; none of those functions takes an update parameter, and `Self` is a type parameter at the call, so the outer generic call's own store covers what they are given.
- **What an operand does** is `MirMoves.roles`, except that `ListOp NewArray` and `NewBoxed` take their element (n copies of it are made), `Unbox` and a cast read, and the value in `_0` is taken by `Return`.
- **Copy** (`isCopyType`) is Int, Byte, Bool, functions, an array of Copy, and a struct or enum that `CopyDef` named (with Copy fields for an instance of a struct with parameters). It is never moved.
- **Positions.** Lowering writes `GhostPosition line column` (from the parser's `Mark`) before the statements it comes from and at the start of every block, so each error has a line; `stripPositions` takes them out, and no other pass sees one.

`lib/lists.tersus` and `lib/box.tersus` are compiler-owned module units,
lowered with the same move and loan checks as other modules. Imported
signature stubs remain present during those checks, then leave the unit.

## Ownership

The production transformations are `insertOwnership` and `expandRefWrites` in
`lib/mir/ownership/`, hosted by `MirHousekeeping`. The order is ghost
erasure, reference-write expansion, list lowering, native monomorphization,
Tersus ownership, verification, then emission. The
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

`monomorphizeOwnershipWith` fuses adjacent Mono and ownership calls only when
functions are generic. Its `pass mono-ownership` request carries strict MIR3;
the native entry specializes it and feeds the existing ownership reader token
records without another text round trip. It returns the specialized MIR3 and
owned MIR2 receipts, both consumed by the host, so `restoreOwnership` remains
the metadata authority. A program without generic functions still uses the
original MIR2 ownership request and need not serialize its proof AST as MIR3.
The separate `pass mono` and `pass ownership` entries remain available for
staged comparisons. Expansion and list lowering stay before both passes.

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

**The invariant** is that what a value owns (a list or a `Box`, which are on the heap) has exactly one owner: a local, a word of another value (a field, or an element of a list), or a temporary on its way somewhere. So the heap is a forest, a value is freed with what is in it, a copy is a deep copy that shares nothing, and `push` and `set` may change the list they are given when it is theirs. A struct or an enum that holds one is held inline and owns it through its words, so it is moved, copied and dropped like a list: a `Move` copies the words to where they go (what they leave behind is never read or dropped again), `CopyOf` is a deep copy, and a `Drop` frees what the words own. Where a value is wanted by two the program has to say so (`clone`, see Moves), and the pass makes that copy where `CopyOf` is; it still clones a part of a value that is read and then not used before the whole changes (a view that cannot look at the value in place), which a program cannot see.

**What an operand does** decides what happens to the local it names:

| The operand | The local |
|---|---|
| reads the value: `size`, `==`, `is`, the list of a `get` | nothing |
| takes it: `y = x`, the list and the element of `push`/`set`, a field of a list or struct that is made, an argument of a call, `_0` | `Move x` when it is not used again (`x` is left holding nothing), and otherwise a `CopyOf` of it |

A local is dropped before an assignment or call overwrites a value it still owns, and remaining owned values are dropped at return. A value taken apart by a destructuring assignment (its `dissolve L`, which the erasure makes a peek of `L`'s bytes cleared, and native code makes nothing) owns nothing after it and is not dropped, as after a move; `listPush`, `listSet` and `listPop` take their list apart this way on every call. Ownership tracks whole values and partial fields across control-flow joins and uses flags where cleanup is conditional. A value with fields taken out and no drop of its own is dropped as the fields that are left, each on its own and under its flag if it was taken on some paths only, and not at all when no owning field is left; a value with a drop of its own has a field taken only by the reads that take it apart, so it is always dropped whole. So no drop runs on a value that was moved out, and native code neither clears moved-out words nor tests a value before its drop. A parameter declared with `&` or `&mut` borrows its referent; a consuming argument transfers the value it owns. If the caller still needs an owning value, it supplies a clone.

**A part of a value** (`get`, `first`, `last`, a field) is part of what contains it:

- A field of a value that is not used again is taken out of it (`TakeField`; the fields left are dropped one by one). A value whose type has a drop of its own keeps its fields, except in the reads of a destructuring assignment that takes it apart. This is what makes a `match` on a tree not copy the tree: the fields are taken from the scrutinee one by one. The check is by field: a field is taken when neither it nor the whole value is used later (the tag, read by `is`, does not count).
- A temporary used only by reads can `Peek` when its source and the source's loan/view origins stay live and undisturbed through those uses. Assignments, consumes, reference writes and call arguments are checked through their loan origins, not just the local named in the syntax. A part a copy of which would copy a value with a drop bitwise (a struct or an enum with an `impl Drop` and no `Clone` of its own, at any depth, the elements of a list or a Box included) is always looked at in place, for its whole live range: `MirMoves` refuses to change what it is a part of while it is live, and the pass checks the same again at the types native code is made of, refusing a change to the owner while such a look is live and any copy of such a value (DROPS.md, decision 6). A part of a part is looked at in place too when the chain starts at a local given a field taken out of another value, which owns what it holds, and a field can be taken out of such a local in turn. A temporary used as the root of a `Borrow` is copied instead of peeked, because that borrow can outlive its last direct use. Cross-block peeks and the hidden `$list` local of a `for` additionally require a chain to an unchanged read-only lent parameter; mutable parameters do not qualify. A cast is forwarded to subsequent reads so they read the original value directly.
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

### Ownership and storage

After the types, versions 1 and 2 may say what a program's types are beyond their declarations. `storage "L" "B"` names
the declarations that native storage's list and Box are. `ownership N` and its `N` lines `owned "T" "C" "DP" "DF" "KP"
"KF" "RP" "RF"` give each type's checked ownership facts, as the elaborator checked them (`AST_DATA.md`, "Ownership
transport"): the Copy provider, then the provider and function of Drop, of Clone and of Deref, each empty when the
type has none. With them, the facts say what drops or clones a value, whatever the functions are named; a declared type
without its row, a provider without its function, or a function the program does not have is refused, and
`ownership 0` is a checked program whose types have no ownership at all. Without them (the form the compiler writes
today), a type's drop is `<T as Drop>::drop`, its clone `<T as Clone>::clone`, and native storage the declarations
named `List` and `Box`. The emitter written in Tersus and its ownership passes read both forms.

### Version 3: a lowered unit

`MirData.writeLowered` and `MirData.readLowered` (`readLoweredBytes` for the
lines of a response as bytes) write and read a whole module as lowering gives
it, `Mir.Lowered`: the program before `MirMoves.finishLowered` completes its
instances, checks its moves, takes out its source positions and drops the
stubs of imported functions and of the copies it names, with the sets the check
of moves needs and what the host takes from the module's statements. A program
lowered on its own (a statement list) is the whole program, so
`Lowering.finishProgram` also makes its copies (`MirCopies`); a module's are
made when the program is linked. It is the contract of the lowering written in
Tersus (`REPLACING_HASKELL.md`, "MIR lowering in Tersus"), which the host will
finish with the same code. The elaborator written in Tersus writes it in the
`mir` section of its answer (`AST_DATA.md`); the host reads it only to compare
it with its own lowering yet.

Version 3 keeps the type, operand, constant, rvalue, statement and terminator
words of the earlier versions. Its records come in this order, each kind by
name (functions, then `main`), and a function's loops by header block:

```
tersus-mir 3
struct ... | enum ...                  as in version 1
generic "S" N "n"... M ("f" TYPE)...   a struct with sizes: its sizes and fields
invariant "S" P                        what every value of the struct meets
bounded "f" N "s"... M "p"... K "g"... a function with bounds: the sizes its bounds name, its
  J LOOP...                            type parameters bounded by Copy, the functions lifted out of it,
                                       and its loops over a pack, each `HEADER BODY EXIT N BLOCK... M LOCAL...
                                       INDEX ELEMENT "type" LO HI TAKEN|none` (Mir.PackLoop)
instance "n" "f" N ARG...              what the name of a copy stands for: the function with bounds
                                       and its arguments (each ARG `size SIZE` or `type T`); "" and
                                       none for a function a bound gives
shared N ("x" OPERAND)...              a shared environment, numbered from 0 in order
function ... | main ...                the version 1 header line, then:
spec requires P ensures P termination P|none writes N "w"... mutparams N "p"... from N "p"...
env ENV
local ...
loop B body B invariant P termination P|none env ENV
block B, its statements and terminator, ..., end
copies N "x"...
linear N "x"...
drops N "x"...
stubs N "x"...                         the imported functions seeded as stubs
declared N "x"...                      the names the module declares at its top
nested N "x"...                        the names it declares inside its functions
assumes N P...                         every `assume` and `Block::assume` call of its statements
data N
N lines of AST data, stage mir
```

`ENV` is `S N ("x" OPERAND)...`: the names listed (by name), and those of
shared environment `S` that are not listed, or none when `S` is `none`. The
writer puts the function constants of an environment (the program's functions,
which nearly every environment names) in a shared environment, so that each
set of them is written once; without that a compiler package is tens of times
larger. A ghost statement names its kind and carries its environment:

```
ghost validation ENV P
ghost axiom ENV P
ghost proof ENV P
ghost function ENV "name" "source name" true|false
ghost position ENV LINE COLUMN
ghost dissolve ENV L
```

The bare `ghost`, the numbered `ghost N` and `dissolve L` of version 2 are not
records of version 3. The sets (`copies` to `nested`) are in ascending order.
`declared` holds the structs, enums and traits at the module's top and the
functions at its top and in its impls, the names a package module's library
units do not declare again (`PackageCompile.moduleDeclaredNames`); `nested`
holds the structs, enums and traits declared inside its functions and blocks,
which a single file's library units do not declare again either
(`Compile.ownNames` is both). `assumes` holds every `assume` and every
`Block::assume` call in order, dead code included.

A count is nonnegative and no more than the tokens that follow it in its
record. A local, a block, a line or column and an index are signed 64-bit
numbers; an integer constant and a size are numbers of any size, so the unit
holds every value lowering gives. The fixed-width types are `i8 i16 i32 u16
u32`: `writeLowered` gives an error, not data its reader refuses, for a unit
with any other fixed-width type or a narrowing to one, as the AST data writer
does for its payloads.

`P` is a zero-based index into the root list of the AST data block
(`AST_DATA.md`, stage `mir`). A payload is one existing statement record:

| Referred to by | Payload |
|---|---|
| `ghost validation` | `ValidationStatement V` |
| `ghost axiom` | `AxiomDef NAME PARAMS REQUIRES ENSURES` |
| `ghost proof` | `ProofDef NAME PARAMS REQUIRES ENSURES BODY` |
| `requires`, `ensures`, `invariant` (of a loop or a struct) | `Block STATEMENTS`, each a `ValidationStatement` |
| `termination` | `While` with the condition `true` (`Val (VBool true)`), no invariant, the termination and no body |
| `assumes` | `ValidationStatement (Assume PROOF)` for an `assume`; `Return CALL` for a `Block::assume` call, which is trusted, never a proof |

The reader refuses a payload of the wrong kind, an index with no payload, a
payload referred to twice or not at all, a shared environment that does not
exist, a name twice in an environment or a set, a type, generic, invariant,
function, local, loop or block twice, a count that is negative or longer than
its record, a number out of range, a record out of this order or that it does
not know, and a `data` count that is not the block's length. `testMirLowered` round trips every unit the compiler
lowers from `examples/`, `examples/modules`, the compiler libraries and the
compiler's own packages (the elaborator and the MIR reader among them), with
the examples the elaborator refuses listed; checks the names a module declares
where it declares them; checks the finished MIR and the move error
of small programs against fixed text; and checks the refusals.

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
| `mir/ownership/ownership.tersus` | Declarations-only request dispatcher imported by the emitter. `pass ownership` or `pass expand` followed by MIR v2 produces MIR v2. `isOwnershipRequest` and `runOwnership` dispatch to the algorithms in `rewrite` and `refwrites`; `common`, `analysis` and `drops` provide their shared data and analyses. The host retains metadata sidecars; native monomorphization runs first through the full MIR3 codec |
| `mir/mir_reader/mir_reader.tersus` | The round-trip entry: imports the shared reader and writer |
| `mir/emit/emit.tersus` | Emitter entry and program assembly. It writes LLVM IR for MIR v1, dispatches `pass ownership` and `pass expand` over MIR v2, and runs `pass mono` and `pass link` over the shared complete MIR3 codec. The pinned emitter seed must contain both native-pass entries |
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

The validator is written in Tersus (`lib/validation/`, one root module with explicit sibling-file imports and `driver.tersus` as its only entry, compiled to native code by `ValidatorNative`), and `SelfHostedMir` translates the MIR into its data: each function is a list of `ExecutionBlock`s whose steps run over numbered terms, and `validateExecution` sweeps them, each block once, with states that hold the term each local holds and the facts known. Values never change, so an assignment gives the local a new term and a fact stays true for the rest of the path.

- **Reuse.** A verdict on a function is kept for the rest of the process under the data the bridge makes of it (its blocks, its contracts and the contracts of what it calls, the invariants of the types it makes and the rules it uses), so a verdict is reused only where it would be the same; `testValidationCache` checks hits and cached/uncached parity. See [README.md, Interpreter flow](README.md#interpreter-flow).
- **Container proofs.** Validation keeps the logical List/Box model: list facts come from operation contracts, and a Box has the value of its payload (the bridge leaves the library's physical `List` and Box structs out of what it reads, `SelfHostedMir.sourceContainerView`). The native library itself, `lib/lists.tersus` and `lib/box.tersus`, is validated with its physical layouts instead (`SelfHostedMir.encodeLibrary`): a List and a Box are the structs they are, with their invariants, an operation of the logical list or Box is refused there, and its generic functions are checked as written, for any type. Native code of the validator is made with the library, so the validator is built first without validation and then validates the library before it is used (`ValidatorNative.validatorExecutable`). A Box's own `addr` and `blk` are field functions of their own in the logical view only, so a payload field of the same name says nothing of them.
- **Checks.** A check asks about the facts near its goal, not the whole state: its slice, walked from the goal's terms within a budget, with the write chain behind a list or block it reads (LANGUAGE.md, What a check sees). Code after an assumption that its nearby facts contradict is not checked.
- **Statements.** An operation records what it establishes and checks what it needs (the contracts of the builtins, `StdLib`), as an application of the builtin to the terms of its operands. `Use` of a local gives the destination the same term. A `Call` terminator checks the callee's input contract and assumes its output contract (only the contract: the callee's body is neither run nor read for facts). `Ghost` statements read their names through their `Env`.
- **Edges.** A `SwitchBool` adds the truth of its condition to each edge's state, and the relation the condition compares (`a < b`; negated on the false edge). A constant condition has one edge.
- **Joins.** Where branches meet again the states that arrive are joined by `mergeStates` (a fresh term for a local that differs, the facts both paths establish rewritten to the joined terms, and the bounds both paths give a joined term), and the block runs once on the result; a return, and a jump back to a loop header, is checked once for each arriving state.
- **Loops.** A header with a `LoopSpec` is checked by its invariant: the invariant on entry, the locals the loop assigns replaced by fresh terms with the invariant and the condition assumed, the region (the header and every block that can get back to it) walked once, and every edge back to the header must establish the invariant again and shrink the variant; the loop is left at its exit, and a block outside the region that the body reaches must lead only to returns. A condition of several tests joined by `&&` or `||` is checked as written. Invariants are inferred from what the entry state proves, each kept only where the loop preserves it.
- **References.** A reference local holds the term of its place. An `AssignRef`, and a call that updates through a reference, give a new version to the local its chain of borrows starts from (borrows, copies, and calls whose `from` places the result: `SelfHostedMir.Aliasing`). After any new version of a local, an `Assign` of any form and a call's destination included, the references the bridge follows into it are bound again, and if a reference to it escaped (into a struct, a list, a Box, a call or a local the bridge does not follow) every local holding a shared or update reference the bridge cannot place gets a fresh term. A loop assigns those locals, and binds the references into them again after their fresh terms. Through a reference the bridge cannot place (one read out of a struct, a list or a Box, or a call result no contract places), every place a reference escaped from gets a fresh term too, as it does at a call given something that holds an update reference. A fresh term keeps the size and the fields of a value that only a part of was lent.
- **Returns and functions.** `Return` checks the output contract on its path. Each function is checked on its own, from its input contract and the contracts of what it calls; a generic function is checked as the copies a call decides. A function that calls itself, alone or in a cycle, must say why it ends.

## Notes on the implementation

- A condition (of an `if` or a `while`) made of `&&`, `||` and `!` is lowered to a test for each part that is evaluated, each a `SwitchBool` to the next test or to the block of the whole condition (`lowerConditionWith` in `lib/elaborate/lowerexpr.tersus`); a Bool wanted as a value (`ok = a && b;`) is the same tests ending in two blocks that assign `true` and `false` to a temporary, so the tests of a chain know the ones before them (`i >= 0 && i < size(l) && get(l, i) = 0`). A `LoopSpec` therefore says which block is the first of the body (`loopBody`) and the validator starts an iteration (the variant is bounded below and kept) when that block is entered, once the ways in have met, and not on the true edge of a single test.

- Lowering takes each local's type from the expression types `elaborate` hands over with the program, so `x = []; x = push(x, 1)` gives `x` the type `List<Int>`. A type no use decided (a list that is only created) is `Int`.
- A function defined at the top of the program is found by name from the functions after it and from itself. In the scope that defines it, a function is a name that stands for the lifted function and is called by name, unless the program assigns that name elsewhere (`f = size;`): then it is a local that holds the function, assigned like any variable (so the nearest binding changes), and a call of it is a call of a local. The bodies of the functions at the top still find the original by name.
- A program has one return type, that of its first `return` (the checker rejects a later one of another type), so `_0` has one type.
- Falling off the end of `main` is a `Return` (a program may end without a value); falling off the end of any other function is `Unreachable`, which fails with `Function did not return a value`.
- Blocks nothing jumps to are dropped and the rest are numbered in the order a walk from the entry reaches them, so the printed MIR reads from the top.
- `Pipeline` runs the stages (parse, `elaborate`, lower, validate) and checks the program's types once: `elaborate` lowers what it checked, the host finishes that unit (`Lowering`), and the validator takes the MIR (`validateProgram`).
- A statement after a `return` is not lowered, so it is not validated either: nothing can run it, and a proof about it would be about no run.

## Open issues

- **Top-level `return` with no value** (`main` without one) leaves `_0` unassigned and `fnReturns = Nothing`.
- **Recursive types** (`Tree`) need a pointer in a native layout; the MIR only names them.
- **Mutual recursion** is ordinary in the MIR: `progFunctions` holds every function before validation, and the validator works out the call cycles from it.
