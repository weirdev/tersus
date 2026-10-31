# Allocators (design)

> **Draft.** This is the design for step 32 of the roadmap in `README.md`. It builds on `POINTERS.md` (step 25), `DROPS.md` (step 26), the library `Box` and `List` of step 29 and the drops made per type of step 30 (a). Nothing here is built. It is the second version: the first stored an allocator in every container and inferred which functions allocate from their bodies, and three reviews (of soundness, of use and of cost) found that too costly, too implicit and unsound in places. What they found and how this version answers it is at the end.

## The idea

Every value on the heap comes from one allocator today: `allocate`, `release` and `reallocate` in `LlvmRuntime`, over `malloc`. A program cannot put a tree in an arena, build a parser's tokens in memory that is thrown away whole, or run under a checking allocator except by compiling the runtime with `-DTERSUS_CHECK`.

This design lets a block choose the allocator of what is made inside it, including what the functions it calls make:

```tersus
fn parse(text: &String) -> Int {
    arena = Arena::new(65536);
    n = 0;
    with arena {
        tokens = tokenize(text);   // the list and the strings in it are made in the arena
        tree = build(tokens);      // and so is every Box of the tree
        n = count(tree);
    };                             // tokens and tree end here, and the arena's memory is not walked to free them
    return n;
};
```

`tokenize`, `build` and `count` name no allocator. Four rules make that safe and free of cost:

1. **Where a value's memory comes from is part of its type**, as a *region*: `List<Token, arena>`. The validator and the program's proofs never see it.
2. **A region that a program does not write is the context**: in a function, the region it is called in; at the top of the program, `System`. So `fn tokenize(text: &String) -> List<Token>` makes its list where it is called.
3. **The context decides only where a value is made.** What is done to a value that exists (`push`, `set`, its growth, its drop) uses the region in its type.
4. **A value made in a local allocator cannot leave the `with` block that opened it**, and is dropped at every exit of the block. This is a check of scopes, with no lifetimes.

At run time a region is a pointer to its allocator, passed to the functions that need one, and nothing for `System`. No container holds an allocator, so no value grows by a word, and a program that uses only `System` compiles to the same IR as today.

## Regions

### A region is a parameter of a type

The types that own memory take a region parameter, written `a: Alloc`. These are the types that hold a `Block`, and the types that hold one of those:

```tersus
struct Box<T, a: Alloc> {
    addr: Addr<T>,
    ghost blk: Block<T, a>,
} invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm filled(blk, 0); affirm allocator(origin(blk)) = a; }];
```

The same holds for `Buffer<T, a>`, `StdList<T, a>` (a `Box<Array<T>, a>` and a count), `Vec<T, a>` and `String<a>`. The layout of each is what it is today. The region is not a field, and `blk` is a ghost, which takes no room (`POINTERS.md`, Ghost values: a ghost field is not in `slotsOf`, and a ghost part of a result is not in the call). A `Box` is one word and a list three.

A region is one of these:

- **A global allocator**, a type of no fields whose state, if it has any, is the system's: `System`. A value made in it can go anywhere.
- **A region parameter** of a function or a type: `fn f<a: Alloc>(...)`, `struct Doc<a: Alloc> { ... }`. The context `ctx` is one too (see Functions).
- **A local allocator opened by `with`**: in the block `with arena { ... }`, the name `arena` is a region (see The with block).

As a size parameter `n` is both a part of a type and an `Int` in the body (LANGUAGE.md, Size parameters), a region `a` is both a part of a type and the allocator in the body. Its value is what `Box::new` uses. Where the region is `System`, that value is nothing.

### Where a region is written, and where it is not

- **In a function**, a region left out of a type is the function's context. `fn tokenize(text: &String) -> List<Token>` is `fn tokenize<ctx: Alloc>(text: &String<ctx>) -> List<Token<ctx>, ctx>`.
- **In a struct or an enum**, a region left out of a field is the type's own implicit region, and all the fields that leave one out share it. `struct Doc { lines: List<String> }` is `struct Doc<r: Alloc> { lines: List<String<r>, r> }`. A type then lives in one region all through, which is what an arena wants: `Box<Node>` in `Node` is in `Node`'s region. Whether a type has the implicit region is worked out over its fields, as a fixpoint over the types that hold each other. A type that holds nothing on the heap (`Int`, `Array<Int, 4>`, a struct of numbers, an `Addr<T>`) has no region at all.
- **A written region is fixed.** `struct Cache { entries: List<Int, System> }` has no implicit region, and a `Cache` is made in `System` under any context. A type that wants two regions declares them: `struct Pair<a: Alloc, b: Alloc> { left: List<Int, a>, right: List<Int, b> }`.

### The region of a borrow does not matter

A function that is lent a value only reads it. It cannot grow the value, free it, or keep a part of it without a copy. Its region is used by nothing the function can do, so **a `&T` is accepted for any region of `T`**: `fn total(l: &List<Int>)` totals a list of any region, under any context. Through the borrow the function sees the type with its own context, and that is sound, because a read never uses the region.

Three things follow:

- **Equality ignores regions.** `=` between two lists compares what they hold, whatever their regions are. A `Box`, a list and every type that holds an `Addr` already have an equality that is a relation of their library and not equality of terms (`POINTERS.md`, `Box<T>`), so nothing in the proof engine changes.
- **The validator never sees a region.** Regions are erased from the terms it reasons about, so `affirm return = l` holds between a list and its copy in another region, and no proof of a program mentions one.
- **`clone` copies into the region it is expected in.** The trait function is `fn clone(self: &Self) -> Self`. The borrow ignores `self`'s region, so the result's region is decided like any other made value: by the type it is expected to have, else the context. `kept: List<Token, System> = clone(tokens);` copies the tokens out of the arena. `fn first(l: &List<String>) -> String { return clone(get(l, 0)); }` gives a string in the caller's context. A derived `Clone` and a written one both work this way, with no other trait.

## Making values

### What makes a value, and where it is made

The places that allocate are `Box::new`, a list literal, `[]`, `Array::boxed`, a string literal and `clone`. Each makes its value **in the region its expected type says, and in the context where nothing says one**:

```tersus
with arena {
    a = [1, 2];                   // List<Int, arena>: nothing expects a region, so it is the context
    b: List<Int, System> = [3];   // System: the type says so
    names = push(names, "x");     // names: List<String, ctx> from before the block, so "x" is made in ctx
};
```

A struct literal allocates nothing, since a struct is held where it is made. Its fields keep their regions, which have to agree with the struct's: `Doc { lines: l, ..base }` with `l` and `base` in different regions is the error `lines is in arena, but base is a Doc in ctx`.

### Functions take their context from the call

A function's context `ctx` is a region parameter of every function. A call decides it as it decides any parameter of a type, and the rule is one sentence:

> **A call's context is what its types decide, and the context of the caller when they decide nothing.**

- `sort(l: List<Int>) -> List<Int>` called with a list in `System` sorts it in `System` under any context, because the argument decides `ctx`. Called with a list made in the arena, it sorts in the arena.
- `make() -> List<Int>` called with nothing expected is in the caller's context. `l: List<Int, System> = make()` is in `System`, because the expected type decides.
- `tokenize(text: &String) -> List<Token>` is decided by nothing, since a borrow ignores its region. So it makes the tokens in the caller's context, which is how the example at the top puts them in the arena.
- `merge(a: List<Int>, b: List<Int>) -> List<Int>` takes both lists in its one context. Given lists in two regions, it is rejected: `merge takes a and b in one region (its context), but a is in System and b in arena; give merge two regions, fn merge<a: Alloc, b: Alloc>(...), or clone one`.

This is unification, the rule every parameter of a type has. Only the last step differs: a size that nothing decides is an error (LANGUAGE.md, Size parameters), while a region that nothing decides is the caller's. At the top of the program, in `main`, in a proof and in a test, the context is `System`.

`tersus sig <file> <function>` prints a signature with its regions, `fn sort<ctx: Alloc>(l: List<Int, ctx>) -> List<Int, ctx>`. A message about regions names them the way a program writes them: `System`, `ctx`, the parameter's name, or the name of the local opened by `with`.

### Existing values use their own region

`push`, `set`, `pop` and the growth of a list are `fn push<T, a: Alloc>(l: List<T, a>, x: T) -> List<T, a>`. The region comes from the list, and the context plays no part. A drop uses the region of the type it drops. So the wrong allocator never frees a value: the region a value is freed with is the one in its type, which is the one it was made in, and the proof of the library's drop (`allocator(origin(blk)) = a`, in the invariant of `Box`) says so.

## The with block

`with x { ... }` makes `x` the context of the block. `x` is one of two things:

- **A global allocator type**: `with System { ... }`. The block is like any other.
- **A local whose type implements `Allocator`**: `with arena { ... }`. Inside the block:
  - `arena` is lent. It is read, and it cannot be moved, assigned or dropped.
  - `arena` names a region, as a type parameter names a type in a function's body. It is a fresh type variable of the block (the brand of Haskell's `runST`, or of Rust's `GhostCell`). It is equal to no other region, not even in a recursive call that opens the same block again, because a callee knows only its own parameters.

**Escape is scope.** A type that mentions the region `arena` is not a type outside the block. So:

- A local whose type mentions it belongs to the block. It is new each time the block is entered, it is not seen after the block, and it is not carried around a loop that holds the block.
- An outer local cannot be given one, since the outer local's type cannot mention the region.
- `return` from inside the block cannot give one, since the function's result type cannot mention it.
- **A permission is one of these too.** What an allocator's own functions give is `Block<T, arena>`, so a raw `(p, b) = arena.alloc(n)` in the block is scoped like a list is. The permission is linear, so it must be freed, or held by a value that is dropped, before the block ends: a permission still owned at an exit is the rejected program of `POINTERS.md`, "a permission dropped". An arena that frees in bulk (`BulkFree`) takes the permission in `free` all the same, which only does nothing else.

The messages: `tokens is in arena, and cannot be used after the with block that opened it; clone it into another region first`, and `names is a List<String, ctx>, and cannot hold a String in arena; clone it`.

**Every exit drops.** At each edge out of the block (its end, `return`, `break`, `continue`), the locals of the block that are still owned are dropped, the latest made first, and then the lend of `arena` ends. This is a scope end in `MirOwnership`, at a block instead of a function. So nothing made in the arena is alive when `arena` can next be assigned, moved or dropped, and `arena = Arena::reset(arena);` after the block is sound with no proof about what points into it.

`with` blocks nest, and the inner one is the context inside it. A value made in an outer arena may be used in an inner block, since its region is in scope there.

## Allocators

### The trait

An allocator gives out and takes back the blocks of `POINTERS.md`. A block's ghost `origin(b)` gains one fact, `allocator(origin(b))`, the allocator it came from. `split`, `join` and `cast` keep the origin, so they keep that fact with no rule of their own.

**A permission is branded with its region.** `Block<T>` becomes `Block<T, a: Alloc>`, a ghost type that names the region of the allocator the memory came from, and the allocator's own functions give and take `Block<T, Self>` (`Self` is the region the allocator is: `System`, a parameter, or the fresh region of a `with`). `Addr<T>` stays as it is, since an address allows nothing without its permission. The brand is what the escape rule needs. A permission is a value like any other, so a permission from a local arena's `alloc` that was not branded could leave the block as a bare `(Addr<T>, ghost Block<T>)`, outlive the arena, and be used with `Addr::write` or `Addr::get` on freed memory, and the equation `allocator(origin(b)) = self` could not stop that, because regions are erased from validation and those operations ask for the permission and not for a live allocator. With the brand, `Block<T, arena>` is a type that mentions `arena`, so it is scoped to the block like `List<T, arena>` is (see The with block). The same holds for a region parameter: a function cannot return a `Block<T, a>` for a region it was not given. The brand is ghost and is erased with the permission, so it takes no room and no code.

```tersus
trait Allocator {
    fn alloc<T>(self: &Self, n: Int) -> (Addr<T>, ghost Block<T, Self>) [{ affirm n >= 0; }]
        [{ affirm base(return.1) = return.0; affirm cap(return.1) = n; affirm whole(return.1); affirm fresh(origin(return.1));
           affirm allocator(origin(return.1)) = self; affirm forall i in 0..n: !filled(return.1, i); }];
    fn resize<T>(self: &Self, p: Addr<T>, b: Block<T, Self>, n: Int) -> (Addr<T>, ghost Block<T, Self>)
        [{ affirm base(b) = p; affirm whole(b); affirm allocator(origin(b)) = self; affirm n >= 0; affirm forall i in n..cap(b): !filled(b, i); }]
        [{ affirm base(return.1) = return.0; affirm cap(return.1) = n; affirm whole(return.1); affirm allocator(origin(return.1)) = self;
           affirm forall i where i >= 0, i < n, i < cap(b): filled(return.1, i) = filled(b, i);
           affirm forall i where i >= 0, i < n, i < cap(b), filled(b, i): at(return.1, i) = at(b, i); }];
    fn free<T>(self: &Self, p: Addr<T>, b: Block<T, Self>)
        [{ affirm base(b) = p; affirm whole(b); affirm allocator(origin(b)) = self; affirm forall i in 0..cap(b): !filled(b, i); }] [{ }];
};
```

These are the contracts of `Addr::alloc`, `Addr::resize` and `Addr::free` in `POINTERS.md`, with the allocator added. Those three stay as the primitives that `System` is written with. A container calls `a.alloc`, `a.resize` and `a.free` on its region, never the primitives, so the `Vec::push` of `POINTERS.md` calls `a.resize`.

An allocator is state that is shared and changes, and the language has no other such value. So an allocator's functions are not functions of their arguments: two calls of `alloc` give two blocks, as `fresh(origin(...))` says, and the validator treats them as it treats the readers of the input (`Mir.readersOfInput`, `fnReads`), never taking two calls to be the same value. An allocator's own code is where the memory model of the program meets one it manages itself. `System` is `extern fn` calls of the system's `malloc`, `realloc` and `free`, and an `Arena` hands out pieces of its chunks, which needs `Block::assume` until ghost collections of permissions exist (`POINTERS.md`, decision 3). So the allocators of the library are trusted code, few and short, and `tersus assumptions` lists them. A program that uses them proves everything else.

### The allocators of the library

- **`System`**: no fields, global. Its functions are direct calls of `malloc`, `realloc` and `free`, with the check for `Out of memory` of `tersus_box_new`.
- **`Arena`**: a bump allocator over chunks it takes from `System`, which it frees all at once when it is dropped. `free` of the last block given out takes the room back, and `free` of any other block does nothing. `resize` of the last block grows it where it is. `resize` of any other block copies it and leaves the old room unused, so a list that grows by doubling in an arena leaves at most as much again behind it. `Arena::reset(arena)` keeps the first chunk and frees the rest. An arena takes its chunks from `System` and has no region of its own, which keeps the number of kinds of allocator finite (see Native code).
- **`Checked`**: the checking allocator of `TERSUS_CHECK`, in Tersus. It counts the live blocks, fills a freed one with `0xDD`, reports a block freed twice, and reports a leak when it is dropped with blocks still out. It is a local like an arena (`checked = Checked::new(); with checked { ... };`), so it needs no statics.
- **`Fixed<n>`**: a bump allocator over an `Array<Int, n>` held inline, for code that must not use the heap. It is used only through a lend, as every local allocator is, so its words are never copied. `tryAlloc` gives an `Option` when it is full.

Every value is a number of words today, so every block is aligned to a word. When step 25 brings a layout in bytes, `alloc` takes the alignment of `T`, and a bump allocator rounds up to it.

### Failure

Every allocation made through a region ends the program with `Out of memory` when it fails, as today. An allocator that can be expected to fail also has `fn tryAlloc<T>(self: &Self, n: Int) -> Option<(Addr<T>, ghost Block<T, Self>)>`, which is called by name. A context that can fail would make every function that allocates return a failure, and that is not part of this design.

## Native code

### A region is a pointer to its allocator, or nothing

After the type checker, every region in the program is known at every call: a global allocator, a parameter, or a local opened by `with`. For native code:

- **A region parameter of a function is a hidden parameter**, `&K` for the kind `K` of its allocator (the type the region is, or the type of the local that `with` opened). For a `K` of no fields that is nothing, so a region in `System` passes nothing. For an `Arena` it is one word, the address of the local that `with` lent. That address is safe to pass because the block outlives every value in the region.
- **`MirMono` makes a copy of a function for each kind of allocator** its regions take, keyed by the kind and not by the region. A thousand `with` blocks over arenas give one copy of `build` for `Arena`, not a thousand, and recursion through `with` reaches no new key. The kinds are the allocator types of the program, which are few. A kind that names another (an allocator with a region of its own) could grow without end under recursion, so `MirMono` rejects that, naming the cycle.
- **A function that does not use its region does not take it.** A function whose body, and whose callees' bodies, make and free nothing in a region has the hidden parameter removed and is not copied per kind. So `count(tree: &Tree)` is compiled once, whatever region the tree is in. This is an optimization over the call graph, and it changes no type. The signature says the region whether or not the body uses it.
- **Drops are code made per type** (step 30 (a)), after `MirMono`, so the drop of a `Box<Node, a>` is a direct call of `Arena.free` with the hidden handle, and the drop of `Box<Node, System>` a direct call of `free`. Nothing dispatches at run time. The C runtime's walk of descriptors, which calls `release` and cannot reach an allocator, is gone before this step.

**Programs that use only `System` do not change.** A `System` region is erased before `MirMono`. A copy of a function or a type for `System` keeps the name it has today (`StdList<Int>`, not `StdList<Int, System>`, so the matching of `StdList` instances by name in `MirLists` and the MIR checker is unchanged), and a program with no other region skips the region passes, as `MirMono` already returns a program that has no generics unchanged. The tests of that are `TestMirEmit`, the fixpoint of `TestBootstrap`, and a test that the descriptor tables of every example are the same text.

### Drops that free nothing

A drop of a list of `Int` in an arena walks nothing, but it calls `free`, which does nothing unless the list was the last thing given out. A drop of a tree in an arena walks every node to free each one. Neither is wanted.

An allocator that frees in bulk says so by implementing the marker trait `trait BulkFree: Allocator { };`. Where the drop of a type is made for a region of such a kind, the frees are left out, and so is the walk of every part that owns nothing but memory. A part owns nothing but memory when it has no `impl Drop` and nothing linear in it (step 27), worked out over its fields. A file in an arena is still closed.

The drops are made per type after `MirMono` (step 30 (a)), so the question "does this drop do anything" is asked of the type with its kinds known. `MirOwnership` still places every drop. The decision is only what the drop's code does, so the pass order does not change. The proof of `Box`'s drop is unchanged: `BulkFree` is a promise of the allocator's (trusted) code that `free` may be left out, and it is erased like the permission it would have consumed. This is a cost and not a meaning, and it is the reason for the comment in the example at the top.

## Implementation

What it needs first:

- step 25: `Addr`, `Block`, tuples, ghost fields and results erased from the layout;
- step 26: drops;
- step 29: `Box` and `List` in the library;
- step 30 (a): drops and clones made per type, after `MirMono`;
- step 22: functions of a trait with type parameters of their own (`alloc<T>`).

It does not need the linear types of step 27. An allocator is not Copy, and `with` lends it, which the language already has.

The stages, each with the tests that show it done:

1. **Regions with only `System`.** The kind `Alloc`, region parameters on the types of the library, regions in the type checker (unwritten is the context, borrows and equality ignore regions, made values take the expected region, `tersus sig`), and their erasure. Every program means what it does today, and the IR, the descriptors and the bootstrap seed are byte for byte the same.
2. **`with`, written regions, and `Arena`, `Checked` and `Fixed`.**
   - The block, its fresh region, its scope and the drops at its exits, built on the CFG in `MirOwnership`.
   - Hidden handles, and `MirMono` by kind.
   - The heap of `MirEval` keeps blocks per allocator, so the interpreter that `testNative` compares with reports a block freed by the wrong allocator.
   - A new group, `TestAllocators`: a tree in an arena, a list in a `Fixed`, a leak caught by `Checked`, and a recursive function that opens a `with` in each call.
   - `examples/arena.tersus`, with its expectation in `TestPipeline`.
   - Rejected programs in `examples/rejected/` for: a value used after its block, one returned from inside it, one put into an outer list, a `merge` of two regions, and an arena assigned inside its own block.
3. **`TERSUS_CHECK` in Tersus.** The native tests run under `with checked { ... }` in place of `-DTERSUS_CHECK`, and the checking code in `LlvmRuntime` is deleted (step 30 (c)). Valgrind stays the second opinion.
4. **`BulkFree`.** A test that a dropped tree in an arena calls nothing, and that a file in an arena is still closed.

Stage 1 is where the cost to users shows: every message about a type is now able to name a region. Before stage 2, the messages of the examples and of `examples/emit.tersus` (with only `System`, none should mention one) and the output of `tersus sig` are reviewed. That review is the checkpoint for whether the elision rules are right.

## Limitations, and what is left for later

- **Function values.** A function taken as a value is taken with its context `System`, unless its type writes a region: `fn() -> List<Int, a>`. A function value in another region needs its handle with it, which is a closure, and closures and the validation of calls of function values (step 18) come first.
- **Tasks.** The language has none. When step 28 adds them, a task may be given a value in a global region, or be lent a local allocator by name. It is never given the context implicitly, so that two tasks do not share an arena without saying so.
- **One handle for many kinds.** A `Dyn` allocator (an address and a table of `alloc`, `resize` and `free`) would let code that allocates seldom be compiled once for every kind, at the cost of an indirect call. Nothing needs it while programs use two or three kinds.
- **Arenas proved, not assumed**, once ghost collections of permissions exist (`POINTERS.md`, decision 3): the arena keeps the blocks it gave out in a ghost map and proves that a chunk is freed whole.

## What the reviews of the first version found

| Found | Answer |
|---|---|
| An allocator stored in every `Box` and list costs a word each (a tree node of 24 bytes became 40), and the brand already proves what the word was for | Containers store no allocator. A region is a hidden parameter of the functions that use one, nothing for `System` (Native code) |
| The runtime's `tersus_drop` cannot reach the right allocator | Drops are made per type after `MirMono` (step 30 (a), now a prerequisite), as direct calls with the handle |
| "Linear and lent" contradicted "held by every Box" | The allocator is a local that `with` lends. What a function gets is `&K`, and values hold nothing |
| `clone` could not move a value between allocators | A borrow ignores its region, so `clone(self: &Self) -> Self` gives the region it is expected in |
| Equality and literals failed across allocators | Equality ignores regions, and a made value takes its expected region |
| Which functions allocate was inferred from bodies, so a signature changed when a callee did | Every function has the context in its signature, and the call graph only removes unused handles, as an optimization |
| "Arguments win, then context" was a special rule | It is unification, with the caller's context for a region that nothing decides |
| An accumulator from before a block could not be pushed to inside it | `push` takes its region from the list, and the pushed value is made where the list expects it |
| Drops at a function's end let an arena be freed before what was in it | Every exit of a `with` drops its locals, and the arena is lent for the block |
| A brand per `with` gave a copy of a function per block, and no end under recursion | Copies are per kind of allocator, and a brand is a type variable of the block, which no callee can name |
| `System` would rename instances and change the descriptors | `System` is erased, and a copy for it keeps today's name |
| `Arena` needed assumptions that the design said it had none of, and `Checked` needed statics | Allocators are trusted code listed by `tersus assumptions`, and `Checked` is a local |
| A permission from a local allocator's `alloc` could leave the block with a bare address, and be used after the arena was gone | `Block<T, a>` is branded with its region, so it is scoped like any value of that region (Allocators, The trait; The with block) |
| The contracts differed from `POINTERS.md` | They are the contracts of `Addr::alloc`, `resize` and `free`, with `allocator(origin(b))` in place of a new relation |
| `FREES` needed per-instance drops and could skip a file's | `BulkFree` acts on drops made per type after `MirMono`, and only on parts that own nothing but memory |

## Changes to other documents

- `README.md`: step 32 points here. When stage 3 is begun, step 30 (c) says that it is done here.
- `POINTERS.md`, when step 25 is built: the region of `Block<T, a>` (ghost, so erased with it), `allocator(origin(b))` and `fresh(origin)` in its table of ghost functions, `Addr::alloc`, `resize` and `free` as the primitives of `System`, and the library's containers calling their region.
- `LANGUAGE.md`, at stage 1: regions, where they are left out, borrows and equality; at stage 2: `with`, its scope, and the messages.
