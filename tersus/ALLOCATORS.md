# Allocators (design)

> **Draft.** This is a proposal for step 32 of the roadmap in `README.md`. It builds on `POINTERS.md` (step 25), `DROPS.md` (steps 26 and 27) and the library `Box` and `List` of step 29. Nothing here is built.

## The idea

Every value on the heap comes from one allocator today: `allocate`, `release` and `reallocate` in `LlvmRuntime`, over `malloc`. A program cannot put a tree in an arena, build a parser's tokens in a buffer that is thrown away whole, or run a test under a checking allocator except by compiling the runtime with `-DTERSUS_CHECK`.

The design lets a block of code choose the allocator for what is made inside it, including what the functions it calls make:

```tersus
fn parse(text: &String) -> Int [{ }] [{ }] {
    arena = Arena::new(4096);
    with arena {
        tokens = tokenize(text);   // the list and every string in it are made in the arena
        tree = build(tokens);      // so is every Box of the tree
        n = count(tree);
    };
    return n;                      // the arena is freed whole when it is dropped, with no walk of the tree
};
```

`tokenize` and `build` name no allocator, so they use the one the caller is in. The rest of this document is how that is made safe and free of cost: the context is written as a block, but it is decided when the program is compiled, and the allocator of every value on the heap is in its type.

## Design choices

### The context decides what is made, not what is freed

A context that is only known at run time (a global "current allocator" that `with` sets and puts back, as in Odin or Jai) is the obvious way to do this, and it is unsound in two ways:

- **The wrong allocator frees.** A list made in the arena and returned from the block is pushed to, or dropped, outside it. `stdListPush` grows it with whatever allocator is current then, and its drop gives it back to that allocator, which never gave it out.
- **A value outlives its allocator.** The arena is freed while something made in it is still held, and that thing points at freed memory. The validator cannot see it: the allocator is in neither the types nor the facts.

The first can be patched at run time by recording the allocator in a header of every allocation, which costs a word and a load at every free. The second cannot be patched at run time at all. So:

- **Rule 1.** The context chooses the allocator only where a value is made: `Box::new`, a list literal, `stdListNew`, `Array::boxed`, a string literal and a `clone`. Everything done to a value that already exists (`push`, `set`, `pop`, the growth of a list, its drop) uses the value's own allocator, which it holds.
- **Rule 2.** The allocator of a value is part of its type, so that rule 1 is a check of types, and a value that would outlive its allocator is rejected (see Escape).

### The allocator is a trait over blocks

An allocator gives out and takes back the blocks of `POINTERS.md`. Each block gains one ghost fact, which allocator it came from, so that "freed by the allocator that made it" is an ordinary proof obligation of `free` and costs nothing at run time:

```tersus
trait Allocator {
    fn alloc<T>(self: &Self, n: Int) -> (Addr<T>, ghost Block<T>) [{ affirm n >= 0; }]
        [{ affirm base(return.1) = return.0; affirm cap(return.1) = n; affirm whole(return.1); affirm from(return.1, self); }];
    fn resize<T>(self: &Self, p: Addr<T>, b: Block<T>, n: Int) -> (Addr<T>, ghost Block<T>)
        [{ affirm base(b) = p; affirm whole(b); affirm from(b, self); affirm n >= cap(b); }]
        [{ affirm cap(return.1) = n; affirm whole(return.1); affirm from(return.1, self); }];
    fn free<T>(self: &Self, p: Addr<T>, b: Block<T>) [{ affirm base(b) = p; affirm whole(b); affirm from(b, self); affirm empty(b); }] [{ }];
};
```

(`resize` keeps what the slots of `b` hold, as `Addr::resize` of `POINTERS.md` does; `empty(b)` is that no slot is filled.) `from(b, a)` is a ghost relation like `origin(b)`: `split` and `join` keep it, and `join` asks it of both parts.

The allocators of the library:

- **`System`**, of no fields, over the system's `alloc`, `realloc` and `free` (the `extern fn`s of step 30 (b)). It is the default everywhere.
- **`Arena`**, a bump allocator over blocks of its own: `free` does nothing unless the block is the last one given out, and dropping the arena frees all of it.
- **`Checked`**, the allocator of `TERSUS_CHECK` written in Tersus (step 30 (c)): it counts the live blocks, fills a freed one with `0xDD`, and reports a leak when it is dropped with blocks still out.
- **`Fixed<n>`**, a bump allocator over an `Array<Word, n>` held inline, for code that must not use the heap at all.

### Containers carry their allocator, with a default

The types that own an allocation directly, the ones whose code calls `alloc` and `free`, take the allocator as a type parameter with a default, and hold a value of it:

```tersus
struct Box<T, A: Allocator = System> {
    addr: Addr<T>,
    alloc: A,
    ghost blk: Block<T>,
} invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm filled(blk, 0); affirm from(blk, alloc); }];
```

and the same for `Buffer<T, A>`, `StdList<T, A>` (over a `Buffer<T, A>`), `Vec<T, A>` and `String<A>`. The drop of a `Box` frees its block with `self.alloc`, and the invariant `from(blk, alloc)` is what proves it the right allocator, so rule 1 is proved and not only type-checked.

The value of `A` costs what the allocator is: no words for `System`, `Checked` or any allocator of no fields, and one word (the address of the arena) for an `Arena` used through a handle. A program that names no allocator has `System` everywhere and the same IR as today, so `TestMirEmit` and the fixpoint test of `TestBootstrap` are unchanged by every stage that leaves `System` the only allocator in use.

### Where the allocator is in a type

The question is whether only containers say their allocator. They are the only types that *have* one: an allocator parameter is introduced by a type that holds a `Block`, and nothing else. But every type that *holds* a container has its allocator too, as a `struct Doc { lines: List<String> }` does through its field. If that were not in `Doc`'s type, `Doc` could only hold lists of `System`, and

```tersus
with arena {
    d = Doc { lines: readLines() };   // the lines are in the arena
};
```

would be rejected, because the field is a `List<String, System>`. Writing `struct Doc<A: Allocator> { lines: List<String<A>, A> }` by hand on every type would make the context useless in practice, since most types are user types, and Rust's experience with `Vec<T, A>` (an allocator parameter that every type and function above it has to repeat) is the cost to avoid.

So the allocator is in every type that owns memory, but it is written only where the program wants to fix it:

- **An unwritten allocator is a parameter.** A struct or an enum whose fields mention a type that takes an allocator, with that allocator left out, gains one implicit parameter, `Doc` is `Doc<A>`, and all such fields share it. A value is then in one allocator all through (a tree made under an arena has every node in it, through `Box<Node>` in `Node`), which is what an arena is for.
- **A written allocator is fixed.** `struct Cache { entries: List<Int, System> }` has no implicit parameter, and a `Cache` is made the same way under any context. A type that wants two allocators says them: `struct Pair<A: Allocator, B: Allocator> { left: List<Int, A>, right: List<Int, B> }`.
- **A type that holds nothing on the heap has no parameter**, so `Int`, `Array<Int, 4>`, a struct of numbers and an `Addr<T>` are unchanged. A `Block<T>` says its allocator with the ghost `from`, not with its type, so that the primitives of `POINTERS.md` stay the same.
- **A borrow does not add one.** A `&List<Int, A>` is the list's type behind a borrow, with the list's `A`.

This is the rule Rust has for lifetimes in a function signature, applied to types: elided where there is one obvious choice, and written where there is not.

### Functions take the allocator of their caller

A function that makes something on the heap without naming an allocator, or calls one that does, has an implicit allocator parameter as a generic function has a type parameter. One rule decides it, for the whole signature and the body together:

- Every unwritten allocator in the types of the parameters taken by value and of the result (`fn build(tokens: List<Token>) -> Tree`) is the function's implicit `A`, and so is the allocator of everything the body makes with none named.
- An unwritten allocator behind a borrow (`fn tokenize(text: &String) -> List<Token>`) is a fresh parameter of its own, decided by the argument and by nothing else. What is borrowed is only read, so its allocator is never used, and `tokenize` called in the arena makes its tokens in the arena whatever the text was made in.
- `A` is unified with the allocators of the arguments taken by value at a call. If they decide it, they win: a value's allocator is a fact about the value, the function may grow or free what it is given, and the context is only the default.
- If they do not decide it (`fn make() -> List<Int>`, or arguments that are borrowed or hold nothing on the heap), `A` is the allocator of the context at the call: the one of the `with` the call is in, else the caller's own `A`, else `System` at `main` and in a proof.
- A function that wants two allocators, or a fixed one, says so: `fn copyTo<A: Allocator, B: Allocator>(l: &List<Int, A>, into: &B) -> List<Int, B>`.

Which functions allocate is worked out over the call graph, as `Mir.readersOfInput` works out which ones read the input, and `MirMono` makes a copy of a function for each allocator it is called with, as it does for the type parameters of generics. A call never dispatches at run time, and a function called only under `System` is compiled once, as today.

### Escape is a type check

An allocator of no fields, used by its type, lives for the whole run: `System`, `Checked` and an allocator in a static are *global*, and a value made in one can go anywhere. An `Arena` held in a local is not: it is freed when the local is dropped. `with` is where the two differ:

- `with a { ... }` over an allocator of a global type uses that type, and values made in the block are like any others.
- `with a { ... }` over a local gives the block a fresh, private type for the allocator (an existential, opened for the block), as a type parameter of a function is private to its body. The allocator held by the containers made inside is the address of `a` (one word), of that type.
- **No value whose type mentions the private type may leave the block**: the block's locals that are used after it, an assignment to a local of the function that was declared before it, a `return` from inside it. `tokens` in the example above may not be used after the block, and `n`, an `Int`, may. The message names the value and the allocator: `tokens is made in arena and cannot be used after the with block that made it; clone it into another allocator first`.
- A value is moved out of the arena by a `clone` under another context, which makes a copy in that allocator: `kept = clone(tokens);` in a block of `System` inside the arena's block.

The private type is what makes holding the address of the arena in every container safe without lifetimes on stored borrows, which the language does not have: nothing that holds the address can be reached once the block has ended, and the arena outlives the block because it is a local of the function that holds the block.

An allocator is a linear value (step 27): it is not copied (a `with` lends it), and dropping it is what frees what it holds, so an `Arena` that is reset needs no proof that nothing points into it, because the escape check has already said that nothing can.

### Dropping what is in an arena

A value in an arena is dropped as any other value is: its drop runs the drops of what it holds, which matters for an element that owns something that is not memory (a file, a handle of step 27). For memory alone that work is wasted, since the arena's `free` does nothing. An allocator may say so, `const FREES: Bool = false;` in its impl, and `MirOwnership` then emits no drop for a value whose only ownership is memory in such an allocator (it asks this in `needsDrop`, as it asks whether a type has a drop). This is a cost and not a meaning: a program that relies on it is not wrong if it is not done.

### Allocation that fails

`alloc` of `System` ends the program with `Out of memory` when the system has none, as `tersus_box_new` does today, and so does every allocation made through the context. An allocator that can be expected to fail (`Fixed<n>`, an arena of fixed size) also has `tryAlloc`, which gives an `Option`, and is used by name. A context that can fail would make every function that allocates return a failure, which the language has no light way to say, so it is not part of this design.

## Implementation

The stages, each with the tests that show it done:

1. **Prerequisites.** Steps 25 (addresses and blocks), 26 (drops), 27 (linear values) and 29 (`Box` and `List` in the library). Until those are done the allocator is in the C runtime, where only the context at run time is possible, and this design does not add one: a stop-gap would be the unsafe design above, to be taken out again.
2. **The trait and `System`.** `Allocator`, `from(b, a)` in the proof engine, `System`, and the allocator parameter with its default on `Box`, `Buffer`, `StdList`, `Vec` and `String`. Nothing in a program changes, and the IR of every example is the same (`TestMirEmit`, `TestBootstrap`).
3. **Allocators by name.** `Box::newIn(x, a)`, `List::newIn(a)`, `Array::boxedIn(n, x, a)`, `cloneIn(x, a)`; `Arena`, `Checked` and `Fixed<n>`; the heap of `MirEval` keeps one map of blocks per allocator, so that the interpreter that `testNative` compares with reports a block freed by the wrong one. A new group, `TestAllocators`, runs a tree in an arena, a list in a `Fixed`, and a leak caught by `Checked`.
4. **The implicit parameter of types and functions.** The rule of where the allocator is in a type, in `TypeCheck` (an unwritten allocator in a field or a signature is a fresh variable, unified at construction and at calls); which functions allocate, over the call graph; the copies per allocator in `MirMono`.
5. **`with`.** The block in `Parse` and `TypeCheck`, the private type of a local allocator, and the escape check; `examples/arena.tersus` with its expectation in `TestPipeline`, and rejected programs in `examples/rejected/` for a value used after its block, a value returned from inside it, an assignment to an outer local, and two allocators in one container without a second parameter.
6. **`TERSUS_CHECK` in Tersus.** The native tests run under `with Checked { ... }` around `main` in place of `-DTERSUS_CHECK`, and the checking code in `LlvmRuntime` is deleted (step 30 (c)). Valgrind stays the second opinion.
7. **No drop for memory in an arena** (`FREES`), last, since it is an optimization, with a test that a file in an arena is still closed.

## Changes to other documents

- `README.md`: step 32 points here (done), and says that it is where the allocator of the runtime and the checking allocator of step 30 (b) and (c) go; step 30 can say the same when either is begun.
- `POINTERS.md`: `alloc`, `resize` and `free` become the methods of `System`, and blocks gain `from(b, a)`.
- `LANGUAGE.md`, when stage 5 is built: `with`, the allocator parameter of types, the escape check and its message.

## Decisions to make

1. **The syntax of the block.** `with a { ... }` reads well; `using a { ... }` would leave `with` for a later resource block (a file closed at the end, as Python's `with`). Neither is a keyword yet.
2. **A handle that dispatches at run time.** A copy of every allocating function per allocator can make a program large. A `Dyn` allocator (an address and a table of `alloc`, `resize` and `free`) that a program can choose by name would trade the copies for an indirect call, for code that allocates seldom.
3. **Allocators in statics.** A global arena (`static scratch: Arena`) needs statics, which the language does not have, and a rule for when it may be reset.
4. **Tasks and threads.** The language has neither. When step 28 adds tasks, a task should take the allocator of the code that starts it only if it is global, and be given a local one by name, so that two tasks never share an arena without saying so.
5. **Whether an unwritten allocator in a field of a recursive type may differ along the recursion.** The rule above says no (one parameter for all of a type's fields, and `Box<Node>` in `Node` has `Node`'s), which is what an arena wants; a type that wants its nodes in different allocators writes a second parameter.
