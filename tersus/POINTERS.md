# Raw pointers (design)

> This is the design of step 25 of the roadmap in `README.md`, and of the part of step 29 that puts `Box` in the library. It replaces Part 3 of `DROPS.md`, and the `*T` that step 25 sketches. It is built: see Status, at the end, for how it differs from what is written here, and for what is left to step 29.

## The idea

The validator never models a heap. A local's value never changes, an assignment gives the local a new iota, and a fact stays true for the rest of the path (MIR.md, Validation). Every proof the language has relies on that. A raw address breaks it: two addresses can name the same memory, a store changes memory without assigning a local, and nothing about an address says whether its memory is still allocated.

The design splits a pointer into two values, following separation logic (and Verus's `PointsTo`):

- **`Addr<T>`, the address**: a runtime word. It is Copy, can be aliased, offset, kept in many places and passed to C, and allows nothing by itself.
- **`Block<T>`, the permission**: a *ghost*, *linear* value that `alloc` returns with the address. It has no runtime form and is erased after validation. It says which memory it is for and what that memory holds. Every operation on memory needs it.

The permission is a value, so the validator's model survives. A write takes the permission and gives a new one, which is an assignment with a new iota, as `set` is for an array. Addresses can alias because the permission cannot: it is linear, so there is only ever one for a piece of memory. The properties that make raw memory safe are then **proved, in ordinary code**:

- every access is in bounds;
- no slot is read before it is written;
- nothing is used after it is freed, and nothing is freed twice;
- no element is lost when a block is freed;
- the permission to memory is exclusive.

**What is unsafe is an assumption, not a pointer.** Code that uses addresses needs no mark, because what it does is proved. What cannot be proved is said with `assume`, `Block::assume` or the contract of an `extern fn`, and `tersus assumptions` lists them. Rust marks `unsafe fn` because its caller has to uphold something the compiler cannot check; in Tersus that something is an input contract, which the caller proves. So no function is marked.

## Design choices

These are the choices the rest of the document follows from, with the alternatives and why they lose.

### A Block names its memory, as a ghost

A permission has to say which memory it is for. If it did not, nothing would stop a program from using the permission of one block with the address of another, and the proof about the first would be applied to memory it does not describe. So a `Block` has a ghost `base(b)`, an `Addr<T>`, and every operation asks `p = base(b)` of the address it is given.

The address is not *in* the `Block` as runtime data. If it were, the `Block` would be the owning pointer of the first draft (`Ptr<T>`), and could not be aliased. The two halves are separate values tied by one equation that the proof carries. Natively the operation uses `p`; the validator checks that `p` is the address the permission names.

A library type that wants the two together has them as two fields and the equation as its invariant (`Box`, `Vec`, and `Buffer<T>` below), so a program working with a buffer never writes the equation.

### Facts are about indexes, not addresses

An operation takes the base address and an index: `Addr::get(p, i, b)`, not the address of the slot. What the validator knows of a block is then two ghost arrays indexed from 0, which `filled(b, i)` and `at(b, i)` read. Every fact about a block is a fact about an array, which the engine already proves things about: `forall`, its triggers, the frame facts of `set`, and the case splits of A linked list in an array.

The alternative keys facts by address (`filled(b, p)` for `p = offset(base(b), i)`). To use a fact the engine would have to find the `i` for an arbitrary address term, `p` being a field read from a node or a result of a call, which needs an `index(b, p)` function and a rewrite of every address into `offset(base, index)` form: new engine machinery, for every access. With indexes, address arithmetic leaves the proofs almost entirely. The engine needs two facts about addresses, `offset(p, 0) = p` and `offset(offset(p, i), j) = offset(p, i + j)`, used when a block is split or joined.

An address into the middle of a block (to give part of a buffer to a function, or to C) is made by splitting the permission, so that the address is the base of a block of its own (see Splitting).

### Separation needs no proof

Two blocks never overlap, because every block comes from an allocation or from splitting another, and permissions cannot be copied. So a write through one block cannot change what another says, and nothing has to prove that two addresses differ or that two ranges are disjoint. The engine needs no injectivity of `offset` and no inequalities between addresses. This is the main thing linearity buys: the frame is free.

### A block knows its allocation

Splitting a block and joining it back means that a block can be a part of an allocation. `free` and `resize` need the whole of one, and `join` must not glue together two blocks that are adjacent by chance but were allocated apart (freeing the result would free memory the allocator gave out twice). So each block has a ghost `origin(b)`, the allocation it is part of, and `whole(b)`, which says it is all of it. `alloc` gives a whole block with a new origin, `split` keeps the origin and makes the parts not whole, and `join` needs both parts to have the same origin and gives back a whole block when the parts cover it.

### Blocks of slots, not of bytes

A slot holds a whole `T`, and is filled or empty as a whole. Writing the fields of a struct in a slot one at a time, or one byte of an `I32`, is not possible. Rust's `MaybeUninit` and C allow it; here it would need permissions per field, which is a later extension (see Decisions). Most code writes whole values, and code that fills memory piece by piece (a C function filling a buffer) does it through an `extern fn` whose contract says what it filled.

### Typed addresses

`Addr<T>` carries a type, though it promises nothing about the memory. What says the memory holds `T`s is the `Block<T>`. The `T` gives a stride for `Addr::offset`, the types of what an operation reads and writes, and a static match: an operation needs a `Block<T>` for an `Addr<T>`, so using a `Block<Int>` with an `Addr<Node>` is a type error, found before any proof. An untyped address would be simpler, but it would lose that check and the types in the signatures of `extern fn`s. Casting an address is free; reinterpreting memory is a change of permission, `Block::cast`, and that is checked.

### Primitives, and a buffer over them

The builtins take the address and the permission apart, because that is the general form (an address can be in a node, in a C struct, in many places). The library adds `Buffer<T> { addr: Addr<T>, ghost blk: Block<T> }`, the two together with the invariant `base(blk) = addr`, with the same operations as methods. That is the type most code uses, and it reads like the owning pointer of the first draft.

## `Addr<T>`

`Addr<T>` is the address of a `T`, or null. It is one word, Copy, and `=` compares addresses. These operations need no permission and are allowed anywhere:

| Operation | Gives |
|---|---|
| `Addr::null()` | the null address |
| `Addr::offset(p, i)` | the address `i` values of `T` past `p` (an `Int` `i`, negative allowed) |
| `Addr::cast(p)` | the same address as an `Addr<U>`, with `U` decided by the use, as for `Array::empty()` |
| `Addr::toInt(p)` and `Addr::fromInt(n)` | the address as a number and back (for hashing, alignment, and memory-mapped I/O) |

None of them can do harm: an address that is wrong is useless without a permission for it. The validator knows the two offset facts above and nothing else about addresses.

**`void*` is `Addr<Opaque>`.** `Opaque` is a type with no size. Its address has no stride, so it cannot be offset; it can be compared, passed and cast, as in C. A `Block<Opaque>` cannot exist.

## `Block<T>`

`Block<T>` is the permission to a run of slots of `T`. It is a ghost type: it can be held in a ghost local, a ghost parameter (lent as `&Block<T>`, or by value), a ghost field or the ghost part of a tuple (see Ghost values), and it is linear: it has to be freed, given on, or put in a value that is. It has no literal: a program cannot write one, only get one from the operations below.

The validator knows a block through ghost functions, usable in contracts, `affirm`, `define` and invariants:

| Function | Is |
|---|---|
| `base(b)` | the `Addr<T>` of slot 0 |
| `cap(b)` | the number of slots, at least 0 |
| `filled(b, i)` | slot `i` holds a value |
| `at(b, i)` | that value, known only when it is filled |
| `origin(b)` | the allocation the block is part of (an opaque ghost value, compared with `=`) |
| `whole(b)` | the block is all of its allocation |

`filled(b, i)` and `at(b, i)` are `get(filledOf(b), i)` and `get(contentsOf(b), i)` on two ghost arrays of size `cap(b)`, so what is proved about them is proved as for arrays.

### Operations on memory

`p` is the address the permission names (each operation needs `p = base(b)`), and `i` an index with `0 <= i < cap(b)`.

| Operation | Needs besides | Gives |
|---|---|---|
| `Addr::alloc(n)` | `n >= 0` | `(p, ghost b)`: `base(b) = p`, `cap(b) = n`, `whole(b)`, a new `origin(b)`, no slot filled |
| `Addr::get(p, i, b)` | `filled(b, i)` | `at(b, i)`, a view: reading it moves nothing, and `b` is lent |
| `Addr::write(p, i, x, b)` | `!filled(b, i)` | a block with slot `i` filled with `x` |
| `Addr::take(p, i, b)` | `filled(b, i)` | `(at(b, i), ghost b2)`: the value, and a block with slot `i` empty |
| `Addr::dropValue(p, i, b)` | `filled(b, i)` | a block with slot `i` empty; the value is dropped in place |
| `Addr::dropRange(p, i, n, b)` | `n >= 0`, `i + n <= cap(b)`, slots `i..i + n` filled | a block with those slots empty, each value dropped in place |
| `Addr::resize(p, n, b)` | `whole(b)`, `n >= 0`, no slot from `n` filled | `(q, ghost b2)`: `base(b2) = q`, `cap(b2) = n`, `whole(b2)`, a new origin, slots below `min(n, cap(b))` as they were |
| `Addr::free(p, b)` | `whole(b)`, no slot filled | `0` (there is no unit type); `b` is consumed |

Every operation that gives a block back says the rest: the same `base`, `cap`, `origin` and `whole` (except `resize`), and every slot it does not name as it was.

- **Dropping a value and freeing a block are different things.** `dropValue` ends the value in one slot: it runs that value's drop, which frees what the value owns (a list's elements, the block of a `Vec` in the slot) and leaves the slot empty. The block's memory stays allocated. `free` returns the memory of a whole allocation to the allocator, and runs nothing. A block is emptied with `take`, `dropValue` or `dropRange`, and then freed. This is Rust's `drop_in_place` and `dealloc`.
- **Why `free` needs every slot empty.** Natively nothing records which slots are filled: that is only in the permission, which is erased. So `free` cannot drop what is left, and a value still in a slot would be lost with everything it owns. Requiring empty slots makes "nothing is lost" a proof.
- **`write` needs an empty slot.** Writing over a filled one would lose a value that may own something. Replacing a value is `dropValue` then `write`.
- **A view does not outlive its block.** `get` is a view of `b`, as `get` of a list is a view of the list (MIR.md, Moves). Once `b` is given to an operation that changes it, the view is gone (`MirMoves` reports a use of it as a use of a moved value), which is what stops a read through a view after `resize` moved the memory or `take` emptied the slot. Moving the view out is refused (`cannot move x out of a Block, which still holds it: write clone(x), or Addr::take`).
- **`dropValue` and `dropRange` run `tersus_drop` with the descriptor of `T`.** For a type that owns nothing they do nothing natively, and are there only for the proof.
- **`resize` is `realloc`.** Moving a value in Tersus is copying its bytes, so a bitwise move of every filled slot is right. It needs the whole allocation, and the result is a new one.
- **What fails at run time and not in a proof**: an allocation the system refuses, and a size whose bytes overflow an `Int`. The program ends with an error, as for an overflow. No contract can promise memory.

### Splitting and joining

| Operation | Needs | Gives |
|---|---|---|
| `Block::split(b, i)` | `0 <= i <= cap(b)` | `(ghost lo, ghost hi)`: slots `0..i` and `i..cap(b)`; `base(lo) = base(b)`, `base(hi) = Addr::offset(base(b), i)`, slot `j` of `hi` is slot `i + j` of `b`, the same origin, neither whole unless the other is empty |
| `Block::join(lo, hi)` | `origin(lo) = origin(hi)`, `base(hi) = Addr::offset(base(lo), cap(lo))` | one block of `cap(lo) + cap(hi)` slots, whole when it covers its origin |

Both are ghost: they erase to nothing. Splitting is how a function gets part of a buffer (`fn fill(p: Addr<Byte>, ghost b: Block<Byte>)` given the upper half) and how an address into the middle of a block is the base of a permission (to pass to C). Linearity guarantees the parts can be joined back for `free`.

### Making blocks

A block comes from one of these, and from nothing else:

| Source | Proved |
|---|---|
| `Addr::alloc` and `Addr::resize` | yes |
| `Block::split` and `Block::join` of blocks the program holds | yes |
| `Block::cast` of a block the program holds | yes, when the layouts match (below) |
| a ghost field or tuple part of a value that is taken apart | yes: it is a move |
| `Block::assume(p, n)` | no: an assumption |
| the contract of an `extern fn` that returns one | no: an assumption |

Since a program cannot write a `Block` and cannot copy one, it can only use memory it was given a permission for. This is what makes `Box`, `Vec` and the rest safe to build by hand: a struct literal with a ghost `Block` field needs a block from one of these sources, and the struct's invariant ties it to the address.

Memory in a frame (the address of a local) is not in this list: Tersus has no address-of, and a permission to a frame would need to end when the function returns, which is a scoped ghost value the language does not have. It is a later extension.

### Reinterpreting memory

`Block::cast(b)` gives a `Block<U>` for the same memory, with the same base, origin and filled slots. It is allowed when `T` and `U` have the same layout (see Layout), and either no slot is filled or both `T` and `U` are *plain bits*: a type whose every bit pattern is a value and that owns nothing (the integers, `Byte`, and structs and arrays of them, with no ghost field). `Int` to a struct of two `I32`s is allowed; `I32` to `Bool` is not, since a `Bool` is 0 or 1. The source has to be plain bits too, because a value that owns something can have the layout of one that does not: a ghost field takes no room, so a one-word `Box<Int>` has the layout of an `Int`, and casting a filled slot of one to an `Int` would lose its allocation and its permission without dropping or consuming them. Anything else is an assumption.

## Interaction with proofs

**What a block is to the engine.** A `Block` local holds an iota like any value. Its facts are equations about `base`, `cap`, `origin` and `whole`, and facts about two ghost arrays. Each operation gives a new iota, with the equations carried over and the arrays changed by `set`. So a `Vec` with a `Block` is proved as a struct with an array and a length is proved now; the engine gains the ghost functions and the two offset facts, and no new kind of reasoning.

**Loops.** A loop that writes a block reassigns it, so its invariant has to say what it needs of the block at the head. `base`, `cap`, `origin` and `whole` are kept by every operation but `resize`, so they are candidates for the inferred invariants (LANGUAGE.md, Inferred invariants), and a program states only the facts about slots.

**Functions that take a block.** A function given a block by value, which gives one back, has to say in its contract what it kept: the equations, and which slots it did not change. That is the price of separation logic everywhere it is used, and it is the main burden on a programmer. Most code uses `Buffer`, `Vec` or `Box`, whose functions say it once, or lends the block (`&Block<T>`) to a function that only reads, which keeps every fact without saying so. A shorthand for "the same block except slots `i..j`" may be worth adding once examples show how often it is written (see Decisions).

**Values in slots.** `at(b, i)` is the value written there, and values do not change, so `Addr::take` gives back exactly the `x` that `write` put. For a slot that holds a list, `at` is the list, and its facts (`size`, its elements) carry over as for any value.

**Cost.** Every operation adds a frame `forall` over a ghost array, and a `Vec`'s invariant has two foralls of its own, so the proofs of a collection may be slow, as the proofs of a chain of `concat` are (LANGUAGE.md, Current Limitations). The first examples measure this before anything is built on them.

## Ghost values

A ghost value exists only for the validator. The ones this design needs are permissions, but the mechanism is general.

- **Where they are**: a ghost local (one that holds a ghost type), a parameter written `ghost b: Block<T>` (or `ghost b: &Block<T>`, lent), a struct field written `ghost b: Block<T>`, and a part of a tuple written `ghost` in its type, `(Addr<T>, ghost Block<T>)`.
- **They flow only into ghost places.** A ghost value can be given to a ghost parameter, field or tuple part, and mentioned in contracts. It can never become part of a runtime value (`b is a ghost value and the program cannot use it`). A runtime value can be used in a ghost place. A ghost function (`filled`, `at`, ...) cannot be called in code, so no branch depends on a ghost.
- **They are moved and linear like any value.** `MirMoves` runs before validation on MIR that still has them, so a permission used after it is consumed, or left unused, is reported as for any linear value.
- **They are erased after validation.** A pass after `validateProgram` and before `insertOwnership` removes ghost locals, ghost arguments, ghost fields and ghost tuple parts. `eval`, the ownership pass, `MirData` and both emitters never see them, and a struct's layout is its runtime fields only.
- **A struct with a ghost linear field is linear** (DROPS.md, Part 2), unless it has a `Drop`.

## Tuples

Every primitive above gives back two things: an address and a permission, or a value and a permission. A function returns one value, so these need tuples:

- **Types**: `(A, B)`, any number of parts, and a part can be `ghost`.
- **Values**: `(a, b)`, and the parts read as `t.0`, `t.1`.
- **Destructuring**: `(p, b) = Addr::alloc(4);`. Each part is moved separately, so a tuple can be taken apart without being Clone.
- **The validator** sees a tuple as a term with projections: `(a, b).0 = a`.
- **Natively** a tuple is an anonymous struct of its runtime parts, so the MIR and the emitters barely change.

Tuples are useful well beyond pointers: `replace` (below), a function that returns a result and a count, and every `Popped`-like struct a library declares today.

## Layout: bytes, not words

Natively every value is held in 64-bit words today: an `Int`, a `Bool` and a `Byte` are a word each, and a struct, an enum or an array is its parts' words (`LlvmRuntime`, `slotsOf` in `LlvmEmit`). An address makes layout visible, because the stride of `Addr::offset`, the bytes `Block::cast` compares and the memory a C function reads all depend on it. A `String` also takes eight times the memory it needs. So layout changes to C's, before addresses are built:

- **`Byte` is 8 bits**, and `Bool` is 8 bits (C's `_Bool`, 0 or 1).
- **Fixed-width integers**: `I8`, `I16`, `I32`, `U16` and `U32` join `Byte` (which is `U8`) and `Int` (which is `I64`). Each is a type of its own, with its range known to the validator wherever a value comes from, as `Byte`'s is (LANGUAGE.md, Bytes). Arithmetic and order stay on `Int`: `toInt(x)` widens, and `I32::from(x)`, `U16::from(x)` and so on narrow, with the range proved at the call, as `toByte(x)` does now. A number written out where one is wanted is converted, as for `Byte`. There is no `U64`, since it does not fit in an `Int`; a C `size_t` is an `Int`, which holds every size a program can allocate.
- **Structs use C's rules**: fields in the order they are declared, each at an offset that is a multiple of its alignment, and the size rounded up to the largest alignment. So every struct of fixed-width fields has the layout of the same C struct, and needs no annotation to be passed to C. Ghost fields take no room.
- **Enums** keep a tag followed by the largest variant, with the tag a `U32`. C has no equivalent, so an enum is not passed to C by address.
- **Arrays** are their elements, each `size(T)` bytes apart, as in C. The limit of an array held in a frame becomes 64 KB of bytes and not 8192 words.
- **What does not change**: an `Int`, an address, a function and a `Box` are 8 bytes, and the validator sees values, not bytes, so no proof changes. `eval` holds values and is unaffected.

**What it costs.** The emitters (both, in step), the runtime's descriptors and walks (`words` becomes a size in bytes and an alignment, and `tersus_drop`, `tersus_clone`, `tersus_equal` and `tersus_print` step by field offsets), the stride of a list's elements in `StdList`, `MirData`'s types, the `bootstrap/emitter.ll` seed, and the builtins that move bytes in and out (`writeByte`, `readByte`, `fileByte`, which become 8-bit). The same tests are the check: `TestNative` against `eval`, the heap model, `TERSUS_CHECK` and valgrind. It is mechanical, but it touches every place that counts words.

## Assumptions

What the validator cannot prove, a program says explicitly, in one of four ways:

| Form | What is assumed |
|---|---|
| `assume e;` | a fact, which the rest of the path then knows, as after an `affirm` |
| `Block::assume(p, n)` | a whole block of `n` slots of `T` at `p`, with a new origin and no slot filled, for memory the program did not allocate |
| `extern fn` | the contract of a function with no body that the emitter declares (step 30: `write`, `exit`, the system's allocator, a C library) |
| `axiom` | a rule of proof, as now |

`tersus assumptions <file>` prints every one in the program and its prelude, with its line. That list is everything the program's proofs take on trust, besides the builtins.

**What needs an assumption, at first:**

- **Memory that `alloc` did not make**: from C, the system, `mmap`, memory-mapped I/O. An `extern fn` that returns `(Addr<T>, ghost Block<T>)` gives the permission in its contract (with the slots it says are filled), or the program uses `Block::assume`.
- **Shared memory that is written**: a reference count over a mutable value, or memory shared between threads. Shared memory that is only read can be proved later with fractional permissions (a permission split into read-only parts that join back).
- **Reinterpretation** beyond what `Block::cast` checks.
- **A structure spread over many blocks**, such as a linked list of nodes allocated one by one. Each node has its own permission, so the structure needs a ghost collection of permissions (Verus uses ghost maps). Until that exists, a structure inside one block is proved (an arena, where links are indexes into the same block), and one over many blocks uses `Block::assume`.

## The library on top

### `Buffer<T>`

The address and the permission together, which is what most code that manages memory wants:

```tersus
struct Buffer<T> {
    addr: Addr<T>,
    ghost blk: Block<T>,
} invariant [{ affirm base(blk) = addr; affirm whole(blk); }];
```

with `Buffer::alloc(n)`, `get`, `write`, `take`, `dropValue`, `dropRange`, `resize` and `free` as methods that call the builtins with `self.addr` and `self.blk`, and contracts in terms of `cap(self.blk)`, `filled(self.blk, i)` and `at(self.blk, i)`.

### `Box<T>` (step 29)

A `Box` is a buffer of one filled slot. It has no assumption in it:

```tersus
struct Box<T> {
    addr: Addr<T>,
    ghost blk: Block<T>,
} invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm filled(blk, 0); }];

impl<T> Box<T> {
    fn new(x: T) -> Self [{ }] [{ affirm at(return.blk, 0) = x; }] {
        (a, b) = Addr::alloc(1);
        return Self { addr: a, blk: Addr::write(a, 0, x, b) };
    };

    fn unbox(self: Self) -> T [{ }] [{ affirm return = at(self.blk, 0); }] {
        (x, b) = Addr::take(self.addr, 0, self.blk);
        done = Addr::free(self.addr, b);
        return x;
    };
};
```

Making a `Box` by hand is safe: the invariant is checked at every struct literal, and a block for the address comes only from the sources above, so no code can wrap an address it does not own.

What the compiler does for `Box` by name today (looking through it for fields and `match`, `Box::new(p) = Box::new(q)` meaning `p = q`, the recursion check) becomes a language item, as step 29 describes. For the validator, `=` written between two `Box`es in a program means that they hold equal values, `at(a.blk, 0) = at(b.blk, 0)`, and not that they are the same value. The two cannot be the same relation: the engine substitutes equals into every term (congruence), so taking two separately allocated boxes with equal contents to be equal values would give `a.addr = b.addr`, a false equation that satisfies the check that ties an address to its permission. The same holds for every type that holds an `Addr` or a `Block`:

- **It has no structural `=`.** The `=` a program writes on it is the equality its library gives (for `Box`, the language item), which the validator reads as a relation of its own, defined by that equality's contract, and never as the equality of the two values as terms.
- **A `clone` of it does not promise `return = self`**, which is what `clone(x) = x` gives every other type (LANGUAGE.md, Moves, Clone And Copy). A copy is a new allocation, so its contract says what the contents are (`at(return.blk, 0) = at(self.blk, 0)`), and the copy is a different value with a different address.

### `Vec<T>`

`examples/vec.tersus` on an address. It needs no filler value, its `pop` gives the element back, and nothing in it is assumed:

```tersus
struct Vec<T> {
    addr: Addr<T>,
    cap: Int,
    len: Int,
    ghost blk: Block<T>,
} invariant [{
    affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = cap;
    affirm 0 <= len; affirm len <= cap;
    affirm forall j in 0..len: filled(blk, j);
    affirm forall j in len..cap: !filled(blk, j);
}];

impl<T> Vec<T> {
    fn new() -> Self [{ }] [{ affirm return.len = 0; }] {
        (a, b) = Addr::alloc(4);
        return Self { addr: a, cap: 4, len: 0, blk: b };
    };

    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm at(return.blk, self.len) = x; }] {
        (a, b) = (self.addr, self.blk);
        cap = self.cap;
        if self.len = cap {
            cap = cap * 2 + 4;
            (a, b) = Addr::resize(a, cap, b);
        };
        return Self { addr: a, cap: cap, len: self.len + 1, blk: Addr::write(a, self.len, x, b) };
    };

    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = at(self.blk, i); }] {
        return clone(Addr::get(self.addr, i, self.blk));
    };

    fn pop(self: Self) -> (Self, T) [{ affirm self.len >= 1; }] [{ affirm return.0.len = self.len - 1; }] {
        (x, b) = Addr::take(self.addr, self.len - 1, self.blk);
        return (Self { addr: self.addr, cap: self.cap, len: self.len - 1, blk: b }, x);
    };

    // Until step 26 gives Vec a Drop, a Vec is linear (it holds a permission), and the program frees it with this
    fn free(self: Self) -> Int [{ }] [{ }] {
        return Addr::free(self.addr, Addr::dropRange(self.addr, 0, self.len, self.blk));
    };
};
```

Before drops exist (step 26), linearity makes a `Vec` safe rather than leaky: a `Vec` that is not freed is an error (`v is linear and is not used`). `StdList` moves to the same form after step 26, which gives it a `Drop`.

### `Uninit<T>`: empty slots without addresses

Not every collection needs addresses. `Uninit<T>` is room for one `T` that may hold nothing, laid out as a `T`, with no tag and no drop of its own. It is the lighter way to get empty slots in a `Box` or an inline array (`Array<Uninit<T>, 8>`, a buffer in a frame).

- Ghost facts `filled(u)` and `at(u)`, and the operations `Uninit::empty()`, `Uninit::new(x)`, `Uninit::get(u)` (a view, needs `filled(u)`) and `Uninit::take(u)` (needs `filled(u)`, moves `u`).
- `array(n, Uninit::empty())` is accepted for any `T`, and `Array::uninit(n)` is a `Box<Array<Uninit<T>>>` of `n` empty slots.
- `replace(a, i, x)` moves `x` into element `i` of an array or list and gives `(set(a, i, x), get(a, i))`. It is useful beyond `Uninit`: today nothing can be moved out of an element.
- An `Uninit<T>` of a `T` that owns something is linear, and `Uninit::discard(u)`, which needs `!filled(u)`, consumes an empty one.

## Running it

- **`eval` needs a heap for `Addr`.** Addresses can be shared, so `MirEval` gets a store of allocations (a map from an allocation to its slots, with an address encoded as an allocation and an index) that the operations work on. It runs after ghost values are erased. It fails on a read of an empty or freed slot and on a double free, which a proved program cannot do, so on such a program it is a check of the assumptions. The older executor in `StdLib` refuses addresses. `Uninit` needs no heap: it is `VUninit (Maybe Value)`.
- **MIR.** The operations are `ListOp`s (`AddrAlloc`, `AddrNull`, `AddrOffset`, `AddrCast`, `AddrToInt`, `AddrFromInt`, `AddrGet`, `AddrWrite`, `AddrTake`, `AddrDropValue`, `AddrDropRange`, `AddrResize`, `AddrFree`, and the `Uninit`, `replace` and tuple operations), with words in `MirData`. `Addr T`, `Block T`, `Uninit T` and tuple types are new `Type` constructors; a ghost local has a flag. The ghost operations (`Block::split`, `join`, `cast`, `assume`) erase to nothing.
- **Native code.** An `Addr` is an `i64`. `alloc`, `resize` and `free` call the runtime's `allocate`, `reallocate` and `release`, so `TERSUS_CHECK` counts the blocks. `get`, `write` and `take` copy `size(T)` bytes at `p + i * size(T)`, `offset` adds `i * size(T)`, and `dropValue` and `dropRange` call `tersus_drop` with the descriptor of `T`. An `Uninit<T>` is laid out as a `T`, with a descriptor that drops, clones and compares nothing.
- **Both emitters, in step.** `LlvmEmit` and `examples/emit.tersus` gain the same cases, `examples/mir_reader.tersus` reads the new words, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` keeps them equal.

## Order of work

1. **Tuples**: types, values, projections, destructuring, moves of the parts, the validator's terms, and the emitters. These are independent of everything else.
2. **Linear types** (DROPS.md, Part 2), which permissions rely on.
3. **`Uninit<T>` and `replace`**, on the builtin `Box`: a proved `Vec` with no addresses, and a test of whether the invariant's foralls are cheap enough to prove at each operation.
4. **Ghost values**: ghost locals, parameters, fields and tuple parts, the check that they do not flow into runtime values, the linear check over them, and the erasure pass.
5. **Layout in bytes**: 8-bit `Byte` and `Bool`, the fixed-width integers, C's rules for structs, in both emitters and the runtime. This is independent of 1 to 4 and can be done at any point before 6.
6. **`Addr<T>` and `Block<T>`**: the types, the operations, the ghost functions and the two offset facts in the proof engine, split and join, the heap in `MirEval`, the emitters and runtime, `Buffer<T>`, `examples/addresses.tersus` (a buffer, a buffer split between two functions, and an arena-linked list, all proved), and a rejected program for each contract: read of an empty slot, write over a filled one, out of bounds, the permission of one block with the address of another, free of a part, join of blocks from two allocations, free with a slot filled, use after free, a view used after its block changed, a permission dropped.
7. **Assumptions**: `assume`, `Block::assume`, `extern fn`, and `tersus assumptions`.
8. **Drops (step 26)**, then `StdList` on an address, then `Box` in the library (step 29).

## Changes to other documents

- `README.md`, step 25: `Addr<T>`, `Block<T>`, ghost values, tuples and assumptions in place of `*T`, the marker in signatures and the contracts on `valid(p)`. Step 29: `struct Box<T> { addr: Addr<T>, ghost blk: Block<T> }` in place of `ptr: *T`, and `*[T]` as a `Buffer<T>`. Step 30: `extern fn` as an assumption.
- `DROPS.md`, Part 3: points here. Its owning pointer is now an address and a permission, and `Uninit` and `replace` cover what Part 1's section on containers needed. The order there changes: linear types come before pointers.
- `LANGUAGE.md`, when it is built: sections on tuples, ghost values, addresses and permissions, and assumptions, with the list of what `tersus assumptions` reports. Bytes (a `Byte` is 8 bits natively) and a new section on the fixed-width integers and layout.

## Decisions to make

1. **How a `drop` frees a permission (postponed).** Part 1 of `DROPS.md` gives `drop` a lent `self: &Self`, which cannot consume the linear permission inside the value. A type that holds a permission needs a `drop` that takes `Self`, without its fields being dropped again afterwards. This is decided with step 26.
2. **Must `free` find every slot empty?** It cannot drop what is left itself, since natively nothing records which slots are filled. The alternative is a `free` that asks nothing, and leaks whatever the filled slots own. That is safe, but loses the proof that nothing is lost. `dropRange` keeps the cost of the strict rule to one call for a `Vec`; whether the engine proves `free`'s `forall` over `0..cap` from `dropRange`'s result over `0..len` and the invariant over `len..cap` without help is untested.
3. **Ghost collections of permissions**, for structures over many blocks: a ghost map from addresses to `Block`s, and when to add it.
4. **Fractional permissions**, for proved sharing of memory that is only read (`Rc` of an immutable value, a buffer read by several functions at once).
5. **Permissions finer than a slot**: one per field of a struct in a slot, for building a value in place a field at a time and for an address of a field to give to C.
6. **Scoped permissions**, for the address of a local in a frame: a ghost value that has to be given back before the function returns.
7. **A shorthand for framing**, "this block is the one given except slots `i..j`", if the contracts of functions that take blocks turn out to repeat it.
8. **Wrapping arithmetic** on the fixed-width integers (for hashes and checksums), or only arithmetic on `Int` with checked narrowing, as above.

## Status

Built, as LANGUAGE.md (Tuples, Addresses and permissions, Linear types, Uninit, Assumptions, Fixed-width integers, Layout) describes it. Each step of the order of work above:

1. **Tuples**: `(A, B)`, `(a, b)`, `t.0` and `(a, b) = e;`. A tuple is an instance of a struct of the language, `Tuple2<A, B>` with fields `0` and `1`, so the MIR, the validator, the ownership pass and both emitters needed nothing new; the checker makes the instance from the types of the parts, and the lowering names it again once they are known.
2. **Linear types**: `linear struct` and `linear enum`, and every permission, struct or tuple that holds one, and `Uninit` of a value that owns something. `MirMoves` follows the places that hold a linear value along every path and reports one that is still held at a return or when its local is given another value. A linear value is used by giving it on, or by a function of its own impl that takes it apart (reads a field, or matches it); a linear type has no `Clone` or `Copy`, and is in no list, array, Box, function value or type parameter.
3. **`Uninit<T>` and `replace`**: `Uninit::empty`, `new`, `get`, `take` and `discard`, `filled(u)` and `at(u)` in proofs, `Array::uninit(n)`, and `replace(a, i, x)` on a list or an array (the element is copied out, then `set`). Natively an `Uninit<T>` is a `T` (`MirGhost.withoutUninit`, before native code), an empty one its bytes cleared.
4. **Ghost values**, by type: a value is ghost when its type is `Block<T>` (or a struct made only of them, as the tuple `Block::split` gives). `ghost` before a parameter, a field or a part of a tuple is checked to be before such a type. `MirGhost.eraseGhosts` runs after `validateProgram` and before everything else, as written above, and also checks that `Block::cast` is between slots laid out alike.
5. **Layout in bytes**: `Byte` and `Bool` are 8 bits, the fixed-width integers `I8`, `I16`, `I32`, `U16` and `U32` exist (with `I32::from` and the others, and `toInt` to widen), structs use C's rules, an enum is a `U32` tag and its variant, and arrays are their elements (`Mir.layoutOf`, `Mir.fieldOffsets`). In both emitters a number is an `i64` in a register and its own width in memory; the runtime's descriptors hold a size in bytes and each field's offset, and `tersus_drop`, `tersus_clone`, `tersus_equal` and `tersus_print` walk values by them. The array that a frame can hold is still counted in words (8192), not in bytes.
6. **`Addr<T>` and `Block<T>`**: the types, every operation of the tables above, the ghost functions, `Block::split`, `join`, `cast` and `assume`, the heap in `MirEval`, both emitters (an address is an `i64`) and the runtime (`tersus_addr_alloc`, `tersus_addr_resize`, `tersus_addr_free`, `tersus_drop_slots`), and `examples/addresses.tersus` with a buffer, a `Vec<T>` (`examples/vec.tersus` on an address), a buffer split between two functions and an arena-linked list, all proved; `TestPointers` has a rejected program for each contract.
7. **Assumptions**: `assume e;`, `Block::assume`, `extern fn` (a function of C with no body: native code declares and calls it, `eval` refuses to, and its contract is assumed) and `tersus assumptions`.

Where the built form differs from the text above:

- **`count(b)`**, the number of filled slots, is a ghost function that every operation keeps (a write adds one, a take or a drop takes one away, a split divides it and a join adds the parts), and `free` and `Block::cast` ask for `count(b) = 0` instead of a `forall` over the slots. A proof that every slot is empty after a split, two calls and a join needs the facts of four blocks chained through index arithmetic, which the proof engine does not instantiate (it instantiates a `forall` at indexes of a low generation), while a count is a sum. This settles decision 2: `free` finds every slot empty, by a count. A `Vec` says `count(blk) = len` in its invariant. Every block is known to have `0 <= count(b) <= cap(b)` and `cap(b) >= 0`, as a `Byte` is known to be in its range.
- **`whole(b)`** is two facts, `start(b) = 0` and `cap(b) = extent(origin(b))`, where `start(b)` is where the block starts in its allocation and `extent(o)` the size of the allocation `o`. A split gives the parts their starts, and a join needs `start(hi) = start(lo) + cap(lo)` and the same origin, which is what "next to each other in one allocation" is; `affirm whole(b);` is a statement of its own.
- **The operations that give two things** are each two operations of the MIR and a tuple: `Addr::alloc(n)` is `p = AddrAlloc(n)` and `b = BlockNew(p, n)`, `Addr::take` is `AddrTake` (which lends the permission) and `BlockTaken`, `Addr::resize` is `AddrResize` and `BlockResized`, `Block::split` is `BlockSplitLo` and `BlockSplitHi`. The `Block` operations are ghost and erased; an operation that runs and gives a permission (`AddrWrite`, `AddrDropValue`, `AddrDropRange`) gives `0` once it is erased.
- **The two offset facts are not given** (`offset(p, 0) = p` and `offset(offset(p, i), j) = offset(p, i + j)`): an address of an offset is the term `Addr::offset(p, i)`, which is what the upper part of a split is based at, so a program passes that term (or a local that holds it) where the upper part's address is wanted.
- **Addresses in `eval`** are numbers (allocation `k` starts at `k * 2^32`, and a slot is one more than the slot before), so `Addr::toInt` gives another number than native code does.
- **The view of a slot** (`Addr::get`, `Uninit::get`) is a view of the permission or the `Uninit` in `MirMoves` (`cannot move x out of the memory of a permission or an Uninit, which still holds it`), and a read of it after the permission changed is a use of a moved value, as designed.
- **Facts with a `forall` are not kept where two paths meet**, so a function that changes a block in one branch of an `if` returns there (as `Vec::push` does), and a loop that changes a block names what it keeps of the first one with `define` (`define o = origin(b);`), which can read what the validator knows of a permission.
- **An `extern fn`** takes and gives an `Int`, a `Byte`, a `Bool`, an address and permissions (which are not given to C), as 64-bit words: what the C function is given and gives must fit that.

8. **`StdList` on an address**: the list of native code (`lib/lists.tersus`) is an address, the count and the room, with the permission as a ghost field and the invariant of a `Vec`, and its functions are proved with the contracts of the operations on memory (a `set` drops the element it replaces, a `pop` the one it takes off, a full `push` resizes). It is copied, printed and compared by the runtime, which knows it by its name, as it was before. Since drops (9) it is freed by a drop of the library (`impl<T> Drop for StdList<T>`, which drops the elements in use and frees the memory), and a function of the library that makes a list of the memory of the one it is given takes that one apart (`StdList { ... } = l;`), so nothing in the ownership pass or the runtime frees a list by its name.

9. **Drops (step 26)**: `impl Drop for T { fn drop(self: Self) -> Int ... }` (the trait is in `lib/prelude.tersus`), which settles decision 1: the drop takes `Self`, so it can use the permission, and the fields are freed by the runtime after it, which frees only what they own (an `Addr` owns nothing). A type with a drop is not linear (`MirMoves`), a value is taken apart without its drop by `T { f: x, ... } = v;` (`GhostDissolve` in the MIR, which clears the value's bytes in native code), a permission is not moved out of a value with a drop by a field read, and a drop is not called by the program. `MirMono` makes the drop of each instance of a generic type (`<Vec<Int> as Drop>::drop`), `needsDrop` is true for a type with a drop, and the descriptor of a struct or an enum has the address of its drop, which `tersus_drop` calls before it walks the fields (both emitters). `examples/drops.tersus` is a `Vec<T>` with a drop, in a struct and in a list.

10. **`Box` on an address (step 29, the native part)**: `lib/box.tersus` is the `Box<T>` of the section above as `StdBox<T>`, proved, with a drop that drops the value and frees the slot, and `MirLists` makes each `Box<T>` of a validated program (not of an array) one: `Box::new` and `Box::unbox` are calls of `stdBoxNew` and `stdBoxUnbox`, and a field read, a variant test or a cast through a Box stays one through the `StdBox`, which native code reads at its address (its only word) as it read a Box, so a `match` still takes the fields out of a Box that is not used again. A Box of an array, of a size or of any, is a `StdList` with as many elements as room (`Array::boxed` is `stdListFilled`, unsizing is the list as it is, and `Box::new` and `Box::unbox` of an array move the elements into memory of the list and out of it). Native code has no Box of its own any more: the runtime frees a `StdBox` by its drop, and prints, compares and copies it as the value at its address (`Variants.tagged` is 3).

What this design describes is built. What it leaves to README step 29 is the language items: the checker and the validator still know `Box` by name (looking through it for fields and `match`, the recursion check, `=` on two Boxes, the unsizing coercion), which step 29 turns into general rules (a deref for any type with one, a recursion check asked of `Addr<T>`, the equality and the coercion of the library), along with `List` as a struct of the prelude.
