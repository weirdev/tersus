# Raw pointers (design)

> **Draft.** This is a proposal for step 25 of the roadmap in `README.md`, and for the part of step 29 that puts `Box` in the library. It replaces Part 3 of `DROPS.md`, and the `*T` that step 25 sketches. Nothing here is built.

## The idea

The validator never models a heap. A local's value never changes, an assignment gives the local a new iota, and a fact stays true for the rest of the path (MIR.md, Validation). Every proof the language has relies on that. A raw address breaks it: two addresses can name the same memory, a store changes memory without assigning a local, and nothing about an address says whether its memory is still allocated.

The design splits a pointer into two values, following separation logic (and Verus's `PointsTo`):

- **`Addr<T>`, the address**: a runtime word. It is Copy, can be aliased, offset, kept in many places and passed to C, and allows nothing by itself.
- **`Block<T>`, the permission**: a *ghost*, *linear* value that `alloc` returns with the address. It has no runtime form and is erased after validation. It says what the block holds: its base, its capacity, which slots are filled and with what. Every operation on memory needs it.

The permission is a value, so the validator's model survives. A write takes the permission and gives a new one, which is an assignment with a new iota, as `set` is for an array. Addresses can alias because the permission cannot: it is linear, so there is only ever one for a block. The properties that make raw memory safe are then **proved, in ordinary code**:

- every access is in bounds;
- no slot is read before it is written;
- nothing is used after it is freed, and nothing is freed twice;
- no element is lost when a block is freed;
- the permission to a block is exclusive.

**What is unsafe is an assumption, not a pointer.** Code that uses addresses needs no mark, because what it does is proved. What cannot be proved is said with `assume`, `Block::assume` or the contract of an `extern fn`. These are local and named, and `tersus assumptions` lists them. Rust marks `unsafe fn` because its caller has to uphold something the compiler cannot check; in Tersus that something is an input contract, which the caller proves. So no function is marked.

## `Addr<T>`

`Addr<T>` is the address of a `T`, or null. It is one word, Copy, and `=` compares addresses. These operations need no permission and are allowed anywhere:

| Operation | Gives |
|---|---|
| `Addr::null()` | the null address |
| `Addr::offset(p, i)` | the address `i` values of `T` past `p` (an `Int` `i`, negative allowed) |
| `Addr::cast(p)` | the same address as an `Addr<U>`, with `U` decided by the use, as for `Array::empty()` |

**What the `T` gives.** It does not describe the memory: an `Addr<T>` can dangle, be null, or point at something else, as Rust's `*const T` can. What says the memory holds `T`s is the permission, `Block<T>`. The parameter gives three things:

1. **A stride.** `offset(p, i)` moves `i` values of `T`.
2. **Result types.** An operation through an `Addr<T>` gives a `T` or takes one, with no annotation at each use.
3. **A static match with the permission.** An operation needs a `Block<T>` for an `Addr<T>`, so using a `Block<Int>` with an `Addr<Node>` is a type error, found before any proof.

So `Addr<T>` to `Addr<U>` is a free cast, since it only changes the stride and the types. Reinterpreting memory is a change of permission, `Block<T>` to `Block<U>` (see Reinterpreting memory), and that is where it is checked.

**`void*` is `Addr<Opaque>`.** `Opaque` is a type with no size. Its address has no stride, so it cannot be offset, read or written; it can be compared, passed and cast, as in C. A `Block<Opaque>` cannot exist.

## `Block<T>`

`Block<T>` is the permission to a block of `n` slots of `T`. It is a ghost type: it can be held in a ghost local, a ghost parameter, a ghost field or the ghost part of a tuple (see Ghost values), and it is linear: it has to be freed, given on, or put in a value that is.

The validator knows it through ghost functions, usable in contracts, `affirm`, `define` and invariants:

- `base(b)`: the `Addr<T>` of the first slot.
- `cap(b)`: the number of slots, at least 0.
- `inside(b, p)`: `p` is a slot of the block, that is `p = offset(base(b), i)` for an `i` with `0 <= i < cap(b)`.
- `filled(b, p)`: the slot at `p` holds a value.
- `at(b, p)`: that value, known only when it is filled.

**Addresses as terms.** The proof engine learns four facts about addresses: `offset(p, 0) = p`; `offset(offset(p, i), j) = offset(p, i + j)`; `offset(p, i) = offset(p, j)` exactly when `i = j`; and `inside(b, offset(base(b), i))` exactly when `0 <= i < cap(b)` (null is inside no block). A fact about the slot at `offset(base(b), i)` is a fact about element `i` of two ghost arrays, so `filled` and `at` are `get` on arrays that the engine already reasons about. `forall`, its triggers, the frame facts of `set` and the case splits of A linked list in an array all apply unchanged.

### Operations

| Operation | Needs | Gives |
|---|---|---|
| `Addr::alloc(n)` | `n >= 0` | `(p, ghost b)`: `base(b) = p`, `cap(b) = n`, no slot filled |
| `Addr::get(p, b)` | `inside(b, p)`, `filled(b, p)` | `at(b, p)`, a view: reading it moves nothing, and `b` is lent |
| `Addr::write(p, x, b)` | `inside(b, p)`, `!filled(b, p)` | a new block, with `p` filled with `x` and every other slot as it was |
| `Addr::take(p, b)` | `inside(b, p)`, `filled(b, p)` | `(at(b, p), ghost b2)`: the value, and a block with `p` empty |
| `Addr::drop(p, b)` | `inside(b, p)`, `filled(b, p)` | a block with `p` empty; the value is dropped in place |
| `Addr::resize(p, n, b)` | `p = base(b)`, `n >= 0`, no slot from index `n` filled | `(q, ghost b2)`: `base(b2) = q`, `cap(b2) = n`, the slots below `min(n, cap(b))` as they were, by index |
| `Addr::free(p, b)` | `p = base(b)`, no slot filled | `0` (there is no unit type); `b` is consumed |

- **`write` needs an empty slot.** Writing over a filled one would lose a value that may own something. Replacing a value is `drop` then `write`.
- **`get` is a view**, as `get` of a list is (MIR.md, Moves). `MirMoves` refuses to move it out (`cannot move x out of a Block, which still holds it: write clone(x), or Addr::take`).
- **`drop` runs `tersus_drop` with the descriptor of `T`.** It does nothing for a type that owns nothing.
- **`resize` is `realloc`.** Moving a value in Tersus is copying its words, so a bitwise move of every filled slot is right.
- **What fails at run time and not in a proof**: an allocation the system refuses, and a size whose bytes overflow an `Int`. The program ends with an error, as for an overflow. No contract can promise memory.

The contracts of these builtins are axioms, as the contract of `get` is. Code written with them is proved.

### Splitting a block

A function that should see only part of a buffer gets part of the permission: `Block::split(b, i)` gives `(ghost lo, ghost hi)`, the slots below index `i` and from it, and `Block::join(lo, hi)` needs `base(hi) = offset(base(lo), cap(lo))` and gives them back as one. Both are ghost operations with no runtime form. A `free` needs the whole block back, which linearity guarantees can be done.

### Reinterpreting memory

`Block::cast(b)` gives a `Block<U>` for the same memory. It is allowed when `T` and `U` have the same words, and every filled slot's words are a valid `U`. `Int` to a struct of `Int`s is allowed; `Int` to `Bool` needs every filled slot to be 0 or 1, which a proof can give; `Int` to a list is never allowed. Anything else is an assumption (`Block::assume`).

## Ghost values

A ghost value exists only for the validator. The ones this design needs are permissions, but the mechanism is general.

- **Where they are**: a ghost local (one that holds a ghost type), a parameter written `ghost b: Block<T>`, a struct field written `ghost b: Block<T>`, and a part of a tuple written `ghost` in its type, `(Addr<T>, ghost Block<T>)`.
- **They flow only into ghost places.** A ghost value can be given to a ghost parameter, field or tuple part, and mentioned in contracts. It can never become part of a runtime value (`b is a ghost value and the program cannot use it`). A runtime value can be used in a ghost place.
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

## Assumptions

What the validator cannot prove, a program says explicitly, in one of four ways:

| Form | What is assumed |
|---|---|
| `assume e;` | a fact, which the rest of the path then knows, as after an `affirm` |
| `Block::assume(p, n)` | a permission for `n` slots of `T` at `p`, with no slot filled, for memory the program did not allocate |
| `extern fn` | the contract of a function with no body that the emitter declares (step 30: `write`, `exit`, the system's allocator, a C library) |
| `axiom` | a rule of proof, as now |

`tersus assumptions <file>` prints every one in the program and its prelude, with its line. That list is everything the program's proofs take on trust, besides the builtins.

**What needs an assumption, at first:**

- **Memory that `alloc` did not make**: from C, the system, `mmap`, memory-mapped I/O. An `extern fn` that returns `(Addr<T>, ghost Block<T>)` gives the permission in its contract, or the program uses `Block::assume`.
- **Shared memory that is written**: a reference count over a mutable value, or memory shared between threads. Shared memory that is only read can be proved later with fractional permissions (a permission split into read-only parts that join back).
- **Reinterpretation** beyond what `Block::cast` checks.
- **A structure spread over many blocks**, such as a linked list of nodes allocated one by one. Each node has its own permission, so the structure needs a ghost collection of permissions (Verus uses ghost maps). Until that exists, a structure inside one block is proved (an arena, where links are addresses into the same block), and one over many blocks uses `Block::assume`.

## The library on top

### `Box<T>` (step 29)

A `Box` is an address with one filled slot and its permission. It has no assumption in it:

```tersus
struct Box<T> {
    addr: Addr<T>,
    ghost blk: Block<T>,
} invariant [{ affirm base(blk) = addr; affirm cap(blk) = 1; affirm filled(blk, addr); }];

impl<T> Box<T> {
    fn new(x: T) -> Self [{ }] [{ affirm at(return.blk, return.addr) = x; }] {
        (a, b) = Addr::alloc(1);
        return Self { addr: a, blk: Addr::write(a, x, b) };
    };

    fn unbox(self: Self) -> T [{ }] [{ affirm return = at(self.blk, self.addr); }] {
        (x, b) = Addr::take(self.addr, self.blk);
        done = Addr::free(self.addr, b);
        return x;
    };
};
```

Making a `Box` by hand is safe. The invariant is checked at every struct literal, as struct invariants already are, and it needs a permission for the address. A permission comes only from `alloc`, from taking another value apart, or from an assumption, so no code can wrap an address it does not own.

What the compiler does for `Box` by name today (looking through it for fields and `match`, `Box::new(p) = Box::new(q)` meaning `p = q`, the recursion check) becomes a language item, as step 29 describes. For the validator, the item says that a `Box` is the value it holds: `a = b` exactly when `at(a.blk, a.addr) = at(b.blk, b.addr)`.

### `Vec<T>`

`examples/vec.tersus` on an address. It needs no filler value, its `pop` gives the element back, and nothing in it is assumed:

```tersus
struct Vec<T> {
    addr: Addr<T>,
    cap: Int,
    len: Int,
    ghost blk: Block<T>,
} invariant [{
    affirm base(blk) = addr; affirm cap(blk) = cap;
    affirm 0 <= len; affirm len <= cap;
    affirm forall j in 0..len: filled(blk, Addr::offset(addr, j));
    affirm forall j in len..cap: !filled(blk, Addr::offset(addr, j));
}];

impl<T> Vec<T> {
    fn new() -> Self [{ }] [{ affirm return.len = 0; }] {
        (a, b) = Addr::alloc(4);
        return Self { addr: a, cap: 4, len: 0, blk: b };
    };

    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; }] {
        (a, b) = (self.addr, self.blk);
        cap = self.cap;
        if self.len = cap {
            cap = cap * 2 + 4;
            (a, b) = Addr::resize(a, cap, b);
        };
        return Self { addr: a, cap: cap, len: self.len + 1, blk: Addr::write(Addr::offset(a, self.len), x, b) };
    };

    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = at(self.blk, Addr::offset(self.addr, i)); }] {
        return clone(Addr::get(Addr::offset(self.addr, i), self.blk));
    };

    fn pop(self: Self) -> (Self, T) [{ affirm self.len >= 1; }] [{ affirm return.0.len = self.len - 1; }] {
        (x, b) = Addr::take(Addr::offset(self.addr, self.len - 1), self.blk);
        return (Self { addr: self.addr, cap: self.cap, len: self.len - 1, blk: b }, x);
    };

    // Until step 26 gives Vec a Drop, a Vec is linear (it holds a permission), and the program frees it with this
    fn free(self: Self) -> Int [{ }] [{ }] {
        b = self.blk;
        i = 0;
        while i < self.len [{
            affirm i >= 0; affirm i <= self.len;
            affirm base(b) = self.addr; affirm cap(b) = self.cap;
            affirm forall j in 0..i: !filled(b, Addr::offset(self.addr, j));
            affirm forall j in i..self.len: filled(b, Addr::offset(self.addr, j));
            affirm forall j in self.len..self.cap: !filled(b, Addr::offset(self.addr, j));
        }] shrinks self.len - i {
            b = Addr::drop(Addr::offset(self.addr, i), b);
            i = i + 1;
        };
        return Addr::free(self.addr, b);
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

- **`eval` needs a heap for `Addr`.** Addresses can be shared, so `MirEval` gets a store of blocks (a map from a block to its slots, with an address encoded as a block and an index) that `alloc`, `get`, `write`, `take`, `drop`, `resize` and `free` work on. It runs after ghost values are erased. It fails on a read of an empty or freed slot and on a double free, which a proved program cannot do, so on such a program it is a check of the assumptions. The older executor in `StdLib` refuses addresses. `Uninit` needs no heap: it is `VUninit (Maybe Value)`.
- **MIR.** The operations are `ListOp`s (`AddrAlloc`, `AddrNull`, `AddrOffset`, `AddrCast`, `AddrGet`, `AddrWrite`, `AddrTake`, `AddrDrop`, `AddrResize`, `AddrFree`, and the `Uninit`, `replace` and tuple operations), with words in `MirData`. `Addr T`, `Block T`, `Uninit T` and tuple types are new `Type` constructors; a ghost local has a flag. The ghost operations (`Block::split`, `join`, `cast`, `assume`) erase to nothing.
- **Native code.** An `Addr` is an `i64`. `alloc`, `resize` and `free` call the runtime's `allocate`, `reallocate` and `release`, so `TERSUS_CHECK` counts the blocks. `get`, `write` and `take` copy `words(T)` words, `offset` adds `i * words(T) * 8`, and `drop` calls `tersus_drop` with the descriptor of `T`. An `Uninit<T>` is laid out as a `T`, with a descriptor that drops, clones and compares nothing.
- **Both emitters, in step.** `LlvmEmit` and `examples/emit.tersus` gain the same cases, `examples/mir_reader.tersus` reads the new words, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` keeps them equal.

## Order of work

1. **Tuples**: types, values, projections, destructuring, moves of the parts, the validator's terms, and the emitters. These are independent of everything else.
2. **Linear types** (DROPS.md, Part 2), which permissions rely on.
3. **`Uninit<T>` and `replace`**, on the builtin `Box`: a proved `Vec` with no addresses, and a test of whether the invariant's foralls are cheap enough to prove at each operation.
4. **Ghost values**: ghost locals, parameters, fields and tuple parts, the check that they do not flow into runtime values, the linear check over them, and the erasure pass.
5. **`Addr<T>` and `Block<T>`**: the types, the operations, the address facts and ghost arrays in the proof engine, the heap in `MirEval`, the emitters and runtime, `examples/addresses.tersus` (a buffer and an arena-linked list, both proved), and a rejected program for each contract: read of an empty slot, write over a filled one, out of bounds, free with a slot filled, use after free, a permission dropped.
6. **Assumptions**: `assume`, `Block::assume`, `extern fn`, and `tersus assumptions`.
7. **Drops (step 26)**, then `StdList` on an address, then `Box` in the library (step 29).

## Changes to other documents

- `README.md`, step 25: `Addr<T>`, `Block<T>`, ghost values, tuples and assumptions in place of `*T`, the marker in signatures and the contracts on `valid(p)`. Step 29: `struct Box<T> { addr: Addr<T>, ghost blk: Block<T> }` in place of `ptr: *T`, and `*[T]` as an address, a length and a block. Step 30: `extern fn` as an assumption.
- `DROPS.md`, Part 3: points here. Its owning pointer is now an address and a permission, and `Uninit` and `replace` cover what Part 1's section on containers needed. The order there changes: linear types come before pointers.
- `LANGUAGE.md`, when it is built: sections on tuples, ghost values, addresses and permissions, and assumptions, with the list of what `tersus assumptions` reports.

## Decisions to make

1. **How a `drop` frees a permission (postponed).** Part 1 of `DROPS.md` gives `drop` a lent `self: &Self`, which cannot consume the linear permission inside the value. A type that holds a permission needs a `drop` that takes `Self`, without its fields being dropped again afterwards. This is decided with step 26.
2. **Must `free` find every slot empty?** It is what makes "no element is lost" a proof, and `Vec::free` above shows its cost: a loop with three foralls in its invariant. The cheaper rule is that `free` drops whatever is filled, which needs no proof and is always safe.
3. **Ghost collections of permissions**, for structures over many blocks: a ghost map from addresses to `Block`s, and when to add it.
4. **Fractional permissions**, for proved sharing of memory that is only read (`Rc` of an immutable value, a buffer read by several functions at once).
5. **C layout.** Tersus lays every value out in 8-byte words, a `Byte` included, which is not C's layout. Addresses passed to C need types with C's layout (`i32`, a real `u8`, structs with C's rules), probably a step of their own before `extern fn` is useful beyond whole words.
6. **Should `assume` carry a reason** (`assume e because "...";`) that `tersus assumptions` prints?
