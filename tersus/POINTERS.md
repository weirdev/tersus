# Raw pointers (design)

> **Draft.** This is a proposal for step 25 of the roadmap in `README.md`, and for the part of step 29 that puts `Box` in the library. It replaces Part 3 of `DROPS.md`, and the `*T` that step 25 sketches. Nothing here is built.

## The constraint, and what follows from it

The validator never models a heap. A local's value never changes, an assignment gives the local a new iota, and a fact stays true for the rest of the path (MIR.md, Validation). Every proof the language has relies on that.

A raw address breaks it. Two addresses can name the same memory, a store changes memory without assigning a local, and nothing about an address says whether its memory is still allocated. The properties that make an address safe to use, such as being the only name for a block, written before read, or freed once, are facts about the heap, and the validator cannot check them without a heap model and a frame on every contract. The language needs addresses anyway: `Box` and the allocator in Tersus (steps 29, 30b), system calls that take a buffer (step 30d), and structures that share memory.

So the design separates what can be proved from what has to be trusted, and makes the trusted part small and visible:

1. **`Addr<T>`: a raw address, not validated.** It can be dereferenced only in a `trusted fn`, a function whose body is compiled but not proved, and whose contract the validator assumes as it assumes an `axiom`'s.
2. **`Box<T>`: the owning, exclusive pointer.** It stays a builtin until step 29, then becomes a library struct over an `Addr<T>`, written in trusted functions. Its claim is exclusivity, and that claim is what lets the validator keep treating a `Box` as the value it holds.
3. **`Uninit<T>`: a slot that may hold nothing, validated.** `Vec`, `StdList` and `String`'s storage are built from `Box<Array<Uninit<T>>>` and are fully proved.

The trusted base moves from C and Haskell into a short list of Tersus functions that a command can print. Everything above it stays proved.

## Why not an owning `Ptr<T>`

The first draft of this document proposed `Ptr<T>`, a validated pointer that owned its block and carried its contents as ghost arrays. Compared with `Box<Array<T>>`, which already owns its block exclusively and is caught by the move check after it is moved:

| What `Ptr<T>` gave | Without `Ptr` |
|---|---|
| Exclusive ownership, and use after free caught by moves | `Box` has it |
| An explicit `free` | Not needed: a `Box` is freed when it is dropped, and step 26 lets a type decide what that does |
| `resize` (realloc) | `Box::resize` |
| One word, with a ghost capacity | `Box<Array<T>>` is an address and a length, which a collection needs anyway |
| Slots that hold nothing, with `filled` and `at` | `Uninit<T>`, below |

Only the last row was new, and it is a property of a slot, not of a pointer. As a type of its own it works on the heap (`Box<Array<Uninit<T>>>`) and inline (`Array<Uninit<T>, 8>`, a buffer in a frame), which `Ptr` could not do.

## Layer 1: `Addr<T>` and trusted code

### The type

`Addr<T>` is an address of room for a `T`, or null. It is one word, Copy, and `=` compares addresses. Nothing about it is known to the validator: it is an opaque value.

- **Any code can hold one**: keep it in a local or a field, pass it, return it, compare it. Only trusted code can use one to read or write memory.
- **`T` is any type that has a size**, as for an element of an array. `Addr<Array<T, N>>` is allowed, and an address of an unsized array is an `Addr<T>` and a length that the program keeps.
- **Not printable.** `main` cannot return one (`an Addr cannot be the result of a program`).

### Operations

These are written as calls, as `Box::new` is, and are allowed only in the body of a trusted function (`Addr::read is a raw memory operation and needs a trusted fn`). Offsets are in units of `T`.

| Operation | Does |
|---|---|
| `Addr::alloc(n)` | room for `n` values of `T`, uninitialized; the program ends with an error if the system refuses it or the size in bytes overflows |
| `Addr::resize(a, n)` | `realloc`: room for `n`, with the first `min(old, n)` kept, and possibly a new address |
| `Addr::free(a)` | frees the room `a` was allocated with; returns `0` |
| `Addr::null()` | the null address |
| `Addr::offset(a, i)` | the address `i` values of `T` past `a` |
| `Addr::read(a)` | the words of the `T` at `a`, as a value: a bitwise copy, so a `T` that owns something now has two owners |
| `Addr::write(a, x)` | moves `x` into the room at `a` without dropping what was there; returns `0` |
| `Addr::cast(a)` | the same address as an `Addr<U>`, with `U` decided by the use, as for `Array::empty()` |

`read` and `write` are Rust's `ptr::read` and `ptr::write`. Trusted code decides which copy of a value is the owner, and drops exactly one.

### `trusted fn`

```tersus
trusted fn f(...) -> T [{ in }] [{ out }] { ... };
```

- **The body is checked for types and moves, and compiled. It is not validated.** `MirMoves` still runs, so a value moved twice in trusted code is still an error.
- **Its contract is checked at every call and assumed afterwards.** A caller proves the input contract and gets the output contract, as for any function. The function also counts as ending unless it is marked `~`.
- **Where it can be:** any function, an impl's function, and the `drop` of a `Drop` impl. A trusted function can call any function, and any function can call it.
- **`trusted impl`.** A structural `impl Clone` or `impl Copy` for a type that holds an `Addr` copies the address, which would make a second owner of whatever the address owns, so it must be written `trusted impl Clone for T { };`. Without the mark it is refused (`Handle holds an Addr: a structural copy of it is trusted`).
- **Making a value that holds an `Addr` is trusted.** Without field visibility, this is what stops other code from building a `Box { addr: a }` around an address that is not its own: a struct literal, an enum variant or an update (`..base`) that gives an `Addr` field a value is allowed only in trusted code. Reading such a field is not restricted, because a copy of an address does nothing outside trusted code.
- **`extern fn`** (step 30d: `write`, `exit`, the allocator symbols) is trusted by definition: a declaration with no body that the emitter turns into an LLVM `declare`, whose contract is assumed.
- **`tersus trusted <file>`** prints every trusted function and impl of a program and its prelude, with their contracts. That is the whole of what the program's proofs take on trust, apart from the builtins.

### Ghost functions

Trusted code needs to tell the validator what a value it built means, in terms the validator can carry around. A ghost function is a function with no body that only contracts and validation statements can call:

```tersus
ghost fn contents<T>(b: &Box<T>) -> T;
```

It is an uninterpreted symbol: `contents(b)` is a term with no facts of its own. The facts come from contracts, and only a trusted function or an `axiom` can promise a fact about it that it cannot derive. An ordinary function can only pass on what its callees promise. Calling one in code is an error (`contents is a ghost function: it has no body`).

### What trusted code owes the validator

These are the rules that a trusted function has to follow, and that nothing checks. Each one is a property the validator relies on and cannot see.

1. **Its contract is true.** Whenever the input contract holds, the function ends (unless it is `~`) and the output contract holds.
2. **Stability.** What a contract says of a value stays true while the value is alive, from the assignment that makes it until it is moved or its function returns, whatever code runs in between. In practice: trusted code writes the memory that a live value's meaning depends on only when it was given that value by value (moved in), and the value it returns is a new one. Through a lent `&T` it only reads.
3. **Exclusivity.** Two live values never depend on the same memory, unless that memory is never written while either is alive. The exception allows sharing what does not change (a reference count over an immutable value).
4. **Memory safety.** No read of memory that is freed or was never written, no double free, no access out of the room allocated, and of the copies `Addr::read` makes of an owning value, exactly one is used as the owner.
5. **Drops.** A value's `drop` frees what the value owns, once.

Rule 2 is the exact form of "the validator treats values as immutable" at the boundary with memory, and rule 3 is what makes it possible. The tests that stand in for a proof are the ones that exist now: the heap model of `TestOwnership`, `TERSUS_CHECK` and valgrind in `TestNative`, and the comparison of native code with `eval`.

## Layer 2: `Box<T>` on `Addr<T>` (step 29)

Until step 29 `Box` stays a builtin, and nothing below needs it to change. When it moves to the library:

```tersus
struct Box<T> { addr: Addr<T> };

ghost fn contents<T>(b: &Box<T>) -> T;

impl<T> Box<T> {
    trusted fn new(x: T) -> Self [{ }] [{ affirm contents(return) = x; }] {
        a = Addr::alloc(1);
        done = Addr::write(a, x);
        return Self { addr: a };
    };

    trusted fn unbox(self: Self) -> T [{ }] [{ affirm return = contents(self); }] {
        x = Addr::read(self.addr);       // x is now the owner of what the room held
        done = Addr::free(self.addr);
        return x;
    };
};

impl<T> Drop for Box<T> {
    trusted fn drop(self: &Self) -> Int [{ }] [{ }] {
        x = Addr::read(self.addr);       // dropped when drop returns
        return Addr::free(self.addr);
    };
};
```

`Box<T>` meets rule 3 because `new` is the only code that makes one, and it allocates fresh room. It meets rule 2 because nothing writes through the address of a live `Box`. A `Box` that is moved into a trusted function and changed in place is a new value when it comes back.

What the compiler does for `Box` by name today (looking through it for fields and `match`, `Box::new(p) = Box::new(q)` meaning `p = q`, the recursion check) becomes a language item, as step 29 describes. For the validator, the lang item says that a `Box` is its `contents`: `a = b` exactly when `contents(a) = contents(b)`, an axiom of the item and not something each program states. `Box<Array<T>>` keeps its length in a second field, `len: Int`, with `Addr` arithmetic in its trusted functions.

## Layer 3: `Uninit<T>`

### The type

`Uninit<T>` is room for one `T` that may or may not hold one. Natively it is the words of a `T` and nothing else: there is no tag, and whether it is filled is known only to the validator.

- **Ghost facts**: `filled(u)` says it holds a value, and `at(u)` is that value, known only when it is filled. They are used in contracts, `affirm`, `define` and invariants.
- **Dropping one drops nothing**, whether or not it is filled. Forgetting a filled one leaks what it holds, which is safe. Once linear types exist (DROPS.md, Part 2), an `Uninit<T>` of a `T` that owns something is linear, and `Uninit::discard(u)`, which needs `!filled(u)`, is how an empty one is consumed.
- **Copy when `T` is Copy**, and otherwise neither Copy nor Clone, since a copy cannot know at run time whether there is a value to copy. No `=`.
- **Any `T` that has a size.** In `MirOwnership` it is plain: its words are moved, and nothing about it is freed.

### Operations

| Operation | Needs | Gives |
|---|---|---|
| `Uninit::empty()` | | `!filled(return)` |
| `Uninit::new(x)` | | `filled(return)`, `at(return) = x` |
| `Uninit::get(u)` | `filled(u)` | `return = at(u)`, a view of `u`: reading it moves nothing |
| `Uninit::take(u)` | `filled(u)` | `return = at(u)`; `u` is moved |
| `Uninit::drop(u)` | `filled(u)`, in a `drop` only | drops the value in place, through the lent `self` of the drop |

`Uninit::drop` is the one operation that changes memory through a lent value. It is allowed only in the body of a `drop`, where the value is ending and nothing will look at it again (see Decision 3).

### On sequences

Two additions to arrays make `Uninit` usable as an element:

- **Empty arrays without a filler.** `array(n, Uninit::empty())` is accepted for any `T` (an empty slot is copied by copying words that mean nothing), and `Array::uninit(n)` is a `Box<Array<Uninit<T>>>` of `n` empty slots, allocated without being written.
- **`replace(a, i, x)`** moves `x` into element `i` and gives back the element that was there: a `Replaced<S, E> { seq: S, old: E }` (from the prelude, since there are no tuples), with `return.seq = set(a, i, x)` and `return.old = get(a, i)`. This is useful beyond `Uninit`: today nothing can be moved out of an element of an array or a list, and `replace` is the way.
- **`Box::resize(b, n)`** for a `Box<Array<Uninit<T>>>`: the size is `n`, the elements below `min(n, size(b))` are as they were, and the new ones are empty. It is `realloc`, so the moves of the elements cost nothing.

The validator needs nothing new. `filled(get(a, i))` and `at(get(a, i))` are terms over `get`, so the `forall` facts of arrays, their triggers and the frame facts of `set` work as they do for any element.

### A `Vec` on `Uninit`

`examples/vec.tersus` without the filler that `Array::boxed` needs, with a `pop` that gives the element back, and with nothing trusted:

```tersus
struct Vec<T> {
    data: Box<Array<Uninit<T>>>,
    len: Int,
} invariant [{
    affirm 0 <= len; affirm len <= size(data);
    affirm forall j in 0..len: filled(get(data, j));
    affirm forall j in len..size(data): !filled(get(data, j));
}];

struct Popped<T> { vec: Vec<T>, value: T };

impl<T> Vec<T> {
    fn new() -> Self [{ }] [{ affirm return.len = 0; }] {
        return Self { data: Array::uninit(4), len: 0 };
    };

    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm at(get(return.data, self.len)) = x; }] {
        data = self.data;
        if self.len = size(data) {
            data = Box::resize(data, size(data) * 2 + 4);
        };
        return Self { data: set(data, self.len, Uninit::new(x)), len: self.len + 1 };
    };

    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = at(get(self.data, i)); }] {
        return clone(Uninit::get(get(self.data, i)));
    };

    fn pop(self: Self) -> Popped<T> [{ affirm self.len >= 1; }] [{ affirm return.vec.len = self.len - 1; }] {
        r = replace(self.data, self.len - 1, Uninit::empty());
        return Popped<T> { vec: Self { data: r.seq, len: self.len - 1 }, value: Uninit::take(r.old) };
    };
};

impl<T> Drop for Vec<T> {
    fn drop(self: &Self) -> Int [{ }] [{ }] {
        i = 0;
        while i < self.len [{ affirm i >= 0; affirm i <= self.len; }] shrinks self.len - i {
            Uninit::drop(get(self.data, i));
            i = i + 1;
        };
        return 0;
    };
};
```

`set(data, self.len, ...)` drops the empty slot it replaces, which does nothing. The invariant says it was empty, so no element is lost. Before step 26, a `Vec` that holds values which own something leaks them when it is dropped. A `Vec<Int>` loses nothing.

## Running it

- **`eval` needs a heap for `Addr`.** An `Addr` can be shared, so `MirEval` gets a store of blocks (a map from a block to its slots, with an address encoded as a block and an index) that `alloc`, `read`, `write`, `offset` and `free` work on. It fails on a read of a freed or unwritten slot and on a double free, so `eval` is the first check of trusted code. The older executor in `StdLib` refuses trusted code, and `testNative` uses `eval` for those programs. `Uninit` needs no heap: it is `VUninit (Maybe Value)`.
- **MIR.** The `Addr` operations and the `Uninit` operations are `ListOp`s (`AddrAlloc`, `AddrResize`, `AddrFree`, `AddrNull`, `AddrOffset`, `AddrRead`, `AddrWrite`, `AddrCast`, `UninitNew`, `UninitEmpty`, `UninitGet`, `UninitTake`, `UninitDrop`, `ArrayUninit`, `Replace`, `BoxResize`), with words in `MirData`. `Addr T` and `Uninit T` are new `Type` constructors (`addr T`, `uninit T` in the data). Functions carry a `trusted` flag, which `MirValidate` uses to skip the body and assume the contract.
- **Native code.** An `Addr` is an `i64`. `alloc`, `resize` and `free` call the runtime's `allocate`, `reallocate` and `release`, so `TERSUS_CHECK` counts the blocks. `read` and `write` copy `words(T)` words, and `offset` adds `i * words(T) * 8`. An `Uninit<T>` is laid out as a `T`, and its descriptor is `KIND_UNINIT`, which drops, clones and compares nothing. `Uninit::drop` calls `tersus_drop` with the descriptor of `T`.
- **Both emitters, in step.** `LlvmEmit` and `examples/emit.tersus` gain the same cases, `examples/mir_reader.tersus` reads the new words, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` keeps them equal.

## Order of work

1. **`Uninit<T>`, `replace`, `Array::uninit` and `Box::resize`**, on the builtin `Box`. This is validated code with no trust in it, and it gives `examples/vec.tersus` its new form. The test is whether the invariant's two foralls are cheap enough to prove at each operation. `Uninit::drop` waits for step 26.
2. **`trusted fn` and `ghost fn`**, with no `Addr` yet: a trusted function over the types that exist, `tersus trusted`, the `MirValidate` flag, and tests that a trusted contract is assumed and that a ghost function cannot be called in code.
3. **`Addr<T>`**: the type, the operations, the rules on making values that hold one and on structural copies, the heap in `MirEval`, the emitters and runtime, `examples/addresses.tersus` (a buffer managed by hand in trusted functions behind a validated interface), and rejected programs for each rule a checker enforces.
4. **Drops (step 26)**, then `StdList` on `Uninit`, and `Uninit::drop`.
5. **`Box` in the library (step 29)**, on `Addr`.

## Changes to other documents

- `README.md`, step 25: `Addr<T>`, `trusted fn`, `ghost fn` and `Uninit<T>` in place of `*T` and the contracts on `valid(p)`. Step 29: `struct Box<T> { addr: Addr<T> }` in place of `ptr: *T`, and `*[T]` as an `Addr<T>` and a length. Step 30: `extern fn` as trusted.
- `DROPS.md`, Part 3: points here. Its owning pointer is gone; `Uninit` and `replace` cover what Part 1's containers section needed of it.
- `LANGUAGE.md`, when it is built: sections "Uninitialized slots" and "Trusted code", the ghost functions, and the rules of trusted code as a list a reader of a library can check it against.

## Decisions to make

1. **Is the body of a trusted function validated at all?** Here it is not: its contract is assumed, as an `axiom`'s is. The alternative is to validate it with the `Addr` operations giving nothing, and to report what fails as a warning. That proves the arithmetic and the calls around the raw memory, at the cost of contracts written for the validator in code that is trusted anyway.
2. **Who can make a value that holds an `Addr`.** Here it is trusted code, which stands in for private fields. With fields that can be private, this rule would become "a private field", and `Box` would need no special rule.
3. **`Uninit::drop` through a lent `self`.** Part 1 of `DROPS.md` gives `drop` a `&Self`, so a drop cannot take its elements out. This allows the one change through a lent value that is unobservable. The alternatives are a `drop` that takes `Self` with its fields not dropped afterwards, or dropping the elements of a `Vec` in a trusted `drop`.
4. **`Replaced<S, E>` in the prelude, or tuples.** A struct is all the language has. If tuples come, `replace` should return one.
5. **Spelling: `Addr<T>` or `*T`.** `Addr<T>` reads like `Box<T>` and needs no change to the parser. `*T` is shorter and familiar, and makes `*` mean two things.
