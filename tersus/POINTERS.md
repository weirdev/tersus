# Raw pointers (design)

> **Draft.** This is a proposal for step 25 of the roadmap in `README.md`. It replaces Part 3 of `DROPS.md` and changes what step 25 says about `*T`; the reasons are under "Why not an address". Nothing here is built.

## The constraint that decides it

The validator never models a heap. A local's value never changes, an assignment gives the local a new iota, and a fact stays true for the rest of the path (MIR.md, Validation). Every proof the language has, from the contracts of `set` to the invariant of `StdList`, relies on that. An ordinary raw pointer breaks it twice. Two pointers can name the same memory, so a store through one changes what a load through the other gives. And a store changes memory without assigning a local, so no new iota records it. Supporting both would need a heap in `ProofState`, plus a frame on every contract that says which memory a call may touch: separation logic, retrofitted onto every function.

The design below avoids that. **A pointer owns its block, and the block's contents are part of the pointer's value.** Nothing else can name the block, so there is no aliasing. A write moves the pointer in and gives a new pointer back, so it is an assignment with a new iota, as `set` is. The program does everything a raw pointer is for: it allocates, works with memory that holds nothing yet, writes, moves elements out and frees, all by hand, and the compiler inserts none of it. The validator proves, with the facts it already uses for arrays, that no slot is read before it is written, no index is out of range, and no element is lost. The move check proves that nothing is used after it is freed.

## The type

`Ptr<T>` is a builtin type: room for a number of `T`s on the heap, owned by whoever holds the pointer.

- **One word natively**: the address. The capacity is not stored (see Ghost facts), so `struct Box<T> { ptr: Ptr<T> }` has the layout that `Box<T>` has today (step 29). A type that needs the capacity at run time keeps it in a field.
- **Not Copy, not Clone.** A copy would be a second owner. `clone(p)` is an error (`Ptr<Int> is not Clone`). A struct that holds a `Ptr` can be Clone only through a `Clone` with a body of its own (DROPS.md, Part 1).
- **No `=`.** Two live pointers never share an address, so comparing addresses would always be false, and comparing contents is what a type built on a pointer defines itself. A struct or enum that holds a `Ptr` gets no structural `=`.
- **No implicit drop.** `MirOwnership` treats a `Ptr` as plain: it moves the word and never frees it. Freeing is `Ptr::free`, and a pointer that is dropped without it leaks its block. That is safe (nothing is used after it is freed) and becomes an error once `Ptr` is linear (see Ownership).
- **What it can point at**: any type that has a size, as for an element of an array (`Ptr<Int>`, `Ptr<Node>`, `Ptr<List<Int>>`, `Ptr<Ptr<Int>>`). There is no `Ptr<Array<T>>`: a block of `n` is already the unsized array.
- **Not printable.** `main` cannot return one (`a Ptr cannot be the result of a program`).

## Operations

Eight builtins, written as calls like `Box::new` and `Array::boxed`, none of them usable as a value. `i` is an index into the block, not a byte offset. There is no pointer arithmetic, because an interior pointer would be a second name for the block.

| Operation | Needs | Gives |
|---|---|---|
| `Ptr::alloc(n)` | `n >= 0` | `cap(return) = n`, no slot filled |
| `Ptr::write(p, i, x)` | `0 <= i < cap(p)`, `!filled(p, i)` | `filled` and `at(_, i) = x` at `i`, the other slots as they were |
| `Ptr::get(p, i)` | `0 <= i < cap(p)`, `filled(p, i)` | `return = at(p, i)`: a view, as `get` of a list is |
| `Ptr::set(p, i, x)` | `0 <= i < cap(p)`, `filled(p, i)` | `at(_, i) = x`; the old element is dropped |
| `Ptr::take(p, i)` | `0 <= i < cap(p)`, `filled(p, i)` | a `Taken<T>`: `.value = at(p, i)`, and `.ptr` with slot `i` empty |
| `Ptr::clear(p, from, to)` | `0 <= from <= to <= cap(p)`, every slot in `from..to` filled | those slots empty, their elements dropped |
| `Ptr::resize(p, n)` | `n >= 0`, no slot in `n..cap(p)` filled | `cap(return) = n`, slots below `min(n, cap(p))` as they were |
| `Ptr::free(p)` | no slot in `0..cap(p)` filled | `0` (there is no unit type) |

- **`write`, `set`, `take`, `clear` and `resize` take the pointer and give one back**, in place natively. The validator sees a new value, so each one is an assignment: `p = Ptr::write(p, i, x);`.
- **`get` reads the pointer and moves nothing**, so its pointer operand can be a lent `&Ptr<T>`, or a field of a lent `&Self`, and the result is a view (MIR.md, Moves). `MirMoves` refuses to move the result out (`cannot move x out of a Ptr, which still holds it: write clone(x), or Ptr::take`), as it does for an element of a list.
- **`write` needs an empty slot, `set` a filled one.** Writing over a filled slot would lose an element that may own something, and setting an empty slot would drop memory that was never written. For a `Ptr<Int>` that costs nothing: `set` drops nothing.
- **`take` gives two values back.** There are no tuples, so the prelude declares `struct Taken<T> { ptr: Ptr<T>, value: T };`, and the program takes its fields: `t = Ptr::take(p, i); x = t.value; p = t.ptr;`.
- **`clear` and `set` drop what they remove** with the runtime's `tersus_drop`, walking the descriptor of `T`, as a list frees its elements today. This is the only place a pointer operation runs code on an element, and it does nothing for a type that owns nothing.
- **`resize` is `realloc`.** Moving an element is copying its words in Tersus, so the bitwise copy that `realloc` makes is a move of every filled slot.
- **What fails at run time and not in the proof**: an allocation the system refuses, and a size whose bytes overflow an `Int`. Both end the program with an error, as an overflow does. No contract can promise memory.

The contracts are axioms, the trusted base, as the contract of `writeByte` is. Everything written on top of them is proved.

## Ghost facts

Three functions describe a pointer to the validator. They can be used in contracts, `affirm`, `define` and invariants, and nowhere else (`cap is known to the validator only: keep the capacity in a field`).

- `cap(p)`: the number of slots, which is at least 0.
- `filled(p, i)`: slot `i` holds an element.
- `at(p, i)`: the element in slot `i`, which is known only when it is filled.

**They are arrays the validator already knows.** Internally `filled(p, i)` is `get(filledOf(p), i)` and `at(p, i)` is `get(contentsOf(p), i)`, over two ghost arrays of size `cap(p)`. Each operation's facts are then those of `set` on the arrays: `write` gives `contentsOf(return) = set(contentsOf(p), i, x)` and `filledOf(return) = set(filledOf(p), i, true)`. The `forall` triggers, frame facts, case splits and linked-list proofs of LANGUAGE.md work unchanged, and no new term reaches the proof engine. This is the main reason for modelling the contents as values: none of `ProofEngine` changes.

## Examples

A `Vec` built on a pointer. This is `examples/vec.tersus` without the filler value that `Array::boxed` needed, and with a `pop` that gives the element back:

```tersus
struct Vec<T> {
    ptr: Ptr<T>,
    cap: Int,
    len: Int,
} invariant [{
    affirm 0 <= len; affirm len <= cap; affirm cap = cap(ptr);
    affirm forall j in 0..len: filled(ptr, j);
    affirm forall j in len..cap: !filled(ptr, j);
}];

struct Popped<T> { vec: Vec<T>, value: T };

impl<T> Vec<T> {
    fn new() -> Self [{ }] [{ affirm return.len = 0; }] {
        return Self { ptr: Ptr::alloc(4), cap: 4, len: 0 };
    };

    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm at(return.ptr, self.len) = x; }] {
        v = self;
        if v.len = v.cap {
            n = v.cap * 2 + 4;
            v = Self { ptr: Ptr::resize(v.ptr, n), cap: n, len: v.len };
        };
        return Self { ptr: Ptr::write(v.ptr, v.len, x), cap: v.cap, len: v.len + 1 };
    };

    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = at(self.ptr, i); }] {
        return clone(Ptr::get(self.ptr, i));
    };

    fn pop(self: Self) -> Popped<T> [{ affirm self.len >= 1; }] [{ affirm return.vec.len = self.len - 1; }] {
        t = Ptr::take(self.ptr, self.len - 1);
        return Popped<T> { vec: Self { ptr: t.ptr, cap: self.cap, len: self.len - 1 }, value: t.value };
    };

    // Until step 26 gives Vec a Drop, a program frees a Vec by calling this
    fn free(self: Self) -> Int [{ }] [{ }] {
        return Ptr::free(Ptr::clear(self.ptr, 0, self.len));
    };
};
```

`Box<T>` in Tersus (step 29) is a pointer with one filled slot:

```tersus
struct Box<T> { ptr: Ptr<T> } invariant [{ affirm cap(ptr) = 1; affirm filled(ptr, 0); }];

fn boxNew<T>(x: T) -> Box<T> [{ }] [{ affirm at(return.ptr, 0) = x; }] {
    return Box<T> { ptr: Ptr::write(Ptr::alloc(1), 0, x) };
};

fn unbox<T>(b: Box<T>) -> T [{ }] [{ affirm return = at(b.ptr, 0); }] {
    t = Ptr::take(b.ptr, 0);
    done = Ptr::free(t.ptr);
    return t.value;
};
```

## Ownership and moves

- **Use after free and double free are already caught.** A `Ptr` is not Copy, so `Ptr::free(p)` moves `p`, and `MirMoves` reports any use after it (`p was moved at line 12:5`) on every path. The same holds for the pointer given to `write` and the other operations that take one. This needs no new analysis, so pointers do not have to wait for linear types.
- **Leaks are caught once `Ptr` is linear** (DROPS.md, Part 2). A `Ptr` is then a linear type: it has to be given to `free`, returned, or put in a value that is used. A struct that holds one is linear unless it has a `Drop`, which is how a `Vec` becomes affine at step 26. Until then a forgotten pointer leaks, `TERSUS_CHECK` and valgrind report it, and nothing unsafe happens.
- **No element is lost.** `free` needs every slot empty, and an element can only leave a slot through `take` (to the program) or `clear` and `set` (dropped), so a block is never freed with something in it.
- **Containers.** `List<Ptr<T>>`, `Array<Ptr<T>, N>` and a type parameter that is not bounded are refused for a `Ptr`, or anything that holds one, with a message that names the type: `StdList` copies its element into its slack, and an unbounded `T` is taken to be Clone (DROPS.md, Decision 5). `Box<Ptr<T>>`, fields and enum payloads hold exactly one and are fine. The restriction on lists ends when `StdList` is built on a `Ptr`, as `Vec` is above.

## Running it

- **`eval` and the executor keep values.** Since nothing else can name the block, a `Ptr` can be a value in the interpreters: `VPtr cap (Map Int Value)`, with each operation a function from value to value. `MirEval` and `StdLib.evalBuiltinFunct` need no heap, and `testNative` compares them with native code as it does now.
- **The heap model of `TestOwnership`** learns blocks that are allocated, written, taken from and freed by hand, and reports a slot read before it is written, a block freed with a slot filled, and a block left at the end.
- **MIR.** The operations are `ListOp`s (`PtrAlloc`, `PtrWrite`, `PtrGet`, `PtrSet`, `PtrTake`, `PtrClear`, `PtrResize`, `PtrFree`), with words in `MirData`. `PtrGet` is a `Peek` when the ownership pass would make it one, so a read in place costs nothing. `roles` makes the pointer operand of `PtrGet` a read and that of the others a consume. `MirVerify` checks the types. `Ptr` is a new `Type` constructor (`ptr T` in the data).
- **Native code.** A `Ptr` is an `i64` address. `alloc` and `resize` call the runtime's `allocate` and `reallocate`, so the `TERSUS_CHECK` accounting covers them. An element is `words(T)` words at `address + i * words(T) * 8`, read and written as an element of an array is. `clear` and `set` call `tersus_drop` on the slot. The descriptor gets `KIND_PTR = 8`: dropping it does nothing, and it is never cloned, compared or printed.
- **Both emitters, in step.** `LlvmEmit` and `examples/emit.tersus` gain the same cases, `examples/mir_reader.tersus` reads the new words, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` keeps them equal.

## Why not an address

The roadmap's sketch of step 25 was `*T`: a Copy word with `*p`, `p.offset(i)`, `load` and `store`, where the validator tracks `valid(p)` and `size(p)` through contracts, and a function that uses one is marked in its signature. Three things go wrong with it against the validator as it is:

1. `valid(p)` is a fact about the heap and not about `p`. After `free(q)` it is false for every `p` that aliases `q`, so a fact the validator holds would stop being true without any assignment, which the validator rests on never happening.
2. A `load` through `p` after a `store` through an alias `q` needs to know whether `p` and `q` overlap. That is a heap and a frame on every contract, a bigger change than everything else in this document combined.
3. `p.offset(i)` makes an interior pointer, which is an alias by construction.

What `*T` would add over `Ptr<T>` is sharing. The users the roadmap names don't need it: `Box`, `StdList`, `Vec` and `String`'s storage (steps 29 and 30b) own their blocks. The runtime's descriptor walking is replaced by code made per type (step 30a) and not by type-erased pointers. `write(fd, ptr, n)` (step 30d) can take a lent `&Ptr<Byte>` and a range. A graph or a doubly linked list is a block of nodes linked by index, as in A linked list in an array, and now with no filler values.

If something does need sharing later (a C struct passed by address, an intrusive list, `mmap`), it should be a separate, explicitly unchecked type, `Addr<T>`. It would be a Copy word whose loads give a value the validator knows nothing about, usable only in a `trusted fn`: a function whose body is checked for types and compiled, and whose contract is assumed, the way an `axiom`'s is. That is a contained escape hatch and not the memory model, and it is left out until something in the repository needs it.

## Changes to other documents

- `README.md`, step 25: `Ptr<T>` and the operations above in place of `*T`, `*p` and `p.offset(i)`, no marker in signatures, and `Ptr` as the way a value holds its block. Step 29's `struct Box<T> { ptr: *T }` becomes `ptr: Ptr<T>`, and `*[T]` becomes a `Ptr<T>` with a capacity field.
- `DROPS.md`, Part 3: points here. Its sketch (`alloc`, `store` giving the pointer back, `load` through a lent pointer, `take`, contents as an array) is this design, with `filled`, `set`, `clear`, `resize`, `Taken` and the non-linear first step added.
- `LANGUAGE.md`: a section "Pointers" after "Box", the ghost functions in Validation Statements, and the container refusals in Current Limitations, when it is built.

## Order of work

1. **The type and the operations**, with nothing built on them: the checker (`TPtr`, the builtins, the refusals, ghost-only `cap`/`filled`/`at`), `StdLib` contracts, the executor and `MirEval`, `MirMoves` roles, the emitters and runtime, `examples/pointers.tersus` (a hand-managed buffer that is filled, read, emptied and freed) and `examples/rejected/` programs for each contract: read before write, write over a filled slot, index out of range, free with a slot filled, use after free.
2. **`Vec` on a pointer** (`examples/vec.tersus` as above), which tests whether the invariant's two foralls are cheap enough to prove at every operation.
3. **Linear `Ptr`**, when DROPS.md, Part 2 lands. It turns leaks into errors.
4. **`StdList` on a pointer** after drops (step 26), which gives it a `Drop`, then lists of values with drops, then `Box` (step 29).

## Decisions to make

1. **Ghost capacity, or a fat pointer.** Here the capacity is ghost and the pointer is one word, which keeps `Box` at one word and leaves a `Vec` holding a `cap` field equal to `cap(ptr)`. A fat pointer (address and capacity, readable as `Ptr::cap(p)`) saves that field and matches today's `Box<Array<T>>`, at a word per `Box`.
2. **Must `free` find every slot empty?** It is what makes "no element is lost" a proof. For `Vec` it is a `forall` over `0..cap` from two foralls over `0..len` and `len..cap`, after `clear(ptr, 0, len)`, and whether the engine splits that range without help is untested. If it doesn't, the cheaper rule is that `free` drops what is filled (like `clear(0, cap)`, which needs no proof, and leaves leaks to the linear check).
3. **`write` and `set` as two operations**, or one `put` that drops whatever is there. Two keep "this slot was empty" in the proof, which is what catches a lost element at the place it is lost. One is simpler for a `Ptr<Int>`.
4. **`Taken<T>` in the prelude**, or tuples. A struct is all the language has now. If tuples come, `take` should return one.
5. **Whether `Addr<T>` and `trusted fn` are worth designing now** or only when a user appears. The recommendation is the latter.
