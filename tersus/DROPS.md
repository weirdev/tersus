# Drops, linear types and raw pointers (design)

This is the design for steps 25 to 27 of the roadmap in `README.md`, written against the code as it is: `MirOwnership` (who owns what), `LlvmRuntime` (`tersus_drop` walks a type descriptor), the two emitters (`LlvmEmit` and `examples/emit.tersus`, which must write the same IR), `MirEval` (which ignores `Drop`), and a validator that treats values as immutable. Nothing here is built yet.

## Where things stand

- Ownership is implicit and structural. `needsDrop` says a type owns something to free (a list, a `Box`, or a struct, enum or array that holds one). `insertOwnership` turns every use into a `Move` or a `Clone` and puts a `Drop` for every owned local at each `Return`. `tersus_drop` frees by walking the descriptor. A moved-from slot holds cleared words, and dropping that does nothing.
- Copying is implicit: a value wanted twice is cloned. That is what keeps the language one of values, and why a proof about a value stays true.
- A drop is memory only. Nothing a program writes runs when a value goes away, and nothing stops a program from forgetting a handle.
- There is no unit type (a function that does something returns an `Int`), no `&mut` (`&T` is a lent parameter that is only read), no visibility of fields, and a trap ends the process with no unwinding.
- `eval` runs the validated MIR, which has no ownership in it. `testNative` compares `eval` with the executable, so any effect a drop has must be in both.

## Three kinds of type, and one new rule

| Kind | Copied implicitly | Dropped implicitly | Made by |
|---|---|---|---|
| plain / owning (today) | yes | yes | everything now |
| **affine** | no (moved; an `impl Clone` makes it copyable) | yes, at the end of its life, running its `Drop` | `impl Drop for T` |
| **linear** | no | no: it has to be consumed | `linear struct`, `linear enum` |

The kind of a type is that of its most restrictive part: a struct, enum, array or `Box` that holds a linear value is linear, one that holds an affine value is affine (the same walk as `needsDrop`, which is where it is computed). `List<T>` and `Array<T, N>` of such a type are refused for now (see Containers).

A type has a `Drop` or is `linear`, not both: a drop is the implicit use of a value at the end of its life, and a linear value has none.

## Part 1: user defined drops (step 26)

```tersus
trait Drop {
    fn drop(self: &Self) -> Int [{ }] [{ }];
};

struct Logged { id: Int };

impl Drop for Logged {
    fn drop(self: &Self) -> Int {
        writeByte(self.id);        // an effect the validator does not look at
        return 0;
    };
};
```

**The signature is `self: &Self`, not `&mut Self`.** The drop reads the value, and the compiler drops the fields afterwards, so closing a descriptor, writing a trailer or calling `free` on a pointer in a field needs nothing to be written to. This avoids adding `&mut` for one use. The trait is in `lib/prelude.tersus` like `Sequence`, and is the one trait the compiler knows by name (`progDrops :: Map Name Name` in the MIR, type to impl function).

**The contract is empty on purpose.** A drop is called where the program says nothing, so it may not ask for anything: no input contract (an impl may ask for less than a trait, and the trait asks for nothing), the invariant of the struct is assumed as for any value of it, and the function must end (a `~` drop is refused). The validator checks the `drop` function like any other impl function. It does not need to see the implicit calls: the drop reads a value and returns an `Int`, so it cannot change any value of the program, and what was proved about values stays true after it runs. (The roadmap asks for the validator to see the call; the immutability of values makes that unnecessary, and the contract above makes it safe.)

**When it runs.**

1. When a local that holds the value is assigned over: before the new value is stored.
2. When the function returns, for every local that still holds one, in the reverse order of the locals (the highest local number first). Nested blocks share the function's scope, so this is the end of the function and not the end of the block. This is the order `insertOwnership` has to emit; it is ascending today, and only becomes visible once a drop has an effect.
3. When what contains it is dropped: the `drop` of the value first, then its fields in declaration order (as Rust does), and a `Box` drops what it holds before it frees.
4. Never on a trap. `fail` exits the process; nothing unwinds. A program that wants a file closed on every path uses a linear type (Part 2), which cannot reach the end without closing it.
5. A value that `main` returns is dropped after it is printed.

An explicit early drop is a function, not a feature: `fn discard<T>(x: T) -> Int { return 0; }` takes the value, and the parameter is dropped at its return.

**Moved-from values need a flag.** Today the pass relies on cleared words, so that dropping a moved-from slot frees nothing. A `File { fd: 0 }` cleared to zeros is a valid file, so a type with a drop cannot do that. The options:

- *A hidden word in the value* (recommended): a struct or enum with a `Drop` has one more word, the first, which `MakeData` sets to 1 and `Move` clears with the rest of the words. `tersus_drop` calls the drop function only when the word is 1, then clears it. Equality, printing and `==` ignore it. Costs a word per such value and changes the layout in two places (below), but there is only one rule and it works through `Box`, fields and `TakeField` leftovers.
- *Drop flags as `Bool` locals in the MIR*, as Rust does. No layout change, but it covers locals only, and a value nested in another has no flag. Rust avoids that by refusing to move a field out of a type with a `Drop`; Tersus can do the same (below) and still prefer one flag mechanism.

**A value with a drop is not taken apart.** A `match` that binds an owning field of it would move the field out and leave the rest. Following Rust (E0509), a field of a type with a `Drop` is read, never taken: a plain field is copied, and an owning field is a `Peek` or a `Clone` (which needs the field's type to be cloneable). So the cleared-words case cannot occur inside a value, and the flag only has to describe whole values.

**Copying.** `insertOwnership` emits `Clone` where a value is wanted twice. For an affine type that is an error, reported by the check of Part 2 (`x was moved`), unless the type has `impl Clone`:

```tersus
trait Clone { fn clone(self: &Self) -> Self [{ }] [{ }]; }
```

The `Clone` call is then an ordinary `Call` in the MIR, so a refcount can be written. The runtime's deep copy never copies an affine value bitwise (it would be freed twice): the descriptor of a type with a `Clone` impl names that function, and `tersus_clone` calls it.

### Containers (the reason step 25 comes first)

`StdList<T>` is a `Box<Array<T>>` and a length. A push into a full list makes `Array::boxed(2n + 4, x)`, which **copies `x` into every slot** (the slack), and `pop` leaves the popped element in the array, to be written over or freed with it. Both are wrong for a value with a drop: the slack would hold clones that run the drop, and the popped element would be dropped late or twice. So the first cut refuses `List<T>`, `Array<T, N>`, `Array::boxed` and `Vec<T>` of a type with a `Drop` or a linear type, with a message that names the type and the container. A `Box<T>`, a struct field and an enum payload are fine: they hold exactly one value or none.

Lists of such values come with raw pointers (below): the slack is memory that holds nothing, and the list's own `Drop` drops elements `0..len` and frees the block.

### Implementation

1. Checker: `Drop` and `Clone` in the prelude, `impl Drop for T` allowed for a struct or enum, one per type, a `~` drop refused; `Program.progDrops` and `progClones`.
2. `MirOwnership`: `needsDrop` is true for a type with a drop, whatever its fields; a local of an affine type is never `Clone`d (the check of Part 2 refuses first); locals are dropped in reverse.
3. `LlvmRuntime`: the descriptor gets `dropfn` (and `clonefn`); `tersus_drop` calls `dropfn(slot)` on a live value before the fields; the flag word counts in `words`.
4. Both emitters, in step: `slotsOf` adds the flag, `MakeData` stores 1, the descriptor has the new fields, `MirData` writes `progDrops`, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` fails if they differ, so they cannot drift. (This is the main cost of the layout change; keeping the new behaviour in the descriptor and the runtime rather than in new MIR statements keeps it to this.)
5. `MirEval`: `Move` leaves a moved-from marker, `Drop` runs the user drop for a live value and then the fields. `Cli.eval` runs the owned MIR whenever the program has an `impl Drop` (and everywhere, once nothing depends on `eval` being cheap), so the reference semantics of a drop live in one place.
6. `TestOwnership`'s model of the heap learns the same, and a program of the tests writes a byte in each drop, so that order is compared between `eval` and the executable.

## Part 2: linear and affine checking (step 27)

A linear value must be consumed on every path, and a value that cannot be copied must not be used after it is moved. Both are one analysis of the MIR, written next to `MirOwnership` and sharing its notion of what an operand does (`roles`: `Read` or `Consume`). **The module is called `MirMoves`** (`Linear.hs` is the Fourier-Motzkin solver of the proof engine).

### Syntax

```tersus
linear struct File { fd: Int, open: Bool };
linear enum Opened { Ok { file: File }, Failed { code: Int } };
```

`linear` is a reserved word before `struct` or `enum`. Nothing else in the language changes: there are no new operators and no annotations on `let`, since the kind belongs to the type.

### What uses a value

| Operand | Effect on a local of a linear or affine type |
|---|---|
| reads it: `==`, `size`, `x.f`, `x is V`, a `&T` argument, a ghost statement | none |
| takes it: `y = x`, a by-value argument, a struct or enum made from it, `return x`, `Box::new(x)` | the local is moved |
| takes a part: a `match` arm that binds a field, `Box::unbox` | that part is moved |

A ghost mention (`affirm`, `define`, a contract) is never a use. The validator's locals are immutable, so a fact about a moved value is still a fact about that value: `x2 = close(x);` followed by `affirm x.fd = 3;` is sound and needs no new rule. (The roadmap expects the validator to learn that a linear value is used once; it does not need to.)

### The analysis

A forward dataflow over the basic blocks. For each local of a linear or affine type it keeps the **obligations**: the set of `(variant, field)` pairs that still hold a linear value, starting full at the assignment that gives the local its value (a struct has one variant).

- A move of the whole local clears all its obligations; a move of a field clears that one.
- `x is V` on a `SwitchBool` edge prunes the obligations of the other variants on the true edge and those of `V` on the false edge, the way the validator already adds the condition to a path. This is what lets a `match` consume an enum in each arm by taking only what that variant holds, and an arm of `Opened::Failed` owes nothing.
- A block that joins paths takes the union of their obligations.
- A use of a local whose obligations are empty, or of a part already moved, is `x was moved` (an affine value too: there is no `Clone` to fall back on).
- Assigning to a local that still has obligations is `x is linear and is overwritten`.
- At each `Return` (and at the end of `main`) a linear local with obligations left is `x is linear and is not used`. An affine local with some is fine: the drop of Part 1 takes it, or the flag says it was moved.
- A `Call` whose result is a linear value and is not used (the `$call` assignment of a call written as a statement) is `the result of f is linear and is not used`.

A loop needs no rule of its own. The join at the header gives `x was moved` for a value of the loop that a body moves and the next iteration uses (obligations empty at the back edge, full at the entry), and a body that rebuilds it (`f = write(f, b);` moves `f` into the call and assigns the result) is fine. A `~` function may leave a linear value, since it never reaches a `Return` that way: that falls out of the dataflow and is not a special case.

The check runs on the lowered MIR **before validation** (a source error is cheaper than a proof) and again on the monomorphized MIR that `MirOwnership` runs on, so a generic `fn dup<T>(x: T)` that is fine for `T = Int` is refused for `T = File` at that instance. That is the same template rule steps 21 and 24 give bounded functions. Making it modular means a kind bound on a type parameter (`T: Copy`), which waits for step 24.

Errors name the function and the local, and the source line when the MIR has one; today only ghost statements carry positions, so the first version reports `in fn close: file is linear and is not used`. Adding a position to `Assign` is useful elsewhere and can follow.

### Consuming a linear value

A linear struct with only plain fields has no function that ends it, so the language has to give one: **taking it apart is consuming it.** A struct can already be matched as the only variant of its type:

```tersus
fn close(f: File) -> Int [{ affirm f.open; }] [{ }] {
    match f { File { fd: fd } => { return closeFd(fd); } };
};
```

A linear field in the pattern is moved into the arm and must itself be consumed. Plain fields are dropped with the rest. A function with a `linear` parameter is a consumer by that alone; the body decides how.

### Typestate through contracts

The renaming that functions already give (`f2 = write(f, b)`) is what makes linear values useful to a program that proves things. The type holds the state, the contract states the protocol, and the linear check says the old state cannot be used again:

```tersus
linear struct Conn { fd: Int, open: Bool };

fn send(c: Conn, b: Byte) -> Conn [{ affirm c.open; }] [{ affirm return.open; }] { ... };
fn shut(c: Conn) -> Conn [{ affirm c.open; }] [{ affirm !return.open; }] { ... };
```

`send(shut(c), b)` fails to validate (`Could not prove: c.open`), and `shut(c); send(c, b);` fails the linear check. Neither needed a new proof rule.

### Containers and generics

`List<File>` and `Array<File, N>` are refused until a list can give an element back (`get` clones, and `pop` forgets the element; there is no `take`). With raw pointers the library list gets `swapRemove`-like consuming operations and the restriction goes. `Box<File>`, fields and payloads work now (`Box::unbox` consumes).

### What this does not give

There are no fields hidden from other code, so any code can destructure a `File` and discard its parts. Linear types guard against forgetting by accident, and a program that matches on someone's linear struct is doing it in the open. Making the guarantee a boundary needs private fields or opaque types, which is a separate step (the invariant of a struct is already safe against code that builds the struct by hand, because the validator checks it at each `MakeData`; there is no equivalent for a protocol that code outside is not allowed to bypass).

## Part 3: raw pointers (step 25), as far as 26 and 27 need

The roadmap sketch (`*T`, `alloc`, `free`, `load`, `store`) stands. The one design question this document answers is **how the validator sees memory**, and the answer comes from Part 2: **a pointer to memory the program owns is a linear value that holds its contents as an array.**

- `alloc<T>(n)` returns `Ptr<T>`, linear, with `cap(p) = n`. Its contents are an array value of `n` slots the program may not read until it writes them.
- `store(p, i, x) -> Ptr<T>` moves the pointer in and out, with `i < cap(p)`: the result has the contents of `set(contents(p), i, x)` and the same capacity. It is `set`, so the facts about arrays carry over without a heap model.
- `load(&p, i)` reads through a lent pointer.
- `free(p)` consumes it. Linear says it is freed once and not used after; the contracts say index in range.
- The contents of slots past what the library has written are not known, and that is the point: `Vec<T>` is `{ ptr: Ptr<T>, len: Int }` with the invariant `len <= cap(ptr)`, and its `Drop` drops elements `0..len` (a builtin `take(&p, i)` that moves an element out, trusted, with `i < len` proved by the program) and frees the block.
- `Ptr<T>` itself is linear and has no drop. `Vec<T>` is affine because it has one. `Box<T>`, `StdList<T>` and `String`'s storage move to this in steps 29 and 30.

The builtins `alloc`, `free`, `take` and the descriptor-walking drop are the trusted base, the way `writeByte` is: their contracts are axioms, and the library built on them is proved. Whether `Ptr<T>` holds a pointer and a length (a fat pointer, like `Box<Array<T>>` today) or a pointer only is a layout decision for that step.

## Order of work

1. **Linear checking and affine types without drops.** `MirMoves`, `linear struct` and `enum`, the refusal of a linear element in a list, the examples `examples/linear_file.tersus` and `examples/typestate.tersus`, tests of each error and of a program that passes. No emitter change, no runtime change, and the value is real already (a handle that cannot be forgotten).
2. **Drops.** `Drop` in the prelude, `progDrops`, the flag word, the descriptor and runtime change, the same change in both emitters, `MirEval` and the heap model, tests that compare the order of effects between `eval` and the executable, and a check under valgrind that nothing is dropped twice.
3. **`Clone`** as a user trait, for types with a drop that can be copied.
4. **Raw pointers**, then lists of values with drops and linear values, then `Box` and lists written in Tersus (steps 29 and 30).

## Decisions to make

1. **The flag word, or flags as locals.** A hidden word is the simplest, and costs a word and a change to both emitters. Locals only work if types with a drop cannot be nested in a way that needs a flag, which is true while they cannot be list elements, and is a bigger change to the ownership pass.
2. **Drops at the end of the function, or at the last use.** The end of the function is predictable (a file stays open to the end of its function) and is what the pass does now. The last use closes sooner and puts the order of effects at the mercy of liveness.
3. **`eval` runs the owned MIR.** Required for the reference interpreter to run drops. It is a change in what `eval` costs and in what it is the oracle for.
4. **Linear types before drops.** The first step needs no runtime work at all and the guarantee does not depend on the second.
5. **Template checking of generics now, a kind bound later.**
