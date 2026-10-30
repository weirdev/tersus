# Drops, linear types and raw pointers (design)

> **Provisional.** This is a plan, not a decision, and it was revised once already: the first draft assumed implicit copies, and explicit `Clone`/`Copy` and the `MirMoves` check were built before any of it. Expect more changes when the drops are started (the flag word, the moment a drop runs and the `eval` change are open, see Decisions). Where the text says "now", it means the code as of the explicit-copies change.

This is the design for steps 25 to 27 of the roadmap in `README.md`, written against the code as it is: `MirOwnership` (who owns what), `LlvmRuntime` (`tersus_drop` walks a type descriptor), the emitter (`examples/emit.tersus`), `MirEval` (which ignores `Drop`), and a validator that treats values as immutable. Nothing here is built, except what came first and changed the plan: copies are explicit (`clone`, `impl Clone for T { };`, `impl Copy for T { };`), statements carry their line (`Mark`, `GhostPosition`), and `MirMoves` finds a use of a moved value, see LANGUAGE.md, Moves, Clone And Copy.

## Where things stand

- Ownership is implicit and structural. `needsDrop` says a type owns something to free (a list, a `Box`, or a struct, enum or array that holds one). `insertOwnership` turns every use into a `Move` or a `Clone` and puts a `Drop` for every owned local at each `Return`. `tersus_drop` frees by walking the descriptor. A moved-from slot holds cleared words, and dropping that does nothing.
- Copying is explicit (it was implicit: a value wanted twice was cloned): a value that is not Copy is moved, and the program writes `clone(x)` to keep it. A clone has the value of what it copies, which is why a proof about a value stays true. `MirMoves` already does the first half of the check that Part 2 asks for: it follows places (a local with the fields and elements followed from it, and the views that `get`, a field read, a cast, `Box::unbox`, `match` and `for` make of them) along every path, and reports with a line. The linear check is that pass with one more fact per local, the obligations to move it. Positions in errors, which the first draft listed as future work, exist.
- A drop is memory only. Nothing a program writes runs when a value goes away, and nothing stops a program from forgetting a handle.
- There is no unit type (a function that does something returns an `Int`), no `&mut` (`&T` is a lent parameter that is only read), no visibility of fields, and a trap ends the process with no unwinding.
- `eval` runs the validated MIR, which has no ownership in it. `testNative` compares `eval` with the executable, so any effect a drop has must be in both.

## Three kinds of type, and one new rule

| Kind | Copied wherever wanted | `clone(x)` | Dropped implicitly | Made by |
|---|---|---|---|---|
| **Copy** (now) | yes | if Clone | yes (nothing to free) | `Int`, `Byte`, `Bool`, functions, `impl Copy for T { };` |
| **moved** (now: every other type) | no | if `impl Clone` | yes, freeing what it owns | everything else |
| **affine** | no | only if the type says it has `Clone` | yes, at the end of its life, running its `Drop` | `impl Drop for T` |
| **linear** | no | no | no: it has to be consumed | `linear struct`, `linear enum` |

"Moved" is the old "plain / owning" row without the implicit copy; affine is moved plus a `Drop`. A type with a `Drop` is never Copy (the checker refuses `impl Copy` for it), and a type with a drop cannot be built by `array(n, x)` or `Array::boxed(n, x)` unless it is Clone, which is the container rule below arriving for free.

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

**Copying.** `Clone` and `Copy` exist already, as traits with no functions that a type says it has (`impl Clone for T { };`): `clone(x)` is the structural copy, the MIR's `Clone`, and a value that is not Copy is moved. A type with a drop is not Copy, and it is Clone only if it says so, and a structural `impl Clone` for a type with a `Drop` is refused (the copy would be bitwise, and freed twice), so `x was moved` (the check of `MirMoves`) is what a second use of an affine value already is. What this step adds is a `Clone` with a body of its own, for a type whose copy is more than its fields (the trait then has a function, where `Clone` has none now, so the prelude's trait and the check of the impl change, and `clone(x)` on such a type becomes a call):

```tersus
impl Clone for Counted { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { ... }; };
```

`clone(x)` is then an ordinary `Call` in the MIR, so a refcount can be written. The runtime's deep copy never copies an affine value bitwise (it would be freed twice): the descriptor of a type with such an impl names that function, and `tersus_clone` calls it.

### Containers (the reason step 25 comes first)

`StdList<T>` is a `Box<Array<T>>` and a length. A push into a full list makes `Array::boxed(2n + 4, x)`, which **copies `x` into every slot** (the slack), and `pop` leaves the popped element in the array, to be written over or freed with it. Both are wrong for a value with a drop: the slack would hold clones that run the drop, and the popped element would be dropped late or twice. So the first cut refuses `List<T>`, `Array<T, N>`, `Array::boxed` and `Vec<T>` of a type with a `Drop` or a linear type, with a message that names the type and the container. A `Box<T>`, a struct field and an enum payload are fine: they hold exactly one value or none.

Lists of such values come with raw pointers (Part 3 and `POINTERS.md`): the slack is slots that hold nothing, and the list's own `Drop` drops elements `0..len` and frees the block.

### Implementation

1. Checker: `Drop` in the prelude (`Clone` is there already), `impl Drop for T` allowed for a struct or enum, one per type, a `~` drop refused, `impl Copy` refused for a type with a drop; `Program.progDrops` (and a table of the types with a `Clone` of their own). A `CopyDef`-like statement carries each to the lowering, as `CopyDef` does for Copy.
2. `MirOwnership`: `needsDrop` is true for a type with a drop, whatever its fields; locals are dropped in reverse. The pass still clones a read-only view that cannot look at its value in place; for a value with a drop that is an error, since a clone of it runs the drop twice, so `MirMoves` must refuse a view of one that the pass would clone.
3. `LlvmRuntime`: the descriptor gets `dropfn` (and `clonefn`); `tersus_drop` calls `dropfn(slot)` on a live value before the fields; the flag word counts in `words`.
4. Both emitters, in step: `slotsOf` adds the flag, `MakeData` stores 1, the descriptor has the new fields, `MirData` writes `progDrops`, and `bootstrap/emitter.ll` is regenerated. `TestMirEmit` fails if they differ, so they cannot drift. (This is the main cost of the layout change; keeping the new behaviour in the descriptor and the runtime rather than in new MIR statements keeps it to this.)
5. `MirEval`: `Move` leaves a moved-from marker, `Drop` runs the user drop for a live value and then the fields. `Cli.eval` runs the owned MIR whenever the program has an `impl Drop` (and everywhere, once nothing depends on `eval` being cheap), so the reference semantics of a drop live in one place.
6. `TestOwnership`'s model of the heap learns the same, and a program of the tests writes a byte in each drop, so that order is compared between `eval` and the executable.

## Part 2: linear and affine checking (step 27)

A linear value must be consumed on every path, and a value that cannot be copied must not be used after it is moved. Both are one analysis of the MIR, written next to `MirOwnership` and sharing its notion of what an operand does (`roles`: `Read` or `Consume`). **The module is `MirMoves`, which exists** (`Linear.hs` is the Fourier-Motzkin solver of the proof engine, hence the name).

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

`MirMoves` already runs on the lowered MIR **before validation**, from `lowerElaborated` (not on the monomorphized MIR). A function with bounds (`<T: Clone>`, `<T: Copy>`) is made for each type it is called with, so it is checked for those types. An unbounded type parameter is taken to be Clone and not Copy, and not checked against what it is given, so `fn dup<T>(x: T)` would be accepted for `T = File`: a `File` is not Clone, so `clone(x)` there is a hole until type parameters can say what they need (step 24), or until the check also runs on the instances that native code is made of. Linear and affine types make that hole matter, so closing it comes before they are allowed in generic code (refuse them as arguments of an unbounded type parameter until then).

Errors name the function, the line and column of the statement, and the variable, as `MirMoves` does now (`in close, line 9:5: file is linear and is not used`). The check does not distinguish a move that happens on some paths from one on all of them in its messages; the linear rule needs that difference (it is the union of obligations at a join).

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

`List<File>` and `Array<File, N>` are refused until a list can give an element back (`get` clones, and `pop` forgets the element; there is no `take`). With raw pointers (`POINTERS.md`: `Addr::take`, or `replace` on slots of `Uninit<T>`) the library list gets consuming operations and the restriction goes. `Box<File>`, fields and payloads work now (`Box::unbox` consumes).

### What this does not give

There are no fields hidden from other code, so any code can destructure a `File` and discard its parts. Linear types guard against forgetting by accident, and a program that matches on someone's linear struct is doing it in the open. Making the guarantee a boundary needs private fields or opaque types, which is a separate step (the invariant of a struct is already safe against code that builds the struct by hand, because the validator checks it at each `MakeData`; there is no equivalent for a protocol that code outside is not allowed to bypass).

## Part 3: raw pointers (step 25)

Raw pointers have a design of their own, `POINTERS.md`, which replaces the sketch that was here (a linear `Ptr<T>` that held its contents as an array). The question this section answered, how the validator sees memory, has the same answer in a different shape: an address `Addr<T>` is a runtime word that can be aliased, and the permission to the memory, `Block<T>`, is a ghost linear value whose contents are ghost arrays, so a write is `set` and the facts about arrays carry over without a heap model. What Part 1 and Part 2 need of it:

- **Lists of values with drops or linear values** are built on a block whose slots can be empty: the slack holds nothing, `take` moves an element out, and the list's `Drop` drops slots `0..len` (`Addr::dropRange`) and frees the block. `Uninit<T>` and `replace` give the same without addresses.
- **A permission is linear**, so linear checking (Part 2) comes before pointers, and a struct that holds one is linear until it has a `Drop`.
- **A `drop` that frees a permission** has to consume it, which a lent `self: &Self` cannot: that is Decision 1 of `POINTERS.md`, decided with step 26.

## Order of work

0. **Done: explicit copies.** `Clone`, `Copy`, `clone`, `MirMoves` (moves, views, lent parameters) and positions.
1. **Linear checking.** Extend `MirMoves` with the obligations, `linear struct` and `enum`, the refusal of a linear element in a list and of a linear type for an unbounded type parameter, the examples `examples/linear_file.tersus` and `examples/typestate.tersus`, tests of each error and of a program that passes. No emitter change, no runtime change, and the value is real already (a handle that cannot be forgotten).
2. **Drops.** `Drop` in the prelude, `progDrops`, the flag word, the descriptor and runtime change, the same change in both emitters, `MirEval` and the heap model, tests that compare the order of effects between `eval` and the executable, and a check under valgrind that nothing is dropped twice.
3. **`Clone` with a body of its own**, for types with a drop that can be copied.
4. **Raw pointers** (`POINTERS.md`, which has its own order: tuples, ghost values and layout in bytes come first), then lists of values with drops and linear values, then `Box` and lists written in Tersus (steps 29 and 30).

## Decisions to make

1. **The flag word, or flags as locals.** A hidden word is the simplest, and costs a word and a change to both emitters. Locals only work if types with a drop cannot be nested in a way that needs a flag, which is true while they cannot be list elements, and is a bigger change to the ownership pass.
2. **Drops at the end of the function, or at the last use.** The end of the function is predictable (a file stays open to the end of its function) and is what the pass does now. The last use closes sooner and puts the order of effects at the mercy of liveness.
3. **`eval` runs the owned MIR.** Required for the reference interpreter to run drops. It is a change in what `eval` costs and in what it is the oracle for.
4. **Linear types before drops.** The first step needs no runtime work at all and the guarantee does not depend on the second.
5. **The hole for unbounded type parameters** (above): refuse linear and affine arguments until bounds exist, or check the instances native code is made of. It was a choice to take type parameters as Clone for the explicit-copies change; it is the first thing this plan has to revisit.
6. **Whether a `for` loop and a `match` may keep reading a value that has a drop.** They are views now, and native code may copy a view that is disturbed; for a value with a drop that copy must be an error, which needs `MirMoves` to know what native code will do.
