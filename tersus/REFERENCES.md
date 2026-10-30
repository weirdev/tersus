# References and borrowing (design plan)

> Draft, not implemented. This extends today's parameter-only `&T` lending.
> It complements `POINTERS.md`, `DROPS.md` and `ALLOCATORS.md`; it does not
> change the current language. The syntax below is proposed for review, not supported
> by the parser.

## Recommendation

Use **scoped access capabilities** as the core: shared read access or exclusive
update access to a place, with compiler-inferred validity intervals. Keep ordinary
values immutable in the proof model. An update produces a new logical value,
even when native code changes the same storage. Add explicit, checked mechanisms
for shared mutable structures rather than weakening ordinary references.

This retains Rust's useful default, shared reads or an exclusive writer, without
requiring Rust's lifetime syntax, reference operators, trait names or pinning API.
The important extension for Tersus is that borrowing must protect proofs as well
as memory. Validate the proposed syntax against representative programs and their
diagnostics in a small model before implementing it.

## Safety contract

For code without trusted assumptions, including calls through safe library APIs:

- Every read accesses live, initialized, correctly typed, aligned, in-bounds
  storage. No dangling reference, invalid discriminant or use after move.
- Every update has authority over the affected storage. Overlapping accesses
  cannot invalidate a reference or violate its read/update permissions.
- Ownership is not duplicated; cleanup cannot double-free. Replacement handles
  the old value and its destructor correctly. Ordinary ownership is affine;
  mandatory resource discharge is the stronger, separate linear feature.
- Concurrent conflicting non-atomic accesses are impossible. This includes
  aliases hidden inside containers, closures and user abstractions.
- Facts about a previous value cannot be used as facts about updated storage.
  Library invariants hold whenever a caller can observe the value.
- Compiler transformations, library lowering and native alias annotations
  preserve these properties.

This is a goal of at least safe Rust's memory and data-race guarantees, not a
claim of full equivalence before a model and implementation exist. Rust does
not generally prevent leaks, deadlocks, logical races or arbitrary incorrect
contracts. Tersus's proof checks and linear obligations can provide more.
`assume`, axioms and foreign contracts remain explicit trust boundaries; a
reference API must not introduce a hidden escape from them.

## Starting point and alpha migration

`LANGUAGE.md` documents `&T` only on parameters, read-only views, explicit clones
and value semantics. `MirMoves` follows projected places; `MirOwnership` can
copy a disturbed read-only view to preserve its old value. `MirValidate` reasons
about immutable iotas, not a mutable heap. These are foundations, not already a
general borrow checker.

Tersus is in alpha: compatibility is not a design constraint. Replace today's
parameter-only lending with the uniform `&T`/`&mut T` syntax below and migrate
callers, libraries, examples and tests. Do not retain a second spelling merely for compatibility.
Value expressions and references should still have clearly different meanings:
a reference cannot silently become a snapshot clone to resolve a conflict.
Revisit implicit value views and disturbed-view copying on their own merits;
retaining them is not a prerequisite for this design.

## Proposed syntax

Use `&T` for shared references and `&mut T` for exclusive references, with
explicit borrowing at call sites. Keep `*` for dereferencing: it is compact, composes with field access and does not reserve
a field name such as `value`. All snippets in this section are proposed syntax,
including indexed places, result origins and contract extensions.

| Form | Meaning |
|---|---|
| `&T` | Shared read reference to a `T` |
| `&mut T` | Exclusive update reference to a `T` |
| `&place` | Borrow a place for reading |
| `&mut place` | Borrow a place for updating |
| `*r` | The place accessed through reference `r` |
| `&T from input` | Result borrows from the named input |
| `&T from (a, b)` | Result may borrow from either input; both constrain validity |
| `writes(x.field)` | Upper bound on the storage a function may update |
| `old(expression)` | Entry-state logical snapshot, usable only in contracts/proofs |

`&` and `&mut` introduce references in type and expression positions; `mut`
is a keyword. They bind to a type or place; parentheses resolve composition.
A place is a local, `*reference`, a field place, or an indexed place supported by
its container. `(*r).field` and `(*r)[i]` require explicit dereferencing; no implicit
reference dereference or borrow is part of this proposal. An arbitrary function
result is not a place. First bind it to a local if it needs borrowing.
Indexing requires a bounds proof and a container access contract; it is not a
new way to bypass `get`'s safety checks or encapsulated invariants.

### Parameters, locals and updates

```tersus
fn count(xs: &List<Int>) -> Int {
    return size(*xs);
};

fn increment(n: &mut Int) -> Int
    writes(n)
    [{ affirm *n < 9223372036854775807; }]
    [{ affirm *n = old(*n) + 1; affirm return = *n; }]
{
    *n = *n + 1;
    return *n;
};

n = 4;
r: &Int = &n;
a = *r;                         // Int is Copy; a is an independent value
increment(&mut n);             // allowed: r has no later use
// affirm *r = 5;                // adding this would make the call conflict
```

The postcondition uses Tersus's existing `return` result name. The input condition
prevents signed integer overflow. Calls below assume the same bound has been
established for each incremented field. The existing `[{ ... }]` pre/post blocks
stay; `writes(...)` is a proposed signature clause
before them. `writes(n)` names the referent reached through parameter `n`, not
the local binding containing the reference. Footprints may name fields and
indexed ranges using the same place grammar. In the first implementation,
support whole referents and fields; defer range notation until range access lands.

Without `writes`, every update parameter grants a whole-referent write footprint;
read parameters grant none. An explicit footprint narrows that default. Footprints
include nested calls and forbid writes outside the declared places. Future
shared-mutation effects need additional contracts; `writes` alone does not make
shared mutation valid. A footprint describes possible writes, not a postcondition
that they occurred, and does not reduce the exclusive loan of a whole-root
`&mut` argument. Borrow a field instead when the caller needs disjoint access.

`*r = value` replaces the referent and disposes of its previous value according
to normal drop rules. Evaluate the new value before replacement. Reading a
non-Copy referent is an observation, not an implicit move or clone; a consuming
context requires `clone(&*r)` or a replacement operation. Propose
`replace(&mut place, value)` to return the old owned value while installing
the new one, leaving the place initialized. It consumes neither the owner nor
an enclosing update capability.

### Reborrowing and disjoint access

```tersus
r = &mut point;
x = &mut (*r).x;
y = &mut (*r).y;               // disjoint fields
increment(&mut *x);            // temporary update reborrow
increment(&mut *y);
// r can be used again after the final uses of x and y
s = &*r;                     // read reborrow; freezes overlapping updates
observe(&*s);                // observe takes &Point
```

Deriving a child loan through a parent is permitted for a disjoint place even
while another child is live. The parent cannot otherwise access the borrowed
portion. `&mut *r` reborrows rather than moves `r`; passing `r` directly to an
update parameter transfers that reference value. A read reference can be copied;
an update reference cannot implement Copy or Clone. Reassigning the reference
binding changes its target, whereas assigning through `*r` changes its referent.
Ordinary access ends at the last dependent use, including uses stored elsewhere;
no explicit end-loan statement is needed initially.

### Returning and storing references

```tersus
fn first<T>(xs: &List<T>) -> &T from xs
    [{ affirm size(*xs) > 0; }]
    [{ }]
{
    return &(*xs)[0];
};

fn choose(flag: Bool, a: &Int, b: &Int)
    -> &Int from (a, b)
{
    if flag { return a; } else { return b; };
};

struct Window<T> { first: &T, last: &T };

fn ends<T>(xs: &List<T>) -> Window<T> from xs
    [{ affirm size(*xs) > 0; }]
    [{ }]
{
    return Window {
        first: &(*xs)[0],
        last: &(*xs)[size(*xs) - 1]
    };
};
```

`from` names parameter bindings, not allocator regions or numeric addresses.
It bounds all references nested in the result, including a reference's referent;
`Window<T> from xs` conservatively gives all its reference fields the same bound.
Local aggregate origins are inferred from their field values. Different field
origins can initially use a conservative union; a per-field public notation is
future work. A caller cannot return or store a result beyond any bound it carries.
Returning a shortened update reborrow follows the same rule using `&mut T`.
A source annotation never grants stronger access than the source supplies.

When exactly one reference parameter exists, omission of `from` infers that
source for a result containing references. With multiple reference parameters,
require `from` explicitly, even if the body happens to select only one. With no
reference input, borrowing a local cannot produce an escaping reference.
Function types carry the same relationships, using named parameters, for example
`fn(xs: &List<Int>) -> &Int from xs`. Implementations of a trait function
must satisfy its declared origin and footprint bounds.

This avoids lifetime variables for these cases, but is intentionally conservative.
It does not yet express independent field lifetimes, higher-rank callbacks,
static references or all nested-reference coercions. Reject unsupported cases;
add notation only with an accompanying sound rule.

### Why this spelling

`&` and `&mut` are compact, familiar and extend today's `&T` spelling uniformly.
`mut` grants exclusive access with permission to update; mutation is not required.
The explicit expressions make borrowing visible at the call and distinguish a
reference from an owned argument. They replace implicit parameter lending.
`from` states the input/result relationship without introducing a named lifetime
for common cases. Method receiver borrowing follows the same explicit rule
initially. These spellings do not commit Tersus to Rust's other design choices.

## Core rules

Describe a reference internally by its target place, permission and validity
interval. A place includes an owning root and field, element, range or dereference
projections. Allocation identity must survive address reuse; a numeric address
alone is not a target identity.

| Access | May coexist on overlapping storage | Owner while access is live |
|---|---|---|
| Read | Other reads | May read, cannot update, move, replace or drop target |
| Update | No independent read or update | Cannot access overlapping storage except through the capability |

Reference bindings and permission to modify the referent are separate concepts.
Reassigning a binding does not grant update permission.

Read capabilities may be duplicated within their validity interval. Update
capabilities cannot be duplicated; they may move or be temporarily reborrowed.
A reborrow suspends the conflicting parent permission until all child uses end.
Deriving read access from update access freezes updates for that interval.
Distinct fields may be updated separately. Unknown indexes overlap by default;
proved unequal indexes or a checked range-splitting operation can establish
disjointness. User assertions alone cannot mint permissions.

Use control-flow-sensitive last-use analysis, including uses through returned
references and aggregates. At joins, conservatively retain possible outstanding
loans; loops require a fixed point. Moving an inline owner invalidates its address
and is forbidden while borrowed. A heap owner may eventually move without
moving its allocation, but start with the conservative restriction.

Borrowing an element prevents container operations that can relocate, remove or
invalidate it. Disjoint element writes may be allowed; growing the container
requires whole-container authority. Taking a non-Copy value through a reference
needs a checked replacement or an explicit empty-slot protocol, not an ordinary
read. Cleanup runs only after dependent loans end, on every exit path.

## Function boundaries and escaping references

Published signatures must say which inputs a result may borrow from and which
places may change. Infer local intervals; infer a result origin only when
unambiguous. Multiple possible sources require an explicit relationship, not
guessing from the body at each call. A result can depend on several inputs.
Intervals express outlives constraints; they need not be written as Rust lifetimes.

Start with nonescaping parameter access, then locals and returned references,
then reference fields and closure captures. A returned reference cannot depend
on a temporary or callee-local owner. An aggregate containing references carries
their constraints through moves and drops. Generic substitution, function values
and trait implementations preserve access, result-origin and effect contracts.
Do not implicitly make an update capability covariant in its stored type;
initially use invariant reference types and add coercions only with a sound rule.
Support call-scoped callback borrowing before more general higher-rank contracts.

Allocator provenance and borrow validity are different constraints. A reference
cannot outlive its allocation region. `ALLOCATORS.md`'s region erasure for reads
must be revisited for escaping references and updates: an update cannot install
arena-owned data in a longer-lived owner. A clone still chooses a destination
allocator; a borrow does not extend an allocation's life.

## Mutation in the proof model

An update capability carries the current logical version of its target. Updating
a field builds a fresh enclosing value, with frame facts for unaffected fields.
At capability return, the caller's owning root receives that version. The old
iota still denotes the old value, never the current contents of its storage.

For example, if a caller proves `size(xs) = 3` and an update call appends an
element, the old fact remains about `xs_before`. A post-call assertion about
`xs` uses `xs_after`, whose size comes from the append contract. It must not
inherit size 3. Facts about a disjoint owner survive unchanged.

Contracts for update parameters relate entry and exit snapshots and state their
write footprint. Callee validation uses those same contracts. With no stronger
postcondition, forget knowledge of the written portion and retain only type and
restored invariant facts. Two disjoint field updates reconstruct one root version;
do not independently overwrite each other's changes. Loop invariants refer to
the current versions and must be re-established after updates.

Snapshots are logical values, not an implicit deep copy or an owning handle.
Ghost snapshots cannot keep storage alive, mint an owner, or become executable
references. Define which operations may observe them before exposing snapshots.
Invariant-bearing abstractions control field access: temporary invariant breaks
are permitted only inside exclusive encapsulated operations that restore them
before callbacks, reentrant access or return can expose the value.

## Alternatives and shared mutation

### Owning references: possible later extension

Rust's open [owning-reference RFC #4000](https://github.com/rust-lang/rfcs/pull/4000)
proposes `&own T`: ownership of a value in storage whose allocation remains
controlled elsewhere. The value need not relocate when ownership transfers.
This differs from `&mut T`, which must leave a valid value for the lender.
An owning reference can consume its pointee without replacement and drops any
remaining owned value when dropped; it does not deallocate the backing storage.
Applications include consuming unsized values and avoiding large by-value moves.
Earlier proposals also used `&move`; this is not an alternative name for `&mut`.

For Tersus, retain `&T` and `&mut T` as the initial reference forms. Leave room
in the permission model for value ownership separate from allocation ownership,
initialization state, and address stability. An eventual owning-reference operation
would transfer the local's or slot's cleanup obligation and mark the original
place moved out once its loan ends. It must not make that place readable merely
because the reference's last use has passed. Partial consumption needs per-place
initialization and cleanup tracking; container invariants must account for holes.

This is closely related to `Block`'s filled/empty slots and `take`, but `take`
returns an ordinary owned value, whereas an owning reference can leave the value
in its original slot while transferring its ownership. A library representation
may suffice if checked projection and cleanup transfer are expressible; otherwise
this needs compiler support. Treat allocator lifetime constraints independently.
Ordinary affine ownership does not guarantee destruction if ownership may be
forgotten. A linear variant could strengthen that, but needs explicit discharge
and cancellation rules. Neither ordinary `&own` nor `&mut` alone promises pinning.
See also [The Algebra of Loans in Rust](https://nadrieril.github.io/blog/2025/12/21/the-algebra-of-loans-in-rust.html)
for the distinction between access during a loan and initialization after it.

### Shared ownership and mutation mechanisms

| Mechanism | Strength | Cost / decision |
|---|---|---|
| Scoped read/update capabilities | Static safety, predictable storage costs | Recommended default; rejects unresolved aliasing |
| Consume and return an updated value | Already fits Tersus proofs | Keep as the simplest option when references add no benefit |
| Copy on write / persistent values | Convenient snapshots and sharing | Useful library option; allocation and cloning are observable costs |
| GC or reference counting | Convenient shared ownership | Does not by itself solve races, invalidation or stale proofs |
| Runtime checked borrow guards | Supports aliases static analysis cannot resolve | Explicit API; conflicts fail safely; guards govern all exits |
| Arena handles with generations | Cycles and graph structures without stored references | Check liveness and bounds; generation reuse must not resurrect stale handles |
| Permission tokens / separation logic | Precise disjoint access to complex heaps | Integrate with `POINTERS.md`; avoid requiring manual tokens for ordinary fields |

Use runtime guards for single-thread shared mutation and synchronization guards
for cross-thread mutation. A read of shared mutable state yields a snapshot or
a reference tied to a guard. Its current-value facts cannot survive an arbitrary
call that can mutate that state. Atomics need explicit temporal semantics; atomic
access alone does not establish a multi-location invariant.

Unify reference permissions and `Block<T>` permissions so neither can bypass the
other. Creating a reference from a block temporarily lends the corresponding
permission; writes, take, free, resize and overlapping splits are blocked until
the loan ends. Ending the loan returns updated contents. Raw addresses confer
no reference permission. Define provenance, layout and foreign retention rules
before lowering reference operations to LLVM.

Before concurrency, define checked equivalents of transferability and safe
sharing, including recursively stored references and guards. Exclusive access
alone does not make every resource transferable between threads. Until then,
reject cross-thread transfers rather than claiming concurrent support.
Before suspension, specify frame stability, cancellation cleanup and loans across
suspension. A frame owning its referent is insufficient if moving the frame
invalidates an internal address. Reject self-referential movable values initially;
evaluate stable storage or handles before adopting a pinning concept.

## Delivery plan and acceptance gates

1. **Executable rules and syntax validation.** Model roots, projections, permissions,
   initialization, version changes and scope exit. Specify overlap and reborrow
   rules. Compare accepted and rejected examples with the safety contract above.
   Validate the proposed syntax using those examples, including ambiguous result origins.
2. **Nonescaping read references.** Generalize parameter lending and add local
   loans. Extend type checking and MIR with explicit borrow, reborrow, read and
   loan-end operations. Extend `MirMoves` or add a focused `MirBorrow` pass using
   its place analysis. Migrate parameter lending to explicit `&` arguments; decide value-view and
   clone behavior deliberately, without compatibility requirements.
3. **Nonescaping exclusive updates.** Start with whole roots and fields, scoped
   update calls, replacement, entry/exit contracts and versioned validation.
   Gate on stale-fact rejection and correct cleanup. Then add checked disjoint
   index/range splitting. General references need not wait for raw allocation.
4. **Escaping reads, then updates.** Add result-origin constraints, unsized
   metadata, aggregate fields, generic and function-value contracts. Check region
   containment. Gate each extension on negative escape tests and separate checking
   of callers and callees, without inspecting callee bodies.
5. **Library and raw-memory integration.** Unify `Block` loans; recheck list
   lowering, drops, partial moves and allocator design. Verify generated library
   MIR too: its current exemption from move checking cannot authorize references.
   Introduce explicit guarded mutation and handle libraries when needed.
6. **Concurrency and suspension.** Add transfer/share rules, synchronization
   contracts and frame/cancellation rules before enabling these uses.

Every stage updates `TersusTypes`, elaboration, MIR serialization/verification,
the interpreter, ownership lowering and both LLVM emitters as needed. Recheck
loans after transformations that introduce aliases, moves or storage changes;
make pass boundaries explicit in `Pipeline`. Never emit LLVM `noalias` or other
alias promises stronger than the established semantics. Update `LANGUAGE.md`
only when syntax is implemented; keep this document as the design rationale.

Required tests include: duplicate reads; conflicting update/read and update/update;
nested reborrows; disjoint fields; unknown and proved-disjoint indexes; container
relocation; owner move/drop; temporary and local escape; branch-dependent origins;
loop-carried loans; replacement and destructor paths; unsized metadata; region
escape; mutation invalidating old facts; disjoint facts surviving; and raw-block
free/resize while lent. Include permitted programs as well as refusals.
Run matching `TestBorrow`, `TestCopies`, `TestOwnership`, proof and native groups,
then the full suite and emitter bootstrap checks for implementation changes.
Compare interpreter and native behavior and use the heap model for lifetime
errors. Later add generated small MIR programs checked against the permission
model; tests support but do not replace a preservation/progress argument for the
core rules and a review of the trusted primitives.

Open decisions include whether the proposed notation remains readable at scale,
how much footprint inference to expose, finer origin relationships for aggregate
fields, and which shared-mutation library to build first. The safety contract,
explicit distinction from value views and versioned proof semantics constrain
those choices.
