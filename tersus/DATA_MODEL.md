# Tersus Data Model (design)

Status: phases 1 to 5 are implemented (see Phases below for what each left out). It replaces README items 4 (property objects) and 11 (type layer), and is the route to item 9 (the doubly linked list). The syntax follows Rust where Rust has an answer.

## Goals

The data model has four parts:

1. **Primitives**: `Int`, `Bool`.
2. **Lists**: `List<T>`, today's integer lists generalized to any element type.
3. **Structs**: nominal products with named fields, fixed at compile time.
4. **Enums**: nominal sums whose variants have named fields, taken apart by `match`.

Three constraints from the rest of the language shape every choice below:

- **Values are immutable.** Data is referred to by iotas, and `push`/`set` already return new lists. There is no aliasing, so the validator never reasons about a heap.
- **Validation is a bounded search that is sound but incomplete** (see LANGUAGE.md, How Validation Works). New data forms must reduce to the existing congruence closure plus difference constraints plus `forall` instantiation, not to new decision procedures.
- **Partial operations carry contracts.** `get` needs an in-range index and `/` needs a non-zero divisor, each shown by the caller. Reading a field a value might not have follows the same pattern.

## Decisions

| Question | Decision |
| --- | --- |
| Type annotations | Required on every parameter and on the return type. Local variables are inferred. |
| Product and sum types | `struct` and `enum`, as in Rust. A struct is checked and encoded as a one-variant enum, so there is one mechanism underneath. |
| `match` | Both a statement and an expression. |
| Recursive types | Allowed. See Recursive types and compilation. |
| Naming | PascalCase types and variants, camelCase variables, functions and fields. A convention, not a compiler rule. |
| User generics | Deferred. `List<T>` is the only parameterized type. |
| Field access that may not apply | A contract the caller proves (`x is Variant`), like `get` and `/`. |

## Syntax

```tersus
struct Node { value: Int, prev: Int, next: Int };

enum Shape {
    Circle { radius: Int },
    Rect { width: Int, height: Int },
    Empty,
};

enum Tree {
    Leaf,
    Branch { left: Tree, value: Int, right: Tree },
};
```

- A declaration is a statement and ends with `;`, like `fn`. Fields and variants are comma separated, and a trailing comma is allowed.
- A variant either has no fields (`Empty`) or has named fields (`Circle { radius: Int }`). There are no positional fields.
- Declarations are top-level and visible to the code after them. A type may mention itself but not a later type.
- Types are written `Int`, `Bool`, `List<Node>`, a declared name, and `fn(Int, Int) -> Int` for a function value.

### Using values

```tersus
n = Node { value: 1, prev: 0, next: 2 };       // every field, in any order
v = n.value;                                   // field read
m = Node { next: 3, ..n };                     // a new Node: next replaced, the rest copied from n

s = Shape::Circle { radius: 4 };               // variants are namespaced by their enum
e = Shape::Empty;

if s is Shape::Circle { r = s.radius; };       // `is` tests the variant

area = match s {                               // expression form: arms are expressions
    Shape::Circle { radius: r } => r * r * 3,
    Shape::Rect { width: w, height: h } => w * h,
    Shape::Empty => 0,
};

match s {                                      // statement form: arms are blocks
    Shape::Circle { radius: r } => { total = total + r; },
    Shape::Rect { width: w, height: h } => { total = total + w; },
    Shape::Empty => { },
};
```

- **Struct literal:** `T { f: v, ... }` gives every field. `T { f: v, ..base }` is Rust's update syntax: it names the fields that change and copies the others from `base`. An `enum` variant works the same way (`Shape::Rect { width: 3, ..s }`). Using `..base` requires that `base` is that variant (see field access).
- **Telling a literal from a block:** `Name {` followed by `field :` or `}` is a literal, and a block starts with a statement, which never has `Ident :`. So `if i < n { x = 1; }` is unambiguous without relying on case.
- **Field access:** `x.f` on a struct is always allowed. On an enum value it has the input contract "`x` is a variant that has `f`", checked like the index of `get`. A `match` arm, an `if x is V` branch or an earlier `affirm x is V;` establishes it. `x is V` is a Bool expression and also a proof, so it appears in `affirm`, contracts and `if`.
- **`match`:** an arm is a variant pattern, `=>`, and an expression (in an expression `match`) or a block (in a statement `match`). Patterns are flat; nested data is taken apart with a second `match`. Every variant must have an arm, which is checked syntactically against the declaration. A pattern names each field it wants (`radius: r` binds `r`) and may leave fields out.
- **Equality:** `=` works on every type and is structural. Ordering (`<`, `<=`, ...) is for `Int`.
- **No field assignment at first.** Write `n = Node { next: 3, ..n };`. Sugar (`n.next = 3`, `nodes[i].next = 3`) is a later phase and is only rewriting.

## Types

A type checker runs between parsing and validation. Today a type error (`size(5)`) is found at evaluation, or not at all.

```
Type = Int | Bool | List<Type> | Name | fn(Type, ...) -> Type
```

- **Functions** annotate every parameter and the return type, which come before the contracts: `fn insertAfter(nodes: List<Node>, p: Int, v: Int) -> List<Node> [{ ... }] [{ ... }] { ... }`. A function value is typed by its signature, which also gives a recursive function its type before its body is checked.
- **Locals** need no annotation. A variable takes the type of its first assignment, and reassignment must agree. `[]` has type `List<a>` for a type variable resolved by its first use, and unification is local to a function body.
- **Builtins** have typed signatures (`get : fn(List<a>, Int) -> a`, written once in the checker, not by users).
- **Contracts and proofs** are typed by the same rules, so `affirm get(nodes, i).next < size(nodes)` is checked.
- **Types are erased** after checking. Validation and evaluation never look at them. They exist to resolve field names and variants, and to reject nonsense early.

Because annotations are required, adding them is part of phase 1: every example and test program is updated mechanically (`fn f(l)` becomes `fn f(l: List<Int>) -> Int`).

## Runtime values

`Value` becomes:

```haskell
data Value
    = VInt Integer
    | VBool Bool
    | VList [Value]                 -- replaces VIntList [Integer]
    | VData Name [Value]            -- variant name (Shape::Circle, Node) and its fields, in declaration order
    | VFunct ...                    -- unchanged
```

The checker resolves field names to positions, so the evaluator never looks at names. `evalBuiltinFunct` needs no new cases: `get`, `push`, `set` and `size` are already element-agnostic apart from their matches on `VIntList`.

## Validation encoding

The point of the design is that it needs few new engine concepts, because compile-time field names make every data fact first-order.

**Terms.** A variant `V` is a constant and `V(a1, ..., an)` is an application term. For each field there is a selector `sel_V_i`, also a constant. Proof terms never contain `CTerm (VData ...)`: values are normalized to variant applications, exactly as `canonicalValue` already normalizes builtins. `lightProof` and `constKey` need one more case each.

**Closure rules.** Four facts, all expressible in the existing closure:

1. *Selection*: `sel_V_i(V(a1..an)) = ai`. This is the same kind of step as `evaluateClosure`, which evaluates a builtin when its arguments' classes contain constants. Here it fires when the argument's class contains an application of `V`.
2. *Injectivity* needs no rule: from selection and congruence, `V(a) = V(b)` gives `ai = sel_i(V(a)) = sel_i(V(b)) = bi`.
3. *Distinctness*: a class that contains applications of two different variants is a contradiction. It sets the same "inconsistent, so everything is entailed" flag that a negative cycle sets in `consistent` today. This also makes an impossible `match` arm validate vacuously.
4. *Eta for structs*: for a value `x` of a struct type, `x = S(sel_1(x), ..., sel_n(x))`. The validator adds this fact when a struct-typed iota is created (a parameter, a call result, a `get`), so no engine rule is needed. It is what lets `Node { value: n.value, ..n }` equal `n`.

**Updates are variant applications.** `u = Node { next: 3, ..n }` records `u = Node(sel_1(n), sel_2(n), 3)`. Selection then gives every frame fact (`u.value = n.value`, `u.prev = n.prev`) for free. Compare `set`, whose frame is a `forall` over unboundedly many indexes. A struct's frame is finite and known statically.

**Testers.** `x is V` is the proof term `is_V(x)`. It holds when `x`'s class contains an application of `V`, and rule 3 makes variants exclusive.

**`match` and `if x is V`.** The validator treats `match` like `if`. Each arm is validated from the state with `x = V_i(f1, ..., fn)` assumed for fresh iotas `f1..fn` bound to the pattern's variables, and the arms are joined by keeping the facts all of them establish, with returns handled as in `valReturningIf`. No new join logic is needed. An expression `match` is validated as a statement `match` that assigns the result in each arm, so only facts every arm establishes about the result survive (such as `result >= 0`), not `result = w * h`. As with `if` today, a program that needs the per-arm fact states it inside the arm. Exhaustiveness is checked syntactically against the declaration.

**Lists of data.** A list element is just a term. `set` and `push` keep their `forall` frame contracts, and whole-element equality `get(r, j) = get(l, j)` becomes field equality by congruence on the selectors. An element update is `set(nodes, i, Node { next: 3, ..get(nodes, i) })`.

**`forall` triggers.** Instantiation is currently keyed on `get(L, j)` with `j` itself as the index. The motivating invariant fits this:

```tersus
affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).next).prev = i;
```

The body contains `get(nodes, i)`, so it is instantiated at every `i := t` for which `get(nodes, t)` is in the context. The instance contains the new term `get(nodes, get(nodes, t).next)`, which supplies a fresh index for the next saturation round. The cap of 5 rounds is therefore the limit on how many links a proof can chain through without the user naming the intermediate term with `define`. Whether that is enough in practice is to be measured on the linked-list example, and generalized triggers (patterns such as `get(L, f(j))`) are the fallback if it is not.

**Arithmetic.** Int-typed fields are ordinary terms. `get(nodes, i).next < size(nodes)` takes part in the difference constraints like any other class.

**Errors.** `Pretty.hs` prints `Node { value: 1, .. }`, `Shape::Circle { radius: r }`, selectors as `x.f` and testers as `x is V`.

## The motivating example

A doubly linked list stored in an array, with indexes as links. No references are needed, and the heap is a value:

```tersus
struct Node { value: Int, prev: Int, next: Int };

// Every link is in range and agrees with its neighbour: a ring that includes index 0.
fn insertAfter(nodes: List<Node>, p: Int, v: Int) -> List<Node>
    [{
        affirm size(nodes) > 0;
        affirm p >= 0; affirm p < size(nodes);
        affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).next).prev = i;
        affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).prev).next = i;
    }]
    [{
        affirm size(return) = size(nodes) + 1;
        affirm forall i in 0..size(return): get(return, get(return, i).next).prev = i;
        affirm forall i in 0..size(return): get(return, get(return, i).prev).next = i;
    }]
{
    q = get(nodes, p).next;
    n = size(nodes);
    out = push(nodes, Node { value: v, prev: p, next: q });
    out = set(out, p, Node { next: n, ..get(out, p) });
    out = set(out, q, Node { prev: n, ..get(out, q) });
    return out;
};
```

This is the program where the "supply the rest" workflow is expected to matter. When `p = q` (a one-node ring) the two `set`s hit the same element, and the validator has to be told about the case with `if p = q { ... }`. Having to write that case is the design working as intended: the heuristics prove the general case and the program names the awkward one.

## Recursive types and compilation

Recursive types (`Tree`) are allowed. Values are immutable and finite, so they cannot be cyclic, and the interpreter and validator treat a value as a mathematical term whose size does not matter. With recursive functions they give tree and list recursion, and a field of a value is a natural well-founded measure for termination checking later.

If Tersus is later compiled instead of interpreted, a recursive type will need pointer indirection (a boxed field), because a value's size must be known at compile time. Nothing in this design depends on that, but it constrains what the language promises:

- the source language keeps recursion implicit (`left: Tree`, not `left: Box<Tree>`), and the compiler inserts the indirection, or a later syntax can require it, with no change to the semantics, validation or proofs;
- no feature may observe identity or address, so boxing stays invisible. The language is value-only for that reason, and a `with`-style update never mutates;
- types are erased after checking, so a later layout pass can compute sizes from the declarations without touching validation.

## Phases

Each phase is one PR with examples, rejected examples, tests and docs, as before.

1. **Type layer** (done, `TypeCheck.hs`). `Type`, the checker for the existing language (`Int`, `Bool`, `List<Int>`, functions), required parameter and return annotations, local inference, and the mechanical migration of every example and test program. No new data. Type errors move from evaluation to checking.
2. **Generalized lists** (done). `VIntList [Integer]` becomes `VList [Value]` and `List<T>` typing replaces integer lists. Lists of `Bool` and lists of lists fall out, and `ProofEngine.ConstKey` needs a case for lists of constants.
3. **Structs** (done: `Ctor`/`Field` builtins, the parser keeps declared structs, the closure reads fields of constructions and merges equal constructions; eta is still to do, since it needs the type of a value). `struct`, literals, `.f`, `..base`, eta, and variant/selector normalization in the closure. First examples: points, a `Node` used on its own, a function that updates one field, and a rejected example that breaks the frame.
4. **Enums** (done; `match` rewrites to `if` chains of `Is` tests, and fields of an enum value are read after a cast, `(x as V).f`: a `Cast V` builtin whose contract demands `x is V` and which evaluates to its argument, so the validator checks the cast and execution does not (a wrong cast is undefined behaviour). `..base` of a variant copies fields from `base as V`. Execution never depends on proofs; the engine reads a class's constructors for `Is`, and different constructors or values in one class contradict). `enum`, namespaced variants, `match` (both forms), `is`, partial field access contracts, and distinctness. First examples: an `Option`-like enum and `Shape`, a recursive `Tree` with a recursive function over it, and non-exhaustive and wrong-variant rejections.
5. **Lists of data and the linked list** (done for memory safety: `examples/linked_list.tersus` proves that a push and two sets keep every link in range, with the case splits driven by the guards that block a forall; the agreement of `prev` and `next` needs about six nested splits and is not proved; the checked field read is not done). Lists of structs, `forall` over them, round-count measurements, generalized triggers if needed, and `examples/linked_list.tersus` with its rejected variants.
6. **Sugar** (optional): `l[i]` for `get`, `x.f = v`, `nodes[i].f = v`, and `forall x in l`.

Phases 1 to 3 are independent of 4 and could be reordered with it. Phase 5 needs all of them.

## Details settled by the syntax choice

- `::` is a new token. `Shape::Circle` is a single name to the checker and the validator.
- `..base` shares its token with the `forall` range `lo..hi`. They never appear in the same position, since a range is between two expressions and `..base` follows a field list.
- `=>` is a new token and is read only inside a `match`, so it does not clash with the relations (`=`, `>=`). The relation lexer reads `=>` as two operators, so the `match` parser reads the arm separator before the expression parser sees it.
- A declaration's trailing `;` is required, as for `fn`.

## What stays out of scope

- Mutation, references and aliasing. Everything is a value, and arena-style indexes replace pointers.
- Termination checking, though recursive types prepare the ground for it.
- Subtyping, interfaces and traits.
- Strings, floats and user-defined generics.
