# Tersus Data Model (design)

Status: proposal, nothing here is implemented. It replaces README items 4 (property objects) and 11 (type layer), and is the route to item 9 (the doubly linked list).

## Goals

The data model has four parts:

1. **Primitives**: `Int`, `Bool`.
2. **Lists**: `List T`, today's integer lists generalized to any element type.
3. **Structs**: nominal records whose field names are fixed at compile time.
4. **Algebraic data types**: sums of constructors, each with named fields, taken apart by `match`.

Three constraints from the rest of the language shape every choice below:

- **Values are immutable.** Data is referred to by iotas, and `push`/`set` already return new lists. There is no aliasing, so the validator never reasons about a heap.
- **Validation is a bounded search that is sound but incomplete** (see LANGUAGE.md, How Validation Works). New data forms must reduce to the existing congruence closure plus difference constraints plus `forall` instantiation, not to new decision procedures.
- **Partial operations carry contracts.** `get` needs an in-range index and `/` needs a non-zero divisor, each shown by the caller. Reading a field of a constructor the value might not have follows the same pattern.

## Syntax

Types and constructors start with an uppercase letter, and variables and functions with a lowercase one. That keeps `Node { ... }` unambiguous against `if i < n { ... }`.

```tersus
struct Node { value: Int, prev: Int, next: Int };

data Shape = Circle { radius: Int }
           | Rect { width: Int, height: Int }
           | Empty;

data Tree = Leaf | Branch { left: Tree, value: Int, right: Tree };
```

- `struct T { f: A, g: B }` is sugar for `data T = T { f: A, g: B }`: a data type with one constructor, named like the type. There is one mechanism underneath.
- A constructor's fields are all named, and they are listed in declaration order. There are no positional fields.
- Recursive types are allowed (`Tree`). Values are immutable and finite, so they cannot be cyclic.
- Declarations are top-level and are visible to the code after them, like functions. A type can mention itself but not a later type.

### Using values

```tersus
n = Node { value = 1, prev = 0, next = 2 };   // every field, in any order
v = n.value;                                  // field read
m = n with { next = 3 };                      // new value: next replaced, the rest copied
s = Circle { radius = 4 };
e = Empty;                                    // a constructor with no fields

match s {
    Circle { radius = r }          { area = r * r * 3; }
    Rect { width = w, height = h } { area = w * h; }
    Empty                          { area = 0; }
};
```

- `x.f` is a field read. On a struct it is always allowed. On a type with several constructors it has the input contract "x is built with the constructor that has `f`", written `affirm x is Circle;` in validation statements. It is checked like the index of `get`: a `match` arm, an `if x is Circle` guard or an earlier `affirm` establishes it.
- `match` is a statement. Each arm is a constructor pattern and a block. The arm binds the listed fields to new variables that are visible in the block. Patterns are flat, and nesting is written as a second `match`. An arm for every constructor is required, which is a syntactic check.
- `e with { f = v }` requires that `e` has the constructor with field `f`, with the same contract as a field read.
- There is no field assignment `n.next = 3;` at first. Write `n = n with { next = 3 };`. Assignment sugar (`n.next = 3`, `nodes[i].next = 3`) is a later PR, and is only rewriting.
- Equality `=` works on every type and is structural. Ordering (`<`, `<=`, ...) is for `Int`.

## Types

A type checker runs between parsing and validation. Today a type error (`size(5)`) is found at evaluation, or not at all.

```
Type = Int | Bool | List Type | Name           (a declared data type)
     | Fn [Type] Type                          (function values)
```

- **Parameters** may carry annotations: `fn insertAfter(nodes: List Node, p: Int, v: Int) -> List Node [{ ... }] [{ ... }] { ... }`.
- **Inference** is plain unification, with no let-polymorphism: each function body has its own type variables, local variables take the type of their first assignment, `[]` is `List a` until a later use fixes `a`, and the builtins are typed schemes (`get : List a -> Int -> a`).
- **Unannotated parameters** are inferred from the body. If the body leaves one ambiguous, the error asks for an annotation. So existing programs need no change.
- **Contracts and proofs** are typed with the same rules, so `affirm get(nodes, i).next = j` is checked.
- **Types are erased** before validation and evaluation. They exist to resolve field names and constructors, and to reject nonsense early.

User-defined generic types are out of scope. `List` is the only parameterized type.

## Runtime values

`Value` becomes:

```haskell
data Value
    = VInt Integer
    | VBool Bool
    | VList [Value]                 -- replaces VIntList [Integer]
    | VData Name [Value]            -- constructor name and its fields, in declaration order
    | VFunct ...                    -- unchanged
```

The checker resolves field names to positions, so the evaluator never looks at names. `evalBuiltinFunct` gains no cases: `get`, `push`, `set` and `size` are already element-agnostic apart from their pattern matches on `VIntList`.

## Validation encoding

The point of the design is that this needs few new engine concepts, because compile-time field names make every data fact first-order.

**Terms.** A constructor `C` is a constant, and `C(a1, ..., an)` is an application term. For each field there is a selector `sel_C_i`, also a constant. Proof terms never contain `CTerm (VData ...)`: values are normalized to constructor applications, exactly as `canonicalValue` already normalizes builtins. `lightProof` and `constKey` need one more case each.

**Closure rules.** Four facts, all expressible in the existing closure:

1. *Selection*: `sel_C_i(C(a1..an)) = ai`. This is the same kind of step as `evaluateClosure`, which evaluates a builtin when its arguments' classes contain constants. Here it fires when the argument's class contains an application of `C`.
2. *Injectivity* needs no rule: from selection and congruence, `C(a) = C(b)` gives `ai = sel_i(C(a)) = sel_i(C(b)) = bi`.
3. *Distinctness*: a class that contains applications of two different constructors is a contradiction. It sets the same "inconsistent, so everything is entailed" flag that a negative cycle sets in `consistent` today. This also makes an impossible `match` arm validate vacuously.
4. *Eta for structs*: for a value `x` of a struct type, `x = C(sel_1(x), ..., sel_n(x))`. The validator adds this fact when a struct-typed iota is created (a parameter, a call result, a `get`), so no engine rule is needed. It is what lets `n with { f = n.f }` equal `n`.

**Updates are constructor applications.** `u = n with { next = 3 }` records `u = C(sel_1(n), 3, sel_3(n))`. Selection then gives every frame fact (`u.value = n.value`, `u.prev = n.prev`) for free. Compare `set`, whose frame is a `forall` over unboundedly many indexes. A struct's frame is finite and known statically.

**Testers.** `x is C` is the proof term `is_C(x)`. It holds when `x`'s class contains an application of `C` (rule 3 makes it exclusive).

**`match`.** The validator treats it like `if`. Each arm is validated from the state with `x = C_i(f1, ..., fn)` assumed, for fresh iotas `f1..fn` bound to the pattern's variables. The arms are then joined by keeping the facts all of them establish, with returns handled as in `valReturningIf`. No new join logic is needed. Exhaustiveness is checked syntactically against the declared constructors.

**Lists of data.** A list element is just a term. `set` and `push` keep their `forall` frame contracts, and whole-element equality `get(r, j) = get(l, j)` becomes field equality by congruence on the selectors. An element update is `set(nodes, i, get(nodes, i) with { next = 3 })`.

**`forall` triggers.** Instantiation is currently keyed on `get(L, j)` with `j` itself as the index. The motivating invariant fits this:

```tersus
affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).next).prev = i;
```

The body contains `get(nodes, i)`, so it is instantiated at every `i := t` for which `get(nodes, t)` is in the context. The instance contains the new term `get(nodes, get(nodes, t).next)`, which supplies a fresh index for the next saturation round. The cap of 5 rounds is therefore the limit on how many links a proof can chain through without the user naming the intermediate term with `define`. Whether that is enough in practice is to be measured on the linked-list example, and generalized triggers (patterns such as `get(L, f(j))`) are the fallback if it is not.

**Arithmetic.** Int-typed fields are ordinary terms. `sel_next(get(nodes, i)) < size(nodes)` takes part in the difference constraints like any other class.

**Errors.** `Pretty.hs` prints constructors as `Node { value = 1, ... }` or `C(a, b)`, selectors as `x.f`, and testers as `x is C`.

## The motivating example

A doubly linked list stored in an array, with indexes as links. No references are needed, and the heap is a value:

```tersus
struct Node { value: Int, prev: Int, next: Int };

// Every link is in range and agrees with its neighbour: a ring that includes index 0.
fn insertAfter(nodes: List Node, p: Int, v: Int) -> List Node
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
    out = push(nodes, Node { value = v, prev = p, next = q });
    out = set(out, p, get(out, p) with { next = n });
    out = set(out, q, get(out, q) with { prev = n });
    return out;
};
```

This is the program where the "supply the rest" workflow is expected to matter. When `p = q` (a one-node ring) the two `set`s hit the same element, and the validator has to be told about the case with `if p = q { ... }`. Having to write that case is the design working as intended: the heuristics prove the general case and the program names the awkward one.

## Phases

Each phase is one PR with examples, rejected examples, tests and docs, as before.

1. **Type layer.** `Type`, a checker for the existing language (`Int`, `Bool`, `List Int`, functions), parameter and return annotations, and unification for unannotated code. No new data. All existing programs and tests must pass unchanged. Type errors move from evaluation to checking.
2. **Generalized lists.** `VIntList [Integer]` becomes `VList [Value]` and `List T` typing replaces `IntList`. Lists of `Bool` and lists of lists fall out, and `ProofEngine.ConstKey` needs a case for lists of constants.
3. **Structs.** `struct`, construction, `.f`, `with`, eta, and selector/constructor normalization in the closure. First examples: points, a `Node` used on its own, a function that updates one field and a rejected example that breaks the frame.
4. **Algebraic data types.** `data`, `match`, testers (`is`), partial field access contracts, and distinctness. First examples: `Option`-like and `Shape`, a recursive `Tree` with a recursive function over it, and non-exhaustive and wrong-constructor rejections.
5. **Lists of data and the linked list.** Lists of structs, `forall` over them, round-count measurements, generalized triggers if needed, and `examples/linked_list.tersus` with its rejected variants.
6. **Sugar** (optional): `l[i]` for `get`, `x.f = v`, `nodes[i].f = v`, and `forall x in l`.

Phases 1 to 3 are independent of 4 and could be reordered with it. Phase 5 needs all of them.

## Open questions

Defaults are my recommendation.

1. **Annotations required or inferred?** Default: parameters optional where inference can resolve them, return type inferred, annotation required when the checker cannot decide.
2. **`struct` as sugar for one-constructor `data`, or a separate form?** Default: sugar (one mechanism, one validator encoding).
3. **`match` as a statement or an expression?** Default: statement, matching how `if` works today. An expression form would need blocks that yield values.
4. **Recursive types.** Default: allowed. They fall out of the design, and with recursive functions they give tree and list recursion. They are also the natural measure for termination checking later (a field of a value is smaller than the value).
5. **Case rule.** Default: types and constructors uppercase, variables and functions lowercase. This breaks any existing program with an uppercase variable, so I'd check the examples and tests first. All current ones are lowercase.
6. **Generic user types.** Default: not now. `List` is built in, and `Option<T>` or `Pair<A, B>` is a later extension if wanted.
7. **Partial field access.** Default: a contract the caller establishes (`x is C`), consistent with `get` and `/`. The alternative is to force a `match`, which is simpler but verbose for the common single-use case.

## What stays out of scope

- Mutation, references and aliasing. Everything is a value, and arena-style indexes replace pointers.
- Termination checking, though recursive types prepare the ground for it.
- Subtyping, interfaces and traits.
- Strings, floats and generics.
