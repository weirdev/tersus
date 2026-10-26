# Tersus Examples

Runnable programs showing what the language and standard library can do today. Each file carries `//` comments explaining what it shows; this page gives the overview.

`stack test` loads every file in this directory (`testExamples` in `test/TestTersus.hs`), so the results below are checked.

Run one yourself from the `tersus/` directory:

```
stack run -- run examples/safe_access.tersus     # validates, builds natively (needs clang), runs, prints 38
stack run -- eval examples/safe_access.tersus    # validates, evaluates the MIR with the interpreter, prints 38
stack run -- check examples/rules.tersus         # validates only, prints OK
stack run -- run examples/rejected/affirm.tersus # prints the validation error, exits 1
```

Each program in the top-level directory passes validation, and its concrete evaluation gives the listed result. Each program in `rejected/` is one the validator refuses.

## Accepted programs

| File | Shows | Result |
| --- | --- | --- |
| `basics.tersus` | Integer lists, `size`/`first`/`last`, arithmetic, and a nested block that updates an outer variable | returns `6` |
| `functions.tersus` | `fn` definitions, multiple arguments, and a function that calls `first`/`last` under an input contract | returns `21` |
| `booleans.tersus` | `true`/`false` literals and relations such as `x < 6` producing booleans | returns `true` |
| `proofs.tersus` | `affirm`, `define`, and the `eval`, `eqToGtZero`, and `eqToLtPlus1` rewrites | validates |
| `rewrites.tersus` | The primitive `refl` and `evalAll` rewrites | validates |
| `safe_access.tersus` | A function that only accepts non-empty lists, so `first` and `last` are provably safe | returns `38` |
| `contracts.tersus` | Output contracts, and a proof variable (`s`) exported from a callee to its caller | returns `8` |
| `rules.tersus` | User-defined `axiom` and `proof` rewrite rules | validates |
| `branching.tersus` | `if`/`else if`/`else`, and a guard that makes `first` safe for a list only known at runtime | returns `106` |
| `arithmetic.tersus` | `*`, `/` (rounding down, with a non-zero divisor contract), operator precedence and negative literals | returns `6` |
| `helper_functions.tersus` | Functions calling the functions defined before them, with each call checked against the callee's contract | returns `11` |
| `recursion.tersus` | A function calling itself, validated assuming its own output contract, including recursion over a list; each says what shrinks | returns `26` |
| `termination.tersus` | How code says it ends: `shrinks` on loops and recursive functions (an integer counting down, or a tree losing a field), and `~` for code that is not shown to end, including a call in unreachable code | returns `23` |
| `generic_lists.tersus` | Lists of `Bool` and of lists, built by a `for` loop over the elements, and a contract about a pushed row | returns `[[1, 2], [3, 4], [1, 2]]` |
| `structs.tersus` | A `struct`, literals, field reads, `..base` updates with a contract proving the other fields are unchanged, and updating one element of a list of structs | returns `11` |
| `enums.tersus` | An `enum` with variants, `match` as an expression, a contract that demands a variant, and a recursive tree that holds its subtrees in a `Box` | returns `27` |
| `arrays.tersus` | `Array<T, N>`, `N` elements held inline with the size in the type: `array(5, 0)` and `#[7, 8, 9]`, `get`/`set` as for lists, `set` in a loop that stores into the array, a function that takes two arrays and returns one (`dot`, `squares`), and a grid of arrays inside an array | returns `42` |
| `borrowing.tersus` | A parameter written `&T`, which a function only reads: a call lends it and the caller keeps it; an array lent and a new one given back; a lent parameter given on to another and, as a copy, to one that is owned | returns `138` |
| `array_owners.tersus` | An array of structs that own lists: `array(n, x)` puts a copy in each slot, `get` gives a copy, `set` frees the element it replaces, and a copy of the array shares nothing | returns `207` |
| `generic_structs.tersus` | `struct Pair<T>`, `struct Holder<T>` (a `Box` of an array of the type, with a contract) and `struct Vec<T, n>`: a struct for each type and size, written `Pair<Int>`; a function with type parameters over any of them; one native struct for each | returns `2224` |
| `spec_functions.tersus` | A contract that calls functions of the program (`width(r)`, `offset(r, return)`: checked against the input contract of the function and known by its promise), and `struct Range` with an `invariant` that is proved where a Range is made and assumed for every Range a function is given | returns `25070` |
| `upper.tersus` | Input: `readByte()` (the next byte of the standard input, or `-1` at its end) and `String::read(limit)` / `String::readLine(limit)` (a String of up to `limit` bytes; a line without its new line); it writes its input in capitals, with a loop that proves `size(text)` stays the same | returns `0` with no input |
| `vec.tersus` | A growable list written in Tersus, as a library type of a program's own: `trait Sequence<E>` (`size`, `get`, `set`) and `trait Growable<E>` (`push`), with contracts that call `size(self)` (the traits are in the prelude), `struct Vec<T>` with an invariant (`0 <= len <= size(data)`), `impl<T> Sequence<T> for Vec<T>` and `impl<T> Growable<T> for Vec<T>` (`push` doubles the array when full), and `new` and `pop` in an `impl<T> Vec<T>`, and `fn total<S: Sequence<Int>>`, one function for a Vec, a List and an Array; used as `v.push(x)` and `size(v)`, with loops that say `size(v) = i` | returns `2491212381` |
| `list_methods.tersus` | The functions of a list as methods (`l.push(x)`, `l.pop()`, `l.size()`, `a.set(1, 20)` on an array), `pop` and its contract, and a loop that builds a list and says `size(squares) = i` | returns `508221` |
| `type_parameters.tersus` | `fn head<T>(items: &List<T>) -> T`: a function for any type, which the arguments decide; a type in a result, a `Box` and an array; two types; a type with a size; one native copy for each type | returns `2045` |
| `array_sizes.tersus` | `fn dot<n>(a: Array<Int, n>, b: Array<Int, n>)`: a function over arrays of any size, with the size a value in the body and the contracts, a size in the result (`ones`), two sizes (`cells<rows, columns>`), and a function that passes on its own size; one copy is compiled for each size it is called with | returns `42` |
| `sized_structs.tersus` | `struct Packet<n>`: a struct for each size, written `Packet<3>`; a field that uses the size or holds another struct of it; a function with sizes over any of them; a struct update with `..base` | returns `71` |
| `box_array.tersus` | `Box<Array<Int>>`: an array on the heap whose size the Box carries, made by `Array::boxed(n, x)` with a run-time `n`; a `Box<Array<Int, 4>>` given where any size is wanted; `size`, `get` and `set` looking through the Box | returns `34` |
| `array_data.tersus` | An array as a field of a struct, as the fields of the variants of an enum (each as wide as its fields) and as the elements of a list; a function that builds a struct around a new array | returns `45` |
| `strings.tersus` | String literals (the library struct `String` of UTF-8 bytes, `lib/string.tersus`): `size` counts bytes (`"caf\u{e9}"` is 5), `concat` and `push`, `get` on a pushed `Byte` proved, a string equal to another, and `total`, a function over any `Sequence<Int>`, taking one | returns `980` |
| `traits.tersus` | A `trait` with contracts, `impl`s for an enum and a struct, `Self`, and the three ways to call a function of a type (`Shape::unit()`, `s.sides()` and `Measure::sides(s)`); an impl that asks for less and promises more than its trait | returns `55` |
| `bytes.tersus` | The type `Byte` (a whole number from 0 to 255 that is a type of its own): `toByte(x)` (x has to be proved to be in range, here with a clamp function) and `toInt(b)`, a struct of Bytes (`Pixel`), a list of Bytes, and a function whose result is bounded (0 to 765) because every Byte is known to be from 0 to 255 | returns `275020` |
| `hello.tersus` | Output: `writeByte(b)` (the `Byte` `b` written to the standard output, and `b` as its value; a number written out is a `Byte` where one is wanted), `print()` on a String (writes its bytes and gives how many), and a call that is made for what it does as a statement of its own; what is written comes first and the returned value after it | writes `Hello, café!`, `ok`, and returns `14` |
| `linked_list.tersus` | A doubly linked list stored in an array of structs: inserting a node keeps every link a valid index and keeps `prev` and `next` in agreement, and following links is memory safe | returns `9` |
| `types.tersus` | Parameter and return types, a `Bool`-returning function, and a list built element by element | returns `6` |
| `linear.tersus` | Sums of variables, multiples and division by a constant as linear arithmetic: contracts like `a + b <= 10` and `2 * x <= y`, a loop with an inferred `s + i = n`, `bits` that halves (`shrinks n`, `n / 2`), and a binary search over a range whose `if` states neither the invariant nor the variant | returns `633` |
| `packet_parser.tersus` | A showcase: a parser for `[version, length, payload, checksum]` buffers that takes any input and is proved never to read out of range, with a `checksum` proved to be from 0 to 255 (`% 256`), a `slice` of exactly the requested size, an `encode` whose size and length field are proved, and an enum for the four outcomes | returns `711` |
| `for_loops.tersus` | `for i in lo..hi` and `for x in list` / `for i, x in list`: a sum over a list, an early `return`, a list built to a given size, and nested ranges, with no invariant or termination clause | returns `33` |
| `loops.tersus` | A `while` loop with an invariant, with the counter arithmetic proved by the validator | returns `30` |
| `loop_return.tersus` | `return` inside a `while` body: a bounded search whose invariant must still hold on the paths that keep looping | returns `7` |
| `parallel_sum.tersus` | Parallel iteration: `get` on two lists in one index loop that `push`es each pair's sum, with the equal input sizes, the result's size and each element (the sum of its pair, a `forall`) stated in the function's contract and the loop invariant | returns `[11, 22, 33]` |
| `build_list.tersus` | Building a list with `push` in a `for` loop, with the result's size (worked out for the loop) and each element (twice the input's) stated in an output contract | returns `[2, 4, 6]` |
| `update_list.tersus` | Updating a list: `set` replaces an element of a copy in a loop, with the size worked out by the validator, the bumped and untouched elements carried by the invariant (two `forall`s) and stated in the output contract | returns `[101, 102, 103]` |
| `frame_facts.tersus` | What `push` and `set` leave alone: every other element is unchanged | returns `149` |
| `forall_facts.tersus` | `forall` facts: assumed by an axiom, required by an input contract, passed on by an output contract, and proved directly | returns `5` |
| `element_facts.tersus` | What `set` and `push` say about elements: the element just written, repeated in a function's output contract and used by its caller | returns `106` |
| `early_return.tersus` | Guard clauses: `return` inside an `if` ends the function, and the rest is validated under the guard | returns `104` |

### The safe-access pattern

`first` and `last` require a non-empty list. A function can carry that requirement in its input contract:

```tersus
// spread only accepts non-empty lists, which makes first and last safe inside it.
// The input contract is assumed in the body and checked at every call.
fn spread(lst: List<Int>) -> Int [{
    define s = size(lst);
    rewrite eqToGtZero s;
    affirm s > 0;
}] [{
    affirm s > 0;
}] {
    return last(lst) - first(lst);
};

a = spread([4, 8, 15, 16, 23, 42]);
b = spread([7]);
return a + b;
```

The contract is assumed while validating the body, which is what makes `first(lst)` and `last(lst)` legal. It is checked at every call site, so a call that cannot show `size(lst) > 0` never passes validation. That is what `rejected/unmet_contract.tersus` demonstrates.

## Rejected programs

Each of these parses, but fails validation (a few also fail concrete evaluation). The expected error text is asserted in `testExamples`.

| File | Why it is rejected |
| --- | --- |
| `rejected/affirm.tersus` | `affirm x < 4` when `x = 5`: the assertion is not entailed |
| `rejected/first_of_empty.tersus` | `first([])`: the builtin's contract needs `size > 0` |
| `rejected/unmet_contract.tersus` | Calling `spread([])`: the call site cannot satisfy the input contract |
| `rejected/missing_contract.tersus` | A function calls `first(lst)` without any contract, so nothing proves `lst` is non-empty |
| `rejected/output_contract.tersus` | The output contract says `return = i` but the body returns `i + 1` |
| `rejected/bad_proof_rule.tersus` | A `proof` rule whose body does not establish its declared output |
| `rejected/axiom_input.tersus` | `rewrite eqToGtZero x` when `x = 0`: the axiom's input contract fails |
| `rejected/unknown_rule.tersus` | `rewrite madeUpRule x` with no such rule defined |
| `rejected/unguarded_access.tersus` | The `if` guard says `size(lst) > 1`, which does not show the `size(lst) > 0` that `first` needs |
| `rejected/branch_fact.tersus` | `affirm n < 6` after an `if n < 6`: the condition only holds inside its branch |
| `rejected/guard_condition.tersus` | A guard that returns when `size(lst) > 0`, so the code after it only knows `size(lst) <= 0` and `first` is not provably safe |
| `rejected/loop_return_invariant.tersus` | A loop that returns in one case but increments `i` without re-establishing the invariant in the other |
| `rejected/loop_missing_return.tersus` | A function whose loop can end without reaching its `return`, with nothing returning after the loop |
| `rejected/missing_return.tersus` | A function whose `if` returns in one case and reaches the end without a return value in the other |
| `rejected/get_out_of_range.tersus` | `get(a, 3)` on a three-element list: `3 < size(a)` does not hold |
| `rejected/get_unproven_index.tersus` | A function calls `get(lst, i)` without any contract on `i`, so nothing proves it is in range |
| `rejected/parallel_length.tersus` | A `dot` function indexes `b` with a counter bounded by `size(a)`, and no contract says the sizes match |
| `rejected/call_violates_contract.tersus` | A function calls another without establishing its input contract |
| `rejected/recursion_wrong_contract.tersus` | A recursive function whose base case breaks its output contract |
| `rejected/recursion_input.tersus` | A recursive call that does not meet the function's own input contract |
| `rejected/list_element_mismatch.tersus` | A `List<Bool>` is pushed an `Int` |
| `rejected/enum_contract_unmet.tersus` | A function that needs a `Circle` is called with a `Rect` |
| `rejected/enum_wrong_variant.tersus` | `affirm s is Shape::Rect` for a `Circle` |
| `rejected/linked_list_link_out_of_range.tersus` | An insertion gives the new node a link one past its own index |
| `rejected/linked_list_link_disagrees.tersus` | An insertion that forgets to point the old next node back at the new node, so `prev` and `next` disagree |
| `rejected/linked_list_unchecked_walk.tersus` | A walk over a list whose links nothing says are valid |
| `rejected/struct_update_frame.tersus` | A contract claims a field that an update did not set equals another field |
| `rejected/struct_field_type.tersus` | A struct literal gives a `Bool` for an `Int` field |
| `rejected/body_not_exported.tersus` | A function that returns its argument without saying so in a contract: its caller cannot use that |
| `rejected/trait_input_stronger.tersus` | An impl asks for `by > 5` where its trait allows any `by > 0`: code written against the trait could call it with a step it refuses |
| `rejected/trait_output_weaker.tersus` | An impl of `Measure` returns a product of two unknowns, and the trait promises a result that is not negative |
| `rejected/trait_ambiguous_call.tersus` | Two traits give a type a function of one name, and `c.label()` does not say which |
| `rejected/trait_missing_function.tersus` | An impl lacks one of the functions of its trait |
| `rejected/array_size_mismatch.tersus` | `dot` takes an `Array<Int, 5>` and is given an `Array<Int, 4>`: the size is part of the type |
| `rejected/array_runtime_size.tersus` | `array(n, 0)` with an `n` that is a variable: the size of an inline array is a constant |
| `rejected/array_unsized.tersus` | A parameter of type `Array<Int>`: with the size left out (it is `?`) the array can only be used behind a `Box` |
| `rejected/sized_struct_mismatch.tersus` | A `Packet<2>` given where a `Packet<3>` is wanted: each size is a type of its own |
| `rejected/array_size_param_mismatch.tersus` | `dot<n>` given arrays of 2 and 3 elements: the first decides `n`, and the second has to agree |
| `rejected/box_array_size.tersus` | A `Box<Array<Int>>` made by `Array::boxed` given where a `Box<Array<Int, 3>>` is wanted: the unsizing conversion only goes from a size to no size |
| `rejected/array_push.tersus` | An array has no `push`: its size never changes |
| `rejected/type_return_mismatch.tersus` | A function declared to return an `Int` returns a list |
| `rejected/type_argument_mismatch.tersus` | `size` is applied to an `Int` |
| `rejected/call_before_definition.tersus` | A function calls one defined after it |
| `rejected/division_by_zero.tersus` | A function divides by an argument that nothing shows is non-zero |
| `rejected/push_size.tersus` | An output contract claims `push` leaves the size unchanged |
| `rejected/forall_wrong_element.tersus` | An output contract claims each element is one more than the sum the loop builds |
| `rejected/forall_invariant_gap.tersus` | A loop invariant that does not say the elements from `i` on are untouched, so it is not preserved |
| `rejected/forall_unproven.tersus` | An input contract needs `forall j in 0..size(l)`, but only `0..2` is known |
| `rejected/frame_changed_index.tersus` | Claims `set` left the element it wrote unchanged |
| `rejected/set_out_of_range.tersus` | `set(a, 3, 0)` on a three-element list: `3 < size(a)` does not hold |
| `rejected/set_size.tersus` | An output contract claims `set` makes the list one longer |
| `rejected/element_wrong.tersus` | An output contract claims `set` left the old element at the index it overwrote |
| `rejected/invariant_entry.tersus` | A loop whose invariant does not hold before the first iteration |
| `rejected/invariant_preserved.tersus` | A loop body that increments `i` without re-establishing the invariant |
| `rejected/for_reads_past_end.tersus` | A `for` range that ends one past the last index, so `get` is out of range |
| `rejected/division_not_below.tersus` | `n / 2 < n` claimed for `n >= 0`, which fails at `0` |
| `rejected/sum_bound_too_strong.tersus` | `a + b <= 10` does not give a sum below `10` |
| `rejected/loop_sum_not_kept.tersus` | A loop whose body breaks `s + i = n`, so nothing is inferred and the output contract fails |
| `rejected/packet_off_by_one.tersus` | A parser whose length check leaves out the checksum, so it reads one past the end |
| `rejected/packet_negative_length.tersus` | A parser that does not turn away a negative length, so the range to checksum can be backwards |
| `rejected/packet_checksum_range.tersus` | A checksum that claims to stay below 255, which it does not |
| `rejected/for_assigns_counter.tersus` | A `for` body that assigns its loop variable (refused when the program is read) |
| `rejected/loop_without_termination.tersus` | A loop that says neither `shrinks` nor `~` |
| `rejected/loop_variant_not_shrinking.tersus` | A loop whose variant `3 - i` is never made smaller by its body |
| `rejected/loop_variant_unbounded.tersus` | A countdown on a parameter that nothing shows is at least 0 |
| `rejected/recursion_without_variant.tersus` | A function that calls itself and does not say what shrinks |
| `rejected/recursion_variant_not_shrinking.tersus` | A recursive call that passes the same `n` |
| `rejected/box_infinite_size.tersus` | An enum with a variant that holds the enum itself, which would have no size: the recursion has to be in a `Box` |
| `rejected/recursion_shrinks_not_a_part.tersus` | A recursive call on a tree, passing the tree itself and not a field of it |
| `rejected/diverging_call.tersus` | A function calls one declared `~` and does not say so itself |
| `rejected/diverging_loop.tersus` | A function contains a `~` loop and does not say so itself |
| `rejected/loop_stale_fact.tersus` | `affirm i = 0` after a loop that changes `i`: earlier facts about `i` are not carried out of the loop |

## Writing your own

- Infix operators bind in three levels, tightest first: `*` and `/`, then `+` and `-`, then the relations, so `affirm y = x + 1` means `y = (x + 1)`. Each level associates left.
- Validation knows what rewrites and contracts have told it, plus integer comparisons and adding or subtracting a known constant, for example `s > 0` from `s = 3`. It also understands sums of variables, `x * c` and `x / c` for a known `c` (linear arithmetic, see LANGUAGE.md), and folds `*` and `/` on known values.
- A function body sees its arguments, the standard library, the functions defined before it, and itself, so functions can call earlier functions and recurse (see `helper_functions.tersus` and `recursion.tersus`).
- A variable first assigned inside an `if` branch is local to that branch, so declare it before the `if` (`r = fallback;`) if you want it afterwards.
- Lists can be read with `get`, extended with `push` and updated with `set`, which returns a new list (`a = set(a, i, x)`). `push` and `set` say which element they wrote (`element_facts.tersus`) and the frame rules say the others are unchanged (`frame_facts.tersus`), one index at a time. A `forall` states a fact about every index (`forall_facts.tersus`, `parallel_sum.tersus`), and with lists of structs it expresses the linked-list motivating case, whose link invariants are proved by `linked_list.tersus`.
- `get` and `set` need `0 <= index < size(list)` proved at the call. Concrete lists and indexes are checked directly, and a symbolic index needs a contract or loop invariant that says so (`rewrite checkRel` establishes the fact for concrete arguments at the call).
- Counters in list loops need no axioms (`parallel_sum.tersus`, `build_list.tersus`, `update_list.tersus`), and `affirm` and invariants see through equalities on their own, so a loop needs no `rewrite refl`.
