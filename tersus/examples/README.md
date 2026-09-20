# Tersus Examples

Runnable programs showing what the language and standard library can do today. Each file carries `//` comments explaining what it shows; this page gives the overview.

`stack test` loads every file in this directory (`testExamples` in `test/TestTersus.hs`), so the results below are checked.

Run one yourself from the `tersus/` directory:

```
stack run -- run examples/safe_access.tersus     # validates, evaluates, prints 38
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
| `loops.tersus` | A `while` loop with an invariant, using trusted axioms for the arithmetic | returns `30` |
| `early_return.tersus` | Guard clauses: `return` inside an `if` ends the function, and the rest is validated under the guard | returns `104` |

### The safe-access pattern

`first` and `last` require a non-empty list. A function can carry that requirement in its input contract:

```tersus
// spread only accepts non-empty lists, which makes first and last safe inside it.
// The input contract is assumed in the body and checked at every call.
fn spread(lst) [{
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
| `rejected/missing_return.tersus` | A function whose `if` returns in one case and reaches the end without a return value in the other |
| `rejected/invariant_entry.tersus` | A loop whose invariant does not hold before the first iteration |
| `rejected/invariant_preserved.tersus` | A loop body that increments `i` without re-establishing the invariant |
| `rejected/loop_stale_fact.tersus` | `affirm i = 0` after a loop that changes `i`: earlier facts about `i` are not carried out of the loop |
| `rejected/return_in_loop.tersus` | `return` inside a `while` body, which is not supported yet |

## Writing your own

- All infix operators share one precedence level and associate left, so write `affirm y = (x + 1)`. Without the parentheses this parses as `(y = x) + 1`.
- Validation only knows what a rewrite or contract has told it. It does not do arithmetic on its own, for example it cannot conclude `s > 0` from `s = 3` without `rewrite eqToGtZero s`.
- User functions cannot call other user functions yet, because function bodies only see their arguments and the standard library.
- A variable first assigned inside an `if` branch is local to that branch, so declare it before the `if` (`r = fallback;`) if you want it afterwards.
- Loop invariants about counters need arithmetic facts, and the validator has none of its own, so `loops.tersus` supplies them with trusted `axiom` rules.
- There are no lists you can index or update yet, so the parallel-iteration and linked-list motivating cases in the main README are still not expressible here.
