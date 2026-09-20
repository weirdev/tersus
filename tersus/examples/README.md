# Tersus Examples

Runnable programs showing what the language and standard library can do today. The parser has no comment syntax, so the explanations live here instead of in the `.tersus` files.

`stack test` loads every file in this directory (`testExamples` in `test/TestTersus.hs`), so the results below are checked. The CLI in `app/Main.hs` only parses a single line, so there is no `stack run` entry point for these files yet.

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

### The safe-access pattern

`first` and `last` require a non-empty list. A function can carry that requirement in its input contract:

```tersus
fn spread(lst) [{
    define s = size(lst);
    rewrite eqToGtZero s;
    affirm s > 0;
}] [{
    affirm s > 0;
}] {
    return last(lst) - first(lst);
};

return spread([4, 8, 15, 16, 23, 42]);
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

## Writing your own

- All infix operators share one precedence level and associate left, so write `affirm y = (x + 1)`. Without the parentheses this parses as `(y = x) + 1`.
- Validation only knows what a rewrite or contract has told it. It does not do arithmetic on its own, for example it cannot conclude `s > 0` from `s = 3` without `rewrite eqToGtZero s`.
- User functions cannot call other user functions yet, because function bodies only see their arguments and the standard library.
- There is no control flow yet, so the parallel-iteration and linked-list motivating cases in the main README are not expressible here.
