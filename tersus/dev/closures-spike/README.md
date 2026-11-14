# Closures Phase 0 spike (do not merge)

Hand-written form of what the closures plan's desugaring emits, on master a33c2fa.
Run each with `tersus-exe check|eval|run <file>`.

Passing (check + eval + native agree): s1_map (1233), s1_loop (1233, timing
baseline), s2_counter (1202), s3_once (2), s4_borrow (122), s5_invariant (13).
Failing, both are Phase 1 prerequisites (see the Phase 0 report in the plan):
s6_generic_capture (a bound whose trait arguments mention a sibling type
parameter) and s7_contract (a bound call to a trait method that has contracts
and trait type parameters). s2 uses `self: &Self` mutating through an `&mut`
field; a `self: &mut Self` receiver is not accepted in a trait today.
