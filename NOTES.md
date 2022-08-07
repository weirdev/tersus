Array (collection) element proofs
    Initally we will not retain proof information per array element. (ie. we will know only size)
    Next, we can add proofs applying generally to all elements of the array.
    Per array element info isnt workable for large arrays, and thus for consistency we shouldnt use it for smaller arrays
    However, we could add tuples and allow per element proofs for them.
    Maps probably make sense being treated more like the array case rather than the tuple case

Define a target proof that we want to acheive in order to validate method, rather than manually transforming / checking in each prove method

Cannot "weaken" both sides of a proof
    - Give each object two sets of proofs? stronger and weaker?