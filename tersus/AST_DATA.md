# AST as data

`AstData` and `examples/ast_reader.tersus` exchange syntax without running the
proof engine. This is a development-stage bridge for the frontend and MIR
lowering ports in `REPLACING_HASKELL.md`, not a new CLI command or production
frontend. Parsing, elaboration and validation are unchanged.

## APIs

Haskell (`src/AstData.hs`):

```haskell
writeParsed     :: [Statement] -> Result String String
readParsed      :: String -> Result [Statement] String
writeElaborated :: Elaborated -> Result String String
readElaborated  :: String -> Result Elaborated String
```

`writeParsed` writes the supplied syntax, including `Mark`s when the parser
kept locations. It also handles the resolved syntax inside `Elaborated`, but
use `writeElaborated` to retain its expression-occurrence types. That API
preserves **both** `[Statement]` and the complete ordered `[Type]` of
`TypeCheck.Elaborated`. The types remain in the lowering's visit order; the
bridge neither infers them again nor claims to validate an elaborated program.
A parsed reader refuses an elaborated header, and vice versa.

Tersus (`examples/ast_reader.tersus`, one file, no include/module dependency):

- `readAst() -> Parsed<AstProgram>` reads standard input. Only `ok: true` gives
  a usable program.
- `printAst(p: &AstProgram) -> Int` writes the program and returns its byte count.
- `AstProgram` carries its stage, `List<AstNode>` arena and root ID.
  `AstNode` is a discriminated union of typed syntax payloads: `AstValue`,
  `AstBody`, `AstExpression`, `AstStatement`, `AstTermination`, `AstValidation`,
  `AstProof`, `AstRule`, `AstSignature`, `AstTraitFn`, `AstBound`, `AstArg`,
  fields/variants, options and typed list links. Reference fields are integer
  IDs whose required kinds are checked before the program is returned.
- With no argument, the executable reads and writes. `mutate` changes every
  primitive `Plus` node to `Minus` before writing, to demonstrate an AST edit,
  not token forwarding. It does not repair contracts or occurrence types;
  edits must be checked by the appropriate later compiler stage. `count` writes
  the unmodified AST and returns the writer's byte count, for testing the
  `printAst` API (the runtime prints that count after the data).
- Malformed input or an unknown argument reports an error and returns `1`,
  like the MIR reader (the native runtime prints the returned value).

The syntax includes complete native and builtin function values: parameter
names, signatures, contracts, exported proofs, bodies and termination clauses.
Builtin values are **not** reconstructed from the standard library: that would
lose metadata, because `Eq Value` deliberately ignores a builtin's metadata.
`Ctor` arguments are structural `ArgSize`/`ArgType` nodes, and `Field` preserves
its optional owner. Primitive names come from `BuiltinRegistry`; parameterized
builtins (`Ctor`, `Field`, `Is`, `Project`, `Cast`, `ToWord`, `Rel`) have their
own payloads. All fixed-width converters are covered.

No `Iota`, solver, term table, rule environment or proof-engine execution state
is serialized. Syntactic axioms and proofs are `AxiomDef` and `ProofDef`, not
an execution `RuleContext`.

## Version 1

The first record is exactly one of:

```
tersus-ast 1 parsed
tersus-ast 1 elaborated
```

Each subsequent line is one node. Its zero-based ID is its position after the
header. The final line is `root ID`; no other record or blank line may follow.
A final newline is optional. Empty records are refused.

A reference must point to an earlier node of the required kind. Every node
except the root must be referenced **exactly once**, and the root must be the
last node. Thus the arena is a tree, not an arbitrary graph: dangling, forward,
cyclic, reused, wrong-kind and unreachable references are errors. This avoids
exponential expansion when Haskell reconstructs recursive syntax.

Lists are typed links, not variable-length node records. For example,
`StatementsEnd` has no fields; `StatementsCons HEAD TAIL` references a
`Statement` and another `Statements` node. Other list kinds are `Names`,
`Values`, `Expressions`, `Validations`, `Proofs`, `Fields`, `Variants`,
`ValueFields`, `Types`, `Args`, `TraitFns` and `Bounds`.

Names and decimal literal text are also linked: `NameEnd`, and
`NamePart "TEXT" TAIL`. Haskell splits names into at most 512 Unicode scalar
values per part. Strings use the MIR escaping: printable ASCII bytes except
`"` and `\` appear literally, and all other UTF-8 bytes are uppercase `\xHH`.
Malformed escapes, missing separators and invalid UTF-8 are refused. No name
is normalized. `VInt NAME` contains decimal text, so a constructed Haskell
syntax value outside the runtime's signed-64-bit range is also lossless.
The source parser still rejects out-of-range integer literals before producing
an AST; this bridge does not change that behavior.

Example: the syntax `[Return (Val (VInt 7))]` is:

```
tersus-ast 1 parsed
StatementsEnd
NameEnd
NamePart "7" 1
VInt 2
Val 3
Return 4
StatementsCons 5 0
root 6
```

An elaborated root is `Elaborated STATEMENTS TYPES`, where `TYPES` references
the complete occurrence-type list. All other syntax node tags are their
Haskell constructor names, with fields in constructor order. `FieldBuiltin`
is the builtin `Field`; `Field` is the `(name, Type)` field declaration.
`Bound`, `Variant`, `ValueField` and `Signature` follow their Haskell tuple or
constructor order. Options are `NoName`/`SomeName NAME` and
`NoTermination`/`SomeTermination TERMINATION`. Booleans are `true`/`false`;
relations are `Eq`, `NotEq`, `Lt`, `Gt`, `LtEq`, `GtEq`.

`Type TYPE` and `Size SIZE` use the exact MIR recursive codecs and Tersus
`Type`/`Size` enums, including the MIR `TNamed`'s preserved argument tokens.
The builtin's `Arg` is structural even when its type contains such a named
type. `DataCodec` shares Haskell quoting, token parsing and type/size output
with `MirData`; the AST reader adds strict numeric, count and UTF-8 checks.
The copied Tersus codec is identity-tested against `mir_reader.tersus` and
its type definitions against `emit.tersus`.

Unquoted numeric payloads and MIR type/size numbers are signed 64-bit decimal;
counts must be nonnegative and fit the record. Records are bounded by the
MIR reader's 1,000,000-byte limit. The type codec remains recursive within
one record; syntax/proof/list depth does not grow a record or require a
recursive Tersus walk. The checked Haskell writers return `Error` for
out-of-range type/size numbers, unsupported fixed-width types or a type
record exceeding the limit; they never wrap, truncate or emit unreadable
data. Those cases are not supported by the exact MIR representation;
integer **value** literals have no such numeric limit.

## The parser written in Tersus

`examples/parser.tersus` is a hand-written parser over bytes (in the manner of
`examples/mir_reader.tersus`) for the whole language. It builds the arena of
this document directly and writes `tersus-ast 1 parsed` for it, byte for byte
as `AstData.writeParsed` writes the Haskell parse of the same program,
including every desugaring (a `match` becomes an `if` chain of `Is` and
`Project`, a `for` becomes a `while`, struct literals become `Ctor`
applications, a standard `Eq` or `Clone` impl is written out, and so on). The
arena is built in parse order and renumbered at the end into the emission
order above; nodes a failed speculation built are unreachable and dropped.

The host (`src/TersusParser.hs`) runs it as `MirHousekeeping` runs the checker
and the eraser written in Tersus: a native executable built with clang from
the seed and cached by the hash of the parser source, or the program
interpreted by the MIR executor where it cannot be built. The tool is always
compiled by the Haskell parser (the bootstrap path), never by itself. Its
input is exactly:

```
tersus-parse 1
<locating> <nsegments>
<byte count>
<that many raw bytes>
... (per segment)
```

The segments are the library texts the pipeline puts in front of the program,
then the program itself; `locating` is `1`, and only the last segment is read
with statement places kept (a `Mark` before each statement, as
`Parse.locating` does). On success the AST data is on the standard output and
the return is `0`. On failure the return is `1` and the standard error has one
line, `line L:C: <what was expected>`.

`Pipeline.parseSource` feeds every program to this parser. The Haskell parser
stays as the oracle for one release: `TERSUS_PARSER=haskell` selects it, and
any failure of the tool falls back to it with a note on the standard error.
`Compile.parseSource` is unchanged. Error parity is checked for verdicts, and
for the one fixture the parser itself rejects the message names the same
reason; other messages are the Tersus parser's own. `testParser` checks
byte-for-byte parity over the corpus of `testAstData` plus generated snippets
for every desugaring, and that the writer the parser shares with
`examples/ast_reader.tersus` is identical text in both.

## Tests

`testAstData` checks constructor fixtures, all registry builtins and metadata,
ordered elaborated types, UTF-8/chunking, deep expression syntax, malformed
records and every source in `examples/`, `examples/rejected/` and `lib/`, plus
generated sources. Rejected programs still have syntax and are round-tripped;
elaboration is round-tripped wherever it succeeds, without validation. The
one fixture rejected by the parser itself, `rejected/for_assigns_counter.tersus`,
is counted separately with its exact expected parser error; it has no AST.
Unexpected parser failures fail the corpus test.

`testParser` checks the parser written in Tersus against the Haskell parser
over the same corpus plus generated snippets, as described under "The parser
written in Tersus" above.

`testAstReader` checks small interpreted round trips and the `Plus` to `Minus`
mutation (`7 + 2` becomes `7 - 2`, evaluated as `5` by Haskell), then native
round trips over that whole corpus, the reader's own source, constructor
fixtures and large/deep fixtures. Native refusal checks share the Haskell
malformed-input corpus. `testExamples` also checks the new example with no
input.

The native tests use the validated host-tool bootstrap route already used by
`MirHousekeeping`: the reader goes through `compileOnce` (including production
AST/proof validation), and `Pipeline.nativeProgram` supplies the canonical
container library validated by `validateContainerLibrary` and erased by
`MirHousekeeping`. The owned MIR is compiled by the pinned `Seed.cachedSeed`
executable. The cache key is the actual owned MIR and seed hash. Every
validation, erasure and code-generation result on this route must succeed;
failures still fail the test. There is no separate AST-reader container
validation policy. The reader itself also passes the production `check` command.

```
stack test --test-arguments='-j 2 testAstData testAstReader'
```
