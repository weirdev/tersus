# AST as data

`AstData` and `examples/ast_reader/ast_reader.tersus` exchange syntax without running the
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

Tersus (`examples/ast_reader/ast_reader.tersus`, entry of the `ast_reader` package):

It imports `data::codec::codec` for the shared token, integer, escaping and
size/type wire codec, and `data::ast::ast` for the AST arena schema and writer.
The native parser imports those same modules. The AST reader's strict record
and UTF-8 checks remain local; MIR records and legacy eraser type output remain
in the MIR package.

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
The shared Tersus modules are checked by canonical import identity, exact wire
output, preserved named-type argument tokens, malformed-input refusals and the
existing AST/MIR/native parser parity sweeps.

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

`examples/parser/parser.tersus` is a hand-written parser over bytes (in the manner of
`examples/mir_reader.tersus`) for the whole language. It builds the arena of
this document directly and writes `tersus-ast 1 parsed` for it, byte for byte
as `AstData.writeParsed` writes the Haskell parse of the same program,
including every desugaring (a `match` becomes an `if` chain of `Is` and
`Project`, a `for` becomes a `while`, struct literals become `Ctor`
applications, a standard `Eq` or `Clone` impl is written out, and so on). The
arena is built in parse order and renumbered at the end into the emission
order above; nodes a failed speculation built are unreachable and dropped.

The host (`src/TersusParser.hs`) loads `PreludeSource.parserPackageFiles` through
the ordinary `Modules` resolver and `PackageCompile` Haskell bootstrap, then
runs a native executable. The embedded snapshot includes the package markers,
shared data modules and generated `unicode.tersus` root-module file, whose
predicates use the serving Haskell compiler's Unicode categories. No native
parser is called to build itself. The cache key covers every snapshot path and
source, the emitter and runtime; source changes in an imported module rekey it.
Its fingerprinted disk cache and cross-process lock are the existing
`Native.cachedProgram` mechanism. Unset
`TERSUS_PARSER` or `native` selects it. `interpreted` explicitly selects the MIR
interpreter; `haskell` selects the one-release oracle. Build, process and
protocol failures are errors, never fallback decisions.

Production source and module loading use the file protocol in
`src/FileParserProtocol.hs`:

```
tersus-file-parse 1
decls
... counted maps and context records ...
endDecls
source <UTF-8 byte count>
<exact source bytes, to EOF>
```

The declarations carry all ten `Parse.Decls` fields: constructors, types,
Self name/type, type parameters, generics, impl parameters, own-Clone status,
location mode and field types. Records require LF terminators; duplicate keys,
invalid counts, unsupported types and invalid UTF-8 are rejected.

A successful reply is:

```
tersus-file 1
imports <count>
... import positions, path segments, alias and selected names ...
decls
... final declarations ...
endDecls
ast
tersus-ast 1 parsed
... AST records ...
root <id>
```

The AST suffix is decoded by the unchanged `AstData.readParsed`, including
its single-use tree, stage, position and trailing-record checks. The parser
returns no value on success: stdout ends at the AST root, with no extra `0`.
A syntax refusal returns `1` and writes its diagnostic to stderr. The runtime
prints `1\n`; its process exit may still be successful. A nonzero process exit
is always a tool failure, even when stdout resembles an AST.

The small `tersus-parse 1` interface remains for raw AST tests:

```
tersus-parse 1
<locating> <nsegments>
<byte count>
<that many raw bytes>
... (per segment)
```

`Pipeline.validatedSource` and `compileSource` lower the Tersus-parsed source
AST through `Compile.lowerSourceParts`. A source-only native probe chooses
libraries; their frozen ASTs and declarations come from `Compile`'s existing
cache. The final native file parse receives those declarations. Keeping
library names, library AST and source AST separate preserves the prepared
library-prefix cache. Package loading injects the same native file parser
through `Pipeline.loadFromFilesystem`; imports are linked by the module
pipeline. Standalone compilation still rejects unlinked imports.

`Compile` and the default `Modules` loaders remain the one-way bootstrap and
oracle path. Native parsing never uses Haskell to discover user declarations.
Immutable input is indexed once; consumed state uses lightweight checkpoints
and append-only arena rollback. Flat arena-list emission is iterative.
Identifier classifiers are generated as pure Tersus comparisons from the
serving Haskell oracle's `Data.Char.isLetter`, `isUpper`, `isLower` and
`isAlphaNum` predicates, so identifier grammar and named-type rendering agree
without per-character tables or Haskell source parsing. These helpers are
linked into the parser bootstrap and parser example build, not ordinary
programs.

`testParser` enforces exact AST parity for every source under `examples/` and
`lib/`, including rejected sources, plus generated/desugaring and large-arena
cases. Only three explicit parser smoke programs run interpreted. Tool failures
fail the gate. `testModules` checks imports, final declaration state and real
module compilation; Pipeline substitution and failed-bootstrap tests cover the
production frontend boundary.

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
malformed-input corpus. `testHostValidation` (run only when named) checks the
new example with no input, which validates the reader.

The native tests use the host-tool bootstrap route already used by
`MirHousekeeping`: the reader is one of the compiler's own programs, built
through `programFromFiles` as the host builds it (linked, its ghosts erased,
not validated: `MirHousekeeping.toolProgram`; `testHostValidation` validates
it), and `Pipeline.nativeProgram` supplies the canonical container library
erased by `MirHousekeeping`. The owned MIR is compiled by the pinned
`Seed.cachedSeed` executable. The cache key is the actual owned MIR and seed
hash. Every erasure and code-generation result on this route must succeed;
failures still fail the test. The reader itself also passes the production
`check` command.

```
stack test --test-arguments='-j 2 testAstData testAstReader'
```
