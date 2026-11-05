# AST as data

`AstData` and `examples/ast_reader/ast_reader.tersus` exchange syntax without
running the proof engine. The parsed format is the production parser boundary.
The elaborated format remains a bridge for the MIR lowering port in
`REPLACING_HASKELL.md`; elaboration remains in Haskell, while
`ValidatorNative` runs the validator written in Tersus.

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
`Syntax.Elaborated`. The types remain in the lowering's visit order; the
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
is normalized. The reader consumes its growing string when joining decimal
chunks, preserving their byte order without cloning each accumulated prefix.
`VInt NAME` contains decimal text, so a constructed Haskell
syntax value outside the runtime's signed-64-bit range is also lossless.
The source parser still rejects out-of-range integer literals before producing
an AST; this bridge does not change that behavior. Size arguments also have to
fit the signed-64-bit AST/MIR representation, so the native parser refuses an
oversized size before checking. The retired Haskell grammar could construct
that unsupported AST and leave the rejection to the checker.

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
as `AstData.writeParsed` writes the decoded syntax,
including every desugaring (a `match` becomes an `if` chain of `Is` and
`Project`, a `for` becomes a `while`, struct literals become `Ctor`
applications, a standard `Eq` or `Clone` impl is written out, and so on).
Generated Eq/Clone text consumes owned field and variant accumulators; the
shared `catStrings` helper still borrows both arguments.
The arena is built in parse order and renumbered at the end into the emission
order above; nodes a failed speculation built are unreachable and dropped.

The host (`src/TersusParser.hs`) runs the current packaged parser as a native
executable (P1). `ParserSeed` first verifies `bootstrap/parser.sha256` and builds
its pinned LLVM seed with clang (P0). P0 parses `LibParsed`'s compiler libraries
and the current parser/MIR packages through the ordinary `Modules` resolver
and `PackageCompile` checker/lowering. The embedded snapshot includes package
markers, shared data modules and generated `unicode.tersus`, whose predicates
use the serving GHC's Unicode categories. The emitter seed builds current E1,
which emits P1. `Native.cachedProgram` supplies the existing caches and build
locks; imported source, parser pin, compiler and runtime changes rekey them.

`TERSUS_PARSER` unset or `native` selects P1. `interpreted` explicitly runs the
current parser's linked, type-checked bootstrap MIR, but still requires verified
native P0 to read that parser's source. `haskell` is refused; `Parse.hs` and its grammar are gone.
Build, process and protocol failures never select another parser. Building the
Haskell package still requires neither clang nor network access; the first
language parse now requires clang and verified P0. Native P1 also requires the
emitter seed.

Runtime entry points preflight verified seeds before forcing immutable library
or tool compilation values. Transient IO failures are not cached as tools;
a missing native executable is rebuilt through the existing cache lock.
The pure cached library/program values are read after successful IO bootstrap,
not used as a mutable-configuration or retry interface.

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

The declarations carry all ten `ParsedFile.Decls` fields: constructors, types,
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

The native parser also accepts `tersus-import-prefix 1` and
`tersus-declaration-names 1` in place of the file request header. Both use
exactly the same declaration envelope, UTF-8 byte count and EOF checks;
the host supplies `emptyDecls`. Import-prefix mode reads only the leading
imports and does not parse the body. Declaration-name mode reads top-level declaration headers, skipping balanced braces,
quoted strings and line comments without requiring body types or grammar.

Import-prefix replies contain `tersus-imports 1`, followed by the counted
`imports` section above. Declaration-name replies contain `tersus-names 1`,
`names <count>`, then one `name <quoted name>` record per name. Enum names
include the owner and its source-spelled `Owner::Variant` names, in order.
Both replies end after the last LF-terminated record; extra records are
rejected. These modes do not change file or AST replies.

The native test fragment interface uses the same declaration/source records
and file reply, with a different header and one kind record:

```
tersus-fragment-parse 1
fragment expression
... the same decls and counted source ...
```

`statement` is the other kind. The parser calls its existing expression or
single-statement entry point and then requires EOF. It does not route a
fragment through a statement block or add source text. An expression is carried
in one `Return` AST node for the test helper to unwrap; error and nested AST
positions still refer to the original source. Trailing semicolons or multiple
fragments are refused, while trailing whitespace and comments remain valid.


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
libraries; their frozen ASTs and declarations come from the shared lazy P0 cache in
`SourceParse`. The final native file parse receives those declarations. Keeping
library names, library AST and source AST separate preserves the prepared
library-prefix cache. Package loading injects the same native file parser
through `Pipeline.loadFromFilesystem`; imports are linked by the module
pipeline. Standalone compilation still rejects unlinked imports.

`Compile` and the default `Modules` loaders use P0 only for bootstrap work.
Production source and package loading use P1. `ParsedFile` holds only the file,
import and declaration records; `AstData` depends on `Syntax`, not the checker.
This keeps P0 below the compiler and prevents bootstrap calls from entering a
P1 build already in progress.

Immutable input is indexed once; consumed state uses lightweight checkpoints
and append-only arena rollback. Flat arena-list emission is iterative.
`ParserUnicodeSource` generates pure Tersus comparisons from the serving GHC's
`Data.Char.isLetter`, `isUpper`, `isLower` and `isAlphaNum` predicates. P1 includes
those current classifiers in `PreludeSource.parserPackageFiles` and its fingerprint.
P0 retains the classifier version recorded in its authenticated LLVM asset.
The ASCII identifiers of the bootstrap corpus let P0 read a newer generated
classifier without requiring the two Unicode versions to agree. New bootstrap
identifiers must be accepted by P0 before they can be used. No names or source
bytes are normalized.

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

`testParser` compares P0 and P1 over the same corpus and generated snippets.
The language tests keep their independent literal ASTs, verdicts and rejected
fixtures, parsed through native test fragment wrappers. `TestParserUnicode`
checks current GHC predicate boundaries and version-sensitive P1 identifiers.
`testParserBootstrap` compares P0/P1 ASTs and all final declarations for the
same prepared current parser source, then requires identical checked/lowered
MIR and regenerated IR and tests P2 behavior. It does not require historical
P0 seed IR to equal current IR.

## Refreshing the parser seed

Use the development seed driver, not `llvm examples/parser/parser.tersus`: the raw
example omits the generated Unicode classifier that the serving parser uses.
From `tersus/`, with the current pinned seeds available:

```sh
stack run parser-seed -- /tmp/parser.ll.new "$(git rev-parse HEAD)"
sha256sum /tmp/parser.ll.new
```

The driver uses `TersusParser.emitParserIr` and the same owned program as P1's
build. It writes provenance comments for the source commit, GHC version,
classifier/source fingerprints and emitter seed pin. Only a successful emission
and verified digest may replace a pin. Never redirect into a seed file used by
the running compiler.

Publish the exact verified bytes as `parser.ll` in a new release tagged
`bootstrap-<first 12 digest characters>`, then put the full digest in
`bootstrap/parser.sha256`. `TERSUS_PARSER_SEED_FILE` or the ignored
`bootstrap/parser.ll` supplies local bytes instead; the same pin is verified.
Parser pin changes invalidate P0, E1 and downstream tool caches. Keep the emitter
pin unchanged unless its own fixpoint requires a new seed. The cold, concurrent,
corrupt/missing-seed, cache-reuse and fixpoint gates must pass before release.


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
