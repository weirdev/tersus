# AST as data

`AstData` and `lib/ast_reader/ast_reader.tersus` exchange syntax without
running the proof engine. The parsed format is the production parser boundary.
The elaborated format remains a bridge for the MIR lowering port in
`REPLACING_HASKELL.md`; elaboration remains in Haskell, while
`ValidatorNative` runs the validator written in Tersus. The interface and
builtin-table formats and the elaboration request (below) are the data an
elaborator written in Tersus works from (`REPLACING_HASKELL.md`, "Moving
elaboration into Tersus").

## APIs

Haskell (`src/AstData.hs`):

```haskell
writeParsed     :: [Statement] -> Result String String
readParsed      :: String -> Result [Statement] String
writeElaborated :: Elaborated -> Result String String
readElaborated  :: String -> Result Elaborated String
writeInterfaceRecord :: InterfaceRecord -> Result String String
readInterfaceRecord  :: String -> Result InterfaceRecord String
writeBuiltinTable    :: [BuiltinRecord] -> Result String String
readBuiltinTable     :: String -> Result [BuiltinRecord] String
writeMirPayloadLines :: [Statement] -> Result [String] String
readMirPayloadBytes  :: [ByteString] -> Result [Statement] String
```

`InterfaceData.writeInterface`/`readInterface` write and read an
`Interface.ModuleInterface` through `InterfaceRecord`, its plain-syntax form
(`AstData` stays below the checker). `BuiltinTable.builtinTable` is the
builtin table made from `BuiltinRegistry`.

`writeParsed` writes the supplied syntax, including `Mark`s when the parser
kept locations. It also handles the resolved syntax inside `Elaborated`, but
use `writeElaborated` to retain its expression-occurrence types. That API
preserves **both** `[Statement]` and the complete ordered `[Type]` of
`Syntax.Elaborated`. The types remain in the lowering's visit order; the
bridge neither infers them again nor claims to validate an elaborated program.
A parsed reader refuses an elaborated header, and vice versa.

Tersus (`lib/data/reader/reader.tersus`, read by the entry of the
`ast_reader` package, `lib/ast_reader/ast_reader.tersus`):

The reader imports `data::codec::codec` for the shared token, integer, escaping
and size/type wire codec, and `data::ast::ast` for the AST arena schema and
writer. The native parser imports those same modules but not the reader, which
is a module of its own (`data::reader`) with the strict record, reference and
UTF-8 checks, so that anything written in Tersus that reads the data reads it
the same way. MIR records remain in the MIR package. The
codec's type writer has one mode for older MIR data (`printTypeWith` with
`listTokens`), which the MIR eraser writes with.

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
tersus-ast 1 interface
tersus-ast 1 builtins
tersus-ast 1 mir
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

An elaborated program is the `Instance` records first, then the module's
statements, then a `BoundedDef BOUNDS STATEMENT` for each function with bounds
the module defines: its body as checked against its bounds, an `Assign` of the
function with its type parameters as parameters, whose expression types follow
the module's in the type list. `Instance NAME FUNCTION ARGS NAMES SIGNATURE`
(response only; no parser writes it) says what a callee name the program uses
and does not define stands for: the copy `NAME` (`total[List<Int>]`) of the
function with bounds `FUNCTION` for the type and size `ARGS`, which may name the
type parameters of the function with bounds that uses it, or, with an empty
`FUNCTION` and no `ARGS`, a function a bound gives (`<$param T as Tr>::g`;
`FUNCTION` is `$builtin` for one of the prelude's `Sequence` or `Growable` that a
builtin has), with the parameter names and signature of `NAME`. The records are
in name order and claim no expression types (MIR.md, "The copy step").

A mir root is a `Statements` list: the validator's payloads of a lowered unit,
each one statement record (`MIR.md`, "Version 3: a lowered unit"). Only
Haskell reads this stage; the Tersus reader does not accept it.

An interface root is `Interface PACKAGE MODULE TYPES CTORS GENERICS INVARIANTS
TRAITS TRAITPARAMS FUNCTIONS IMPLS ASSOC IMPLARGS IMPLBOUNDS COPIES LINEAR DROPS
AXIOMS PROOFS EXTERNS TEMPLATES COMPANIONS`, the fields of
`Interface.ModuleInterface` in order (`MODULE` is an optional name). A map is
an `Entries` list (`EntriesEnd`, `EntriesCons ENTRY TAIL`) in ascending key
order, with no key twice, and every entry of one map is of the one kind it
holds: `NamesEntry NAME NAMES` (types, trait parameters, companions),
`CtorEntry NAME OWNER FIELDS`, `GenericEntry NAME NAMES FIELDS`,
`InvariantEntry NAME VALIDATIONS`, `TraitEntry NAME TRAITFNS`,
`FunctionEntry NAME NAMES SIGNATURE VALIDATIONS VALIDATIONS OPTTERMINATION
PROOFS`, `PairEntry NAME NAME` (impls), `AssocEntry NAME NAME OPTNAMES`,
`ImplArgsEntry NAME NAME TYPE ARGS`, `ImplBoundsEntry NAME NAME BOUNDS` and
`TemplateEntry NAME BOUNDS TYPEENTRIES OPTTYPE NAMES SIGNATURE VALIDATIONS
VALIDATIONS OPTTERMINATION STATEMENTS`, of which a call is checked against the
name, bounds, return type, parameter names and signature: the elaborator writes
the `TypeEntry NAME TYPE` list, the contracts, the termination and the body
empty, and reads none of them (the record keeps them for the pinned seed until
the next one). The companions map is written empty. A set is a `Names` list in ascending order; `OptNames` is a
list of `NoName`/`SomeName`, and `NoType`/`SomeType TYPE` an optional type.
Both readers refuse an entry of the wrong kind for its map and entries or set
members out of order (Haskell in `InterfaceData`; names compare by code point,
which is UTF-8 byte order, and a pair by its first name, then its second).

A builtin-table root is an `Entries` list of `BuiltinEntry BUILTIN SURFACES
SCHEME VALUE`: the builtin, the names a program calls it by (`SurfaceEntry
SPACE NAME`, `SPACE` one of `std`, `pointer`, `ghost`, `proof`, `method`,
`syntax`), its signature scheme (`SigFn TYPES TYPE`, with `param` types for its
type parameters; `SigDynamic` when the program's declarations give it, as for a
constructor; `SigValueError MESSAGE` when it cannot be used as a value) and the
value the checker writes for it (`StdLib.builtinFunct`: its parameter names and,
for a primitive contract, its contract). It lists every instance of
`BuiltinRegistry`; the parameterized constructors, fields, projections, `is`
tests and casts are made from a program's declarations. The functions of the
standard library and the contracts of its `builtin fn` declarations are not in
the table: they are `lib/stdlib.tersus`'s (`StdLibDefs`), which an elaborator
reads. `lib/data/builtins.ast`
is the table; `testAstData` checks that it is still `BuiltinTable`'s, and
`stack run frontend-seed -- builtins lib/data/builtins.ast` writes it again.

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

## Elaboration requests

An elaborator answers a request for one module (`ElaborateRequest`). The request
is the module, whether it predeclares its own types (a package module does),
whether it is a module of the compiler libraries (which see a generic struct's
constructor as the struct it builds), which interface to give back (none for a
single-file program, `module` for every ordinary package module, `lib` for a
compiler-library module's physical constructor view), the interfaces of the modules
it imports in merge order (the first wins a name), the interfaces of the modules
that define the functions with bounds it calls (their defining contexts), the
compiler libraries it may be given, and its statements as read:

```
tersus-elaborate 1
module "PACKAGE" none|"MODULE"
predeclare true|false
library true|false
extract none|module|lib
builtins
data LINES          (the builtin table, `tersus-ast 1 builtins`)
...
interfaces N
data LINES          (N times: a `tersus-ast 1 interface` block of LINES lines)
...
definitions N
definition INTERFACES (N times: one provider's checked context)
data LINES          (INTERFACES ordinary interface blocks; provider interface first)
...
libraries N         (when the module may be given compiler libraries)
library "NAME" K "IMPORT"... (N times, in the libraries' order: what the library imports)
data LINES          (its interface)
...
data LINES          (the program's `tersus-ast 1 parsed` syntax, as read)
```

The `definitions` blocks extend the experimental `tersus-elaborate 1` envelope; they are mandatory, and older envelopes without them are refused rather than accepted with missing context. A call of an imported function with bounds is checked against its signature and bounds alone, which may name types, traits and impls of modules the importer does not import: from these blocks the elaborator takes what they declare under canonical names (types, constructors, traits and impls, `contextFacts`), and none of their functions, so nothing becomes visible by a name the module can write. They reuse ordinary interface records and do not change the AST/interface record schema. The `libraries` section is optional, and a request without it is the envelope as it was.

For a module of a package (in a `package` load, below), the elaborator resolves the module's names before it checks them: it names each file's
declarations canonically (`package$module$file$Local`; the entry module's keep their names), rewrites each file's
references through the spellings its imports give, puts the files' statements in the package's order of the module's
files with types and traits first, then impls, then the rest, and refuses a module that declares one of the List and Box helper functions native
code calls (`listNew`, `listLen`, `listGet`, `listFirst`, `listLast`, `listPop`, `listSet`, `listPush`, `listFilled`,
`boxNew`, `boxUnbox`) or impls a trait for a type when neither is the module's. With libraries, it selects those the
module's statements as read call for (the rule a program is parsed with; for a module, the
`String`, `HashMap` and `HashSet` the interfaces it imports name count as mentions) and sees their interfaces, closed
over what they import (the list and Box types only when selected) and without what the module declares itself, in
front of the module's `interfaces`; a module that impls Drop without the prelude sees the prelude's Drop trait alone,
and the `definitions` it is given add only canonical names. A replacement `Eq` beside library
impls checked against the library's `Eq` has to be that `Eq` exactly.

Each function with bounds the module itself defines (a bounded function, a
function of a bounded impl, and the check of a bounded trait impl's function
against the trait) is checked once against its bounds alone, after the module's
statements are, and given back with its type parameters (a `BoundedDef`, above);
a call of a function with bounds, the module's or an imported one, is checked
against its signature and bounds alone and names its copy, which the copy step
makes (LANGUAGE.md, Bounded types). Every program's functions with bounds are
checked, the compiler libraries put in front of a single-file program included.

The response is `tersus-elaborated 1` and then `accepted`, a `data` block of
the elaborated syntax, `interface none` or `interface` with a `data` block of
the interface and, when the elaborator selected compiler libraries,
`libraries N "NAME"...`, which the compiler links; or `refused "MESSAGE"` (the module does not check),
`unresolved "MESSAGE"` (its names do not resolve, or the libraries it calls for
cannot be given it; the message is whole),
`interfaceRefused "MESSAGE"` (it checks, but the requested interface cannot be given)
or `unmodelled "WHAT"` (the elaborator
does not handle the program yet, which is no verdict on it).
The compiler sends a module request itself only for a program it is given as statements
(`Compile.lowerStatementsWith`); files, packages and the compiler libraries go as load requests (below), whose answers
carry module responses. In production the elaborator is an executable of the elaborator written in Tersus
(`ElaboratorTool`): the seed F0 for the compiler's own code (its tools, the compiler libraries and the List and Box
helper units) and the source elaborator for the programs and modules it is given. A failure of the executable refuses
the module; nothing answers in its place. The differential harness (`test/Differential.hs`) records the requests and
puts them to another elaborator too.

## Loading

The elaborator written in Tersus also loads: it reads a program's or a package's files from a snapshot the compiler
captures, parses them in process with the parser's declarations library (`lib/parser/syntax/`), seeds each file with
the declarations its imports name, reads a module's files again until its declarations settle, walks the import graph
and elaborates what the request asks for (`lib/elaborate/load.tersus`, `units.tersus`, `snapshot.tersus`,
`decls.tersus`). The compiler lists directories and reads files (`Modules.captureFilesystemInput`, which follows the
loader's own reads, reading each file's import prefix with P0 to know which modules to follow); it parses nothing else.
One request is one package or one program, so that a process parses each file
once and elaborates the modules in the order it loaded them:

```
tersus-elaborate 1
load graph|package|program|parse|equality|libraries
noPrelude true|false
reserving true|false
roots N ("NAME" "ROOT")*                (the --package-root map)
std none|"ROOT"                         (the --std-root)
entry none|"PATH" file|source           (source: the program came on standard input)
canonical N ("FROM" "TO")*              (each root as the filesystem canonicalized it)
dirs N
dir "PATH" S "SUB"... F "FILE"...       (N times: what listing the directory gave)
files N
file "PATH" BYTES                       (N times, followed by the file's UTF-8 bytes and a line feed)
sources N
source "NAME" implicit|native BYTES     (the compiler libraries' sources, then their bytes and a line feed)
builtins
data LINES
libraries N ...                         (as in a module request: the compiled libraries, for an elaboration)
```

`graph` answers the module graph the compiler reports and tests (each module's files with their declarations, imports
and parsed syntax, the packages' policies and the files read), or `standalone "PATH"` and the program's syntax for a
program with no package; `package` answers every module of the entry's package and its dependencies, in order, each
with the interfaces it is lowered with (`module P M`, `lowering K ...`, then a module response), and stops at the first
refusal (a program with no package is `notLoaded`); `program` answers one single-file program's response; `parse` and
`equality` answer a program as read: `parsed`, `libraries N "NAME"...` for the libraries it is read with (the type,
clone and equality libraries it calls for, for `equality`), each library's statements as read in the libraries'
order, then the program's; `libraries` answers each compiler library (and List and Box helper) with what it imports,
its statements as read and its response. A load that fails answers `notLoaded "MESSAGE"` in the words the Haskell
loader used, and a program that does not parse `unparsed "MESSAGE"`. The compiler asks through a `Loader`
(`Pipeline.loadFromEntry`, `PackageCompile.compileModulesUsing`, `Compile.lowerSourceUsing`,
`LibPackage.compileLibPackageWith`), F0 for its own code and the source elaborator otherwise.

## The packages

`lib/data/` is the `data` package: `codec/codec.tersus` (tokens, escaping, decimal
numbers and size/type wire helpers), `ast/ast.tersus` (AST arena schema and
writer) and `reader/reader.tersus` (the reader of every stage of the data). The parser (`lib/parser/`) and the AST reader (`lib/ast_reader/`) are
packages of their own beside it. The parser is compiled from its embedded
snapshot so its Unicode predicates match the serving Haskell compiler.

| Entry | What it does | With no input |
| --- | --- | --- |
| `parser/parser.tersus` | Native source/file parser: the driver of `parser/syntax/` (the grammar, also imported by the elaborator), which builds exact AST arenas and reads imports plus declaration state. `PreludeSource.parserPackageFiles` embeds the parser package, the generated Unicode file of `parser::syntax` and shared data dependencies; ordinary source does not receive those helpers. `TERSUS_PARSER=haskell` is refused; a pinned native LLVM parser seed bootstraps the current parser | |
| `ast_reader/ast_reader.tersus` | Parsed, elaborated, interface and builtin-table data, read into typed syntax arena payloads and written again, including contracts, proofs, builtin arguments and metadata, source marks and ordered occurrence types. Reuses the MIR type/size codec; `mutate` changes `Plus` to `Minus` as a semantic edit demonstration | returns `1` with no input and reports that the input is not AST data |

## The parser written in Tersus

`lib/parser/parser.tersus` is a hand-written parser over bytes (in the manner of
`lib/mir/mir_reader/mir_reader.tersus`) for the whole language. It builds the arena of
this document directly and writes `tersus-ast 1 parsed` for it, byte for byte
as `AstData.writeParsed` writes the decoded syntax,
including every desugaring (a `match` becomes an `if` chain of `Is` and
`Project`, a `for` becomes a `while`, struct literals become `Ctor`
applications, a standard `Eq` or `Clone` impl is written out, and so on).
Generated Eq/Clone text consumes owned field and variant accumulators; the
shared `catStrings` helper still borrows both arguments.
The arena is built in parse order and renumbered at the end into the emission
order above; nodes a failed speculation built are unreachable and dropped.

The parser's grammar is a library module, `lib/parser/syntax/syntax.tersus`, with
`parser.tersus` a driver of three lines that runs its request loop: the elaborator
imports the library and parses in process (Loading, above), and the driver
answers the file protocol below. The host (`src/TersusParser.hs`) runs the current
packaged parser as a native executable (P1). `ParserSeed` first verifies
`bootstrap/parser.sha256` and builds its pinned LLVM seed with clang (P0). P0 reads
the compiler's own sources where the host still parses them (`StdLibDefs` and the
snapshot's import prefixes), and the current parser and MIR packages are loaded by
F0 and compiled as every package is. The embedded snapshot includes package
markers, shared data modules and `lib/parser/syntax/unicode.tersus`, the
classifiers of code points from 128 up, pinned to Unicode 15.0. The emitter seed builds current E1,
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

The parser executables answer the file protocol in `src/FileParserProtocol.hs`
(the compiler's loads parse in the elaborator's process instead):

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

`Pipeline.validatedSource` and `compileSource` send the source as a `program` load:
the elaborator probes it for the libraries it calls for, parses it with their
declarations and elaborates it in one process. Standalone compilation still
rejects unlinked imports. `ParsedFile` holds only the file, import and
declaration records; `AstData` depends on `Syntax`, not the checker.

Immutable input is indexed once; consumed state uses lightweight checkpoints
and append-only arena rollback. Flat arena-list emission is iterative.
`lib/parser/syntax/unicode.tersus` is checked in: balanced comparisons over the
Unicode 15.0 general categories (letter is L*, upper is Lu or Lt, lower is Ll,
alphanum is L* or N*), split into functions of at most 32 intervals so that each
validates. `dev/parser-unicode/generate.py` writes it and refuses to run on a
Python whose `unicodedata` is not Unicode 15.0, so a regeneration cannot change
the tables unnoticed; moving to another Unicode version is a change of that
script. P1, the elaborator's in-process parser and the frontend fingerprint all
include the file, so a classifier change needs a new frontend seed. P0 retains
the classifier recorded in its authenticated LLVM asset (made with GHC 8.10's
tables). The ASCII identifiers of the bootstrap corpus let P0 read the sources
without requiring the two Unicode versions to agree. New bootstrap
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

It also round-trips every module interface of the compiler's tools and
libraries, checks that `lib/data/builtins.ast` is the registry's table and
refuses interfaces with entries out of order or of the wrong kind;
`testAstReader` round-trips those interfaces and the table natively and refuses
the malformed interfaces. `testDifferential` records every request the compiler
makes over the corpus (single files, the tool packages, `examples/modules` and
the compiler libraries as loads, and the programs of `testTypeCheck` as module
requests) and requires the compiler's frontend to agree with itself on each: a
module request and its response take a second trip through the text protocol,
so one that loses something fails; a load is asked again as it was (the host has
no reader of load requests, so a load request that loses something is not caught
here), and load requests with a section malformed must go unanswered. It
also checks that a candidate with a wrong type, other words or nothing modelled
is not counted as agreeing, and that the lowering takes exactly the elaborated
expression types, in their order.

`testParser` compares P0 and P1 over the same corpus and generated snippets. A
file alone is parsed by both with the declarations of every compiler library; a
package file with the declarations accumulated where its package's load reads
it (the libraries', then those of the modules before its own, then its own
module's, round after round), and P0 has to read every package file.
The language tests keep their independent literal ASTs, verdicts and rejected
fixtures, parsed through native test fragment wrappers. `TestParserUnicode`
checks the classifiers at every boundary of the checked-in intervals and parses
identifiers of letters new in Unicode 13 to 15 through the production frontend
and P1.
`testParserBootstrap` compares P0/P1 ASTs and all final declarations for every
file of the current parser package, read with its accumulated declarations, then requires identical checked/lowered
MIR and regenerated IR and compares P1 and P2 the same way. It does not require historical
P0 seed IR to equal current IR. Within one fixpoint, successful P0 replies are
reused only for byte-identical complete file requests. The loaded package is
lowered once; the result must equal P1's actual prepared emitter input. Independent E1 emission must equal the LLVM saved by
P1's successful build before P2 is built and checked. P1 and P2 parsing and all
comparisons still execute.

P1's executable and `.ll` sidecar share its compiled-input identity and
publication lock. The sidecar is atomically replaced after clang succeeds and
before the executable is published. A missing executable or sidecar rebuilds
both from the prepared input, rather than treating regenerated IR as the
previous build's output.

## Refreshing the parser seed

Use the development seed driver, not `llvm lib/parser/parser.tersus`: it emits
the exact prepared parser package and writes the header that names the commit,
the classifier and package fingerprints and the emitter seed.
From `tersus/`, with the current pinned seeds available:

```sh
stack run parser-seed -- /tmp/parser.ll.new "$(git rev-parse HEAD)"
sha256sum /tmp/parser.ll.new
```

The driver uses `TersusParser.emitParserIr` to read the LLVM retained by P1's
successful build from its exact prepared owned input. It writes provenance
comments for the source commit, classifier/source fingerprints
and emitter seed pin. Only a successful build and verified digest may replace
a pin. Never redirect into a seed file used by the running compiler.

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
