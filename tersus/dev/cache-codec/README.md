# Lossless test-program codec experiment

Retain this candidate for a separate cache integration. Fully forced decoding of the existing 58,487,149-byte entry fell from a median 17.401 seconds to 3.022 seconds (5.76×). This commit does **not** switch `TestHarness` to the new format or claim whole-suite savings.

Plan: https://artifacts.internalmeta.com/a/1135240875628977

## Scope and implementation

Base: `29b52e967a116dd21f06531af8ba06faadec217b`.
Branch: `speed-codec-experiment-fd20ab17`.
All changes and generated fixtures stay in the isolated codec worktree. No children, publication, native bootstrap or full test suite.

`src/TestProgramBinary.hs` is a development-only module. Its 33 standalone `Generic` derivations, with default `Binary` and `NFData` instances, cover every type reachable from `Mir.Program`. There is no duplicated constructor/field schema and no modification to the production MIR types. Adding a field is picked up structurally; a new unsupported field type fails compilation.

The envelope has a versioned header, an exact 64-digit cache key, an exact payload length, and an FNV-1a byte checksum. Decoding rejects trailing bytes both outside and inside the payload. The reader and decoder impose a 256 MiB entry limit; the reader checks file size before allocation and rejects size changes during reading. The checksum detects accidental corruption, **not hostile modification**. A file deliberately produced by someone who recomputes the checksum is not authenticated or semantically validated. No compression is used and no legacy decoder fallback exists in this module.

Only the development executable depends on the newly declared packages. Measured installed versions: GHC 8.10.7, binary 0.8.8.0, bytestring 0.10.12.0, deepseq 1.4.4.0. `package.yaml` declares `binary >= 0.8.8 && < 0.9`, `bytestring >= 0.10.12 && < 0.13`, and `deepseq >= 1.4.4 && < 1.6`. `tersus.cabal` was regenerated with hpack 0.37.0, not edited manually. Other compiler/package versions are not benchmarked.

## Measurements

Each operation ran three times in a fresh process, pinned to CPU 0 (chosen from `os.sched_getaffinity(0)`), with `-O2`, `+RTS -N1 -T`, and warmed copied fixtures. Both decoded Programs were forced through every field with `NFData` **before** stopping the timer. Both encoders consumed the identical, already forced Program and fully materialized their output. Input preparation and explicit pre/post `performGC` are outside the reported interval. CPU time uses `getCPUTime`, wall time the monotonic clock, and allocations GHC RTS allocation counters. Allocation totals are not peak RSS.

Raw byte reads are measured separately from each codec's actual input reader. The old `readFile` reader constructs and forces a `String`; the candidate reader produces strict bytes and performs its size checks. The large difference between these input-reader times is predominantly materialization, not disk throughput.

Medians (wall / CPU / allocated bytes):

| Fixture | Operation | Old | Binary |
|---|---|---|---|
| Large | Raw disk byte read | 0.023680 s / 0.023439 s / 58,515,048 | 0.021747 s / 0.021554 s / 55,377,264 |
| Large | Read + input materialization | 2.920332 s / 2.885988 s / 2,359,734,144 | 0.040050 s / 0.039644 s / 110,723,096 |
| Large | Fully forced decode | 17.401445 s / 17.232577 s / 80,228,926,544 | 3.022363 s / 2.997643 s / 8,448,191,536 |
| Large | Fully materialized encode | 4.540182 s / 4.507664 s / 7,416,907,264 | 1.450266 s / 1.438167 s / 1,673,000,320 |
| Small | Raw disk byte read | 25.258 us / 24.047 us / 27,008 | 28.843 us / 28.363 us / 31,760 |
| Small | Read + input materialization | 24.647 us / 24.126 us / 58,728 | 36.084 us / 35.544 us / 31,632 |
| Small | Fully forced decode | 487.046 us / 480.071 us / 785,400 | 56.395 us / 55.944 us / 33,912 |
| Small | Fully materialized encode | 43.084 us / 42.613 us / 106,392 | 55.545 us / 55.033 us / 31,080 |

Large decode wall repetitions: old **17.182302 / 17.401445 / 17.437042** seconds; binary **3.046787 / 3.022363 / 2.991282** seconds. Decode allocation reduction: **89.47%**. Large encode median improves 3.13×. Small encode and reads have tiny regressions; do not infer end-to-end wins for all small tests.

File sizes: large 58,487,149 → 55,344,610 bytes (only 5.37% smaller); small 785 → 337 bytes. This candidate is primarily a lexical/allocation improvement, not a major space-saving codec.

All 48 raw measurements, including CPU and allocation repetitions, are in `results.json`.

## Losslessness and rejection checks

Both real copied fixtures passed `decoded == original` **and exact full `show` equality**. The second comparison matters: `Syntax.Value`'s custom equality deliberately ignores contracts on builtin function values.

The rich structural fixture contains requirements, ensures, every ghost-statement variant, proof/axiom contents, quantified proof terms, nested builtin function contracts, function and loop termination, loop environments, generic declarations, invariants, mutable/borrowed/from parameters, reference steps, types and arbitrary-size positive/negative integers. An additional string fixture includes NUL, Unicode boundaries and surrogate `Char` values, without normalization. A valid-envelope reconstruction assertion ensures malformed/trailing payload tests actually reach the inner binary decoder.

The probe checks invalid and mismatched keys; a genuine legacy header; outer and inner trailing data; nine truncation points; payload and framing corruption; malformed binary with a correct checksum; oversized declared payloads; truncated disk input; a successful bounded disk read; and a sparse oversized disk file rejected before materialization. No existing repository tests were edited or weakened.

## Actual cache reuse and identity

`reuse.py` copies the flat compiler sources and the actual `TestHarness`/`TestParserFragments` into a disposable input mirror under `identity/`. Other required source inputs are read-only links. It runs the **actual unmodified `sharedProgram` implementation**, not `testStrings` or `testBytes`:

- Seed one correctly keyed entry from the real small Program fixture through `sharedProgram`.
- In a fresh process, invoke `sharedProgram` with a throwing fallback; the existing disk entry is returned and its full serialization forced.
- Change the source argument and stage; keys differ, and changed source actually reaches the throwing fallback.
- Recompile after changing an actual copied compiler source file and, separately, the actual copied harness file. Both produce new keys and reach the fallback.
- Restore the source inputs; a fresh-process throwing-fallback lookup hits again.

Exact identities and keys are in `identity-results.json`. The supported existing identity covers stage, source, compiler source/embedded libraries/seeds, harness/parser-fragment source, package/Stack configuration, format header, and raw `TERSUS_PARSER`. These checks do **not** establish identity for actual GHC/package/toolchain versions, build flags supplied outside package configuration, or all native tool/seed overrides.

Before production integration, wire the binary reader/writer into `TestHarness`, put its source in the harness dependency fingerprint, include the binary schema/version in the cache key, and explicitly handle unsupported toolchain/override identity. A corrupted new entry must be a rejected entry/recomputation, never a legacy-codec attempt. Retain the textual helper API only where existing tests use it, while adding binary disk-entry coverage. No lossy `MirData` representation is proposed.

## Reproduce

Work from `tersus/`. The fixture files, build outputs, and input mirror are ignored, not committed. Locate fixtures with a **single-level** cache metadata listing, copy only targeted files, and never scan the 11k+ cache entries recursively.

Selected old files under `~/.cache/tersus/test-programs/`:

- Small: `01cd7b3bf6b28f0bf3798d15b68ffa447d419ed08ace28cd1a36b9d70ce1bcba`; SHA-256 `3be4e7dec71620e07e26d38a2eb1970abe4730dd73d621819c3f13b9fdd15a8f`.
- Large: `f0407a286d0c7b69cdfc63575dc74da637b55ef9cbf1d692b4e58c778521258b`; SHA-256 `90d403d33007a4649566e07f06971ca8fc522db5a338142ca5fd53d34d8ea670`.

```sh
mkdir -p dev/cache-codec/build dev/cache-codec/fixtures
ghc --make -O2 -threaded -rtsopts -Wall -isrc -idev/cache-codec/src \
  -odir dev/cache-codec/build -hidir dev/cache-codec/build \
  dev/cache-codec/src/Main.hs -o dev/cache-codec/probe
# Copy the two targeted old entries to fixtures/small.show and fixtures/large.show.
dev/cache-codec/probe checks +RTS -N1 -T
dev/cache-codec/probe prepare dev/cache-codec/fixtures/small.show +RTS -N1 -T
dev/cache-codec/probe prepare dev/cache-codec/fixtures/large.show +RTS -N1 -T
python3 dev/cache-codec/benchmark.py
python3 dev/cache-codec/reuse.py
```

`prepare` verifies the full-state roundtrip before writing each `.binary` fixture. The driver selects an allowed single CPU. `checks` and `reuse.py` do not parse/compile language input, build native compiler tools, or run a cold bootstrap.

The first offline Cabal attempt failed while trying to initialize Hackage metadata (403); its newly created default `~/.cabal/config` was removed and its absence verified. The subsequent `cabal --config-file=dev/cache-codec/cabal.config v2-build --offline exe:cache-codec-probe`, with repositories disabled and cache/store paths in the worktree, passed using GHC 8.10.7 (`-O1`). Its built executable passed all **27 codec checks** too. Build outputs were moved under the ignored `cabal-build/` directory. The benchmark uses the separately compiled `-O2` executable, not this `-O1` build. Stack is not installed on this host, so the LTS-22.24 toolchain is not tested.
