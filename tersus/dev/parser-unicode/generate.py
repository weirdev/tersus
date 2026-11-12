#!/usr/bin/env python3
"""Writes lib/parser/syntax/unicode.tersus: the parser's classifiers of code points from 128 up.

Run from tersus/ with a Python whose unicodedata is Unicode 15.0: python3 dev/parser-unicode/generate.py
"""
import sys
import unicodedata

VERSION = "15.0.0"
PART_SIZE = 32  # intervals per function, so that no function is too large for the validator
OUTPUT = "lib/parser/syntax/unicode.tersus"

if unicodedata.unidata_version != VERSION:
    sys.exit(f"unicodedata is Unicode {unicodedata.unidata_version}; the classifier is pinned to {VERSION}")

PREDICATES = [
    ("parserUnicodeLetter", lambda c: c.startswith("L")),
    ("parserUnicodeUpper", lambda c: c in ("Lu", "Lt")),
    ("parserUnicodeLower", lambda c: c == "Ll"),
    ("parserUnicodeAlphaNum", lambda c: c.startswith("L") or c.startswith("N")),
]


def ranges(classify):
    out = []
    start = None
    for cp in range(128, 0x110000):
        inside = classify(unicodedata.category(chr(cp)))
        if inside and start is None:
            start = cp
        elif not inside and start is not None:
            out.append((start, cp - 1))
            start = None
    if start is not None:
        out.append((start, 0x10FFFF))
    return out


def branch(intervals):
    if not intervals:
        return "return false;"
    if len(intervals) == 1:
        lo, hi = intervals[0]
        return f"return cp >= {lo} && cp <= {hi};"
    left, right = intervals[: len(intervals) // 2], intervals[len(intervals) // 2 :]
    return f"if cp < {right[0][0]} {{\n{branch(left)}\n}} else {{\n{branch(right)}\n}};"


def split(name, intervals):
    if len(intervals) <= PART_SIZE:
        part = f"{name}Part{intervals[0][0]}"
        return f"return {part}(cp);", [f"fn {part}(cp: Int) -> Bool ~ {{\n{branch(intervals)}\n}};\n"]
    left, right = intervals[: len(intervals) // 2], intervals[len(intervals) // 2 :]
    left_body, left_parts = split(name, left)
    right_body, right_parts = split(name, right)
    return f"if cp < {right[0][0]} {{\n{left_body}\n}} else {{\n{right_body}\n}};", left_parts + right_parts


def predicate(name, classify):
    body, parts = split(name, ranges(classify))
    return "".join(parts) + f"fn {name}(cp: Int) -> Bool ~ {{\n{body}\n}};\n"


header = (
    "// Unicode 15.0 general categories: letter = L*, upper = Lu or Lt, lower = Ll, alphanum = L* or N*"
    " (dev/parser-unicode/generate.py)\n"
)
with open(OUTPUT, "w", encoding="ascii", newline="\n") as out:
    out.write(header + "".join(predicate(name, classify) for name, classify in PREDICATES))
