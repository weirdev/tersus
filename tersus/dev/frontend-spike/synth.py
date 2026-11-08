"""Writes programs of the spike's slice with N functions and N structs, for timing the elaborators at scale.

Usage: python3 dev/frontend-spike/synth.py OUTDIR [N ...]   (default N: 10 50 200 800)
"""
import os
import sys


def program(n):
    lines = []
    for k in range(n):
        call = f"f{k - 1}(a + 1, b, p.ok)" if k > 0 else "a"
        lines.append(f"struct P{k} {{ x: Int, y: Int, ok: Bool }};")
        lines.append(f"""fn f{k}(a: Int, b: Int, c: Bool) -> Int [{{ affirm a >= 0; }}] [{{ }}] {{
    p = P{k} {{ x: a, y: b, ok: c && a > 0 }};
    t = 0;
    i = 0;
    while i < 10 [{{ affirm i >= 0; affirm i <= 10; }}] shrinks 10 - i {{
        t = t + p.x * i - p.y / 2;
        i = i + 1;
    }};
    if t > b && a != 0 || !p.ok {{ return t - p.y; }} else {{ return {call}; }};
}};""")
    lines.append(f"return f{n - 1}(1, 2, true);")
    return "\n".join(lines) + "\n"


def main():
    out = sys.argv[1]
    sizes = [int(a) for a in sys.argv[2:]] or [10, 50, 200, 800]
    os.makedirs(out, exist_ok=True)
    for n in sizes:
        with open(os.path.join(out, f"synth{n}.tersus"), "w") as f:
            f.write(program(n))


if __name__ == "__main__":
    main()
