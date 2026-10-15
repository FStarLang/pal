#!/usr/bin/env python3
"""Check that F* comments in the given files are balanced.

F* comments nest, and C code quoted inside one is full of accidental
delimiters: `_ensures(*x == 1)` opens a comment and `(int *)` closes one. An
unbalanced file is not an error -- F* simply treats the rest of it as a comment
and reports "Verified module" for code it never read. This is exactly the
failure mode that hid most of `Pulse.Lib.C.Palow.Examples.fst` for several
milestones, so it is worth a check that runs on every build.
"""

import sys


def unbalanced(path):
    text = open(path).read()
    depth, opened, line, i = 0, [], 1, 0
    while i < len(text):
        if text[i] == "\n":
            line += 1
            i += 1
        elif text.startswith("(*", i):
            depth += 1
            opened.append(line)
            i += 2
        elif text.startswith("*)", i):
            depth -= 1
            if opened:
                opened.pop()
            i += 2
        else:
            i += 1
    return opened if depth != 0 else []


def main(paths):
    bad = False
    for p in paths:
        for line in unbalanced(p):
            print(f"{p}:{line}: unterminated comment", file=sys.stderr)
            bad = True
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
