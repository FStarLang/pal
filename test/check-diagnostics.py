#!/usr/bin/env python3
"""Check that PAL reported the diagnostics a test expects.

Usage: check-diagnostics.py <diagnostics.json> <expected-diagnostics.txt>

Each non-blank, non-comment line of the expectations file is a substring that
must appear in the message of some diagnostic PAL reported. A line may be
prefixed with `<file>:<line>: ` to also pin the diagnostic to a source
location, where `<line>` is 1-based as it is in an editor.
"""

import json
import os
import re
import sys


def load_diagnostics(path):
    with open(path) as f:
        by_uri = json.load(f)
    out = []
    for uri, diags in by_uri.items():
        name = os.path.basename(uri)
        for d in diags:
            out.append((name, d["range"]["start"]["line"] + 1, d["message"]))
    return out


def load_expectations(path):
    out = []
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            m = re.match(r"^([^\s:]+):(\d+):\s*(.*)$", line)
            if m:
                out.append((lineno, m.group(1), int(m.group(2)), m.group(3)))
            else:
                out.append((lineno, None, None, line))
    return out


def main():
    diags_path, expected_path = sys.argv[1], sys.argv[2]
    diags = load_diagnostics(diags_path)
    expectations = load_expectations(expected_path)

    if not expectations:
        sys.exit(f"{expected_path}: no expectations listed")

    failures = []
    for lineno, want_file, want_line, want_msg in expectations:
        for name, line, msg in diags:
            if want_msg not in msg:
                continue
            if want_file is not None and (name != want_file or line != want_line):
                continue
            break
        else:
            where = ""
            if want_file is not None:
                where = f" at {want_file}:{want_line}"
            failures.append(
                f"{expected_path}:{lineno}: no diagnostic{where} containing {want_msg!r}"
            )

    if failures:
        for f in failures:
            print(f, file=sys.stderr)
        print("reported diagnostics:", file=sys.stderr)
        for name, line, msg in diags:
            print(f"  {name}:{line}: {msg}", file=sys.stderr)
        sys.exit(1)

    print(f"{len(expectations)} expected diagnostic(s) reported")


if __name__ == "__main__":
    main()
