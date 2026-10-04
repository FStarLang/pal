#!/usr/bin/env python3
"""Hold a test's preprocessor.json to its preprocessor-expect.json.

`preprocessor.json` is what clang's preprocessor gave PAL's parser, one record
per compilation (see doc/internals.md): a build compares it with what its own
compiler's `-E` makes of the same source. The expectation pins part of a
test's one record. A top-level value it gives must be equal. Each entry of a
list it gives must be in the record's list: `macros`, `consulted`, `pragmas`,
and `files` in the order given; and `tokens`, as `[file, line, spelling]`, or
with a fourth element, the `endLine` a token from a macro call that ends on a
later line has. A file is named by the end of its path. Anything the
expectation leaves out is not checked.
"""

import json
import sys

LISTS = ("macros", "consulted", "pragmas", "files", "tokens")


def same_file(recorded, expected):
    return recorded == expected or recorded.endswith("/" + expected)


def main(record_path, expect_path):
    with open(record_path) as fh:
        units = json.load(fh)["units"]
    with open(expect_path) as fh:
        expect = json.load(fh)
    if len(units) != 1:
        print(f"ERROR: {record_path}: {len(units)} records, expected one",
              file=sys.stderr)
        return 1
    unit = units[0]
    errors = []
    for key, want in expect.items():
        if key not in LISTS and unit.get(key) != want:
            errors.append(f"{key} is {unit.get(key)!r}, expected {want!r}")
    for key in ("macros", "consulted"):
        for want in expect.get(key, []):
            if want not in unit[key]:
                errors.append(f"{key} has no {want!r}")
    for want in expect.get("pragmas", []):
        if not any(same_file(p["file"], want["file"])
                   and all(p[k] == v for k, v in want.items() if k != "file")
                   for p in unit["pragmas"]):
            errors.append(f"pragmas has no {want!r}")
    at = 0
    for want in expect.get("files", []):
        found = next((i for i in range(at, len(unit["files"]))
                      if same_file(unit["files"][i], want)), None)
        if found is None:
            errors.append(f"files has no {want!r} after {unit['files'][:at]!r}")
        else:
            at = found + 1
    names = unit["token_files"]
    for want in expect.get("tokens", []):
        if not any(same_file(names[t[0]], want[0]) and t[1:] == want[1:]
                   for t in unit["tokens"]):
            errors.append(f"tokens has no {want!r}")
    for e in errors:
        print(f"ERROR: {record_path}: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
