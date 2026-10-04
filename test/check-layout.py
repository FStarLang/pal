#!/usr/bin/env python3
"""Hold a test's layout_table.json to its layout-expect.json.

`layout_table.json` is every layout PAL's output may have used (see
src/layout_info.rs): a build compares it with what its own compiler does. A
test translated for a target whose layout is known pins it: each key the
expectation gives, at the top level or for a type of that kind and name, must
have exactly that value. Keys it leaves out are not checked.
"""

import json
import sys


def main(table_path, expect_path):
    with open(table_path) as fh:
        table = json.load(fh)
    with open(expect_path) as fh:
        expect = json.load(fh)
    errors = []
    for key, want in expect.items():
        if key != "types" and table.get(key) != want:
            errors.append(f"{key} is {table.get(key)!r}, expected {want!r}")
    for want in expect.get("types", []):
        what = f"{want['kind']} {want['name']}"
        found = [t for t in table["types"]
                 if t["kind"] == want["kind"] and t["name"] == want["name"]]
        if len(found) != 1:
            errors.append(f"{what}: {len(found)} entries, expected one")
            continue
        for key, value in want.items():
            if found[0].get(key) != value:
                errors.append(f"{what}: {key} is {found[0].get(key)!r}, expected {value!r}")
    for e in errors:
        print(f"ERROR: {table_path}: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
