#!/usr/bin/env python3
"""Body selection never suppresses declaration, contract or selected errors."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

pal = Path(sys.argv[1])
work = Path(sys.argv[2])
work.mkdir(parents=True, exist_ok=True)
fixture = Path.cwd()
source = fixture / "selected_body_clang.c"


def check(name, options, expected, sources=None):
    out = work / name
    out.mkdir(parents=True, exist_ok=True)
    p = subprocess.run(
        [str(pal), "--outdir", str(out), *options, *map(str, sources or [source])],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (out / "translate.log").write_bytes(p.stdout)
    diagnostics = json.loads((out / "diagnostics.json").read_text())
    errors = [d["message"] for ds in diagnostics.values() for d in ds
              if d["severity"] == 1]
    if expected is None:
        assert p.returncode == 0, (name, p.returncode)
        assert not errors, (name, errors)
        messages = [d["message"] for ds in diagnostics.values() for d in ds]
        assert any("--only-function excludes body of `unfinished`" in x
                   for x in messages), messages
        assert (out / "Func_selected.fst").exists()
    else:
        assert any(expected in x for x in errors), (name, expected, errors)
    print(name, "passed")


selection = ["--only-function", "selected"]
check("excluded-invalid-body", selection, None)
check("unfiltered", [], "undeclared")
check("selected-invalid-body", ["--only-function", "unfinished"], "undeclared")
check("invalid-selected-body", [*selection, "-DTEST_BAD_SELECTED"], "missing_selected")
check("invalid-declaration", [*selection, "-DTEST_BAD_DECL"], "missing_type")
check("invalid-contract", [*selection, "-DTEST_BAD_CONTRACT"], "missing_contract")
check("invalid-redeclaration", [*selection, "-DTEST_BAD_REDECL"], "conflicting types")
check("preprocessor-error", [*selection, "-DTEST_BAD_PP"], "excluded_body_preprocessor_error")

# A skipped body is still a C definition, and must participate in duplicate
# external-definition checks. Use a separate copied tree to avoid mutating
# the fixture or relying on a compilation database outside the test.
tree = work / "duplicate-inputs"
tree.mkdir(exist_ok=True)
for name in ("selected_body_clang.c", "pal.h"):
    shutil.copyfile(fixture / name, tree / name)
shutil.copyfile(fixture / "duplicate.inc", tree / "duplicate.c")
check("duplicate-excluded-definition", selection, "conflicting external definitions",
      [tree / source.name, tree / "duplicate.c"])
