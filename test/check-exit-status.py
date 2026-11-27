#!/usr/bin/env python3
"""Check CLI exit status without discarding translation diagnostics or artifacts."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile


pal = Path(sys.argv[1]).resolve()
fixtures = Path(__file__).resolve().parent
valid = fixtures / "block_scope_typedef/block_scope_typedef.c"
invalid = fixtures / "block_scope_typedef_bad/block_scope_typedef_bad.c"
emitter_gap = fixtures / "array_wide_as_bytes/array_wide_as_bytes.c"

cases = [
    ("success", valid, [], 0),
    ("warnings-only", valid, ["--only-function", "widen"], 0),
    ("frontend-error", invalid, [], 1),
    ("quiet-error", invalid, ["--quiet"], 1),
    ("ir-error", invalid, ["--print-ir"], 1),
    ("ir-success", valid, ["--print-ir"], 0),
    ("quiet-ir-error", invalid, ["--quiet", "--print-ir"], 1),
    ("permissive-frontend-error", invalid, ["--palow-permissive"], 1),
    ("emitter-error", emitter_gap, [], 1),
    ("permissive-emitter-gap", emitter_gap, ["--palow-permissive"], 0),
]

with tempfile.TemporaryDirectory(prefix="pal-exit-status-") as work:
    for name, source, options, expected in cases:
        out = Path(work) / name
        proc = subprocess.run(
            [str(pal), "--outdir", str(out), *options, str(source)],
            cwd=source.parent,
            capture_output=True,
            text=True,
        )
        assert proc.returncode == expected, (
            f"{name}: expected exit {expected}, got {proc.returncode}\n{proc.stderr}"
        )
        if "--quiet" in options:
            assert not proc.stderr, (name, proc.stderr)
        if "--print-ir" in options:
            assert proc.stdout.strip(), name
            assert not out.exists(), name
            continue
        diagnostics = json.loads((out / "diagnostics.json").read_text())
        severities = [
            d["severity"] for diags in diagnostics.values() for d in diags
        ]
        assert (1 in severities) == (expected == 1), (name, diagnostics)
        if name == "warnings-only":
            assert 2 in severities, diagnostics
        errors = (out / "TranslationErrors.fst").read_text()
        assert ("assert False" in errors) == (expected == 1), (name, errors)
        assert list(out.glob("Func_*.fst")), name

print(f"{len(cases)} CLI exit-status controls passed")
