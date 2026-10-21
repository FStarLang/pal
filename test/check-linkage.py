#!/usr/bin/env python3
"""Verify linkage controls in both orders and relocated, byte-identical trees."""

import hashlib
import json
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

pal, fstar, original_out, cc = sys.argv[1:]
fixture = Path.cwd()
verify_make = Path(__file__).resolve().with_name("verify.mk")
work = fixture / "_cache/linkage-controls"
work.mkdir(parents=True, exist_ok=True)
source_files = sorted(fixture.glob("*.c"))
identical = len(source_files) == 2 and source_files[0].read_bytes() == source_files[1].read_bytes()
expected_file = fixture / "expected-verification-failures.txt"
expected = expected_file.read_text().split() if expected_file.exists() else []
error_text = fixture / "expected-verification-error.txt"
results = []


def run(command, directory, log_name, success=True):
    with (directory / log_name).open("w") as log:
        proc = subprocess.run(command, cwd=directory, stdout=log, stderr=subprocess.STDOUT)
    if success:
        assert proc.returncode == 0, (command, directory / log_name)
    else:
        assert proc.returncode != 0, command
    return proc.returncode


def manifest(out):
    return {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for pattern in ("*.fst", "*.fsti") for p in out.glob(pattern)
    }


reference = manifest(Path(original_out))


def check_case(name, inputs, compare=True, native=False, two_private=False):
    case = work / name
    case.mkdir(parents=True, exist_ok=True)
    out = case / "out"
    run([pal, "--outdir", str(out), *map(str, inputs)], case, "translate.log")
    diagnostics = json.loads((out / "diagnostics.json").read_text())
    assert not any(d["severity"] == 1 for ds in diagnostics.values() for d in ds), diagnostics
    generated = manifest(out)
    if compare:
        assert generated == reference, {
            "case": name,
            "changed": sorted(k for k in generated if generated[k] != reference.get(k)),
            "missing": sorted(set(reference) - set(generated)),
        }
    expected_here = [n for n in expected if (out / (n + ".fst")).exists()]
    failures = case / "expected.txt"
    failures.write_text("\n".join(expected_here) + "\n")
    run([
        "make", "-f", str(verify_make), "-j2", f"OUT_DIR={out}",
        f"CACHE_DIR={case}/cache", f"FSTAR_EXE={fstar}",
        f"EXPECTED_FAILURES_FILE={failures}", f"EXPECTED_FAILURE_TEXT_FILE={error_text}",
    ], case, "verify.log")
    for path in out.glob("Func_*.fst"):
        assert "admit" not in path.read_text(), path
        if path.stem not in expected_here:
            assert (case / "cache" / (path.name + ".checked")).exists(), path
    if two_private:
        assert len(list(out.glob("Func___pal_tu_*private_value.fst"))) == 2
        assert len(list(out.glob("Global___pal_tu_*private_number.fst"))) == 2
    if native:
        run([*shlex.split(cc), *map(str, inputs), "-o", str(case / "native")], case, "native-build.log")
        run([str(case / "native")], case, "native.log")
    results.append({"name": name, "manifest": generated, "expected_property_failures": expected_here})
    return generated


check_case("original-reverse", list(reversed(source_files)), native=(fixture / "native-check.c").exists(), two_private=identical)
for root_name in ("root-a", "different/depth/root-b"):
    tree = work / root_name / "source"
    tree.mkdir(parents=True, exist_ok=True)
    for pattern in ("*.c", "*.h"):
        for source in fixture.glob(pattern):
            shutil.copyfile(source, tree / source.name)
    inputs = [tree / p.name for p in source_files]
    for order, selected in (("forward", inputs), ("reverse", list(reversed(inputs)))):
        check_case(root_name + "/" + order, selected, native=(tree / "native-check.c").exists(), two_private=identical)
    alias = tree / "alias.c"
    if not alias.is_symlink():
        alias.symlink_to(inputs[0].name)
    check_case(root_name + "/alias", [alias, *inputs[1:]], two_private=identical)
    case = work / root_name / "duplicate-alias"
    case.mkdir(exist_ok=True)
    run([pal, "--outdir", str(case / "out"), str(inputs[0]), str(alias)], case, "reject.log", success=False)
    assert "duplicate selected translation unit" in (case / "reject.log").read_text()
    if identical:
        nested = []
        for side in ("left", "right"):
            directory = work / root_name / "same-basename" / side
            directory.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_files[0], directory / "same.c")
            shutil.copyfile(fixture / "pal.h", directory / "pal.h")
            nested.append(directory / "same.c")
        current = check_case(root_name + "/same-basename-check", nested, compare=False, two_private=True)
        if root_name == "root-a":
            nested_reference = current
        else:
            assert current == nested_reference

if identical:
    single = check_case("single", source_files[:1], compare=False)
    assert "Func_private_value.fst" in single and "Global_private_number.fst" in single
    assert not any("__pal_tu_" in name for name in single)

(work / "result.json").write_text(json.dumps(results, indent=2) + "\n")
print(f"{len(results)} linkage proof/order/relocation controls passed; two duplicate aliases rejected")
