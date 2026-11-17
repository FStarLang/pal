#!/usr/bin/env python3
"""Check the example's extraction boundary without changing tracked files."""

import pathlib
import shutil
import subprocess
import sys
import tempfile


def main():
    tool = sys.argv[1]
    root = pathlib.Path(__file__).resolve().parent
    sources = ("dll.c", "client.c")
    originals = {name: (root / name).read_bytes() for name in (*sources, "dll.h")}
    with tempfile.TemporaryDirectory(prefix="roundtrip-", dir=root / "_build") as directory:
        work = pathlib.Path(directory)
        for name in (*sources, "dll.h", "pal.h"):
            shutil.copyfile(root / "_build" / "annotated" / name, work / name)
        annotated = {name: (work / name).read_bytes() for name in sources}
        assert (work / "dll.h").read_bytes() == originals["dll.h"]

        def run(*args):
            subprocess.run([tool, "--root", str(work), *args], cwd=work, check=True)

        run("--apply", str(root / "proofs.annotations"))
        for name in sources:
            assert (work / name).read_bytes() == annotated[name], name
        run("--extract", *sources, "-o", "roundtrip.annotations")
        for name in sources:
            assert (work / name).read_bytes() == originals[name], name
        assert (work / "dll.h").read_bytes() == originals["dll.h"]
        run("--apply", "roundtrip.annotations", "--check")
        run("--apply", "roundtrip.annotations")
        for name in sources:
            assert (work / name).read_bytes() == annotated[name], name
    for name, original in originals.items():
        assert (root / name).read_bytes() == original, name
    print("DLL overlay: header contracts preserved; C proofs roundtrip exactly")


if __name__ == "__main__":
    main()
