"""Run the GUI tests.

    python tests/gui/run.py                 all of them
    python tests/gui/run.py review scroll   only those whose names match

These are not part of `unittest discover -s tests`, and are meant not to be:
each one opens a real window, drives it, and takes seconds rather than
milliseconds.  `tests/` stays fast enough to run on every change; this is what
you run before letting go of anything that touched the review screen, the
editor panel or the Settings window.

Each test is a script that exits non-zero when it fails and says which check
failed, so it can also be run on its own while working on it:

    python tests/gui/test_scrolling.py

They need a desktop -- there is no headless mode -- and they need nothing else:
every one of them invents its photos, its logs and its settings file in a temp
folder, stubs the Piwigo client, and touches neither the real settings nor the
server.
"""
import subprocess
import sys
import time
from pathlib import Path

here = Path(__file__).resolve().parent


def main(patterns):
    tests = sorted(here.glob("test_*.py"))
    if patterns:
        tests = [t for t in tests
                 if any(p.lower() in t.name.lower() for p in patterns)]
    if not tests:
        print("no tests match", " ".join(patterns))
        return 1

    failed, started = [], time.monotonic()
    for path in tests:
        print(f"\n=== {path.name}", flush=True)
        result = subprocess.run([sys.executable, str(path)], cwd=str(here))
        if result.returncode != 0:
            failed.append(path.name)

    took = time.monotonic() - started
    print(f"\n{len(tests)} GUI test{'s' if len(tests) != 1 else ''} "
          f"in {took:.0f}s")
    if failed:
        print("FAILED:", *failed, sep="\n  ")
        return 1
    print("all passed")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
