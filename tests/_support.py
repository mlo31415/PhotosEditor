"""Load PhotosEditor.py for testing without starting the application.

Importing the module is safe: it defines its functions and creates a
CredentialStore object, but reads no credentials, contacts no server and opens
no window until the PhotosEditor class is instantiated.  That is what lets the
pure helpers be tested with no GUI, no network and no configuration.
"""
import importlib.util
import sys
from pathlib import Path

_HERE    = Path(__file__).resolve().parent
_APP_DIR = _HERE.parent
_HELPERS = _APP_DIR.parent / "PiwigoHelpers"

for _p in (str(_HELPERS), str(_APP_DIR)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

_MODULE_NAME = "photoseditor_under_test"


def load_pe():
    """The PhotosEditor module, imported once per test run."""
    if _MODULE_NAME in sys.modules:
        return sys.modules[_MODULE_NAME]
    spec = importlib.util.spec_from_file_location(
        _MODULE_NAME, _APP_DIR / "PhotosEditor.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[_MODULE_NAME] = mod        # before exec, so self-imports resolve
    spec.loader.exec_module(mod)
    return mod


def write_log(directory: Path, stamp: str, records: list) -> Path:
    """Write records exactly as SlideShow writes them: pretty-printed JSON
    objects separated by a blank line, with each four-number face box compacted
    onto one line.  The compaction matters -- without it the fixture would not
    be in SlideShow's format, and a round-trip comparison would test nothing."""
    import json
    import re
    chunks = []
    for rec in records:
        text = json.dumps(rec, indent=2, ensure_ascii=False)
        text = re.sub(r"\[\s+(-?\d+),\s+(-?\d+),\s+(-?\d+),\s+(-?\d+)\s+\]",
                      r"[\1, \2, \3, \4]", text)
        chunks.append(text)
    path = directory / f"SlideShow Output {stamp}.json"
    path.write_text("\n\n".join(chunks) + "\n\n", encoding="utf-8")
    return path


def record(photo_id, saved, comment="", faces=(), editor="mlo"):
    """A SlideShow record shaped like the real thing."""
    return {"saved": saved, "photo id": photo_id,
            "file": f"p{photo_id}.jpg", "album": "Some/Album",
            "editor": editor, "faces": list(faces), "comment": comment,
            "photo date": ""}
