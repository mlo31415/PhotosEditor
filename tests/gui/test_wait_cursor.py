"""The wait cursor must last as long as the wait does.

The review load happens in two stages: the record's details and the face
thumbnails, then the photo itself -- and the second is the slow one.  This
samples the cursor right through both.  Nothing leaves the machine: the client
and the image download are stubs, each made deliberately slow.
"""
import sys, json, shutil, tempfile, importlib.util, traceback, time
from pathlib import Path
from io import BytesIO

base = Path(__file__).resolve().parents[3]      # the Python tree
sys.path.insert(0, str(base / "PiwigoHelpers"))
sys.path.insert(0, str(base / "PhotosEditor"))
spec = importlib.util.spec_from_file_location("pe", base / "PhotosEditor" / "PhotosEditor.py")
pe = importlib.util.module_from_spec(spec); pe.__spec__ = spec
spec.loader.exec_module(pe)

import tkinter as tk
from tkinter import ttk
from PIL import Image

errors = []


def _report(self, exc, val, tb):
    errors.append("".join(traceback.format_exception(exc, val, tb)))
    print("!! exception in a tk callback:\n", errors[-1], flush=True)


tk.Tk.report_callback_exception = _report
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None

INFO_DELAY, PHOTO_DELAY = 0.4, 1.2          # the details are quick, the photo is not


class StubClient:
    def __init__(self, *a, **k): pass
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        time.sleep(INFO_DELAY)
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": 400, "height": 300, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": f"https://piwigo.invalid/p{pid}.jpg"}


class StubResponse:
    def __init__(self):
        buf = BytesIO()
        Image.new("RGB", (400, 300), "#40c060").save(buf, format="JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


def slow_get(url, **kw):
    time.sleep(PHOTO_DELAY)                 # this is the wait the user notices
    return StubResponse()


pe.AlbumHierarchy.PiwigoClient = StubClient
pe.requests.get = slow_get
pe._pick_derivative_url = lambda *a, **k: ""


def rec(pid, saved):
    return {"saved": saved, "photo id": pid, "file": f"p{pid}.jpg", "album": "A",
            "editor": "a@x", "faces": [], "comment": "", "photo date": ""}


tmp = Path(tempfile.mkdtemp())
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in [rec(11, "t1"), rec(22, "t2")]) + "\n\n",
    encoding="utf-8")

# Its own settings, state and credentials: building a PhotosEditor writes to
# the params file (the start-up migration), and the real one is not the test's
from CredentialStore import CredentialStore as _CredentialStore
pe._store = _CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1400x800")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
app._ss_source = str(tmp)        # as _enter_ss_review would have
app._show_mode(pe.MODE_REVIEW)     # which is what builds a review
root.update()

failures, samples = [], []
loaded = {}
realOnPhotoLoaded = pe.PhotosEditor._on_photo_loaded


def watched(self, pil, img_dict, *rest):
    # *rest: the downloaded bytes go along too, for the backup copy
    loaded["at"] = len(samples)
    return realOnPhotoLoaded(self, pil, img_dict, *rest)


pe.PhotosEditor._on_photo_loaded = watched


def sample(n=[0]):
    samples.append((round(n[0]*0.1, 1), root.cget("cursor"), app.canvas.cget("cursor")))
    n[0] += 1
    if n[0] < 25 and "at" not in loaded:
        root.after(100, sample)
    else:
        root.after(300, finish)


def finish():
    samples.append(("after", root.cget("cursor"), app.canvas.cget("cursor")))
    for t, r, c in samples:
        mark = "  <-- photo arrived" if t != "after" and t == samples[loaded["at"]][0] else ""
        print(f"  t={t:<6} root={r!r:<8} canvas={c!r}{mark}")
    busy = [s for s in samples[:loaded["at"]] if s[1] != "watch"]
    print(f"\nphoto arrived at sample {loaded['at']} "
          f"(~{loaded['at']*0.1:.1f}s); samples before it not showing the wait "
          f"cursor: {len(busy)}")
    try:
        assert loaded["at"] >= 8, ("the stub was not slow enough to be a real "
                                   f"test: arrived at {loaded['at']}")
        assert not busy, f"the cursor was not the wait cursor at {busy}"
        assert samples[-1][1] == "" and samples[-1][2] == "crosshair", samples[-1]
        assert not errors, errors[0][:300]
    except AssertionError as e:
        failures.append(str(e))
    root.destroy()


root.after(50, app._show_ss_photo)
root.after(60, sample)
root.after(20000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nWAIT CURSOR OK — it lasts until the photo is actually on screen")
