"""The renamed button is wired to the same action.

A rename's one risk is a reference left pointing at the old name, so this
builds the real panel, checks the label, and presses it: the reports must end
up marked done in the log on disk, which is what makes the photo not come back.
"""
import sys, json, shutil, tempfile, importlib.util, traceback
from pathlib import Path
from io import BytesIO

base = Path(__file__).resolve().parents[3]      # the Python tree
for d in ("PiwigoHelpers", "HelpersPackage", "PhotosEditor"):
    sys.path.insert(0, str(base / d))
spec = importlib.util.spec_from_file_location("pe", base / "PhotosEditor" / "PhotosEditor.py")
pe = importlib.util.module_from_spec(spec); pe.__spec__ = spec
spec.loader.exec_module(pe)

import tkinter as tk
from tkinter import ttk
from PIL import Image
from CredentialStore import CredentialStore

errors, boxes = [], []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda t, m, **k: True
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.showwarning = lambda t, m, **k: boxes.append(("warn", t, m))

W, H = 900, 700


class Resp:
    def __init__(self):
        buf = BytesIO(); Image.new("RGB", (W, H), "#6688aa").save(buf, "JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


class Stub:
    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass
    def get(self, url, **kw): return Resp()

    def get_image_info(self, pid):
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": W, "height": H, "derivatives": {},
                "categories": [{"id": 77, "name": "A"}],
                "element_url": "https://piwigo.invalid/p.jpg"}


pe.AlbumHierarchy.PiwigoClient = Stub
pe.requests.get = lambda url, **kw: Resp()
pe._pick_derivative_url = lambda *a, **k: "https://piwigo.invalid/p.jpg"

tmp = Path(tempfile.mkdtemp())
logs = []
for n, pid in enumerate((11, 22), start=1):
    p = tmp / f"SlideShow Output 2026-09-0{n} 10.00.00.json"
    p.write_text(json.dumps(
        {"saved": f"2026-09-0{n} 10:00:00", "photo id": pid, "file": f"p{pid}.jpg",
         "album": "A", "editor": "a@x", "comment": "", "photo date": "",
         "faces": [{"number": 1, "name": f"Person {pid}", "box": [80, 80, 120, 150]}]},
        indent=2) + "\n\n", encoding="utf-8")
    logs.append(p)

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))

root = tk.Tk(); root.geometry("1400x700")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def labels():
    out = []

    def walk(w):
        if isinstance(w, ttk.Button):
            out.append(str(w.cget("text")))
        for c in w.winfo_children():
            walk(c)
    walk(app._ss_record_host)       # the reports side, where the buttons are
    return out


def run():
    app._show_mode(pe.MODE_REVIEW); root.update()
    first = app._ss_group[0]["photo id"]
    print(f"reviewing {len(app._ss_groups)} photos, this one is {first}")
    check("the button says Reject Reports", "Reject Reports" in labels(),
          [t for t in labels() if "photo" in t.lower() or "Reject" in t])
    check("nothing still says Skip", not any("Skip" in t for t in labels()))

    app._ss_reject_btn.invoke()
    root.update()

    check("the photo is gone from the review",
          first not in [g[0]["photo id"] for g in app._ss_groups],
          [g[0]["photo id"] for g in app._ss_groups])
    # and that is recorded on disk, which is why it does not come back
    left = [r["photo id"] for r in pe._collect_ss_records(str(tmp))]
    check("and marked done in the log, not just on screen", first not in left,
          left)
    check("the other photo is untouched", len(left) == 1, left)
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(400, lambda: root.after(1200, run))
root.after(20000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nREJECT REPORTS OK")
