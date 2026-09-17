"""Two reports on one photo: dismissing one must leave the column of faces.

The reported fault was that the face pictures vanished and never came back,
because the matrix is rebuilt on dismissal and the load that cut them is over.
Stubbed server; the photo is generated here.
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

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None
pe.messagebox.showinfo = lambda *a, **k: None

W, H = 800, 600


class Stub:
    session = None

    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": W, "height": H, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": "https://piwigo.invalid/p.jpg"}

    def get(self, url, **kw): return Resp()


class Resp:
    def __init__(self):
        buf = BytesIO(); Image.new("RGB", (W, H), "#6688aa").save(buf, "JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


pe.AlbumHierarchy.PiwigoClient = Stub
pe.requests.get = lambda url, **kw: Resp()
pe._pick_derivative_url = lambda *a, **k: "https://piwigo.invalid/p.jpg"


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*150, 100, 90, 110]}


tmp = Path(tempfile.mkdtemp())
# One photo, two reports -- exactly the case reported
recs = [{"saved": "t1", "photo id": 11, "file": "p11.jpg", "album": "A",
         "editor": "a@x", "faces": [face(1, "Bob Tucker"), face(2), face(3)],
         "comment": "", "photo date": ""},
        {"saved": "t2", "photo id": 11, "file": "p11.jpg", "album": "A",
         "editor": "b@x", "faces": [face(1), face(2, "Ann Green"), face(3)],
         "comment": "not sure about the one on the left", "photo date": ""}]
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in recs) + "\n\n", encoding="utf-8")

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1500x900")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
app._ss_source = str(tmp)        # as _enter_ss_review would have
app._show_mode(pe.MODE_REVIEW)     # which is what builds a review
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def faces_shown():
    """How many face rows are actually showing a picture."""
    return sum(1 for l in app._ss_face_labels if str(l.cget("image")))


def start():
    app._show_ss_photo()
    root.after(1500, before)


def before():
    root.update()
    print("with both reports showing:")
    check("two columns", len(app._ss_columns) == 2, len(app._ss_columns))
    check("three face rows", len(app._ss_rows) == 3, len(app._ss_rows))
    check("all three faces have a picture", faces_shown() == 3, faces_shown())
    check("none left as the placeholder",
          not any(str(l.cget("text")) == "…" for l in app._ss_face_labels))
    root.after(100, dismiss)


def dismiss():
    print("\nclicking the X on the first column:")
    app._ss_dismiss_column(app._ss_columns[0])
    root.update()
    root.after(300, after)


def after():
    root.update()
    check("still the same photo", app._ss_group and app._ss_group[0]["photo id"] == 11)
    check("one column left", len(app._ss_columns) == 1, len(app._ss_columns))
    check("three face rows still", len(app._ss_rows) == 3, len(app._ss_rows))
    check("THE FACES ARE STILL THERE", faces_shown() == 3, faces_shown())
    check("no placeholders came back",
          not any(str(l.cget("text")) == "…" for l in app._ss_face_labels),
          [str(l.cget("text")) for l in app._ss_face_labels])

    print("\nand hovering still swaps in the lit copy:")
    lbl = app._ss_face_labels[1]
    plain = str(lbl.cget("image"))
    app._ss_set_hover(1)
    root.update()
    lit = str(lbl.cget("image"))
    app._ss_set_hover(None)
    root.update()
    check("the lit picture exists after the rebuild", lit and lit != plain,
          f"{plain} -> {lit}")
    check("and goes back", str(lbl.cget("image")) == plain)

    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, start)
root.after(20000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nFACES SURVIVE A DISMISSAL")
