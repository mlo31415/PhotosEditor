"""A review record whose photo has been deleted from Piwigo.

Reproduces what happened with photo 9938: the reports show, the photo cannot
be fetched, and the photo side must say so instead of staying at "Loading…".
"""
import sys, json, shutil, tempfile, importlib.util, traceback
from pathlib import Path

base = Path(__file__).resolve().parents[3]      # the Python tree
for d in ("PiwigoHelpers", "HelpersPackage", "PhotosEditor"):
    sys.path.insert(0, str(base / d))
spec = importlib.util.spec_from_file_location("pe", base / "PhotosEditor" / "PhotosEditor.py")
pe = importlib.util.module_from_spec(spec); pe.__spec__ = spec
spec.loader.exec_module(pe)

import tkinter as tk
from tkinter import ttk
from CredentialStore import CredentialStore

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None

GONE, ALIVE = 9938, 10060


class Stub:
    """Answers for the live photo and 404s for the deleted one, as Piwigo does."""
    session = None

    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        if int(pid) == GONE:
            raise Exception("404 Client Error: image_id not found for url: "
                            "https://162.246.254.99/ws.php?format=json")
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": 400, "height": 300, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": None}


pe.AlbumHierarchy.PiwigoClient = Stub
pe._pick_derivative_url = lambda *a, **k: ""
loaded = []
pe.PhotosEditor._on_thumb_click = lambda self, info: (loaded.append(info["id"]), False)[1]


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*60, 20, 40, 50]}


def rec(pid, saved, editor):
    return {"saved": saved, "photo id": pid, "file": f"p{pid}.jpg",
            "album": "Test Photos/Personal Albums/1964", "editor": editor,
            "faces": [face(1, "Buz Busby"), face(2)], "comment": "", "photo date": ""}


tmp = Path(tempfile.mkdtemp())
(tmp / "SlideShow Output 2026-08-26 20.32.25.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in
                [rec(GONE, "t1", "a@x"), rec(GONE, "t2", "b@x"),
                 rec(ALIVE, "t3", "c@x")]) + "\n\n", encoding="utf-8")

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


def canvas_text():
    c = app.canvas
    return " ".join(str(c.itemcget(i, "text")) for i in c.find_all()
                    if c.type(i) == "text")


def start():
    app._show_ss_photo()
    root.after(1200, deleted)


def deleted():
    root.update()
    label = app.photo_label_var.get()
    shown = canvas_text()
    print(f"photo pane label : {label!r}")
    print(f"on the canvas    : {shown[:110]!r}")
    print(f"status           : {app.status_var.get()!r}")

    check("it does not still say Loading", "Loading" not in label, label)
    check("it says the photo is gone", str(GONE) in label and "no longer" in label, label)
    check("the canvas says so too", "no longer on Piwigo" in shown)
    check("and says it was deleted", "deleted since" in shown)
    check("and that the reports are still good", "still readable" in shown)
    check("it names the button that clears them", "Reject Reports" in shown, shown)
    check("the wait cursor came off", root.cget("cursor") == "", root.cget("cursor"))

    print("\nthe reports are there regardless:")
    check("two reports on it", len(app._ss_group) == 2, len(app._ss_group))
    check("its faces are rows", len(app._ss_rows) == 2, len(app._ss_rows))

    print("\nmoving on to the photo that does exist:")
    app._ss_step(+1)
    root.after(1200, alive)


def alive():
    root.update()
    check("the next photo was fetched", loaded == [ALIVE], loaded)
    # _on_thumb_click is stubbed to return False, so the "no image file"
    # message is what should show -- not the deletion one
    label = app.photo_label_var.get()
    print(f"photo pane label : {label!r}")
    check("a different problem is worded differently",
          "no longer" not in label and "cannot be shown" in label, label)
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
print("\nDELETED PHOTO IS EXPLAINED, NOT LEFT LOADING")
