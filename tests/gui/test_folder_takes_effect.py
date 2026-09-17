"""Changing the SlideShow folder while a review is open takes effect on Save.

Every other setting is read from the file where it is used, so saving is
enough.  This one is read once, as the review begins, so the reports on screen
went on coming from the old folder until the review was left and re-entered.

Two folders, each with one report on a different photo, so which one is showing
can be told apart.
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

answer = {"yes": True}
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), answer["yes"])[1]
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))
pe.messagebox.showwarning = lambda t, m, **k: boxes.append(("warn", t, m))
# Nothing here may reach a real file chooser: a folder that needs one is a
# folder the test got wrong.
pe._pick_folder_by_its_files = lambda *a, **k: (_ for _ in ()).throw(
    AssertionError("a folder chooser was opened"))

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
A, B = tmp / "folder A", tmp / "folder B"


def log(folder: Path, pid: int, who: str, faces: int):
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "SlideShow Output 2026-09-01 10.00.00.json").write_text(json.dumps(
        {"saved": "2026-09-01 10:00:00", "photo id": pid, "file": f"p{pid}.jpg",
         "album": "A", "editor": "a@x", "comment": "", "photo date": "",
         "faces": [{"number": n, "name": f"{who} {n}",
                    "box": [n * 150, 80, 120, 150]}
                   for n in range(1, faces + 1)]}, indent=2) + "\n\n",
        encoding="utf-8")


log(A, 11, "Alpha", 3)
log(B, 22, "Beta", 2)

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(A))

root = tk.Tk(); root.geometry("1400x700")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def dialog():
    return next((w for w in root.winfo_children()
                 if isinstance(w, tk.Toplevel)
                 and w.title() == "PhotosEditor Settings"), None)


def walk(w, cls, out=None):
    out = [] if out is None else out
    if isinstance(w, cls):
        out.append(w)
    for c in w.winfo_children():
        walk(c, cls, out)
    return out


def press(dlg, text):
    for b in walk(dlg, ttk.Button):
        if str(b.cget("text")) == text:
            b.invoke(); return True
    return False


def set_folder(dlg, folder: Path):
    """Type a new folder into the folder setting's box."""
    for e in walk(dlg, ttk.Entry):
        if str(e.get()).strip() and Path(str(e.get())).is_dir():
            e.delete(0, "end"); e.insert(0, str(folder))
            return True
    return False


def reported_names():
    """The names in the reports being reviewed.  The rows themselves are the
    photo's detected faces, which say nothing about where the report came
    from; these are what the SlideShow user typed."""
    return sorted(f.get("name") or "" for rec in app._ss_group
                  for f in rec.get("faces") or [])


def photo_id():
    return (app._ss_group or [{}])[0].get("photo id")


def step_open():
    print("a review of folder A:")
    app._enter_ss_review()
    root.update()
    check("review mode is open", app._ss_review_frame is not None)
    check("showing folder A's photo", photo_id() == 11, photo_id())
    check("with A's names", reported_names() == ["Alpha 1", "Alpha 2", "Alpha 3"],
          reported_names())
    check("and it knows which folder they came from", app._ss_source == str(A),
          app._ss_source)
    root.after(1200, step_change)


def step_change():
    print("\nchanging the folder to B and pressing Save:")
    app._show_settings(); root.update()
    dlg = dialog()
    check("the settings window opened", dlg is not None)
    check("the folder box was found", set_folder(dlg, B))
    boxes.clear()
    press(dlg, "Save")
    root.update()
    check("the settings window closed", dialog() is None)
    check("the file has the new folder",
          pe._ss_review_source() == str(B), pe._ss_review_source())
    root.after(1500, step_applied)


def step_applied():
    check("the review is still open", app._ss_review_frame is not None)
    check("it now shows folder B's photo", photo_id() == 22, photo_id())
    check("with B's names, not A's", reported_names() == ["Beta 1", "Beta 2"],
          reported_names())
    check("and B is the folder it will write back to", app._ss_source == str(B),
          app._ss_source)
    root.after(100, step_refused)


def step_refused():
    print("\nunsaved edits: the change is saved, the running review is not "
          "thrown away:")
    app._photo_edited = True             # something on screen not uploaded
    app._show_settings(); root.update()
    dlg = dialog()
    set_folder(dlg, A)
    boxes.clear()
    answer["yes"] = False                # no, don't discard my edits
    press(dlg, "Save")
    root.update()
    check("it asked before discarding", any(b[1] == "Not Uploaded Yet" for b in boxes),
          str([b[1] for b in boxes]))
    check("the setting is saved anyway", pe._ss_review_source() == str(A))
    check("the review that was running is still there", photo_id() == 22, photo_id())
    check("the status says when the new folder applies",
          "next time" in app.status_var.get(), app.status_var.get())
    check("and it still writes back to the folder the reports came from",
          app._ss_source == str(B), app._ss_source)

    # The setting says A, the reports on screen came from B.  Marking them done
    # must find them -- in B.
    boxes.clear()
    all_marked, _ = app._ss_mark_records_done(list(app._ss_group))
    check("marking them done finds them", all_marked,
          str([b[2] for b in boxes]))

    app._photo_edited = False
    answer["yes"] = True
    root.after(100, done)


def done():
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(400, step_open)
root.after(30000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nFOLDER CHANGE TAKES EFFECT OK")
