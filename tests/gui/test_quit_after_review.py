"""Exit Review, then quit.

Reported: after leaving review mode the Exit button and the window's X stop
working.  Both call _on_close, and a callback that raises simply stops -- so
the window sits there and nothing says why.
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
    print("!! an exception escaped a callback:\n", errors[-1], flush=True))
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), True)[1]
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
(tmp / "SlideShow Output 2026-09-01 10.00.00.json").write_text(json.dumps(
    {"saved": "2026-09-01 10:00:00", "photo id": 11, "file": "p11.jpg",
     "album": "A", "editor": "a@x", "comment": "", "photo date": "",
     "faces": [{"number": 1, "name": "Person 1", "box": [80, 80, 120, 150]}]},
    indent=2) + "\n\n", encoding="utf-8")

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


def still_there():
    try:
        return bool(root.winfo_exists())
    except tk.TclError:
        return False


def run():
    print("into review mode, then some work, then out again:")
    app._show_mode(pe.MODE_REVIEW); root.update()
    check("review mode opened", app._mode == pe.MODE_REVIEW)

    # the work: type into one of the editor's fields, the way a review goes
    typed = False
    for key, widget in app.custom_vars.items():
        if isinstance(widget, tk.Text):
            widget.insert("1.0", "someone, someone else"); typed = True
            break
    check("something was typed into the editor", typed)
    root.update()

    was = app.custom_vars.get("comments")
    app._show_mode(pe.MODE_MOVE); root.update()
    check("review mode closed", app._mode != pe.MODE_REVIEW)
    # The bug this test was written for was a field widget destroyed with the
    # review and still held on to.  There is one editor now and it is never
    # destroyed, so what has to be true is the opposite: the widgets are the
    # same ones, alive, and readable in any mode.
    check("the fields are the same widgets", app.custom_vars.get("comments") is was)
    check("which are still alive", bool(was.winfo_exists()))
    check("and can be read outside the review",
          isinstance(app._editor_field_values(), dict))

    print("\nand again after going back in and out:")
    app._show_mode(pe.MODE_REVIEW); root.update()
    app._show_mode(pe.MODE_MOVE); root.update()
    check("still the same widgets", app.custom_vars.get("comments") is was)
    check("still readable", isinstance(app._editor_field_values(), dict))

    print("\nnow quit, the way Exit and the X do:")
    errors.clear()
    app._on_close()
    root.update() if still_there() else None
    check("no exception escaped", not errors,
          errors[0].strip().splitlines()[-1] if errors else "")
    check("the window actually closed", not still_there())

    if still_there():
        root.destroy()


root.after(400, lambda: root.after(1500, run))
root.after(20000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nQUIT AFTER REVIEW OK")
