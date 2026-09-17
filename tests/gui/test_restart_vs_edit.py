"""The exact case: type into a photo's field, do not upload, then change a
setting that needs a restart.  Is the typing lost?

Drives the real window end to end with the server stubbed.
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
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), True)[1]

W, H = 400, 300


class Stub:
    session = None

    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        return {"id": pid, "file": "p11.jpg", "name": "p11.jpg", "width": W,
                "height": H, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": "https://piwigo.invalid/p.jpg",
                "author": "", "comment": "", "date_creation": ""}

    def get(self, url, **kw): return Resp()


class Resp:
    def __init__(self):
        buf = BytesIO(); Image.new("RGB", (W, H), "#557799").save(buf, "JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


pe.AlbumHierarchy.PiwigoClient = Stub
pe.requests.get = lambda url, **kw: Resp()

tmp = Path(tempfile.mkdtemp())
params = tmp / "PhotosEditor Params.json"
params.write_text(json.dumps({"max_upload_pixels": 4000000}), encoding="utf-8")
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

# Pretend "Uploading enabled" is a setting that cannot take effect while running
pe._OP_PARAMS[0] = pe._OP_PARAMS[0]._replace(restart_needed=True)

root = tk.Tk(); root.geometry("1300x850")
app = pe.PhotosEditor(root)
app._build_editor_dialog_content(ttk.Frame(root))
root.update()
failures = []
TYPED = "Bob Tucker, second from the left"


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + detail) if detail else ''}")
    if not ok:
        failures.append(label)


def load_photo():
    app._on_thumb_click({"id": 11, "file": "p11.jpg", "name": "p11.jpg",
                         "width": W, "height": H,
                         "element_url": "https://piwigo.invalid/p.jpg",
                         "categories": [{"id": 77, "name": "A"}]})
    root.after(900, type_into_field)


def type_into_field():
    root.update()
    check("a photo is loaded", app._current_image_dict is not None)
    check("the field baseline was taken on load", bool(app._loaded_fields),
          str(sorted(app._loaded_fields))[:60])
    app.custom_vars["comments"].insert("1.0", TYPED)
    root.update()
    check("the typing is seen as unsaved", app._unsaved_field_labels() == ["Caption"],
          str(app._unsaved_field_labels()))
    root.after(100, change_setting)


def change_setting():
    print("\nnow change a setting that needs a restart, without uploading:")
    boxes.clear()
    app._show_settings(); root.update()
    dlg = next(w for w in root.winfo_children()
               if isinstance(w, tk.Toplevel) and w.title() == "PhotosEditor Settings")

    def walk(w, kinds, out):
        if isinstance(w, kinds):
            out.append(w)
        for c in w.winfo_children():
            walk(c, kinds, out)
        return out

    walk(dlg, ttk.Checkbutton, [])[0].invoke()          # Uploading enabled -> on
    for b in walk(dlg, ttk.Button, []):
        if str(b.cget("text")) == "Save":
            b.invoke(); break
    root.update()
    root.after(200, verdict)


def verdict():
    root.update()
    saved = json.loads(params.read_text(encoding="utf-8"))
    kinds = [b[0] for b in boxes]
    told = boxes[0][2] if boxes else ""

    print()
    check("the setting was saved", saved.get("uploads_enabled") is True)
    check("it is in force for the next upload", pe._uploads_enabled() is True)
    check("NO restart was armed", app._relaunch_on_exit is False)
    check("the user was told, not asked", kinds == ["info"], str(kinds))
    check("told why", "have not been uploaded" in told,
          told.replace("\n", " ")[:90])
    check("told the setting still applies later", "next time you start" in told)
    check("the window is still open", bool(root.winfo_exists()))
    check("THE TYPING IS STILL THERE",
          app.custom_vars["comments"].get("1.0", "end").strip() == TYPED,
          repr(app.custom_vars["comments"].get("1.0", "end").strip()))
    check("and still counted as unsaved",
          app._unsaved_field_labels() == ["Caption"])
    print("\n  what the user saw:\n     " + told.replace("\n", "\n     "))
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, load_photo)
root.after(25000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nNOTHING LOST — the edit survives, the setting is saved, no restart")
