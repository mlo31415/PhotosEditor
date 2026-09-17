"""Uploading is off until the params file says otherwise.

Every operation that would change Piwigo asks first, offering three ways out.
Nothing here touches the network -- the client class raises if it is ever
constructed -- and the params file is a throwaway in a temp folder, so the real
PhotosEditor Params.json is never written.
"""
import sys, json, shutil, tempfile, importlib.util, traceback
from pathlib import Path

base = Path(__file__).resolve().parents[3]      # the Python tree
sys.path.insert(0, str(base / "PiwigoHelpers"))
sys.path.insert(0, str(base / "PhotosEditor"))
spec = importlib.util.spec_from_file_location("pe", base / "PhotosEditor" / "PhotosEditor.py")
pe = importlib.util.module_from_spec(spec); pe.__spec__ = spec
spec.loader.exec_module(pe)

import tkinter as tk
from tkinter import ttk
from PIL import Image
from CredentialStore import CredentialStore

errors = []


def _report(self, exc, val, tb):
    text = "".join(traceback.format_exception(exc, val, tb))
    errors.append(text)
    print("!! exception in a tk callback:\n", text, flush=True)


tk.Tk.report_callback_exception = _report

# A params file of our own, so the real one is never touched
tmp = Path(tempfile.mkdtemp())
params = tmp / "PhotosEditor Params.json"
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"   # keep the real one out of it
# Credentials the workers can load; they point at nothing, and the client class
# below never lets a request out anyway
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")


class NoServer:
    def __init__(self, *a, **k):
        raise AssertionError("a blocked operation reached the server!")


pe.AlbumHierarchy.PiwigoClient = NoServer
warnings = []
pe.messagebox.askyesno = lambda *a, **k: True        # the ordinary confirmations
pe.messagebox.showerror = lambda *a, **k: warnings.append(("ERROR", a))
pe.messagebox.showwarning = lambda *a, **k: warnings.append(("WARN", a))

root = tk.Tk(); root.withdraw()
app = pe.PhotosEditor(root)
# The upload path reads the editor's fields, so they have to exist
app._build_editor_dialog_content(ttk.Frame(root))
root.update()


def settle(flag: dict, seconds: float = 3.0):
    """Let the upload worker get going."""
    import time
    end = time.time() + seconds
    while time.time() < end and not flag:
        root.update()
        time.sleep(0.05)

failures = []


def find_dialog():
    for w in root.winfo_children():
        if isinstance(w, tk.Toplevel) and w.title() == "Uploading Is Turned Off":
            return w
    return None


def buttons(dlg):
    found = {}
    def walk(w):
        for c in w.winfo_children():
            if isinstance(c, ttk.Button):
                found[str(c.cget("text"))] = c
            walk(c)
    walk(dlg)
    return found


def attempt(label, fn, press, expect_dialog=True):
    """Run fn; when its dialog appears, press the button whose text starts with
    `press`.  Returns the button labels that were offered."""
    offered = {}

    def click(tries=[0]):
        dlg = find_dialog()
        if dlg is None:
            tries[0] += 1
            if tries[0] < 40:
                root.after(50, click)
            return
        offered.update(buttons(dlg))
        target = [b for t, b in offered.items() if t.startswith(press)]
        if not target:
            failures.append(f"{label}: no button starting {press!r} in {list(offered)}")
            dlg.destroy(); return
        target[0].invoke()

    if expect_dialog:
        root.after(50, click)
    fn()
    root.update()
    if expect_dialog and not offered:
        failures.append(f"{label}: no dialog appeared")
    return list(offered)


# The photo the upload path needs
def arm():
    app._viewer_image = Image.new("RGB", (40, 30), "#808080")
    app._current_image_dict = {"id": 11, "file": "p11.jpg", "name": "p11",
                               "width": 40, "height": 30,
                               "categories": [{"id": 77, "name": "Some Album"}]}
    app._photo_edited = True
    app.current_album_id, app.current_album_name = 77, "Some Album"
    app.target_album_id, app.target_album_name = 88, "Other Album"


arm()
batch = [{"id": 11, "file": "p11.jpg"}]

print("Uploading off (no params file at all):", pe._uploads_enabled())

print("\nEvery write path asks, and 'Continue without uploading' stops it:")
paths = [
    ("Upload to Piwigo",    app._upload_current_photo),
    ("Move between albums", lambda: app._execute_move_copy(batch, "move", "left", 77, 88)),
    ("Copy between albums", lambda: app._execute_move_copy(batch, "copy", "left", 77, 88)),
    ("Move an album",       lambda: app._execute_album_move(5, "W / N3", 9, "W")),
    ("Remove selection",    lambda: app._remove_selection_confirm(batch, "left")),
    ("Remove one photo",    lambda: app._remove_from_album_confirm(11, batch[0], "left")),
]
app._move_undo_stack.append({"description": "Move 3 photo(s)",
                             "items": [{"image_id": 11, "name": "p11.jpg",
                                        "original_cats": [77], "img_dict": batch[0]}]})
paths.append(("Undo a move", app._undo_drag_drop))

offered = None
for label, fn in paths:
    offered = attempt(label, fn, "Continue without")
    print(f"  {label:<22} asked")
print("\nthe three choices offered:", offered)
if len(app._move_undo_stack) != 1:
    failures.append("declining the undo threw the undo record away")

# What each of the other two choices answers, and what it leaves behind.
# The guard is called directly here: driving a whole upload would need a real
# mainloop, since its worker posts progress back with root.after.
answer = {}
print("\n'Allow this upload only':")
attempt("Allow once", lambda: answer.update(
    v=app._confirm_upload_allowed("This would upload something.")),
    "Allow this upload only")
print("  the operation was allowed:", answer.get("v"))
print("  params file written:", params.exists(), " uploading now:", pe._uploads_enabled())
if answer.get("v") is not True:
    failures.append("'Allow this upload only' did not allow it")
if params.exists() or pe._uploads_enabled():
    failures.append("'Allow this upload only' changed the setting")

print("\n'Turn uploading on':")
answer.clear()
attempt("Turn on", lambda: answer.update(
    v=app._confirm_upload_allowed("This would upload something.")),
    "Turn uploading on")
on_disk = json.loads(params.read_text(encoding="utf-8")) if params.exists() else {}
print("  the operation was allowed:", answer.get("v"))
print("  params file now:", on_disk)
print("  uploading now:", pe._uploads_enabled())
if answer.get("v") is not True:
    failures.append("'Turn uploading on' did not allow it")
if on_disk.get("uploads_enabled") is not True:
    failures.append(f"the setting was not written: {on_disk}")

# And with it on, no dialog at all -- the whole upload path runs untouched
print("\nWith uploading on, nothing asks:")
answer.clear()
answer["v"] = app._confirm_upload_allowed("This would upload something.")
root.update()
print("  allowed with no dialog:", answer["v"], " dialog present:", bool(find_dialog()))
if answer["v"] is not True or find_dialog():
    failures.append("the dialog still appeared after uploading was turned on")

# The whole upload path now runs.  Its worker reports progress with root.after,
# which needs a real mainloop, so what is checked here is the last thing the
# main thread does before starting it: registering the operation as in flight.
arm()
started = []
app._begin_server_op_real = app._begin_server_op
app._begin_server_op = lambda d: (started.append(d),
                                  app._begin_server_op_real(d))[1]
app._upload_current_photo()
root.update()
print("  the upload path ran:", started or "NO")
if not started:
    failures.append("with uploading on, the upload path still did not run")

# Turning it off again is just the setting going away
pe._store.set_op_param("uploads_enabled", False)
print("\nSet back to false in the file -> uploading:", pe._uploads_enabled())
if pe._uploads_enabled():
    failures.append("setting uploads_enabled false did not block again")

root.destroy()
shutil.rmtree(tmp, ignore_errors=True)
if errors:
    failures.append("exception in a tk callback:\n" + errors[0][:400])
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nUPLOAD SETTING OK — off by default, three choices, choice 3 remembered")
