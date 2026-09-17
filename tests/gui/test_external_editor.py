"""The round trip out to another program and back.

A stand-in editor does the work of a real one: a small script that is handed
the file and either saves over it or does not.  That lets the three cases be
driven exactly -- saved, not saved, and the one that catches people out, an
editor that exits the moment it is launched because an instance of it was
already running.
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
from PIL import Image, ImageStat
from CredentialStore import CredentialStore

errors, asked = [], []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.showerror = pe.messagebox.showinfo = lambda *a, **k: None
pe.messagebox.showwarning = lambda *a, **k: None
answer = {"yes": True}
pe.messagebox.askyesno = lambda t, m, **k: (asked.append(t), answer["yes"])[1]

tmp = Path(tempfile.mkdtemp())
pe._SCRIPT_DIR = tmp
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe.PhotosEditor._refresh_hierarchy_on_startup = lambda self: None

# The stand-in editor.  "paint" rewrites the file a different colour and stays
# up; "look" changes nothing and stays up; "handoff" exits at once, the way a
# single-instance editor does when a copy of it is already running.
TOOL = tmp / "Stand In Editor.py"
TOOL.write_text(
    "import sys, time\n"
    "from PIL import Image\n"
    "what, path = sys.argv[1], sys.argv[2]\n"
    "if what == 'paint':\n"
    "    img = Image.open(path); img.load()\n"
    "    Image.new('RGB', img.size, (20, 60, 200)).save(path)\n"
    "if what != 'handoff':\n"
    "    time.sleep(30)\n", encoding="utf-8")

ORIGINAL_COLOUR = (200, 60, 20)
PAINTED_COLOUR = (20, 60, 200)

root = tk.Tk(); root.geometry("1200x800")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def colour_now():
    return tuple(round(v) for v in ImageStat.Stat(app._viewer_image.convert("RGB")).mean)


def load_photo():
    app._show_mode(pe.MODE_EDIT)
    root.update()
    app._on_photo_loaded(Image.new("RGB", (120, 90), ORIGINAL_COLOUR),
                         {"id": 7, "file": "Chicon 1962.jpg",
                          "name": "Chicon 1962.jpg", "width": 120, "height": 90},
                         b"")
    root.update()


def stand_in(mode):
    """A command line that behaves like an editor of the given kind."""
    return [sys.executable, str(TOOL), mode]


def waiting_dialog():
    for w in root.winfo_children():
        if isinstance(w, tk.Toplevel) and w.winfo_exists() \
                and "Editing in" in str(w.title()):
            return w
    return None


def press(dlg, text):
    def walk(w):
        if isinstance(w, ttk.Button) and str(w.cget("text")) == text:
            return w
        for c in w.winfo_children():
            got = walk(c)
            if got:
                return got
    return walk(dlg)


def drive(mode, button, after):
    """Run one round trip: launch the stand-in, wait for the dialog, press."""
    load_photo()
    real_popen = pe.subprocess.Popen
    pe.subprocess.Popen = lambda argv, *a, **k: real_popen(
        stand_in(mode) + [argv[1]], *a, **k)
    root.after(1500, lambda: finish_round(button, after))
    try:
        app._run_external_edit(str(TOOL))       # any existing file will do
    finally:
        pe.subprocess.Popen = real_popen


def finish_round(button, after):
    dlg = waiting_dialog()
    if dlg is None:
        failures.append("the waiting dialog never appeared")
        root.destroy()
        return
    btn = press(dlg, button)
    if btn is None:
        failures.append(f"no {button} button on the waiting dialog")
        root.destroy()
        return
    btn.invoke()
    root.after(400, after)


def step_saved():
    print("the other program saves, and the changes come back:")
    drive("paint", "Done", step_saved_checked)


def step_saved_checked():
    root.update()
    check("the photo here is what was saved there",
          colour_now() == PAINTED_COLOUR, colour_now())
    check("and it counts as an edit to be uploaded", app._photo_edited)
    check("undo is offered", str(app.undo_btn.cget("state")) == "normal")
    app._undo_edit(); root.update()
    check("and undo puts the original back", colour_now() == ORIGINAL_COLOUR,
          colour_now())
    root.after(300, step_not_saved)


def step_not_saved():
    print("\nthe other program saves nothing, and nothing changes here:")
    drive("look", "Done", step_not_saved_checked)


def step_not_saved_checked():
    root.update()
    check("the photo is untouched", colour_now() == ORIGINAL_COLOUR, colour_now())
    check("and it is not marked as edited", not app._photo_edited)
    check("the status says so", "unchanged" in app.status_var.get(),
          app.status_var.get())
    root.after(300, step_cancel)


def step_cancel():
    print("\nCancel after a save asks, and throws the save away:")
    asked.clear()
    answer["yes"] = True                     # yes, discard them
    drive("paint", "Cancel", step_cancel_checked)


def step_cancel_checked():
    root.update()
    check("it asked before discarding", any("Discard" in a for a in asked), asked)
    check("the photo here is unchanged", colour_now() == ORIGINAL_COLOUR,
          colour_now())
    check("and is not marked as edited", not app._photo_edited)
    root.after(300, step_handoff)


def step_handoff():
    print("\nan editor that exits at once is still waited for:")
    load_photo()
    real_popen = pe.subprocess.Popen
    pe.subprocess.Popen = lambda argv, *a, **k: real_popen(
        stand_in("handoff") + [argv[1]], *a, **k)
    root.after(1800, check_handoff)
    try:
        app._run_external_edit(str(TOOL))
    finally:
        pe.subprocess.Popen = real_popen


def check_handoff():
    dlg = waiting_dialog()
    check("the dialog is still up, not closed by the exit", dlg is not None)
    if dlg is not None:
        press(dlg, "Cancel").invoke()
    root.after(400, done)


def done():
    root.update()
    check("the tool was remembered as the last one used",
          pe._store.load_op_params().get(pe.EXTERNAL_EDITOR_LAST) == str(TOOL),
          pe._store.load_op_params().get(pe.EXTERNAL_EDITOR_LAST))
    check("nothing was left in the temp folder",
          not list(Path(tempfile.gettempdir()).glob("PE-edit-*")),
          [p.name for p in Path(tempfile.gettempdir()).glob("PE-edit-*")])
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(500, step_saved)
root.after(60000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nEXTERNAL EDITOR ROUND TRIP OK")
