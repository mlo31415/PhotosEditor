"""The Auto Colour button.

It measures the photo and puts the answer on the Red cast slider, rather than
correcting behind the user's back: the number can then be seen, argued with,
and dragged somewhere else.  What matters here is the wiring -- that pressing
it moves the slider, that the photo on screen changes, and that Revert
Restoration still undoes it.  What the measurement is worth is settled in
tests/test_colour_and_exif.py, without a window.
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
from PIL import Image, ImageStat
from CredentialStore import CredentialStore

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.showerror = pe.messagebox.showinfo = lambda *a, **k: None
pe.messagebox.showwarning = lambda *a, **k: None
pe.messagebox.askyesno = lambda *a, **k: True

# An orange-cast scan, the fault this is all for
ORANGE = (186, 132, 88)

tmp = Path(tempfile.mkdtemp())
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe.PhotosEditor._refresh_hierarchy_on_startup = lambda self: None

root = tk.Tk(); root.geometry("1400x900")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def means(img):
    return tuple(ImageStat.Stat(img.convert("RGB")).mean)


def button(text):
    found = []

    def walk(w):
        if isinstance(w, ttk.Button) and text in str(w.cget("text")).replace("\n", " "):
            found.append(w)
        for c in w.winfo_children():
            walk(c)
    walk(root)
    return found[0] if found else None


def run():
    app._show_mode(pe.MODE_EDIT)
    root.update()

    # A photo on the editor's easel, without going near a server
    photo = Image.new("RGB", (240, 180), ORANGE)
    app._viewer_image = photo
    app._current_image_dict = {"id": 1, "file": "p1.jpg", "name": "p1.jpg"}
    app._set_restoration_base()
    app._display_photo()
    root.update()

    before = means(app._viewer_image)
    print(f"the photo starts at R{before[0]:.0f} G{before[1]:.0f} B{before[2]:.0f}")
    check("the slider starts at nothing", app._restore_red_var.get() == 0)

    btn = button("Auto")
    check("there is an Auto Colour button", btn is not None)
    btn.invoke()
    root.update()

    value = app._restore_red_var.get()
    print(f"   it set Red cast to {value:+.0f}   status: {app.status_var.get()!r}")
    check("it moved the slider", value != 0, value)
    check("and cooled rather than warmed, for an orange photo", value > 0, value)
    check("the number beside the slider agrees",
          app._restore_val_vars["Red cast"].get() == str(int(value)),
          app._restore_val_vars["Red cast"].get())
    check("the status says what it did", "Auto colour" in app.status_var.get(),
          app.status_var.get())

    root.after(600, applied)


def applied():
    root.update()
    after = means(app._viewer_image)
    print(f"the photo is now  R{after[0]:.0f} G{after[1]:.0f} B{after[2]:.0f}")
    check("the photo itself changed", abs(after[0] - ORANGE[0]) > 1,
          f"{ORANGE} -> {tuple(round(v) for v in after)}")
    check("its reds and blues are closer than they were",
          abs(after[0] - after[2]) < abs(ORANGE[0] - ORANGE[2]),
          f"{abs(after[0]-after[2]):.0f} vs {abs(ORANGE[0]-ORANGE[2])}")
    check("and it counts as an edit to be uploaded", app._photo_edited)

    # Not "Revert" alone: Editing Tools has one of those, for the geometry
    print("\nRevert Restoration puts it back:")
    button("Revert Restoration").invoke()
    root.update()
    check("the slider is back to nothing", app._restore_red_var.get() == 0,
          app._restore_red_var.get())
    back = means(app._viewer_image)
    check("and so is the photo",
          tuple(round(v) for v in back) == ORANGE,
          tuple(round(v) for v in back))

    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(500, run)
root.after(25000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nAUTO COLOUR OK")
