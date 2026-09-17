"""Pressing Upload, being told uploading is off, and choosing 'Continue
without uploading' settles the work: moving to the next photo must not then ask
'Not Uploaded Yet'.  Nothing reaches the network."""
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
    errors.append("".join(traceback.format_exception(exc, val, tb)))
    print("!! exception in a tk callback:\n", errors[-1], flush=True)


tk.Tk.report_callback_exception = _report

tmp = Path(tempfile.mkdtemp())
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"   # keep the real one out of it     # uploading off


class NoServer:
    def __init__(self, *a, **k):
        raise AssertionError("reached the server!")


pe.AlbumHierarchy.PiwigoClient = NoServer
asked = []
pe.messagebox.askyesno = lambda title, message, **k: (asked.append(title), True)[1]
pe.messagebox.showerror = lambda *a, **k: asked.append(("ERROR", a))
pe.messagebox.showwarning = lambda *a, **k: asked.append(("WARN", a))


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*60, 20, 40, 50]}


def rec(pid, saved, editor=""):
    return {"saved": saved, "photo id": pid, "file": f"p{pid}.jpg", "album": "A",
            "editor": editor, "faces": [face(1, "Bob")], "comment": "", "photo date": ""}


log = tmp / "SlideShow Output 2026-08-28 20.00.00.json"
log.write_text("\n\n".join(json.dumps(r, indent=2)
                           for r in [rec(11, "t1", "a@x"), rec(22, "t2", "b@x")]) + "\n\n",
               encoding="utf-8")

root = tk.Tk(); root.geometry("1400x800")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
app._ss_source = str(tmp)        # as _enter_ss_review would have
app._show_mode(pe.MODE_REVIEW)     # which is what builds a review
root.update()

# A photo is on screen, exactly as a real load leaves it
app._viewer_image = Image.new("RGB", (40, 30), "#808080")
app._current_image_dict = {"id": 11, "file": "tmp2qfmcfwp.JPG", "name": "PICT0943.JPG",
                           "width": 40, "height": 30,
                           "categories": [{"id": 77, "name": "Some Album"}]}
app._loaded_fields = app._editor_field_values()
app._photo_edited = False

failures, seen = [], {}


def click_dialog(label, then):
    """Wait for the blocked dialog, press the button starting with `label`."""
    def go(tries=[0]):
        dlg = next((w for w in root.winfo_children()
                    if isinstance(w, tk.Toplevel) and w.title() == "Uploading Is Turned Off"),
                   None)
        if dlg is None:
            tries[0] += 1
            if tries[0] < 40:
                root.after(50, go)
            else:
                failures.append("the blocked dialog never appeared")
                root.destroy()
            return
        seen["dialog text"] = [w.cget("text") for w in dlg.winfo_children()[0].winfo_children()]
        btn = [b for b in dlg.winfo_children()[1].winfo_children()
               if str(b.cget("text")).startswith(label)][0]
        btn.invoke()
        root.after(50, then)
    root.after(50, go)


def step1():
    # Type into the Caption, the way the report asks you to
    app.custom_vars["comments"].insert("1.0", "Bob Tucker, second from the left")
    root.update()
    seen["unsaved before"] = app._unsaved_field_labels()
    print("typed into Caption; unsaved fields:", seen["unsaved before"])
    click_dialog("Continue without", step2)
    app._upload_current_photo()


def step2():
    root.update()
    seen["what the dialog said"] = seen.get("dialog text")
    print("the blocked dialog said:", seen["what the dialog said"])
    seen["unsaved after"] = app._unsaved_field_labels()
    seen["photo edited after"] = app._photo_edited
    print("after 'Continue without uploading', unsaved fields:", seen["unsaved after"])
    print("status:", app.status_var.get() if hasattr(app, "status_var") else "(n/a)")

    # Now go to the next photo: nothing should be asked
    asked.clear()
    app._ss_step(+1)
    root.update()
    seen["asked on next"] = [a for a in asked if isinstance(a, str)]
    seen["moved to"] = app._ss_group[0]["photo id"] if app._ss_group else None
    print("moving to the next photo asked:", seen["asked on next"] or "nothing")
    print("now showing photo:", seen["moved to"])
    root.after(50, check)


def check():
    try:
        assert seen["unsaved before"] == ["Caption"], seen["unsaved before"]
        assert seen["unsaved after"] == [], seen["unsaved after"]
        assert seen["photo edited after"] is False
        assert seen["asked on next"] == [], seen["asked on next"]
        assert seen["moved to"] == 22, seen["moved to"]
        # and the dialog named the photo by something meaningful
        text = " ".join(str(t) for t in seen["what the dialog said"])
        assert "PICT0943.JPG" in text, text
        assert "tmp2qfmcfwp" not in text, text
        assert not errors, errors[0][:300]
    except AssertionError as e:
        failures.append(str(e))
    root.destroy()


root.after(200, step1)
root.after(15000, lambda: (failures.append("never reached the checks"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nDECLINING SETTLES THE WORK — no 'Not Uploaded Yet' on the next photo")
