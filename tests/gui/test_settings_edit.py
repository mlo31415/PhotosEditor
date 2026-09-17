"""Editing settings in the real window: save, cancel, bad input, and the
refusal to restart over unsaved work.  Its own params file in a temp folder."""
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

errors, boxes = [], []


def _report(self, exc, val, tb):
    errors.append("".join(traceback.format_exception(exc, val, tb)))
    print("!! exception:\n", errors[-1], flush=True)


tk.Tk.report_callback_exception = _report
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
answer = {"yes": True}
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), answer["yes"])[1]

tmp = Path(tempfile.mkdtemp())
params = tmp / "PhotosEditor Params.json"
START = {"path": ".", "sync_metadata": False, "refresh_representative": True,
         "max_upload_pixels": 4000000}
params.write_text(json.dumps(START, indent=2), encoding="utf-8")
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"   # keep the real one out of it

root = tk.Tk(); root.geometry("1200x800")
app = pe.PhotosEditor(root)
root.update()
failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + detail) if detail else ''}")
    if not ok:
        failures.append(label)


def dialog():
    return next((w for w in root.winfo_children()
                 if isinstance(w, tk.Toplevel) and w.title() == "PhotosEditor Settings"), None)


def widgets(dlg, cls):
    out = []

    def walk(w):
        if isinstance(w, cls):
            out.append(w)
        for c in w.winfo_children():
            walk(c)
    walk(dlg)
    return out


def press(dlg, text):
    for b in widgets(dlg, ttk.Button):
        if str(b.cget("text")) == text:
            b.invoke(); return True
    return False


def entries(dlg):
    return widgets(dlg, ttk.Entry)


def checks(dlg):
    return widgets(dlg, ttk.Checkbutton)


def on_disk():
    return json.loads(params.read_text(encoding="utf-8"))


def step_cancel():
    print("\nCancel throws the edits away:")
    app._show_settings(); root.update()
    dlg = dialog()
    checks(dlg)[0].invoke()                       # tick "Uploading enabled"
    entries(dlg)[0].delete(0, "end"); entries(dlg)[0].insert(0, "123")
    root.update()
    press(dlg, "Cancel"); root.update()
    check("the window closed", dialog() is None)
    check("the file is untouched", on_disk() == START, str(on_disk()))
    root.after(100, step_bad)


def step_bad():
    print("\nbad input is refused and the window stays open:")
    app._show_settings(); root.update()
    dlg = dialog()
    boxes.clear()
    entries(dlg)[0].delete(0, "end"); entries(dlg)[0].insert(0, "lots")
    press(dlg, "Save"); root.update()
    check("an error was shown", any(b[0] == "error" for b in boxes),
          boxes[0][2] if boxes else "")
    check("the window is still open", dialog() is not None)
    check("nothing was written", on_disk() == START)
    press(dlg, "Cancel"); root.update()
    root.after(100, step_save)


def step_save():
    print("\nSave writes, drops the unused key, and takes effect at once:")
    print("   uploading before:", pe._uploads_enabled())
    app._show_settings(); root.update()
    dlg = dialog()
    boxes.clear()
    checks(dlg)[0].invoke()                        # Uploading enabled -> on
    entries(dlg)[0].delete(0, "end"); entries(dlg)[0].insert(0, "2,500")
    press(dlg, "Save"); root.update()
    saved = on_disk()
    check("the window closed", dialog() is None)
    check("uploading is now on in the file", saved.get("uploads_enabled") is True)
    check("2,500 thousand became 2,500,000 pixels in the file",
          saved.get("max_upload_pixels") == 2500000, str(saved.get("max_upload_pixels")))
    check("the unused key is gone", "path" not in saved, str(sorted(saved)))
    check("in force immediately, with no restart", pe._uploads_enabled() is True)
    check("no restart was offered", not any("Restart" in b[1] for b in boxes))
    status = app.status_var.get() if hasattr(app, "status_var") else "?"
    print("   status line:", status)
    check("the status names what changed, not raw keys",
          "uploading enabled" in status and "path" not in status, status)
    check("and mentions the removal", "1 unused setting removed" in status, status)
    root.after(100, step_nochange)


def step_nochange():
    print("\nsaving without changing anything does nothing:")
    before = params.stat().st_mtime_ns
    app._show_settings(); root.update()
    boxes.clear()
    press(dialog(), "Save"); root.update()
    check("the window closed", dialog() is None)
    check("the file was not rewritten", params.stat().st_mtime_ns == before)
    root.after(100, step_restart)


def step_restart():
    print("\na setting that DID need a restart (pretending one does):")
    real = pe._OP_PARAMS[:]
    pe._OP_PARAMS[0] = pe._OP_PARAMS[0]._replace(restart_needed=True)

    # with unsaved work, it must not offer to restart
    app._photo_edited = True
    boxes.clear()
    answer["yes"] = True
    app._offer_restart(["Uploading enabled"])
    root.update()
    kinds = [b[0] for b in boxes]
    check("told, not asked, while work is unsaved", kinds == ["info"], str(kinds))
    check("it says why", "edited and not uploaded" in boxes[0][2] if boxes else False)
    check("and that the setting is saved anyway",
          "will apply the next time" in boxes[0][2] if boxes else False)
    check("no restart was armed", app._relaunch_on_exit is False)

    # with nothing unsaved, it asks
    app._photo_edited = False
    app._loaded_fields = app._editor_field_values() if app.custom_vars else {}
    boxes.clear()
    answer["yes"] = False                      # say no to restarting
    app._offer_restart(["Uploading enabled"])
    root.update()
    check("asked when nothing would be lost",
          any(b[0] == "ask" for b in boxes), str([b[1] for b in boxes]))
    check("answering no arms nothing", app._relaunch_on_exit is False)

    pe._OP_PARAMS[:] = real
    root.after(100, done)


def done():
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, step_cancel)
root.after(25000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nSETTINGS EDITING OK")
