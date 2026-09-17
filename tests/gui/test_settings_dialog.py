"""What the Settings window tells the user, as opposed to what it lets them
change (test_settings_edit.py covers that): the file it is reading, which
values are defaults, what will be removed, and that no credentials appear."""
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
tk.Tk.report_callback_exception = lambda self, e, v, t: errors.append(
    "".join(traceback.format_exception(e, v, t)))

tmp = Path(tempfile.mkdtemp())
params = tmp / "PhotosEditor Params.json"
params.write_text(json.dumps({"path": ".", "sync_metadata": False,
                              "refresh_representative": True,
                              "max_upload_pixels": 4000000}, indent=2),
                  encoding="utf-8")
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")

# Distinctive fake credentials sitting right beside the params file: if the
# window ever put any of them on screen, the check below would find them.
SECRET = {"url": "https://piwigo.invalid", "username": "zzuserzz",
          "password": "zzsecretzz", "verify_ssl": False}
(tmp / "Piwigo Credentials.json").write_text(json.dumps(SECRET), encoding="utf-8")

root = tk.Tk(); root.geometry("1200x800")
app = pe.PhotosEditor(root)
root.update()
failures = []


def walk(w, kinds, out=None):
    out = [] if out is None else out
    if isinstance(w, kinds):
        out.append(w)
    for c in w.winfo_children():
        walk(c, kinds, out)
    return out


def all_text(w, out=None):
    out = [] if out is None else out
    try:
        t = str(w.cget("text"))
        if t:
            out.append(t)
    except Exception:
        pass
    for c in w.winfo_children():
        all_text(c, out)
    return out


def run():
    app._show_settings()
    root.update()
    dlg = next((w for w in root.winfo_children()
                if isinstance(w, tk.Toplevel) and w.title() == "PhotosEditor Settings"), None)
    if dlg is None:
        failures.append("the window did not open"); root.destroy(); return

    labels = all_text(dlg)
    joined = " | ".join(labels)
    entries = [e.get() for e in walk(dlg, ttk.Entry)]
    print("the window says:\n")
    for line in labels:
        print("   " + (line if len(line) < 92 else line[:89] + "…"))
    print("\nentry boxes hold:", entries)

    checks = [
        ("names the params file it is reading",
         "PhotosEditor Params.json" in joined),
        ("marks the settings not in the file",
         "(default — not in the file)" in joined),
        ("shows the pixel limit in thousands, ready to edit", "4000" in entries),
        ("labels the box with its unit", "thousand pixels" in joined),
        ("shows the rate limit's default", "2.0" in entries),
        ("lists the key it does not use", "path:" in joined),
        ("warns that saving removes it", "Saving will take these out" in joined),
        ("says where the credentials are", "Piwigo Credentials.json" in joined),
        ("shows no credential value anywhere",
         not any(v in joined or v in " ".join(entries)
                 for v in (SECRET["username"], SECRET["password"], SECRET["url"]))),
        ("offers Save and Cancel", "Save" in labels and "Cancel" in labels),
        ("describes each setting",
         "Off unless the file says otherwise" in joined),
    ]
    print()
    for label, ok in checks:
        print(f"  {'ok  ' if ok else 'FAIL'} {label}")
        if not ok:
            failures.append(label)

    dlg.destroy()
    root.update()
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, run)
root.after(15000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nSETTINGS WINDOW CONTENTS OK")
