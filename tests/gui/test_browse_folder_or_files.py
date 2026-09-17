"""The two Browse buttons: a whole folder, or particular logs.

A folder means every log in it; Files… means those logs and no others.  Both
choosers show the files, so neither can be confirmed by luck, and choosing
something with no review logs in it warns instead of quietly taking it.
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

pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), True)[1]
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))
pe.messagebox.showwarning = lambda t, m, **k: boxes.append(("warn", t, m))

# The choosers, answered from here.  askdirectory must never be reached: a
# folder chooser shows no files, which is what sent us to these in the first place.
picks, asked = {"one": "", "many": ()}, {}
pe.filedialog.askopenfilename = lambda **k: (asked.update(k), picks["one"])[1]
pe.filedialog.askopenfilenames = lambda **k: (asked.update(k), picks["many"])[1]
pe.filedialog.askdirectory = lambda **k: (_ for _ in ()).throw(
    AssertionError("the folder chooser was opened"))

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
A, EMPTY = tmp / "logs", tmp / "nothing here"
A.mkdir(); EMPTY.mkdir()
(EMPTY / "notes.txt").write_text("not a log", encoding="utf-8")

logs = []
for n, pid in enumerate((11, 22), start=1):
    p = A / f"SlideShow Output 2026-09-0{n} 10.00.00.json"
    p.write_text(json.dumps(
        {"saved": f"2026-09-0{n} 10:00:00", "photo id": pid, "file": f"p{pid}.jpg",
         "album": "A", "editor": "a@x", "comment": "", "photo date": "",
         "faces": [{"number": 1, "name": f"Person {pid}", "box": [80, 80, 120, 150]}]},
        indent=2) + "\n\n", encoding="utf-8")
    logs.append(p)

# A log already finished with.  It carries the prefix, which takes it out of
# the pattern, so it must not be counted or offered for review again.
done_log = A / (pe.SS_COMPLETED_PREFIX + "SlideShow Output 2026-08-30 10.00.00.json")
done_log.write_text(logs[0].read_text(encoding="utf-8"), encoding="utf-8")

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

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


def folder_box(dlg):
    """The widest Entry: the one the folder setting uses."""
    return max(walk(dlg, ttk.Entry), key=lambda e: int(e.cget("width")))


def stored():
    return pe._store.load_op_params().get(pe.SS_REVIEW_DIR_KEY)


def photos_in_review():
    return sorted(g[0].get("photo id") for g in app._ss_groups)


def step_folder():
    print("Folder… takes the whole folder:")
    app._show_settings(); root.update()
    dlg = dialog()
    check("both buttons are there",
          any(str(b.cget("text")) == "Folder…" for b in walk(dlg, ttk.Button))
          and any(str(b.cget("text")) == "Files…" for b in walk(dlg, ttk.Button)),
          [str(b.cget("text")) for b in walk(dlg, ttk.Button)])
    picks["one"] = str(logs[0])            # a file in it names the folder
    boxes.clear(); asked.clear()
    press(dlg, "Folder…"); root.update()
    check("the box holds the folder", folder_box(dlg).get() == str(A),
          folder_box(dlg).get())
    # It is a file chooser on purpose: a folder chooser shows no files, so it
    # cannot be used to tell the right folder from an empty one.
    kinds = asked.get("filetypes") or []
    check("filtered to the SlideShow logs",
          any(pe.SS_LOG_GLOB in str(k) for k in kinds), str(kinds))
    check("with an escape hatch for anything else",
          any("*.*" in str(k) for k in kinds), str(kinds))
    check("the title says to pick a file in the folder",
          "file in the folder" in str(asked.get("title")), str(asked.get("title")))
    check("it says what that amounts to",
          "every" in pe._ss_choice_summary(folder_box(dlg).get(), pe.SS_LOG_GLOB)[0],
          pe._ss_choice_summary(folder_box(dlg).get(), pe.SS_LOG_GLOB)[0])
    press(dlg, "Save"); root.update()
    check("the folder is stored as a folder", stored() == str(A), stored())
    app._enter_ss_review(); root.update()
    check("the review has both logs' photos", photos_in_review() == [11, 22],
          photos_in_review())
    root.after(1200, step_files)


def step_files():
    print("\nFiles… takes just those logs:")
    app._show_settings(); root.update()
    dlg = dialog()
    picks["many"] = (str(logs[1]),)
    boxes.clear(); asked.clear()
    press(dlg, "Files…"); root.update()
    check("it opened where the setting already pointed",
          str(asked.get("initialdir")) == str(A), asked.get("initialdir"))
    check("the box holds the file", folder_box(dlg).get() == str(logs[1]),
          folder_box(dlg).get())
    check("it says that one only",
          pe._ss_choice_summary(folder_box(dlg).get(), pe.SS_LOG_GLOB)[0]
          == "that one file only")
    press(dlg, "Save"); root.update()
    check("it is stored as a list of files", stored() == [str(logs[1])], stored())
    root.after(1500, step_files_applied)


def step_files_applied():
    check("the review now has only that log's photo", photos_in_review() == [22],
          photos_in_review())
    root.after(100, step_warnings)


def step_warnings():
    print("\nchoosing something with no review logs in it warns:")
    app._show_settings(); root.update()
    dlg = dialog()
    before = folder_box(dlg).get()

    picks["many"] = (str(EMPTY / "notes.txt"),)
    boxes.clear()
    press(dlg, "Files…"); root.update()
    check("Files… warned", any(b[0] == "warn" for b in boxes),
          str([(b[0], b[1]) for b in boxes]))
    check("and changed nothing", folder_box(dlg).get() == before,
          folder_box(dlg).get())

    picks["one"] = str(EMPTY / "notes.txt")     # a folder holding no logs
    boxes.clear()
    press(dlg, "Folder…"); root.update()
    check("Folder… warned", any(b[0] == "warn" for b in boxes),
          str([(b[0], b[1]) for b in boxes]))
    check("and changed nothing", folder_box(dlg).get() == before,
          folder_box(dlg).get())

    print("\nsome logs among other files: the others are left out, and said so:")
    picks["many"] = (str(logs[0]), str(EMPTY / "notes.txt"))
    boxes.clear()
    press(dlg, "Files…"); root.update()
    check("the log was taken", folder_box(dlg).get() == str(logs[0]),
          folder_box(dlg).get())
    check("and the other named", any(b[0] == "info" and "notes.txt" in b[2]
                                     for b in boxes),
          str([(b[0], b[1]) for b in boxes]))

    print("\nand what the line under the box says about a path typed by hand:")
    box = folder_box(dlg)
    box.delete(0, "end"); box.insert(0, str(tmp / "nowhere")); root.update()
    check("a folder that is not there is called out",
          pe._ss_choice_summary(box.get(), pe.SS_LOG_GLOB)[1] == "#a04000",
          pe._ss_choice_summary(box.get(), pe.SS_LOG_GLOB)[0])
    check("a finished log is not counted -- it is out of the review",
          pe._count_matching(str(A), pe.SS_LOG_GLOB) == 2,
          pe._count_matching(str(A), pe.SS_LOG_GLOB))
    press(dlg, "Cancel"); root.update()
    root.after(100, done)


def done():
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(400, step_folder)
root.after(40000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nFOLDER-OR-FILES OK")
