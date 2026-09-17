"""A review response longer than the column is wide.

Does the cell still hold the whole thing, and does copying give all of it?
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
from CredentialStore import CredentialStore

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None

LONG = "Robert A. Heinlein (in the back, wearing the hat)"
SHORT = "Bob Tucker"


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*60, 20, 40, 50]}


tmp = Path(tempfile.mkdtemp())
rec = {"saved": "t1", "photo id": 11, "file": "p11.jpg", "album": "A",
       "editor": "a@x", "faces": [face(1, LONG), face(2, SHORT), face(3)],
       "comment": "", "photo date": ""}
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    json.dumps(rec, indent=2) + "\n\n", encoding="utf-8")

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1500x900")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
app._ss_source = str(tmp)        # as _enter_ss_review would have
app._ss_groups = pe._ss_group_by_photo(pe._collect_ss_records(tmp))
app._ss_group_index = 0
app._main_pane.pack_forget()
pane = ttk.PanedWindow(root, orient="horizontal"); pane.pack(fill="both", expand=True)
app._ss_review_frame = pane
left = ttk.Frame(pane); pane.add(left, weight=3)
right = ttk.LabelFrame(pane, text="SlideShow Record"); pane.add(right, weight=2)
app._build_editor_dialog_content(left)
app._build_ss_record_panel(right)
app._ss_set_rows_and_columns(app._ss_group)
app._ss_build_matrix(app._ss_rows, app._ss_columns)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def entries():
    out = []

    def walk(w):
        if isinstance(w, tk.Entry):
            out.append(w)
        for c in w.winfo_children():
            walk(c)
    walk(app._ss_matrix_frame)
    return out


def run():
    cells = entries()
    print(f"{len(cells)} name cells; the column is "
          f"{pe.PhotosEditor._SS_COL_WIDTH} characters wide")
    print(f"the long name is {len(LONG)} characters\n")

    cell = [c for c in cells if c.get().startswith("Robert")]
    check("the long response has a cell", len(cell) == 1)
    if not cell:
        root.destroy(); return
    cell = cell[0]

    check("the cell holds the whole thing", cell.get() == LONG, repr(cell.get()))
    check("which is longer than the column", len(cell.get()) > pe.PhotosEditor._SS_COL_WIDTH)

    print("\nhow much is actually on screen:")
    shown = cell.winfo_width()
    root.update_idletasks()
    import tkinter.font as tkfont
    fw = tkfont.Font(font=cell.cget("font")).measure(LONG)
    print(f"   cell is {shown}px, the text needs {fw}px -> "
          f"{'TRUNCATED on screen' if fw > shown else 'fits'}")

    print("\ncopying it:")
    root.clipboard_clear()
    cell.focus_set()
    cell.selection_range(0, "end")
    root.update()
    cell.event_generate("<<Copy>>")
    root.update()
    got = root.clipboard_get()
    check("the clipboard has all of it", got == LONG, repr(got))

    print("\nCtrl+A then copy, which is what a person reaches for:")
    root.clipboard_clear()
    cell.select_clear()
    cell.focus_set()
    cell.event_generate("<Control-a>", when="now")
    root.update()
    cell.event_generate("<<Copy>>")
    root.update()
    got = root.clipboard_get()
    check("Ctrl+A selected the whole name", got == LONG, repr(got))

    print("\nthe tooltip on a cell too narrow for its text:")
    hidden = app._ss_hidden_text(cell, LONG)
    check("it offers the full name", hidden == LONG, repr(hidden[:30]))
    short_cell = [c for c in cells if c.get() == SHORT][0]
    check("and stays quiet where it all fits",
          app._ss_hidden_text(short_cell, SHORT) == "",
          repr(app._ss_hidden_text(short_cell, SHORT)))

    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(400, run)
root.after(15000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nLONG NAME OK")
