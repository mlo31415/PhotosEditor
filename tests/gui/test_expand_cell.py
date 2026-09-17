"""Clicking a name boxes it and opens it out over the columns to its right."""
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


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*60, 20, 40, 50]}


def rec(saved, editor, first):
    return {"saved": saved, "photo id": 11, "file": "p11.jpg", "album": "A",
            "editor": editor, "faces": [face(1, first), face(2, "Ann Green")],
            "comment": "", "photo date": ""}


tmp = Path(tempfile.mkdtemp())
# Three reports, so the first column has two columns to its right
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in
                [rec("t1", "a@x", LONG), rec("t2", "b@x", "Bob Tucker"),
                 rec("t3", "c@x", "Forry Ackerman")]) + "\n\n", encoding="utf-8")

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
root.update(); root.update_idletasks()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def cells():
    out = []

    def walk(w):
        if isinstance(w, tk.Entry):
            out.append(w)
        for c in w.winfo_children():
            walk(c)
    walk(app._ss_matrix_frame)
    return out


def run():
    print(f"columns: {len(app._ss_columns)}")
    long_cell = [c for c in cells() if c.get() == LONG][0]
    last_col = max(int(c.grid_info()["column"]) for c in cells())
    end_cell = [c for c in cells()
                if int(c.grid_info()["column"]) == last_col][0]

    before_w = long_cell.winfo_width()
    before = long_cell.grid_info()
    print(f"\nbefore the click: width {before_w}px, column {before['column']}, "
          f"span {before.get('columnspan')}, relief {long_cell.cget('relief')}")
    check("no box yet", str(long_cell.cget("relief")) == "flat")

    print("\nclicking it:")
    long_cell.focus_set()
    root.update(); root.update_idletasks()
    after_w = long_cell.winfo_width()
    after = long_cell.grid_info()
    print(f"   width {after_w}px, span {after.get('columnspan')}, "
          f"relief {long_cell.cget('relief')}, border {long_cell.cget('bd')}")
    check("it has a box round it",
          str(long_cell.cget("relief")) == "solid" and int(long_cell.cget("bd")) == 1)
    check("it opened out to the right", after_w > before_w, f"{before_w} -> {after_w}")
    check("over the columns beyond it",
          int(after.get("columnspan", 1)) == len(app._ss_columns),
          after.get("columnspan"))
    check("it is on top of what it covers",
          app._ss_matrix_frame.winfo_children().index(long_cell) >= 0)

    import tkinter.font as tkfont
    need = tkfont.Font(font=long_cell.cget("font")).measure(LONG)
    print(f"   the name needs {need}px; {after_w}px is now given to it")
    check("more of the name fits than did", after_w > before_w)

    print("\nclicking another name:")
    other = [c for c in cells() if c.get() == "Bob Tucker"][0]
    other.focus_set()
    root.update(); root.update_idletasks()
    check("the first went back",
          str(long_cell.cget("relief")) == "flat"
          and int(long_cell.grid_info().get("columnspan", 1)) == 1,
          f"relief={long_cell.cget('relief')} span={long_cell.grid_info().get('columnspan')}")
    check("and its width is back", long_cell.winfo_width() == before_w,
          f"{before_w} -> {long_cell.winfo_width()}")
    check("the new one is open", app._ss_expanded is other)

    print("\nclicking the empty matrix:")
    app._ss_matrix_frame.event_generate("<Button-1>", x=2, y=2, when="now")
    root.update(); root.update_idletasks()
    check("nothing is left open", app._ss_expanded is None)
    check("that one went back too", str(other.cget("relief")) == "flat")

    print("\na cell in the last column has nothing to borrow:")
    end_cell.focus_set()
    root.update(); root.update_idletasks()
    check("it still gets the box", str(end_cell.cget("relief")) == "solid")
    check("but spans only itself",
          int(end_cell.grid_info().get("columnspan", 1)) == 1,
          end_cell.grid_info().get("columnspan"))

    print("\nrebuilding the matrix while one is open:")
    end_cell.focus_set(); root.update()
    app._ss_build_matrix(app._ss_rows, app._ss_columns)
    root.update()
    check("nothing is left pointing at a dead widget", app._ss_expanded is None)

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
print("\nEXPANDING CELL OK")
