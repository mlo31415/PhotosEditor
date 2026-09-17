"""The names and comments in the SlideShow Record columns can be selected and
copied.  Drives the real widgets and the real clipboard."""
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

NAME = "Bob Tucker"
COMMENT = "the third from the left is definitely not Forry Ackerman"


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*60, 20, 40, 50]}


tmp = Path(tempfile.mkdtemp())
rec = {"saved": "t1", "photo id": 11, "file": "p11.jpg", "album": "A",
       "editor": "a@x", "faces": [face(1, NAME), face(2), face(3)],
       "comment": COMMENT, "photo date": ""}
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


def widgets(kinds):
    out = []

    def walk(w):
        if isinstance(w, kinds):
            out.append(w)
        for c in w.winfo_children():
            walk(c)
    # The names are in the scrolling rows; the comments are in the heading,
    # which is frozen above them
    walk(app._ss_matrix_frame)
    walk(app._ss_header_frame)
    return out


def run():
    entries = [e for e in widgets(tk.Entry)]
    texts = [t for t in widgets(tk.Text)]
    print("in the matrix:", len(entries), "name cells,", len(texts), "comment boxes")

    check("the name is in a selectable widget", len(entries) == 1)
    name_cell = entries[0]
    check("it holds the name", name_cell.get() == NAME, name_cell.get())
    check("it cannot be typed into", str(name_cell.cget("state")) == "readonly")
    check("it has no border to spoil the table",
          str(name_cell.cget("relief")) == "flat" and int(name_cell.cget("bd")) == 0)

    check("the comment is in a selectable widget", len(texts) == 1)
    comment = texts[0]
    check("it holds the comment",
          comment.get("1.0", "end").strip() == COMMENT,
          comment.get("1.0", "end").strip()[:40])
    check("it cannot be typed into", str(comment.cget("state")) == "disabled")

    print("\ncopying the name to the clipboard, as select-all + Ctrl+C would:")
    root.clipboard_clear()
    name_cell.focus_set()
    name_cell.selection_range(0, "end")
    root.update()
    name_cell.event_generate("<<Copy>>")
    root.update()
    got = root.clipboard_get()
    check("the clipboard has the name", got == NAME, repr(got))

    print("\nand pasting it into the Caption:")
    app.custom_vars["comments"].delete("1.0", "end")
    app.custom_vars["comments"].focus_set()
    app.custom_vars["comments"].event_generate("<<Paste>>")
    root.update()
    pasted = app.custom_vars["comments"].get("1.0", "end").strip()
    check("it arrived", pasted == NAME, repr(pasted))

    print("\ncopying from the comment:")
    root.clipboard_clear()
    comment.focus_set()
    comment.tag_add("sel", "1.0", "end-1c")
    root.update()
    comment.event_generate("<<Copy>>")
    root.update()
    got = root.clipboard_get().strip()
    check("the clipboard has the comment", got == COMMENT, repr(got[:40]))

    print("\nthe hover tint still reaches the name cell:")
    app._ss_set_hover(0)
    root.update()
    shown = str(name_cell.cget("readonlybackground"))
    check("it lights up with the row", shown.lower() == pe._SS_ROW_HL_BG.lower(), shown)
    app._ss_set_hover(None)
    root.update()
    check("and goes back",
          str(name_cell.cget("readonlybackground")) == app._ss_faces_bg,
          str(name_cell.cget("readonlybackground")))

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
print("\nCOPYABLE OK — names and comments select, copy and paste")
