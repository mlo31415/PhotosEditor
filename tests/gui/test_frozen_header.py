"""The column headings stay put while the face rows scroll under them."""
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


def face(n, name=""):
    return {"number": n, "name": name, "box": [n*40, 20, 30, 40]}


FACES = 40
tmp = Path(tempfile.mkdtemp())
recs = [{"saved": f"2026-08-2{i} 10:00:00", "photo id": 11, "file": "p11.jpg",
         "album": "A", "editor": f"{c}@example.com",
         "faces": [face(n, f"Person {n}{c}") for n in range(1, FACES + 1)],
         "comment": "a note about this photo", "photo date": ""}
        for i, c in enumerate("ab", start=1)]
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in recs) + "\n\n", encoding="utf-8")

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1400x420")
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


def x_boxes():
    out = []

    def walk(w):
        try:
            if str(w.cget("text")) == "✕":
                out.append(w)
        except Exception:
            pass
        for c in w.winfo_children():
            walk(c)
    walk(app._ss_header_frame)
    return out


def top_row():
    top = app._ss_matrix_canvas.winfo_rooty()
    for i, lbl in enumerate(app._ss_face_labels):
        if lbl.winfo_rooty() + lbl.winfo_height() > top:
            return app._ss_rows[i]["number"]
    return None


def run():
    canvas = app._ss_matrix_canvas
    boxes = x_boxes()
    print(f"{len(app._ss_rows)} rows, {len(app._ss_columns)} columns; "
          f"{len(boxes)} ✕ boxes, all in the frozen heading")
    check("the ✕ boxes live in the heading, not the rows", len(boxes) == 2)
    check("there is real scrolling to do",
          app._ss_matrix_frame.winfo_reqheight() > canvas.winfo_height(),
          f"{app._ss_matrix_frame.winfo_reqheight()} vs {canvas.winfo_height()}")

    box_before = boxes[0].winfo_rooty()
    row_before = top_row()
    print(f"\nbefore scrolling: ✕ at y={box_before}, top row #{row_before}")

    canvas.yview_moveto(0.5)
    root.update_idletasks()
    box_after = boxes[0].winfo_rooty()
    row_after = top_row()
    print(f"after scrolling:  ✕ at y={box_after}, top row #{row_after}")

    check("THE HEADING STAYED PUT", box_after == box_before,
          f"{box_before} -> {box_after}")
    check("the rows moved under it", row_after != row_before,
          f"#{row_before} -> #{row_after}")
    check("the heading is still on screen",
          box_after >= app._ss_header_canvas.winfo_rooty())

    print("\nthe heading is above the rows, not overlapping them:")
    head_bottom = (app._ss_header_canvas.winfo_rooty()
                   + app._ss_header_canvas.winfo_height())
    check("rows start below the heading", canvas.winfo_rooty() >= head_bottom,
          f"heading ends {head_bottom}, rows start {canvas.winfo_rooty()}")

    print("\ncolumns line up between the two:")
    for c in range(1, len(app._ss_columns) + 1):
        head_box = app._ss_header_frame.grid_bbox(column=c, row=0)
        body_box = app._ss_matrix_frame.grid_bbox(column=c, row=0)
        print(f"   column {c}: heading x={head_box[0]} w={head_box[2]}, "
              f"rows x={body_box[0]} w={body_box[2]}")
        check(f"column {c} starts at the same x", head_box[0] == body_box[0],
              f"{head_box[0]} vs {body_box[0]}")

    print("\nscrolling sideways moves both together:")
    canvas.xview_moveto(0.3)
    app._ss_header_canvas.xview_moveto(0.3)
    root.update_idletasks()
    check("they agree", abs(canvas.xview()[0] - app._ss_header_canvas.xview()[0]) < 0.01,
          f"{canvas.xview()[0]:.3f} vs {app._ss_header_canvas.xview()[0]:.3f}")

    print("\nthe wheel still scrolls the rows:")
    canvas.yview_moveto(0.4)
    root.update_idletasks()
    before = canvas.yview()[0]
    canvas.event_generate("<Enter>", when="now"); root.update()
    canvas.event_generate("<MouseWheel>", delta=120, when="now")
    root.update_idletasks()
    check("wheel up goes toward the top", canvas.yview()[0] < before,
          f"{before:.3f} -> {canvas.yview()[0]:.3f}")

    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(500, run)
root.after(15000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nFROZEN HEADER OK")
