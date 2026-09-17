"""Scrolling the face rows, once the pictures are in place.

Three faults reported: rows below the fold unreachable, scrolling off into
blank space above the first row, and no thumb in the vertical bar.  All three
came of a scrollregion measured while the rows still held "…" placeholders.
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

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None

W, H, FACES = 1600, 1200, 20


class Stub:
    session = None

    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        return {"id": pid, "file": "p.jpg", "name": "p.jpg", "width": W,
                "height": H, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": "https://piwigo.invalid/p.jpg"}

    def get(self, url, **kw): return Resp()


class Resp:
    def __init__(self):
        buf = BytesIO(); Image.new("RGB", (W, H), "#6688aa").save(buf, "JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


pe.AlbumHierarchy.PiwigoClient = Stub
pe.requests.get = lambda url, **kw: Resp()
pe._pick_derivative_url = lambda *a, **k: "https://piwigo.invalid/p.jpg"


def face(n):
    return {"number": n, "name": f"Person {n}",
            "box": [(n % 8)*180, (n // 8)*260, 120, 150]}


tmp = Path(tempfile.mkdtemp())
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(json.dumps(
    {"saved": "2026-08-26 10:00:00", "photo id": 11, "file": "p.jpg", "album": "A",
     "editor": "a@x", "faces": [face(n) for n in range(1, FACES + 1)],
     "comment": "", "photo date": ""}, indent=2) + "\n\n", encoding="utf-8")

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1400x500")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
app._ss_source = str(tmp)        # as _enter_ss_review would have
app._show_mode(pe.MODE_REVIEW)     # which is what builds a review
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def visible_rows():
    c = app._ss_matrix_canvas
    top, bottom = c.winfo_rooty(), c.winfo_rooty() + c.winfo_height()
    return [app._ss_rows[i]["number"] for i, l in enumerate(app._ss_face_labels)
            if l.winfo_rooty() + l.winfo_height() > top and l.winfo_rooty() < bottom]


def run():
    c = app._ss_matrix_canvas
    root.update_idletasks()
    content = app._ss_matrix_frame.winfo_reqheight()
    region = [int(v) for v in str(c.cget("scrollregion")).split()]
    print(f"{len(app._ss_rows)} rows needing {content}px in a {c.winfo_height()}px canvas")
    print(f"scrollregion: {region}\n")

    check("the region matches the rows", region[3] == content,
          f"{region[3]} vs {content}")

    lo, hi = c.yview()
    check("(3) the bar shows a thumb", (hi - lo) < 0.99, f"{hi - lo:.0%} of the bar")

    print("\n(1) reaching the rows below the fold:")
    first_view = visible_rows()
    c.yview_moveto(1.0)
    root.update_idletasks()
    last_view = visible_rows()
    print(f"   at the top:    {first_view}")
    print(f"   at the bottom: {last_view}")
    check("the last row can be reached",
          app._ss_rows[-1]["number"] in last_view, app._ss_rows[-1]["number"])
    check("and the first is no longer shown",
          app._ss_rows[0]["number"] not in last_view)

    print("\n(2) no blank space above the first row:")
    c.yview_moveto(0)
    root.update_idletasks()
    gap = app._ss_face_labels[0].winfo_rooty() - c.winfo_rooty()
    print(f"   gap at the top: {gap}px")
    check("the first row is at the top", gap < 20, f"{gap}px")

    for _ in range(5):                  # press UP repeatedly at the top
        c.yview_scroll(-1, "units")
    root.update_idletasks()
    gap_after = app._ss_face_labels[0].winfo_rooty() - c.winfo_rooty()
    print(f"   after five more UP presses: {gap_after}px")
    check("pressing up at the top opens no gap", gap_after == gap,
          f"{gap} -> {gap_after}")

    print("\nand the direction is still right:")
    c.yview_moveto(0)
    root.update_idletasks()
    before = visible_rows()[0]
    c.yview_scroll(2, "units")
    root.update_idletasks()
    after_down = visible_rows()[0]
    c.yview_scroll(-2, "units")
    root.update_idletasks()
    after_up = visible_rows()[0]
    print(f"   top row: {before} -> DOWN -> {after_down} -> UP -> {after_up}")
    check("down goes further into the list", after_down > before)
    check("up comes back", after_up == before)

    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, lambda: (app._show_ss_photo(), root.after(1800, run)))
root.after(20000, lambda: (failures.append("never ran"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nSCROLLING OK")
