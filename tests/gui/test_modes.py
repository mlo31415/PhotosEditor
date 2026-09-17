"""The three modes, as tabs.

Review, Edit Photos and Move and Copy Photos replaced the Zoom/Unzoom and
Review buttons.  What has to hold: the strip and the window always agree about
which mode is showing, a switch that would lose typed work can be refused, the
Review tab opens even with nothing to review, and the mode comes back on the
next start.
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

answer = {"yes": True}
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), answer["yes"])[1]
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.showwarning = lambda t, m, **k: boxes.append(("warn", t, m))
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))
# Nothing here may reach a chooser: the Review tab must open without asking.
pe._pick_folder_by_its_files = lambda *a, **k: (_ for _ in ()).throw(
    AssertionError("a chooser was opened"))

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
LOGS = tmp / "logs"
LOGS.mkdir()
(LOGS / "SlideShow Output 2026-09-01 10.00.00.json").write_text(json.dumps(
    {"saved": "2026-09-01 10:00:00", "photo id": 11, "file": "p11.jpg",
     "album": "A", "editor": "a@x", "comment": "", "photo date": "",
     "faces": [{"number": 1, "name": "Person 1", "box": [80, 80, 120, 150]}]},
    indent=2) + "\n\n", encoding="utf-8")

EMPTY = tmp / "no logs here"
EMPTY.mkdir()

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(LOGS))

root = tk.Tk(); root.geometry("1400x700")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def tab_labels():
    return list(app._tab_widgets)


def on_strip(which=None):
    """Which mode the strip is showing as current: the one with the bar
    under it.  Read from the widgets, not from _mode, so that the strip
    disagreeing with the window is something a test can catch."""
    widgets = (which or app)._tab_widgets
    lit = [label for label, (_tab, _text, bar) in widgets.items()
           if str(bar.cget("background")) == app._TAB_BAR]
    return lit[0] if len(lit) == 1 else f"{len(lit)} tabs lit: {lit}"


def click_tab(label):
    """A real click on the tab, so the binding decides what happens."""
    app._tab_widgets[label][1].event_generate("<Button-1>")
    root.update()


def panels_up():
    return len(app._main_pane.panes())


def step_start():
    print("the strip, at rest:")
    check("three tabs, named for the modes",
          tab_labels() == list(pe._MODES), tab_labels())
    check("it opens in Move and Copy Photos", app._mode == pe.MODE_MOVE, app._mode)
    check("and the strip agrees", on_strip() == app._mode, on_strip())
    check("both thumbnail panels are up", panels_up() == 2, panels_up())
    root.after(200, step_edit)


def step_edit():
    print("\nEdit Photos drops the second panel:")
    click_tab(pe.MODE_EDIT)
    check("the mode changed", app._mode == pe.MODE_EDIT, app._mode)
    check("one panel now", panels_up() == 1, panels_up())
    click_tab(pe.MODE_MOVE)
    check("and Move and Copy brings it back", panels_up() == 2, panels_up())
    root.after(200, step_review)


def step_review():
    print("\nReview opens on the reports:")
    click_tab(pe.MODE_REVIEW)
    root.update()
    check("the mode changed", app._mode == pe.MODE_REVIEW, app._mode)
    check("the split screen is up", app._ss_review_frame is not None)
    check("with the report's photo", app._ss_groups
          and app._ss_groups[0][0]["photo id"] == 11,
          [g[0]["photo id"] for g in app._ss_groups])
    root.after(1200, step_refuse)


def step_refuse():
    print("\nleaving Review with something typed can be refused:")
    app._photo_edited = True
    boxes.clear()
    answer["yes"] = False                   # no, don't throw my edits away
    click_tab(pe.MODE_MOVE)
    check("it asked", any(b[1] == "Not Uploaded Yet" for b in boxes),
          str([b[1] for b in boxes]))
    check("the mode did not change", app._mode == pe.MODE_REVIEW, app._mode)
    check("and the strip was put back", on_strip() == pe.MODE_REVIEW, on_strip())

    print("\n...and allowed:")
    boxes.clear()
    answer["yes"] = True
    click_tab(pe.MODE_MOVE)
    check("it asked again", any(b[1] == "Not Uploaded Yet" for b in boxes))
    check("this time it went", app._mode == pe.MODE_MOVE, app._mode)
    check("the strip agrees", on_strip() == pe.MODE_MOVE, on_strip())
    app._photo_edited = False
    root.after(200, step_empty)


def step_empty():
    print("\nReview with nothing to review still opens:")
    pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(EMPTY))
    boxes.clear()
    click_tab(pe.MODE_REVIEW)
    root.update()
    check("the tab is showing", app._mode == pe.MODE_REVIEW, app._mode)
    check("the split screen is up", app._ss_review_frame is not None)
    check("nothing was asked", not boxes, str([b[1] for b in boxes]))
    check("no photos in the queue", app._ss_groups == [], app._ss_groups)
    check("and it says so", "No photos in the queue" in app._ss_count_var.get(),
          app._ss_count_var.get())
    check("with the status pointing somewhere", "No unreviewed" in app.status_var.get(),
          app.status_var.get())
    root.after(400, step_remembered)


def step_remembered():
    print("\nthe mode is remembered:")
    app._show_mode(pe.MODE_EDIT)
    root.update()
    app._finish_close()                      # saves the state and destroys
    saved = json.loads(pe.STATE_FILE.read_text(encoding="utf-8"))
    check("the state file holds the mode",
          saved.get(pe.MODE_KEY) == pe.MODE_EDIT, saved.get(pe.MODE_KEY))
    check("which is not the window's own maximised flag",
          "zoomed" in saved and saved["zoomed"] != pe.MODE_EDIT,
          saved.get("zoomed"))

    # A second window, started from that state file
    second = tk.Tk(); second.geometry("1000x600")
    again = pe.PhotosEditor(second)
    second.update()
    second.after(400, lambda: finish(second, again))


def finish(second, again):
    second.update()
    check("it opens in the mode it was left in", again._mode == pe.MODE_EDIT,
          again._mode)
    check("the strip shows it too", on_strip(again) == pe.MODE_EDIT,
          on_strip(again))
    check("and only one panel is up", len(again._main_pane.panes()) == 1,
          len(again._main_pane.panes()))
    if errors:
        failures.append("an exception escaped")
    second.destroy()


root.after(400, step_start)
root.after(40000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nMODES OK")
