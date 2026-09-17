"""Review mode: arrow keys walk the photos, the wait cursor covers the fetch,
and the column X sits beside its heading.  No server: the client is a stub."""
import sys, json, shutil, tempfile, traceback, importlib.util, time
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

errors = []


def _report(self, exc, val, tb):
    text = "".join(traceback.format_exception(exc, val, tb))
    errors.append(text)
    print("!! exception in a tk callback:\n", text, flush=True)


tk.Tk.report_callback_exception = _report

asked = []
pe.messagebox.askyesno = lambda title, message, **k: (asked.append(title), True)[1]
pe.messagebox.showerror = lambda *a, **k: asked.append(("ERROR", a))
pe.messagebox.showwarning = lambda *a, **k: asked.append(("WARN", a))


def face(n, name=""):
    return {"number": n, "name": name, "box": [n * 60, 20, 40, 50]}


def rec(pid, saved, comment="", faces=(), editor=""):
    return {"saved": saved, "photo id": pid, "file": f"p{pid}.jpg",
            "album": "Worldcons/Noreascon 3 (1989)", "editor": editor,
            "faces": list(faces), "comment": comment, "photo date": ""}


tmp = Path(tempfile.mkdtemp())
records = [rec(11, "t1", faces=[face(1, "Bob Tucker"), face(2)], editor="a@x"),
           rec(11, "t2", faces=[face(1), face(2, "Ann Green")], editor="b@x",
               comment="not sure about the one on the left"),
           rec(22, "t3", faces=[face(1, "Ellen Klages")], editor="c@x"),
           rec(33, "t4", faces=[face(1, "Forry Ackerman")], editor="d@x")]
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    "\n\n".join(json.dumps(r, indent=2) for r in records) + "\n\n", encoding="utf-8")


# A client whose photo fetch is deliberately slow, so the wait cursor is
# observable while it is in flight
class SlowClient:
    session = None

    def __init__(self, *a, **k): pass
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        time.sleep(0.6)
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}",
                "width": 400, "height": 300, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": None}


pe.AlbumHierarchy.PiwigoClient = SlowClient
pe._pick_derivative_url = lambda *a, **k: None
# _on_thumb_click would go to the network for the picture itself; the editor
# side is not what is under test here
loaded = []
pe.PhotosEditor._on_thumb_click = lambda self, info: loaded.append(info["id"])

# Its own settings, state and credentials: building a PhotosEditor writes to
# the params file (the start-up migration), and the real one is not the test's
from CredentialStore import CredentialStore as _CredentialStore
pe._store = _CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1500x850")
app = pe.PhotosEditor(root)
pe._store.set_op_param(pe.SS_REVIEW_DIR_KEY, str(tmp))
pe._collect_ss_records_real = pe._collect_ss_records
app._enter_ss_review()
root.update()

failures, seen = [], {}


def cursors():
    return root.cget("cursor"), app.canvas.cget("cursor")


def press(keysym):
    """Send the arrow to the app the way Tk would."""
    root.event_generate(f"<{keysym}>", when="now")
    root.update()


def step1():
    seen["start_pid"] = app._ss_group[0]["photo id"]
    seen["busy_during_fetch"] = cursors()
    print("photo on entry :", seen["start_pid"])
    print("cursor while fetching:", seen["busy_during_fetch"])
    root.after(1200, step2)


def step2():
    seen["cursor_after"] = cursors()
    print("cursor once loaded   :", seen["cursor_after"], " (editor loaded:", loaded, ")")

    # Right arrow with focus nowhere special -> next photo
    root.focus_set()
    press("Right")
    seen["after_right"] = app._ss_group[0]["photo id"]
    print("\nRight arrow    ->", seen["after_right"])

    press("Left")
    seen["after_left"] = app._ss_group[0]["photo id"]
    print("Left arrow     ->", seen["after_left"])

    # Nothing was settled by walking about
    on_disk = pe._read_ss_records(next(tmp.glob("*SlideShow Output*.json")))
    seen["done_flags"] = [r.get("done") for r in on_disk]
    print("done flags in the log:", seen["done_flags"])

    # Caret in a field: the arrows belong to the field
    for name, widget in (("Date entry", app.date_entry),
                         ("Caption box", app.custom_vars["comments"])):
        widget.focus_set()
        root.update()
        press("Right")
        seen[f"focus_{name}"] = app._ss_group[0]["photo id"]
        print(f"Right arrow, caret in {name} ->", seen[f"focus_{name}"],
              f"({widget.winfo_class()})")
    root.focus_set(); root.update()

    # Unsaved typing must be warned about before moving on.  A real load sets
    # this baseline; _on_thumb_click is stubbed out here, so stand it in.
    asked.clear()
    app._loaded_fields = app._editor_field_values()
    app.custom_vars["photo_source"].set("Fanac")
    root.focus_set(); root.update()
    press("Right")
    seen["warned"] = [a for a in asked if isinstance(a, str)]
    print("\ntyped into Source, then Right:", seen["warned"] or "NO WARNING")
    root.after(1200, step3)


def step3():
    # The X button sits just after the heading, not out at the column edge
    head = None
    for w in app._ss_header_frame.winfo_children():      # headings are frozen now
        if isinstance(w, tk.Frame) and w.grid_info().get("row") == 0:
            head = w; break
    kids = head.winfo_children()
    lbl = [c for c in kids if c.cget("text") != "✕"][0]
    btn = [c for c in kids if c.cget("text") == "✕"][0]
    root.update_idletasks()
    gap = btn.winfo_rootx() - (lbl.winfo_rootx() + lbl.winfo_width())
    space = tk.font.Font(font=lbl.cget("font")).measure(" ")
    seen["gap_px"], seen["space_px"] = gap, space
    seen["btn_relief"], seen["btn_bd"] = btn.cget("relief"), int(btn.cget("bd"))
    seen["btn_size"] = (btn.winfo_width(), btn.winfo_height())
    gf = tk.font.Font(font=btn.cget("font"))
    seen["glyph"] = (gf.measure("✕"), gf.metrics("linespace"))
    print(f"\nX box: {seen['btn_size'][0]}x{seen['btn_size'][1]} "
          f"(was 23x21), glyph {seen['glyph'][0]}x{seen['glyph'][1]} (was 12x14), "
          f"{gap}px after the heading (= {gap / space:.1f} spaces), "
          f"relief={seen['btn_relief']}, border={seen['btn_bd']}")

    # Hovering the X explains it -- after the tooltip's own 500ms delay
    btn.event_generate("<Enter>", when="now")
    root.update()
    root.after(700, lambda: after_hover(btn))


def after_hover(btn):
    root.update()
    # _Tooltip parents its window on the widget it is attached to
    tips = [w for w in btn.winfo_children() if isinstance(w, tk.Toplevel)]
    seen["tip"] = (tips[0].winfo_children()[0].cget("text") if tips else None)
    print("\ntooltip over the X:", repr(seen["tip"]))
    btn.event_generate("<Leave>", when="now")
    root.update()
    seen["tip_gone"] = not [w for w in btn.winfo_children()
                            if isinstance(w, tk.Toplevel)]
    print("tooltip goes away on leaving:", seen["tip_gone"])

    # Clicking the X still marks that report done and moves the review on
    before_pid = app._ss_group[0]["photo id"]
    btn.event_generate("<Button-1>", when="now")
    root.update()
    on_disk = pe._read_ss_records(next(tmp.glob("*SlideShow Output*.json")))
    seen["x_click"] = (before_pid, app._ss_group[0]["photo id"] if app._ss_group
                       else None, sum(1 for r in on_disk if r.get("done")))
    print(f"clicking the X on photo {seen['x_click'][0]}: now showing "
          f"{seen['x_click'][1]}, {seen['x_click'][2]} report(s) marked done")
    root.after(200, check)


def check():
    try:
        assert seen["busy_during_fetch"] == ("watch", "watch"), seen["busy_during_fetch"]
        assert seen["cursor_after"] == ("", "crosshair"), seen["cursor_after"]
        assert seen["start_pid"] == 11, seen["start_pid"]
        assert seen["after_right"] == 22, seen["after_right"]
        assert seen["after_left"] == 11, seen["after_left"]
        assert seen["done_flags"] == [None] * 4, seen["done_flags"]
        assert seen["focus_Date entry"] == 11, "arrow stole the Entry's key"
        assert seen["focus_Caption box"] == 11, "arrow stole the Text's key"
        assert seen["warned"] == ["Not Uploaded Yet"], seen["warned"]
        assert seen["gap_px"] <= 2 * seen["space_px"], (seen["gap_px"], seen["space_px"])
        assert seen["btn_relief"] == "solid" and seen["btn_bd"] == 1, seen["btn_relief"]
        # a quarter smaller each way, to the nearest pixel, X unchanged
        assert seen["btn_size"] == (16, 16), seen["btn_size"]
        assert seen["glyph"] == (12, 14), seen["glyph"]
        assert seen["tip"] and "mark it reviewed" in seen["tip"], seen["tip"]
        assert seen["tip_gone"], "the tooltip stayed up after the mouse left"
        was, now, done = seen["x_click"]
        assert now != was and done == 1, seen["x_click"]
        assert not errors, errors[0][:400]
    except AssertionError as e:
        failures.append(str(e))
    root.destroy()


def watchdog():
    failures.append("the test never reached its checks -- see the traceback above")
    root.destroy()


root.after(200, step1)
root.after(20000, watchdog)
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nREVIEW ARROWS OK")
