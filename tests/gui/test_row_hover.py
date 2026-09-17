"""Hovering a face thumbnail rings the face on the photo AND lights its row.

Drives the real widgets with a stubbed server; the photo and its face crops are
generated locally, so nothing leaves the machine.
"""
import sys, json, shutil, tempfile, importlib.util, traceback, time
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

errors = []


def _report(self, exc, val, tb):
    errors.append("".join(traceback.format_exception(exc, val, tb)))
    print("!! exception in a tk callback:\n", errors[-1], flush=True)


tk.Tk.report_callback_exception = _report
pe.messagebox.askyesno = lambda *a, **k: True
pe.messagebox.showerror = pe.messagebox.showwarning = lambda *a, **k: None

W, H = 800, 600
FACES = [{"number": n, "name": "", "box": [n*150, 100, 90, 110]} for n in (1, 2, 3)]


class StubClient:
    session = None

    def __init__(self, *a, **k):
        self.session = self

    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": W, "height": H, "categories": [{"id": 77, "name": "A"}],
                "derivatives": {}, "element_url": "https://piwigo.invalid/p.jpg"}

    def get(self, url, **kw):
        return StubResponse()


class StubResponse:
    def __init__(self):
        buf = BytesIO()
        Image.new("RGB", (W, H), "#606060").save(buf, format="JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


pe.AlbumHierarchy.PiwigoClient = StubClient
pe.requests.get = lambda url, **kw: StubResponse()
pe._pick_derivative_url = lambda *a, **k: "https://piwigo.invalid/p.jpg"

tmp = Path(tempfile.mkdtemp())
rec = {"saved": "t1", "photo id": 11, "file": "p11.jpg", "album": "A",
       "editor": "a@x", "faces": [dict(f, name=("Bob Tucker" if f["number"] == 2 else ""))
                                  for f in FACES],
       "comment": "", "photo date": ""}
(tmp / "SlideShow Output 2026-08-28 20.00.00.json").write_text(
    json.dumps(rec, indent=2) + "\n\n", encoding="utf-8")

# Its own settings, state and credentials: building a PhotosEditor writes to
# the params file (the start-up migration), and the real one is not the test's
from CredentialStore import CredentialStore as _CredentialStore
pe._store = _CredentialStore(tmp, "PhotosEditor Params.json")
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
root.update()

failures, seen = [], {}


def start():
    app._show_ss_photo()
    root.after(1500, hover)


def hover():
    root.update()
    seen["rows"] = len(app._ss_rows)
    seen["thumbs built"] = sum(
        1 for l in app._ss_face_labels if getattr(l, "_plain_thumb", None) is not None)
    lbl = app._ss_face_labels[1]                       # the middle face
    seen["bg before"] = [w.cget("bg") for w in app._ss_row_cells[1]]
    seen["image before"] = str(lbl.cget("image"))
    seen["rings before"] = len(app._ss_face_hl_ids)

    lbl.event_generate("<Enter>", when="now")
    root.update()
    seen["bg during"] = [w.cget("bg") for w in app._ss_row_cells[1]]
    seen["image during"] = str(lbl.cget("image"))
    seen["rings during"] = len(app._ss_face_hl_ids)
    seen["other rows during"] = [w.cget("bg") for w in app._ss_row_cells[0]]

    lbl.event_generate("<Leave>", when="now")
    root.update()
    seen["bg after"] = [w.cget("bg") for w in app._ss_row_cells[1]]
    seen["image after"] = str(lbl.cget("image"))
    seen["rings after"] = len(app._ss_face_hl_ids)
    root.after(100, from_the_photo)


def from_the_photo():
    """The other direction: point at the face on the photo itself."""
    rect = app._photo_display_rect
    seen["display rect"] = rect
    circle = pe._ss_face_circle_on_canvas(app._ss_rows[2]["box"], (W, H), rect)
    cx, cy = (circle[0]+circle[2])/2, (circle[1]+circle[3])/2
    seen["aimed at"] = (round(cx), round(cy))
    seen["hit test"] = app._ss_face_at(cx, cy)

    app.canvas.event_generate("<Motion>", x=int(cx), y=int(cy), when="now")
    root.update()
    seen["photo hover row"] = app._ss_hover
    seen["bg row3 during"] = [w.cget("bg") for w in app._ss_row_cells[2]]
    seen["rings from photo"] = len(app._ss_face_hl_ids)
    seen["row2 untouched"] = [w.cget("bg") for w in app._ss_row_cells[1]]

    # Now somewhere with no face under it
    app.canvas.event_generate("<Motion>", x=3, y=3, when="now")
    root.update()
    seen["after empty"] = app._ss_hover
    seen["bg row3 after"] = [w.cget("bg") for w in app._ss_row_cells[2]]
    seen["rings after empty"] = len(app._ss_face_hl_ids)
    root.after(100, check)


def check():
    print(f"rows: {seen['rows']}, thumbnails built: {seen['thumbs built']}")
    print(f"\nrow 2 backgrounds")
    print(f"   before: {set(seen['bg before'])}")
    print(f"   during: {set(seen['bg during'])}")
    print(f"   after : {set(seen['bg after'])}")
    print(f"\nrow 1 during (should be untouched): {set(seen['other rows during'])}")
    print(f"\nthumbnail image swapped: {seen['image before'] != seen['image during']}"
          f"  and put back: {seen['image after'] == seen['image before']}")
    print(f"rings on the photo: before {seen['rings before']}, "
          f"during {seen['rings during']}, after {seen['rings after']}")

    print(f"\npointing at face 3 on the photo, at {seen['aimed at']} "
          f"(photo shown in {tuple(round(v) for v in seen['display rect'])})")
    print(f"   hit test says row {seen['hit test']}, hover is {seen['photo hover row']}")
    print(f"   row 3 background: {set(seen['bg row3 during'])}")
    print(f"   row 2 meanwhile : {set(seen['row2 untouched'])}")
    print(f"   rings drawn: {seen['rings from photo']}")
    print(f"\npointing at empty canvas: hover {seen['after empty']}, "
          f"row 3 {set(seen['bg row3 after'])}, rings {seen['rings after empty']}")

    print(f"\nthe two greens: ring {pe._SS_FACE_RING}, row {pe._SS_ROW_HL_BG}")
    try:
        assert seen["rows"] == 3, seen["rows"]
        assert seen["thumbs built"] == 3, seen["thumbs built"]
        hl = pe._SS_ROW_HL_BG.lower()
        assert set(b.lower() for b in seen["bg during"]) == {hl}, seen["bg during"]
        assert set(seen["bg after"]) == set(seen["bg before"]), seen["bg after"]
        assert hl not in [b.lower() for b in seen["other rows during"]], "wrong row lit"
        assert seen["image during"] != seen["image before"], "thumbnail not swapped"
        assert seen["image after"] == seen["image before"], "thumbnail not restored"
        assert seen["rings during"] == 2, seen["rings during"]     # dark + bright
        assert seen["rings after"] == 0, seen["rings after"]

        # the photo -> row direction
        assert seen["hit test"] == 2, seen["hit test"]
        assert seen["photo hover row"] == 2, seen["photo hover row"]
        assert set(b.lower() for b in seen["bg row3 during"]) == {hl}, seen["bg row3 during"]
        assert hl not in [b.lower() for b in seen["row2 untouched"]], "row 2 lit as well"
        assert seen["rings from photo"] == 2, seen["rings from photo"]
        assert seen["after empty"] is None, seen["after empty"]
        assert hl not in [b.lower() for b in seen["bg row3 after"]], seen["bg row3 after"]
        assert seen["rings after empty"] == 0, seen["rings after empty"]

        # one green, lightened for the row -- same hue, not two greens
        import colorsys
        ring = colorsys.rgb_to_hsv(*(int(pe._SS_FACE_RING[i:i+2], 16)/255
                                     for i in (1, 3, 5)))
        row = colorsys.rgb_to_hsv(*(v/255 for v in pe._SS_ROW_HL_BG_RGB))
        assert abs(ring[0]-row[0]) < 0.01, (ring[0], row[0])
        assert not errors, errors[0][:300]
    except AssertionError as e:
        failures.append(str(e))
    root.destroy()


root.after(300, start)
root.after(20000, lambda: (failures.append("never reached the checks"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nROW HOVER OK — the row lights up with the ring, and both go back")
