"""A single click in Edit Photos opens the photo.

The album on the left of Edit Photos shared Move and Copy's click: a click
toggled the photo's selection, and only a double-click opened it.  So clicks
just highlighted photos, and the highlights piled up.  In Edit Photos a click
now puts the photo in the editor, and it is the one photo selected.

Move and Copy keeps its clicks as they were: there they select photos to move.
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
from PIL import Image
from CredentialStore import CredentialStore

errors, boxes = [], []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))

answer = {"yes": True}
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(("ask", t, m)), answer["yes"])[1]
pe.messagebox.askyesnocancel = lambda t, m, **k: (boxes.append(("ask3", t, m)), answer["yes"])[1]
pe.messagebox.askokcancel = lambda t, m, **k: (boxes.append(("okc", t, m)), answer["yes"])[1]
pe.messagebox.showinfo = lambda t, m, **k: boxes.append(("info", t, m))
pe.messagebox.showwarning = lambda t, m, **k: boxes.append(("warn", t, m))
pe.messagebox.showerror = lambda t, m, **k: boxes.append(("error", t, m))

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


panel = app._source_panel
IDS = (11, 12, 13, 14)
PHOTOS = {pid: {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "element_url": "https://piwigo.invalid/p.jpg"} for pid in IDS}

# Every photo asked for, whether or not it then loads
loads = []
_real_thumb_click = app._on_thumb_click
app._on_thumb_click = lambda d: (loads.append(d["id"]), _real_thumb_click(d))[1]


def fill_album():
    panel.clear()
    for pid in IDS:
        panel.thumb_cache[pid] = Image.new("RGB", panel.thumb_size, "#808080")
        panel.album_images.append(PHOTOS[pid])
        panel.add_cell(pid, PHOTOS[pid])
    root.update()


# Event times, in ms.  Tk calls two presses a double-click by their times, and
# generated events all carry the same one unless given their own
clock = [100000]


def press_release(lbl, gap):
    clock[0] += gap
    lbl.event_generate("<ButtonPress-1>", time=clock[0])
    lbl.event_generate("<ButtonRelease-1>", time=clock[0] + 50)
    root.update()


def click(pid):
    """A real single click on the photo's picture, so the bindings decide --
    well apart from the click before it."""
    press_release(panel.img_labels[pid], 5000)


def double_click(pid):
    """Two clicks close together: Tk makes the second the double."""
    lbl = panel.img_labels[pid]
    press_release(lbl, 5000)
    press_release(lbl, 150)


def in_editor():
    d = app._current_image_dict
    return d.get("id") if d else None


def selected():
    return sorted(panel.selected_ids)


def lit(pid):
    """The cell is drawn as selected."""
    return str(panel.cell_by_id[pid].cget("bg")) == "#1a6b9a"


def step_click():
    app._show_mode(pe.MODE_EDIT)
    fill_album()
    print("a click in Edit Photos opens the photo:")
    click(11)
    root.after(800, step_click_landed)


def step_click_landed():
    check("it is in the editor", in_editor() == 11, in_editor())
    check("it alone is selected", selected() == [11], selected())
    check("and drawn so", lit(11))

    print("\na click on another replaces it:")
    click(12)
    root.after(800, step_second_landed)


def step_second_landed():
    check("the second is in the editor", in_editor() == 12, in_editor())
    check("selections do not add up", selected() == [12], selected())
    check("the first is no longer drawn selected", not lit(11))
    check("the second is", lit(12))

    print("\na click on the photo already there leaves it be:")
    del loads[:]
    click(12)
    root.after(400, step_same)


def step_same():
    check("nothing was fetched again", loads == [], loads)
    check("still in the editor", in_editor() == 12, in_editor())
    check("still selected", selected() == [12], selected())

    print("\nwith edits not uploaded, a click asks first -- and No stays:")
    app._photo_edited = True
    boxes.clear()
    answer["yes"] = False
    click(13)
    root.update()
    check("it asked", [b[1] for b in boxes] == ["Not Uploaded Yet"],
          [b[1] for b in boxes])
    check("nothing was fetched", loads == [], loads)
    check("the editor kept its photo", in_editor() == 12, in_editor())
    check("and the selection with it", selected() == [12], selected())
    check("the edits are still marked", app._photo_edited is True)

    print("\n...and Yes goes:")
    boxes.clear()
    answer["yes"] = True
    click(13)
    root.after(800, step_yes_landed)


def step_yes_landed():
    check("it asked", [b[1] for b in boxes] == ["Not Uploaded Yet"],
          [b[1] for b in boxes])
    check("the new photo is in the editor", in_editor() == 13, in_editor())
    check("and selected alone", selected() == [13], selected())

    print("\na double-click opens it once, not twice:")
    del loads[:]
    boxes.clear()
    double_click(14)
    root.after(800, step_double_landed)


def step_double_landed():
    check("fetched once", loads == [14], loads)
    check("in the editor", in_editor() == 14, in_editor())
    check("selected alone", selected() == [14], selected())
    check("nothing asked", boxes == [], boxes)

    print("\nMove and Copy keeps its clicks:")
    app._show_mode(pe.MODE_MOVE)
    app._clear_side_selection('left')
    del loads[:]
    click(11)
    click(12)
    check("clicks add up there", selected() == [11, 12], selected())
    check("and open nothing", loads == [], loads)
    click(12)
    check("a second click takes one off again", selected() == [11], selected())
    root.after(200, finish)


def finish():
    if errors:
        failures.append("an exception escaped")
    app._photo_edited = False
    root.destroy()


root.after(400, step_click)
root.after(30000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nEDIT CLICK OK")
