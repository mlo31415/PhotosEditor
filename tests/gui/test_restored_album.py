"""Starting up in a mode, with the album from last time.

Reported: leave PhotosEditor in Edit Photos, start it again, and the album is
selected but its photos are not there.  Move and Copy Photos, left the same
way, comes back with them -- so the difference is the mode being restored
after the panels were laid out, not the restoring of the album itself.

Both modes are checked here, because a fix that only works for one of them is
not a fix.
"""
import sys, json, shutil, tempfile, time, importlib.util, traceback
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

errors = []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.showerror = pe.messagebox.showinfo = lambda *a, **k: None
pe.messagebox.showwarning = lambda *a, **k: None
pe.messagebox.askyesno = lambda *a, **k: True

ALBUM_ID, ALBUM_NAME, PHOTOS = 42, "Fan Photos/Chicon", 6


class Resp:
    def __init__(self):
        buf = BytesIO(); Image.new("RGB", (120, 90), "#8899aa").save(buf, "JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


class Stub:
    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass
    def get(self, url, **kw): return Resp()

    def get_album_images(self, album_id):
        # Piwigo takes a moment, which matters: the mode is restored shortly
        # after start-up, and against a real server that happens while the
        # photos are still on their way.
        time.sleep(1.2)
        return [{"id": 100 + i, "file": f"p{i}.jpg", "name": f"p{i}.jpg",
                 "width": 120, "height": 90, "derivatives": {},
                 "element_url": "https://piwigo.invalid/p.jpg"}
                for i in range(PHOTOS)]

    def get_image_info(self, pid):
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": 120, "height": 90, "derivatives": {},
                "categories": [{"id": ALBUM_ID, "name": "Chicon"}],
                "element_url": "https://piwigo.invalid/p.jpg"}


pe.AlbumHierarchy.PiwigoClient = Stub
pe.requests.get = lambda url, **kw: Resp()
pe._pick_derivative_url = lambda *a, **k: "https://piwigo.invalid/p.jpg"

tmp = Path(tempfile.mkdtemp())
(tmp / "AlbumHierarchy.json").write_text(json.dumps(
    [{"id": 1, "name": "Fan Photos", "fullname": "Fan Photos",
      "total_nb_images": PHOTOS, "children": [
          {"id": ALBUM_ID, "name": "Chicon", "fullname": ALBUM_NAME,
           "total_nb_images": PHOTOS, "children": []}]}]),
    encoding="utf-8")
pe.AlbumHierarchy._album_hierarchy_file = lambda: tmp / "AlbumHierarchy.json"
# The startup refresh would fetch a new hierarchy over the one above
pe.PhotosEditor._refresh_hierarchy_on_startup = lambda self: None

pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def state_for(mode):
    pe.STATE_FILE.write_text(json.dumps(
        {"mode": mode, "zoomed": False, "geometry": "1300x800+70+70",
         "album_id": ALBUM_ID, "album_name": ALBUM_NAME,
         "target_album_id": ALBUM_ID, "target_album_name": ALBUM_NAME}),
        encoding="utf-8")


def start_in(mode, then):
    """Start a window from a state file that says this mode, and look at the
    left-hand panel once everything has had time to settle."""
    state_for(mode)
    root = tk.Tk()
    app = pe.PhotosEditor(root)

    def look():
        root.update()
        panel = app._source_panel
        cells = len(panel.thumb_cells)
        placed = sum(1 for c in panel.thumb_cells if c.winfo_ismapped())
        print(f"\nstarted in {mode}:")
        print(f"   mode now: {app._mode}   album: {app.current_album_name!r}"
              f"   count says: {app.thumb_count_var.get()!r}")
        check(f"{mode}: the album came back",
              app.current_album_id == ALBUM_ID, app.current_album_id)
        check(f"{mode}: its photos are in the panel", cells == PHOTOS, cells)
        check(f"{mode}: and they are on screen", placed == PHOTOS,
              f"{placed} of {cells} mapped")
        root.destroy()
        then()

    root.after(3500, look)
    root.mainloop()


def edit_then_move():
    start_in(pe.MODE_EDIT, lambda: start_in(pe.MODE_MOVE, done))


def done():
    if errors:
        failures.append("an exception escaped")
    shutil.rmtree(tmp, ignore_errors=True)
    if failures:
        print("\nFAILED:", *failures, sep="\n  ")
        sys.exit(1)
    print("\nRESTORED ALBUM OK")


edit_then_move()
