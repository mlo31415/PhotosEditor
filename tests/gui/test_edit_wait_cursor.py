"""Edit Photos shows the wait cursor while a photo comes down from Piwigo.

Only Review used to: in Edit Photos the full photo took a noticeable while to
arrive with nothing to say it was coming.  The cursor has to last until the
photo asked for last is on screen -- clicking on from one photo to the next
leaves the first one's fetch running, and when that lands late it must neither
take the cursor off nor take the editor over.

Nothing leaves the machine: the client and the download are stubs, made slow.
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
from PIL import Image
from CredentialStore import CredentialStore

errors, boxes = [], []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.askyesno = lambda t, m, **k: (boxes.append(t), True)[1]
pe.messagebox.showinfo = pe.messagebox.showwarning = pe.messagebox.showerror = \
    lambda t, m, **k: boxes.append(t)

# How long each photo takes to come down: 11 is slow, 12 quick, so 11 asked
# for first still lands after 12
DELAY = {11: 2.0, 12: 0.8}
COLOUR = {11: "#c04040", 12: "#40c060"}


class StubClient:
    def __init__(self, *a, **k): pass
    def login(self, *a, **k): pass
    def logout(self): pass

    def get_image_info(self, pid):
        return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
                "width": 400, "height": 300, "derivatives": {},
                "element_url": f"https://piwigo.invalid/p{pid}.jpg"}


class StubResponse:
    def __init__(self, pid):
        buf = BytesIO()
        Image.new("RGB", (400, 300), COLOUR[pid]).save(buf, format="JPEG")
        self.content = buf.getvalue()

    def raise_for_status(self): pass


def slow_get(url, **kw):
    pid = int(url.rsplit("/p", 1)[1].split(".")[0])
    time.sleep(DELAY[pid])
    return StubResponse(pid)


pe.AlbumHierarchy.PiwigoClient = StubClient
pe.requests.get = slow_get

tmp = Path(tempfile.mkdtemp())
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")

root = tk.Tk(); root.geometry("1400x800")
app = pe.PhotosEditor(root)
app._show_mode(pe.MODE_EDIT)
root.update()

failures, samples = [], []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def photo(pid):
    return {"id": pid, "file": f"p{pid}.jpg", "name": f"p{pid}.jpg",
            "element_url": f"https://piwigo.invalid/p{pid}.jpg"}


def in_editor():
    d = app._current_image_dict
    return d.get("id") if d else None


def cursors():
    return root.cget("cursor"), app.canvas.cget("cursor")


def sample_until(stop, then, t=[0.0]):
    """Every 0.1 s, the cursor and the photo in the editor, until stop()."""
    samples.append((round(t[0], 1), *cursors(), in_editor()))
    t[0] += 0.1
    if stop() or t[0] > 6:
        root.after(400, then)
    else:
        root.after(100, lambda: sample_until(stop, then, t))


def step_one():
    print("one photo:")
    app._open_photo_in_editor(photo(12))
    check("the wait cursor is on at once", cursors() == ("watch", "watch"), cursors())
    sample_until(lambda: in_editor() == 12, step_one_done)


def step_one_done():
    waiting = [s for s in samples if s[3] != 12]
    check("it was a real wait", len(waiting) >= 5, len(waiting))
    check("the cursor was the wait cursor all through it",
          all(s[1] == "watch" for s in waiting), waiting)
    check("and is off once the photo is there", cursors() == ("", "crosshair"), cursors())

    print("\nclicking on before the first arrives:")
    samples.clear()
    app._open_photo_in_editor(photo(11))    # the slow one
    root.update()
    app._open_photo_in_editor(photo(12))    # the quick one, asked for last
    sample_until(lambda: in_editor() == 12, step_second_landed)


def step_second_landed():
    waiting = [s for s in samples if s[3] != 12]
    check("the cursor lasted until the last asked for arrived",
          all(s[1] == "watch" for s in waiting), waiting)
    check("and is off once it has", cursors() == ("", "crosshair"), cursors())
    # Now the first one lands, late
    root.after(int((DELAY[11] - DELAY[12]) * 1000) + 800, step_late)


def step_late():
    check("the late one did not take the editor over", in_editor() == 12, in_editor())
    shown = app._viewer_image.getpixel((200, 150)) if app._viewer_image else None
    check("the picture is still the one asked for",
          shown is not None and shown[1] > shown[0], shown)
    check("nor put the cursor back", cursors() == ("", "crosshair"), cursors())
    check("nothing was asked or reported", boxes == [], boxes)
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(300, step_one)
root.after(30000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nEDIT WAIT CURSOR OK")
