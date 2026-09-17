"""A copy is kept before the photo on Piwigo is replaced.

Piwigo keeps no earlier version, so once edited pixels are up, what was there
is gone.  The naming and the writing are settled without a window in
tests/test_photo_backup.py; what is checked here is the wiring: that a real
upload of a real edit puts a copy aside first, that the copy is the file that
came down rather than a re-encode of it, and that saving only the words about
a photo -- which does not touch the picture -- leaves no backup behind.
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

errors, asked = [], []
tk.Tk.report_callback_exception = lambda self, e, v, t: (
    errors.append("".join(traceback.format_exception(e, v, t))),
    print("!!", errors[-1], flush=True))
pe.messagebox.showerror = pe.messagebox.showinfo = lambda *a, **k: None
pe.messagebox.showwarning = lambda *a, **k: None
pe.messagebox.askyesno = lambda t, m, **k: (asked.append(t), True)[1]

uploaded = []


class Stub:
    def __init__(self, *a, **k): self.session = self
    def login(self, *a, **k): pass
    def logout(self): pass

    def upload_image(self, path, *a, **kw):
        uploaded.append((Path(path).name, Path(path).stat().st_size))
        return {"image_id": kw.get("image_id") or 1}

    def __getattr__(self, name):
        """Whatever else the upload asks of a client, answered with nothing.
        Only the uploading is under test here."""
        return lambda *a, **k: {}


pe.AlbumHierarchy.PiwigoClient = Stub
pe.PhotosEditor._refresh_hierarchy_on_startup = lambda self: None
pe.PhotosEditor._refresh_current_thumbnail = lambda self: None

tmp = Path(tempfile.mkdtemp())
pe._SCRIPT_DIR = tmp                      # backups must not land in the repo
pe._store = CredentialStore(tmp, "PhotosEditor Params.json")
pe.STATE_FILE = tmp / "PhotosEditor State.json"
(tmp / "Piwigo Credentials.json").write_text(json.dumps(
    {"url": "https://piwigo.invalid", "username": "u", "password": "p",
     "verify_ssl": False}), encoding="utf-8")
pe._store.set_op_param(pe.UPLOADS_ENABLED_KEY, True)   # or nothing would be sent

BACKUPS = tmp / pe.PHOTO_BACKUP_DIR

# The photo as it sits on Piwigo: these exact bytes are what a backup must hold
buf = BytesIO()
Image.new("RGB", (240, 180), (186, 132, 88)).save(buf, "JPEG", quality=93)
ORIGINAL = buf.getvalue()

root = tk.Tk(); root.geometry("1400x900")
app = pe.PhotosEditor(root)
root.update()

failures = []


def check(label, ok, detail=""):
    print(f"  {'ok  ' if ok else 'FAIL'} {label}{('  ' + str(detail)) if detail else ''}")
    if not ok:
        failures.append(label)


def backups():
    return sorted(p.name for p in BACKUPS.glob("*")) if BACKUPS.exists() else []


def load_photo():
    """Put the photo on the easel the way a finished download does."""
    app._show_mode(pe.MODE_EDIT)
    root.update()
    # An upload files the photo into the album on screen, and refuses without
    # one -- silently here, since the error box is stubbed out
    app.current_album_id, app.current_album_name = 5, "Fan Photos/Chicon"
    app._on_photo_loaded(Image.open(BytesIO(ORIGINAL)),
                         {"id": 77, "file": "Chicon 1962.jpg",
                          "name": "Chicon 1962.jpg", "width": 240, "height": 180},
                         ORIGINAL)
    root.update()


def step_metadata_only():
    print("saving only the words about a photo keeps no copy:")
    load_photo()
    app._photo_edited = False
    uploaded.clear()
    app._upload_current_photo()
    root.after(1500, step_metadata_checked)


def step_metadata_checked():
    root.update()
    # Without this the next check passes whether or not anything happened
    check("the save went through", app.status_var.get().startswith("Saved"),
          app.status_var.get())
    check("the picture was not re-sent", uploaded == [], uploaded)
    check("nothing was backed up", backups() == [], backups())
    root.after(200, step_edit)


def step_edit():
    print("\nediting the picture and uploading keeps one:")
    load_photo()
    app._rotate_photo(90)                 # a real edit, through the real path
    root.update()
    check("it counts as edited", app._photo_edited)
    uploaded.clear()
    app._upload_current_photo()
    root.after(2000, step_edit_checked)


def step_edit_checked():
    root.update()
    check("the photo was uploaded", len(uploaded) == 1, uploaded)
    check("a copy was kept", backups() == ["Chicon 1962.jpg"], backups())
    kept = (BACKUPS / "Chicon 1962.jpg").read_bytes()
    check("and it is the file that came down, byte for byte", kept == ORIGINAL,
          f"{len(kept)} bytes vs {len(ORIGINAL)}")
    root.after(200, step_second_edit)


def step_second_edit():
    print("\nediting it again keeps another, without overwriting the first:")
    load_photo()
    app._rotate_photo(180)
    root.update()
    app._upload_current_photo()
    root.after(2000, step_second_checked)


def step_second_checked():
    root.update()
    check("both copies are there",
          backups() == ["Chicon 1962 - Gen 01.jpg", "Chicon 1962.jpg"], backups())
    check("the first is still the photo from before any edit",
          (BACKUPS / "Chicon 1962.jpg").read_bytes() == ORIGINAL)
    if errors:
        failures.append("an exception escaped")
    root.destroy()


root.after(500, step_metadata_only)
root.after(30000, lambda: (failures.append("never finished"), root.destroy()))
root.mainloop()
shutil.rmtree(tmp, ignore_errors=True)
if failures:
    print("\nFAILED:", *failures, sep="\n  ")
    sys.exit(1)
print("\nBACKUP ON UPLOAD OK")
