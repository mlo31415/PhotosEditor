# PhotosEditor

A desktop editor for the photo collection on a Piwigo server (photos.fanac.org):
browse albums, move and copy photos between them, correct captions, dates,
photographer credits and tags, and make modest repairs to the images
themselves.

Requires the `PiwigoHelpers` folder as a sibling of this one — it holds the
Piwigo client and the shared album-tree widget.

```
pip install Pillow requests opencv-python
```

Pillow and requests are needed; OpenCV only for the Photo Restoration sliders,
which say so and stay inert without it.

## The main window

Two identical panels, each an album tree beside a grid of thumbnails. Having
two means the source and destination of a move are both on screen at once.

* **Drag photos** from one grid to the other, or onto any album in either tree.
  Plain drag moves, **Ctrl-drag copies**; the label under the cursor says which,
  and follows the album name you are hovering over. Select several first and the
  whole selection travels together.
* **Drag an album** onto another to re-parent it.
* **Double-click a photo** to open the Photo Editor.
* **Right-click a photo** to remove it from the album — the photo stays in
  Piwigo, only the album membership goes.
* **Right-click an album** to add a sub-album, rename, delete, or download.
* **Zoom** gives the left panel the whole window; **F5** reloads both.
* **Escape** exits, exactly as the Exit button does.

Every operation that changes the server runs in the background with a progress
dialog and a Cancel; quitting while one is still running asks first, and stops
it at a photo boundary rather than mid-photo.

## The Photo Editor

Opened by double-clicking a thumbnail. The photo is fetched at **full
resolution** — an edit is saved by sending the image back in place of the
original, so anything smaller would quietly shrink the archive master.

* **Custom Fields** — Photographer/Source, Date of Photo, Caption, Tags. The
  *Persist* box beside a field keeps its value as you move between photos.
* **Editing tools** — rotate, crop, undo, revert.
* **Photo Restoration** — exposure, contrast, red-cast and sharpening sliders.
* **Upload to Piwigo** writes the changes back.

Uploading knows the difference between editing the picture and editing the
words about it:

| What changed | What is sent |
|---|---|
| Only the fields | the metadata alone — the image file is not touched |
| The image (rotate, crop, restore) | the full-size image, re-encoded at quality 95 |
| Nothing | it asks whether you meant to |

If the image is larger than `max_upload_pixels`, it offers the choice of
cancelling, reducing to the largest size that fits, or uploading at full size.

Quitting, closing the editor, or moving to another photo with unsaved work
warns and names what would be lost.

### Keyboard shortcuts

| Key | Does |
|-----|------|
| Ctrl+U / Ctrl+S | Upload current photo |
| Ctrl+Y | Crop photo |
| Ctrl+Z | Undo last edit |
| Ctrl+I | Open in IrfanView |
| Ctrl+L | Prepend "L-R: " to caption |
| Shift+Ctrl+L | Replace caption with "L-R: " |
| Ctrl+N | Toggle the "Needs-ID" tag |
| Escape | Close the editor |
| Ctrl+H | Show this list |

## Downloading albums

Right-click any album (or a multi-selection):

* **Download Album** — the album, optionally with its sub-albums, into a folder
  tree mirroring the album hierarchy. Each photo arrives as three files: the
  image, a `.xml` of its Piwigo metadata, and a `.txt` holding its caption.
  Photos already present are skipped, so an interrupted download resumes.
* **Download Need_IDs from Album** — the same, but only photos that still need
  identifying: tagged `Needs-ID`, or with `??` standing in for a name in the
  caption.

The estimate shown before it starts comes from how long recent downloads
actually took, not a guess.

## Review SS Comments

For working through the identifications people submit through SlideShow. It
splits the window: the Photo Editor on the left, the SlideShow record on the
right — who sent it, their comment, and the faces they named, each with a round
thumbnail. **Hovering a face rings it on the photo**, which is how you find one
person in a crowded convention photograph.

Records for the same photo are grouped together, and the whole folder of logs
is read at once. **Skip** marks a record done and moves on; uploading does the
same, since acting on a record settles it. Done is written into the SlideShow
log itself, and a log whose records are all done is renamed `Completed - …`.

## Files beside the program

| File | Holds |
|------|-------|
| `PhotosEditor Params.json` | server URL, credentials and the settings below |
| `Piwigo Credentials.json` | credentials, if kept separately |
| `PhotosEditor State.json` | window geometry, last albums, download timings |
| `AlbumHierarchy.json` | cached album tree, refreshed at startup |

Settings in the params file: `verify_ssl`, `rate_limit_calls_per_second`
(default 2.0), `sync_metadata`, `refresh_representative`, and
`max_upload_pixels`. None of these files are in version control — they hold
credentials or per-machine state.

## Tests

```
.venv\Scripts\python.exe -m unittest discover -s tests
```

Standard library only, no network, no credentials, no window. See
`tests/README.md` for what is covered and what is deliberately left to
hand-checking.

## Building

`Build.bat` runs PyInstaller against `PhotosEditor.spec`, which bundles the
icon and the `PiwigoHelpers` modules into a single executable.
