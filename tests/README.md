# PhotosEditor tests

Run them from the `PhotosEditor` folder:

```
.venv\Scripts\python.exe -m unittest discover -s tests
```

No pytest, no plugins, no configuration: the standard library only, so the
suite runs anywhere the app does. It needs no network, no Piwigo credentials
and opens no windows, and takes well under a second.

## What is covered

These are the pure parts — the ones where a mistake is silent and expensive.

| File | Covers |
|------|--------|
| `test_ss_log.py` | Reading, rewriting and marking SlideShow's output logs |
| `test_downloaded_files.py` | Names and sidecar files written by Download Album |
| `test_selection_and_geometry.py` | Which photos need identifying; face-ring and upload-size arithmetic |

`test_ss_log.py` deserves the most attention: PhotosEditor **writes to the
user's own SlideShow logs**, so it checks that a rewrite reproduces
SlideShow's formatting byte for byte, that a record SlideShow appended while a
review was open is not lost, that marking marks exactly one record, and that a
finished log is renamed without overwriting anything.

## What is not covered, and why

Three kinds of behaviour are deliberately left out, because a suite that needs
a server, a display or a login is a suite that stops being run:

- **Anything touching Piwigo.** Uploads, moves, removes and downloads were
  verified against the live server by hand, including a metadata round-trip
  that restored the photo it used and confirmed the image bytes were untouched.
- **GUI flows.** Review-mode navigation, the upload prompts, the exit guard and
  window-geometry restoring were driven through a real Tk window with the
  Piwigo client stubbed. Worth automating one day; they are slow and need a
  desktop session.
- **Image processing.** Crop, rotate and the restoration sliders are checked by
  eye, which is the honest way to check them.

When adding a test, prefer one that needs none of the three. If a bug turns up
in code that does need them, that is usually a sign the logic wants pulling out
into a function that does not.
