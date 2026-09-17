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
| `test_ss_source.py` | A folder of logs, or particular logs: which is which, and where marks are written back |
| `test_downloaded_files.py` | Names and sidecar files written by Download Album |
| `test_selection_and_geometry.py` | Which photos need identifying; face-ring and upload-size arithmetic |
| `test_settings_view.py` | What the Settings window shows, and what a typed value parses to |

`test_ss_log.py` deserves the most attention: PhotosEditor **writes to the
user's own SlideShow logs**, so it checks that a rewrite reproduces
SlideShow's formatting byte for byte, that a record SlideShow appended while a
review was open is not lost, that marking marks exactly one record, and that a
finished log is renamed without overwriting anything.

## The GUI tests

`tests/gui/` holds the ones that need a real window. They are **not** part of
`unittest discover` and are meant not to be: each opens a Tk window, drives it
and takes seconds. Run them when you have touched the review screen, the
editor panel or the Settings window:

```
.venv\Scripts\python.exe tests\gui\run.py
.venv\Scripts\python.exe tests\gui\run.py review scroll    only matching names
.venv\Scripts\python.exe tests\gui\test_scrolling.py       just the one
```

They need a desktop and nothing else: each invents its photos, logs and
settings file in a temp folder and stubs the Piwigo client, so none of them
touches the real settings, the real logs or the real server. A few do let the
background album refresh try `piwigo.invalid` and log the failure — harmless,
and what the app does when the server is unreachable. Most were written to
catch a specific bug as it was being fixed, and the file's docstring says
which — so a failure is usually that bug come back rather than a new one.

## What is not covered, and why

- **Anything touching Piwigo.** Uploads, moves, removes and downloads were
  verified against the live server by hand, including a metadata round-trip
  that restored the photo it used and confirmed the image bytes were untouched.
- **Image processing.** Crop, rotate and the restoration sliders are checked by
  eye, which is the honest way to check them.

When adding a test, prefer one that needs neither. If a bug turns up in code
that does, that is usually a sign the logic wants pulling out into a function
that does not — and if it cannot be, `tests/gui/` is where it goes.
