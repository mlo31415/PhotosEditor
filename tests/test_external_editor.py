"""Handing the photo to another program and taking it back.

The round trip is the whole feature, and the two ends of it are what these
cover: what gets written out, and how "saved" is told from "closed without
saving".  Driving a real editor is not something a test can do, so the
wiring is checked in tests/gui/test_external_editor.py with a stand-in
program.
"""
import os
import shutil
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()
from PIL import Image                                          # noqa: E402


class WhatGoesOut(unittest.TestCase):

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_it_is_a_png(self):
        """Not JPEG: this is a round trip, and JPEG would cost a generation of
        quality going out and another coming back."""
        path = pe._export_for_external_edit(
            Image.new("RGB", (40, 30), "red"), self.tmp, "Chicon 1962.jpg")
        self.assertEqual(path.suffix, ".png")
        with Image.open(path) as got:
            self.assertEqual(got.format, "PNG")

    def test_it_keeps_the_photo_s_name(self):
        path = pe._export_for_external_edit(
            Image.new("RGB", (40, 30), "red"), self.tmp, "Chicon 1962.jpg")
        self.assertEqual(path.stem, "Chicon 1962")

    def test_it_goes_out_at_full_size(self):
        big = Image.new("RGB", (1600, 1200), "red")
        with Image.open(pe._export_for_external_edit(big, self.tmp, "p.jpg")) as got:
            self.assertEqual(got.size, (1600, 1200))

    def test_the_folder_is_made_if_it_is_not_there(self):
        folder = self.tmp / "not yet"
        pe._export_for_external_edit(Image.new("RGB", (8, 8)), folder, "p.jpg")
        self.assertTrue(folder.is_dir())

    def test_an_awkward_mode_is_converted_rather_than_refused(self):
        path = pe._export_for_external_edit(
            Image.new("CMYK", (20, 20)), self.tmp, "p.jpg")
        self.assertTrue(path.exists())

    def test_a_name_windows_will_not_take_is_made_safe(self):
        path = pe._export_for_external_edit(
            Image.new("RGB", (8, 8)), self.tmp, 'why? "this".jpg')
        self.assertNotIn("?", path.name)
        self.assertTrue(path.exists())


class TellingWhetherItWasSaved(unittest.TestCase):
    """_file_fingerprint is what stands between "saved" and "closed without
    saving".  If it cannot see a change, the edit is silently lost."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.path = self.tmp / "p.png"
        Image.new("RGB", (40, 30), "red").save(self.path)

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_an_untouched_file_looks_untouched(self):
        before = pe._file_fingerprint(self.path)
        time.sleep(0.01)
        self.assertEqual(pe._file_fingerprint(self.path), before)

    def test_a_rewrite_shows_up(self):
        before = pe._file_fingerprint(self.path)
        time.sleep(0.01)
        Image.new("RGB", (40, 30), "blue").save(self.path)
        self.assertNotEqual(pe._file_fingerprint(self.path), before)

    def test_a_rewrite_of_the_same_size_within_a_clock_tick_still_shows_up(self):
        """Why the size is not the whole of it, and the time is not either."""
        before = pe._file_fingerprint(self.path)
        os.utime(self.path, ns=(before[0], before[0]))       # same timestamp
        self.path.write_bytes(self.path.read_bytes() + b"padding")
        self.assertNotEqual(pe._file_fingerprint(self.path), before)

    def test_a_file_that_is_not_there_is_not_an_error(self):
        self.assertEqual(pe._file_fingerprint(self.tmp / "gone.png"), (0, 0))


class NamingTheTools(unittest.TestCase):

    def test_a_program_is_called_what_its_file_is_called(self):
        self.assertEqual(
            pe._editor_label(r"C:\Program Files\Adobe\Photoshop 2026\Photoshop.exe"),
            "Photoshop")

    def test_except_where_that_says_nothing(self):
        """i_view64 is IrfanView, and nobody thinks of it as i_view64."""
        self.assertEqual(
            pe._editor_label(r"C:\Program Files\IrfanView\i_view64.exe"),
            "IrfanView")

    def test_the_case_of_the_file_does_not_matter(self):
        self.assertEqual(pe._editor_label(r"C:\x\I_VIEW64.EXE"), "IrfanView")


class FindingTheTools(unittest.TestCase):
    """_discover_external_editors seeds the list on a machine that has
    something already."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self._real = pe._EDITOR_SEARCH

    def tearDown(self):
        pe._EDITOR_SEARCH = self._real
        shutil.rmtree(self.tmp, ignore_errors=True)

    def make(self, relative):
        path = self.tmp / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"MZ")
        return str(path)

    def test_what_is_there_is_found_and_what_is_not_is_not(self):
        here = self.make("IrfanView/i_view64.exe")
        pe._EDITOR_SEARCH = (here, str(self.tmp / "nothing/at/all.exe"))
        self.assertEqual(pe._discover_external_editors(), [here])

    def test_a_pattern_finds_the_newest_first(self):
        """Photoshop puts its year in the folder name, and the current one is
        the one to offer."""
        self.make("Adobe/Adobe Photoshop 2024/Photoshop.exe")
        newest = self.make("Adobe/Adobe Photoshop 2026/Photoshop.exe")
        pe._EDITOR_SEARCH = (str(self.tmp / "Adobe/Adobe Photoshop*/Photoshop.exe"),)
        self.assertEqual(pe._discover_external_editors()[0], newest)

    def test_nothing_installed_is_an_empty_list_not_a_failure(self):
        pe._EDITOR_SEARCH = (str(self.tmp / "no/such.exe"),)
        self.assertEqual(pe._discover_external_editors(), [])

    def test_the_same_program_is_not_offered_twice(self):
        here = self.make("IrfanView/i_view64.exe")
        pe._EDITOR_SEARCH = (here, here)
        self.assertEqual(pe._discover_external_editors(), [here])


if __name__ == "__main__":
    unittest.main()
