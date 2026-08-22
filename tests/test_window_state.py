"""Saved window geometry, and the state file it lives in.

The point of the geometry check is that a window last used on a monitor that
is no longer attached still comes back somewhere reachable.
"""
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                              # noqa: E402

pe = load_pe()


class _FakeWindow:
    """Stands in for a Tk window with a known desktop: 1920x1080 at the
    origin, plus a second monitor to its left, as an unplugged laptop might."""
    def winfo_screenwidth(self):  return 1920
    def winfo_screenheight(self): return 1080


class GeometryBackOnScreen(unittest.TestCase):

    DESKTOP = (0, 0, 1920, 1080)

    def setUp(self):
        # Pin the desktop so the test does not depend on the machine running it
        self._real = pe._virtual_screen_bounds
        pe._virtual_screen_bounds = lambda win: self.DESKTOP
        self.addCleanup(setattr, pe, "_virtual_screen_bounds", self._real)
        self.win = _FakeWindow()

    def on_screen(self, geo):
        return pe._geometry_on_screen(self.win, geo)

    def test_a_sensible_position_is_left_alone(self):
        self.assertEqual(self.on_screen("1400x820+120+80"), "1400x820+120+80")

    def test_a_window_on_a_monitor_that_is_gone_is_brought_back(self):
        got = self.on_screen("1400x820+3000+200")      # off to the right
        self.assertNotEqual(got, "1400x820+3000+200")
        w, rest = got.split("x", 1)
        h, x, y = rest.split("+")
        self.assertLessEqual(int(x) + int(w), 1920)

    def test_a_window_off_to_the_left_is_brought_back(self):
        got = self.on_screen("800x600+-2500+100")      # Tk writes this as +-2500
        self.assertNotEqual(got, "800x600+-2500+100")
        self.assertGreaterEqual(int(got.split("+")[1]), 0)

    def test_offsets_from_the_right_and_bottom_are_understood(self):
        """-X-Y is as valid as +X+Y. Before this was handled the check simply
        did not look at such a geometry, which is the one thing it is for."""
        # 100 in from the right, 50 up from the bottom: on screen, so untouched
        self.assertEqual(self.on_screen("800x600-100-50"), "800x600-100-50")

    def test_a_right_anchored_window_on_a_vanished_monitor_is_still_caught(self):
        # 5000 in from the right edge puts it far off the left of the desktop
        got = self.on_screen("800x600-5000-50")
        self.assertNotEqual(got, "800x600-5000-50")
        self.assertTrue(got.startswith("800x600+"))
        self.assertGreaterEqual(int(got.split("+")[1]), 0)

    def test_nonsense_is_passed_through_untouched(self):
        for geo in ("", "not a geometry", "1400x820", None):
            self.assertEqual(self.on_screen(geo), geo)


class StateFile(unittest.TestCase):

    def test_accented_album_names_survive_a_round_trip(self):
        """The state file records the last album by name; several in the
        collection carry accents, and the platform default encoding is not
        UTF-8 everywhere."""
        with TemporaryDirectory() as td:
            real = pe.STATE_FILE
            pe.STATE_FILE = Path(td) / "state.json"
            self.addCleanup(setattr, pe, "STATE_FILE", real)

            state = {"album_name": "Sévérine's Worldcon — Björk & Ægir",
                     "geometry": "1400x820+120+80", "zoomed": True}
            pe._save_state(state)
            self.assertEqual(pe._load_state(), state)

    def test_a_missing_state_file_is_not_an_error(self):
        with TemporaryDirectory() as td:
            real = pe.STATE_FILE
            pe.STATE_FILE = Path(td) / "absent.json"
            self.addCleanup(setattr, pe, "STATE_FILE", real)
            self.assertEqual(pe._load_state(), {})

    def test_a_corrupt_state_file_falls_back_to_empty(self):
        with TemporaryDirectory() as td:
            real = pe.STATE_FILE
            pe.STATE_FILE = Path(td) / "state.json"
            self.addCleanup(setattr, pe, "STATE_FILE", real)
            pe.STATE_FILE.write_text("{ broken", encoding="utf-8")
            self.assertEqual(pe._load_state(), {})

    def test_the_file_is_written_as_readable_utf8(self):
        with TemporaryDirectory() as td:
            real = pe.STATE_FILE
            pe.STATE_FILE = Path(td) / "state.json"
            self.addCleanup(setattr, pe, "STATE_FILE", real)
            pe._save_state({"album_name": "Ægir"})
            raw = pe.STATE_FILE.read_text(encoding="utf-8")
            self.assertIn("Ægir", raw)          # not Ægir
            self.assertEqual(json.loads(raw)["album_name"], "Ægir")

    def test_no_temporary_file_is_left_behind(self):
        with TemporaryDirectory() as td:
            real = pe.STATE_FILE
            pe.STATE_FILE = Path(td) / "state.json"
            self.addCleanup(setattr, pe, "STATE_FILE", real)
            pe._save_state({"a": 1})
            self.assertEqual(list(Path(td).glob("*.tmp")), [])


if __name__ == "__main__":
    unittest.main()
