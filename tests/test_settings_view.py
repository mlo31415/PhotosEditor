"""What the Settings window shows.

The values come from the parameters file, but a setting the file does not
mention still has to appear: what the program will actually use is exactly
what a person opening this window wants to know, and the absent ones are the
easiest to get wrong.  So the rows are built from the list of settings the
program reads, not from the file's keys.
"""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "PiwigoHelpers"))
from CredentialStore import CredentialStore                    # noqa: E402


class Rows(unittest.TestCase):
    """Each run gets its own params file; the real one is never read."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self._real_store = pe._store
        pe._store = CredentialStore(self.tmp, "PhotosEditor Params.json")

    def tearDown(self):
        pe._store = self._real_store

    def write(self, params):
        (self.tmp / "PhotosEditor Params.json").write_text(
            json.dumps(params), encoding="utf-8")

    def rows(self, params=None):
        if params is not None:
            self.write(params)
        known, others = pe.PhotosEditor._settings_rows()
        return {label: (value, in_file) for label, value, in_file, _ in known}, others


class EverySettingAppears(Rows):

    def test_all_of_them_even_with_no_file_at_all(self):
        known, others = self.rows()
        self.assertEqual(len(known), len(pe._OP_PARAMS))
        self.assertEqual(others, [])

    def test_a_setting_the_file_omits_shows_what_will_be_used(self):
        """Uploading is off unless the file says so; the window has to say off,
        not blank."""
        known, _ = self.rows({})
        self.assertEqual(known["Uploading enabled"], ("No", False))
        self.assertEqual(known["Sync metadata after upload"], ("Yes", False))
        self.assertEqual(known["Server calls per second"], ("2.0", False))

    def test_a_setting_the_file_gives_is_marked_as_from_the_file(self):
        known, _ = self.rows({"uploads_enabled": True})
        self.assertEqual(known["Uploading enabled"], ("Yes", True))

    def test_the_file_wins_over_the_default(self):
        known, _ = self.rows({"sync_metadata": False,
                              "rate_limit_calls_per_second": 0.5})
        self.assertEqual(known["Sync metadata after upload"], ("No", True))
        self.assertEqual(known["Server calls per second"], ("0.5", True))

    def test_the_real_settings_file_is_covered(self):
        """Every key the live file holds is either a known setting or shown
        under 'also in the file'."""
        self.write({"path": ".", "sync_metadata": False,
                    "refresh_representative": True,
                    "max_upload_pixels": 4000000})
        known, others = self.rows()
        self.assertEqual(known["Maximum upload size"], ("4,000,000", True))
        self.assertEqual(known["Refresh album thumbnail"], ("Yes", True))
        self.assertEqual(others, [("path", ".")])


class KeysTheProgramDoesNotRead(Rows):

    def test_they_are_shown_rather_than_hidden(self):
        """A leftover from an older version, or another program's setting."""
        known, others = self.rows({"path": ".", "left_over": 7})
        self.assertEqual(others, [("left_over", "7"), ("path", ".")])
        self.assertNotIn("left_over", known)

    def test_nothing_extra_means_nothing_shown(self):
        _, others = self.rows({"uploads_enabled": True})
        self.assertEqual(others, [])


class HowValuesAreWritten(unittest.TestCase):

    def test_true_and_false_read_as_yes_and_no(self):
        self.assertEqual(pe._format_setting(True), "Yes")
        self.assertEqual(pe._format_setting(False), "No")

    def test_a_big_number_gets_its_separators(self):
        self.assertEqual(pe._format_setting(4000000), "4,000,000")

    def test_a_small_number_does_not(self):
        self.assertEqual(pe._format_setting(92), "92")
        self.assertEqual(pe._format_setting(2.0), "2.0")

    def test_nothing_set_says_so(self):
        self.assertEqual(pe._format_setting(None), "(not set)")
        self.assertEqual(pe._format_setting(""), "(not set)")

    def test_a_string_comes_through(self):
        self.assertEqual(pe._format_setting("."), ".")


class TheListItself(unittest.TestCase):

    def test_it_covers_every_key_the_program_reads(self):
        """A setting added to the program and not to _OP_PARAMS is one the
        user cannot see, so this checks the source for stragglers."""
        import re
        source = (Path(pe.__file__).read_text(encoding="utf-8")
                  if getattr(pe, "__file__", None) else "")
        if not source:
            self.skipTest("no source to scan")
        read = set(re.findall(r"params\.get\('([a-z_]+)'", source))
        read |= set(re.findall(r"load_op_params\(\)\.get\('([a-z_]+)'", source))
        listed = {key for key, _, _, _ in pe._OP_PARAMS}
        self.assertEqual(read - listed, set(),
                         "settings read by the program but missing from _OP_PARAMS")


if __name__ == "__main__":
    unittest.main()
