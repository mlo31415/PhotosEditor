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
        self.assertEqual(known["Maximum upload size"],
                         ("4000 thousand pixels", True))
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


class ShownInItsOwnUnits(unittest.TestCase):
    """The file keeps a pixel count -- width × height, as w*h > max_pixels
    compares it -- which is an awkward number to read.  The window shows it in
    thousands, so four megapixels reads as 4000."""

    def setting(self, key):
        return next(s for s in pe._OP_PARAMS if s.key == key)

    def test_four_million_pixels_shows_as_4000(self):
        self.assertEqual(
            pe._setting_display(self.setting("max_upload_pixels"), 4000000), "4000")

    def test_and_survives_the_round_trip(self):
        setting = self.setting("max_upload_pixels")
        for pixels in (4000000, 2500000, 500000, 1000):
            with self.subTest(pixels=pixels):
                shown = pe._setting_display(setting, pixels)
                self.assertEqual(pe._parse_setting(setting, shown), pixels)

    def test_an_odd_number_keeps_its_fraction_rather_than_lying(self):
        self.assertEqual(
            pe._setting_display(self.setting("max_upload_pixels"), 4000500), "4000.5")

    def test_not_set_shows_as_an_empty_box(self):
        self.assertEqual(
            pe._setting_display(self.setting("max_upload_pixels"), None), "")

    def test_an_unscaled_setting_shows_its_own_number(self):
        self.assertEqual(
            pe._setting_display(self.setting("rate_limit_calls_per_second"), 2.0),
            "2.0")

    def test_a_checkbox_setting_reads_yes_or_no(self):
        uploads = self.setting("uploads_enabled")
        self.assertEqual(pe._setting_display(uploads, True), "Yes")
        self.assertEqual(pe._setting_display(uploads, False), "No")


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


class WhatGetsWritten(Rows):
    """Saving replaces the file, which is also how a setting the program no
    longer reads leaves it."""

    def written(self, values):
        out = pe.PhotosEditor._settings_to_write(values)
        self.assertTrue(pe._save_op_params(out))
        return json.loads((self.tmp / "PhotosEditor Params.json").read_text())

    def test_the_settings_are_written(self):
        on_disk = self.written({"uploads_enabled": True,
                                "max_upload_pixels": 2000000,
                                "sync_metadata": False,
                                "refresh_representative": True,
                                "rate_limit_calls_per_second": 1.5})
        self.assertEqual(on_disk["uploads_enabled"], True)
        self.assertEqual(on_disk["max_upload_pixels"], 2000000)
        self.assertEqual(on_disk["rate_limit_calls_per_second"], 1.5)

    def test_a_key_the_program_does_not_read_is_dropped(self):
        self.write({"path": ".", "left_over": 7, "uploads_enabled": True})
        on_disk = self.written({"uploads_enabled": True})
        self.assertNotIn("path", on_disk)
        self.assertNotIn("left_over", on_disk)

    def test_a_blank_setting_is_left_out_rather_than_written_as_null(self):
        on_disk = self.written({"max_upload_pixels": None})
        self.assertNotIn("max_upload_pixels", on_disk)

    def test_what_is_written_reads_back_the_same(self):
        self.written({"uploads_enabled": True, "max_upload_pixels": 500000,
                      "sync_metadata": False, "refresh_representative": False,
                      "rate_limit_calls_per_second": 3.0})
        known, others = self.rows()
        self.assertEqual(known["Uploading enabled"], ("Yes", True))
        self.assertEqual(known["Maximum upload size"], ("500 thousand pixels", True))
        self.assertEqual(known["Refresh album thumbnail"], ("No", True))
        self.assertEqual(others, [])


class ReadingWhatWasTyped(unittest.TestCase):

    def setting(self, key):
        return next(s for s in pe._OP_PARAMS if s.key == key)

    def test_typed_units_become_the_number_the_file_keeps(self):
        """The box is in thousands of pixels; the file stays in pixels."""
        self.assertEqual(pe._parse_setting(self.setting("max_upload_pixels"),
                                           "4000"), 4000000)

    def test_separators_are_forgiven(self):
        self.assertEqual(pe._parse_setting(self.setting("max_upload_pixels"),
                                           "2,500"), 2500000)

    def test_a_fraction_of_a_unit_is_fine_when_the_pixels_come_out_whole(self):
        self.assertEqual(pe._parse_setting(self.setting("max_upload_pixels"),
                                           "4000.5"), 4000500)

    def test_an_unscaled_setting_is_unaffected(self):
        self.assertEqual(pe._parse_setting(
            self.setting("rate_limit_calls_per_second"), "1.5"), 1.5)

    def test_a_blank_means_not_set_where_that_is_allowed(self):
        self.assertIsNone(pe._parse_setting(self.setting("max_upload_pixels"), "  "))

    def test_a_blank_is_refused_where_there_is_a_default_to_lose(self):
        with self.assertRaises(ValueError):
            pe._parse_setting(self.setting("rate_limit_calls_per_second"), "")

    def test_words_are_refused(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting("max_upload_pixels"), "lots")
        self.assertIn("whole number", str(caught.exception))

    def test_a_fraction_is_refused_when_the_pixels_would_not_come_out_whole(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting("max_upload_pixels"), "3.0005")
        self.assertIn("whole number", str(caught.exception))

    def test_the_message_says_which_units(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting("max_upload_pixels"), "lots")
        self.assertIn("thousand pixels", str(caught.exception))

    def test_zero_and_below_are_refused(self):
        for text in ("0", "-1"):
            with self.subTest(text):
                with self.assertRaises(ValueError) as caught:
                    pe._parse_setting(self.setting("rate_limit_calls_per_second"), text)
                self.assertIn("greater than zero", str(caught.exception))


class WhenARestartIsNeeded(unittest.TestCase):
    """Every setting is read from the file where it is used, so none of them
    need one today.  The machinery is here for one that ever does."""

    def test_nothing_currently_asks_for_a_restart(self):
        self.assertEqual([s.key for s in pe._OP_PARAMS if s.restart_needed], [])

    def test_no_setting_is_read_once_at_start_up(self):
        """Which is why nothing needs a restart.  If a params read ever moves
        into __init__ or module scope, this fails and the flag must be set."""
        import ast
        source = Path(pe.__file__).read_text(encoding="utf-8")

        class Where(ast.NodeVisitor):
            def __init__(self):
                self.stack, self.bad = [], []

            def visit_FunctionDef(self, node):
                self.stack.append(node.name)
                self.generic_visit(node)
                self.stack.pop()

            def visit_Call(self, node):
                func = node.func
                if (isinstance(func, ast.Attribute)
                        and func.attr == "load_op_params"
                        and (not self.stack or self.stack[0] == "__init__")):
                    self.bad.append(node.lineno)
                self.generic_visit(node)

        finder = Where()
        finder.visit(ast.parse(source))
        self.assertEqual(finder.bad, [],
                         "a setting is now read at start-up and held; the "
                         "matching _OP_PARAMS entry needs restart_needed=True")


class TheSlideShowFolder(Rows):
    """It used to be remembered in the state file, as a relative path resolved
    against wherever the program was started from.  It is a setting now."""

    def setting(self):
        return next(s for s in pe._OP_PARAMS if s.key == pe.SS_REVIEW_DIR_KEY)

    def test_it_is_a_setting_the_window_shows(self):
        known, _ = self.rows({})
        self.assertIn("SlideShow output folder", known)

    def test_an_absolute_folder_is_taken_as_it_is(self):
        self.assertEqual(pe._parse_setting(self.setting(), str(self.tmp)),
                         str(self.tmp.resolve()))

    def test_a_relative_one_is_made_absolute(self):
        """So it no longer depends on the directory the program started in."""
        got = pe._parse_setting(self.setting(), ".")
        self.assertTrue(Path(got).is_absolute(), got)

    def test_a_folder_that_is_not_there_is_refused(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting(), str(self.tmp / "no such folder"))
        self.assertIn("no folder at", str(caught.exception))

    def test_blank_means_not_set_rather_than_an_error(self):
        self.assertIsNone(pe._parse_setting(self.setting(), "  "))

    def test_it_is_written_to_the_params_file(self):
        out = pe.PhotosEditor._settings_to_write(
            {pe.SS_REVIEW_DIR_KEY: str(self.tmp)})
        self.assertEqual(out[pe.SS_REVIEW_DIR_KEY], str(self.tmp))

    def test_reading_it_back_resolves_a_relative_one(self):
        self.write({pe.SS_REVIEW_DIR_KEY: "XX Photos"})
        got = pe._ss_review_dir()
        self.assertTrue(Path(got).is_absolute(), got)
        self.assertTrue(got.endswith("XX Photos"), got)

    def test_nothing_set_reads_as_empty(self):
        self.write({})
        self.assertEqual(pe._ss_review_dir(), "")


class MovingItOutOfTheStateFile(Rows):

    def test_an_old_state_file_hands_it_over(self):
        state = {"ss_review_dir": str(self.tmp), "zoomed": True}
        pe._migrate_ss_review_dir(state)
        self.assertNotIn("ss_review_dir", state, "left behind in the state")
        self.assertEqual(pe._store.load_op_params()[pe.SS_REVIEW_DIR_KEY],
                         str(self.tmp.resolve()))
        self.assertEqual(state["zoomed"], True, "the rest of the state survived")

    def test_a_setting_already_there_is_not_overwritten(self):
        self.write({pe.SS_REVIEW_DIR_KEY: str(self.tmp)})
        state = {"ss_review_dir": str(self.tmp / "somewhere else")}
        pe._migrate_ss_review_dir(state)
        self.assertEqual(pe._store.load_op_params()[pe.SS_REVIEW_DIR_KEY],
                         str(self.tmp))

    def test_a_folder_that_has_gone_is_not_carried_over(self):
        state = {"ss_review_dir": str(self.tmp / "gone")}
        pe._migrate_ss_review_dir(state)
        self.assertNotIn(pe.SS_REVIEW_DIR_KEY, pe._store.load_op_params())

    def test_nothing_to_move_is_not_an_error(self):
        state = {"zoomed": False}
        pe._migrate_ss_review_dir(state)
        self.assertNotIn(pe.SS_REVIEW_DIR_KEY, pe._store.load_op_params())


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
        listed = {s.key for s in pe._OP_PARAMS}
        self.assertEqual(read - listed, set(),
                         "settings read by the program but missing from _OP_PARAMS")


if __name__ == "__main__":
    unittest.main()
