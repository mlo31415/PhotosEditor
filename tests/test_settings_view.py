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
        self.written({"uploads_enabled": True, "max_upload_pixels": 500,
                      "sync_metadata": False, "refresh_representative": False,
                      "rate_limit_calls_per_second": 3.0})
        known, others = self.rows()
        self.assertEqual(known["Uploading enabled"], ("Yes", True))
        self.assertEqual(known["Maximum upload size"], ("500", True))
        self.assertEqual(known["Refresh album thumbnail"], ("No", True))
        self.assertEqual(others, [])


class ReadingWhatWasTyped(unittest.TestCase):

    def setting(self, key):
        return next(s for s in pe._OP_PARAMS if s.key == key)

    def test_a_number_is_taken(self):
        self.assertEqual(pe._parse_setting(self.setting("max_upload_pixels"),
                                           "4000000"), 4000000)

    def test_separators_are_forgiven(self):
        """The window shows 4,000,000, so it has to accept it back."""
        self.assertEqual(pe._parse_setting(self.setting("max_upload_pixels"),
                                           "4,000,000"), 4000000)

    def test_a_blank_means_not_set_where_that_is_allowed(self):
        self.assertIsNone(pe._parse_setting(self.setting("max_upload_pixels"), "  "))

    def test_a_blank_is_refused_where_there_is_a_default_to_lose(self):
        with self.assertRaises(ValueError):
            pe._parse_setting(self.setting("rate_limit_calls_per_second"), "")

    def test_words_are_refused(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting("max_upload_pixels"), "lots")
        self.assertIn("whole number", str(caught.exception))

    def test_a_fraction_is_refused_where_a_whole_number_is_wanted(self):
        with self.assertRaises(ValueError):
            pe._parse_setting(self.setting("max_upload_pixels"), "3.5")

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
