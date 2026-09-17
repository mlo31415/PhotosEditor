"""A folder, or particular logs.

Review SS Comments used to read one folder.  It now reads either a folder --
every log in it, including any SlideShow writes while the review is open -- or
a list of particular logs, meaning those and no others.  The difference is not
visible in a path, so what matters is that each is carried through the setting,
the reading and the writing-back without being quietly turned into the other.
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


def a_record(pid, saved, name="Someone"):
    return {"saved": saved, "photo id": pid, "file": f"p{pid}.jpg",
            "album": "A", "editor": "a@x", "comment": "", "photo date": "",
            "faces": [{"number": 1, "name": name, "box": [10, 10, 40, 50]}]}


class Logs(unittest.TestCase):
    """Three logs in one folder, one record each."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.logs = []
        for n, pid in enumerate((11, 22, 33), start=1):
            path = self.tmp / f"SlideShow Output 2026-09-0{n} 10.00.00.json"
            path.write_text(json.dumps(a_record(pid, f"2026-09-0{n} 10:00:00"),
                                       indent=2) + "\n\n", encoding="utf-8")
            self.logs.append(path)
        self._real_store = pe._store
        pe._store = CredentialStore(self.tmp, "PhotosEditor Params.json")

    def tearDown(self):
        pe._store = self._real_store

    def setting(self):
        return next(s for s in pe._OP_PARAMS if s.key == pe.SS_REVIEW_DIR_KEY)


class WhichLogsASourceNames(Logs):

    def test_a_folder_means_every_log_in_it(self):
        self.assertEqual(pe._ss_logs_in(str(self.tmp)), sorted(self.logs))

    def test_a_list_means_those_and_no_others(self):
        chosen = [str(self.logs[0]), str(self.logs[2])]
        self.assertEqual(pe._ss_logs_in(chosen), [self.logs[0], self.logs[2]])

    def test_a_folder_picks_up_a_log_written_later(self):
        """Which is why a folder is kept as a folder rather than turned into
        the list of files it held at the time."""
        later = self.tmp / "SlideShow Output 2026-09-09 10.00.00.json"
        later.write_text(json.dumps(a_record(44, "2026-09-09 10:00:00"),
                                    indent=2) + "\n\n", encoding="utf-8")
        self.assertIn(later, pe._ss_logs_in(str(self.tmp)))
        self.assertNotIn(later, pe._ss_logs_in([str(p) for p in self.logs]))

    def test_a_chosen_log_that_has_gone_is_left_out(self):
        self.logs[1].unlink()
        self.assertEqual(pe._ss_logs_in([str(p) for p in self.logs]),
                         [self.logs[0], self.logs[2]])

    def test_nothing_set_names_nothing(self):
        self.assertEqual(pe._ss_logs_in(""), [])
        self.assertEqual(pe._ss_logs_in([]), [])

    def test_a_folder_that_is_not_there_names_nothing(self):
        self.assertEqual(pe._ss_logs_in(str(self.tmp / "gone")), [])


class ReadingRecordsFromEither(Logs):

    def test_a_folder_yields_every_log_s_records(self):
        got = [r["photo id"] for r in pe._collect_ss_records(str(self.tmp))]
        self.assertEqual(sorted(got), [11, 22, 33])

    def test_chosen_logs_yield_only_theirs(self):
        got = [r["photo id"]
               for r in pe._collect_ss_records([str(self.logs[1])])]
        self.assertEqual(got, [22])

    def test_marking_done_writes_back_to_a_chosen_log(self):
        chosen = [str(self.logs[1])]
        rec = pe._collect_ss_records(chosen)[0]
        found, _ = pe._ss_mark_record_done_in_log(chosen, rec)
        self.assertTrue(found)
        self.assertEqual(pe._collect_ss_records(chosen), [])

    def test_a_record_from_a_log_outside_the_choice_is_not_found(self):
        """Not an error to report as one: the choice is what it says it is."""
        rec = pe._collect_ss_records(str(self.tmp))[0]      # from the first log
        found, _ = pe._ss_mark_record_done_in_log([str(self.logs[2])], rec)
        self.assertFalse(found)


class TheSettingHoldsEither(Logs):

    def test_one_folder_is_stored_as_a_folder(self):
        got = pe._parse_setting(self.setting(), str(self.tmp))
        self.assertEqual(got, str(self.tmp.resolve()))

    def test_one_file_is_stored_as_a_list_of_one(self):
        got = pe._parse_setting(self.setting(), str(self.logs[0]))
        self.assertEqual(got, [str(self.logs[0].resolve())])

    def test_several_files_are_split_on_semicolons(self):
        typed = f"{self.logs[0]} ; {self.logs[2]}"
        self.assertEqual(pe._parse_setting(self.setting(), typed),
                         [str(self.logs[0].resolve()),
                          str(self.logs[2].resolve())])

    def test_a_file_that_is_not_there_is_refused(self):
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting(),
                              f"{self.logs[0]};{self.tmp / 'gone.json'}")
        self.assertIn("nothing at", str(caught.exception))

    def test_two_folders_are_refused(self):
        other = self.tmp / "another"
        other.mkdir()
        with self.assertRaises(ValueError) as caught:
            pe._parse_setting(self.setting(), f"{self.tmp};{other}")
        self.assertIn("only one folder", str(caught.exception))

    def test_a_list_survives_the_round_trip_through_the_file(self):
        chosen = [str(self.logs[0]), str(self.logs[1])]
        out = pe.PhotosEditor._settings_to_write({pe.SS_REVIEW_DIR_KEY: chosen})
        (self.tmp / "PhotosEditor Params.json").write_text(
            json.dumps(out), encoding="utf-8")
        self.assertEqual(pe._ss_review_source(), chosen)

    def test_the_box_shows_a_list_the_way_it_reads_one_back(self):
        chosen = [str(self.logs[0]), str(self.logs[1])]
        shown = pe._setting_display(self.setting(), chosen)
        self.assertEqual(pe._parse_setting(self.setting(), shown), chosen)


class WhatTheBoxSaysItAmountsTo(Logs):
    """The line under the box, which is the only thing saying whether a path
    means a folderful of logs or just those files."""

    def summary(self, text):
        return pe._ss_choice_summary(text, pe.SS_LOG_GLOB)[0]

    def colour(self, text):
        return pe._ss_choice_summary(text, pe.SS_LOG_GLOB)[1]

    def test_a_folder_is_counted_and_said_to_be_open_ended(self):
        said = self.summary(str(self.tmp))
        self.assertIn("every", said)
        self.assertIn("3", said)

    def test_an_empty_folder_is_called_out(self):
        empty = self.tmp / "empty"
        empty.mkdir()
        self.assertIn("no", self.summary(str(empty)))
        self.assertEqual(self.colour(str(empty)), "#a04000")

    def test_one_file_says_that_one_only(self):
        self.assertEqual(self.summary(str(self.logs[0])), "that one file only")

    def test_several_files_are_counted(self):
        said = self.summary(f"{self.logs[0]};{self.logs[1]}")
        self.assertIn("those 2 files only", said)

    def test_a_file_that_has_gone_is_called_out(self):
        self.logs[1].unlink()
        said = self.summary(f"{self.logs[0]};{self.logs[1]}")
        self.assertIn("no longer there", said)
        self.assertEqual(self.colour(f"{self.logs[0]};{self.logs[1]}"), "#a04000")

    def test_a_file_that_is_not_a_slideshow_log_is_called_out(self):
        stray = self.tmp / "notes.txt"
        stray.write_text("hello", encoding="utf-8")
        said = self.summary(f"{self.logs[0]};{stray}")
        self.assertIn(f"not a {pe.SS_LOG_GLOB} file", said)

    def test_an_empty_box_says_nothing(self):
        self.assertEqual(self.summary("   "), "")


if __name__ == "__main__":
    unittest.main()
