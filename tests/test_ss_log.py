"""The SlideShow log handling: identity, ordering, and the writes PE makes.

This is the code that edits the user's own SlideShow logs, so it gets the
closest attention: a rewrite must reproduce SlideShow's formatting exactly,
must not lose a record SlideShow appended in the meantime, and must mark
exactly the record it was asked to mark.
"""
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe, write_log, record          # noqa: E402

pe = load_pe()


class RecordKey(unittest.TestCase):
    """A record's identity has to survive PE's own annotations, or a record
    would stop being findable the moment PE touched it."""

    def setUp(self):
        self.rec = record(11, "2026-08-18 16:04:55", "Bob Tucker")

    def test_log_file_annotation_does_not_change_it(self):
        annotated = dict(self.rec, **{"_log file": "SlideShow Output x.json"})
        self.assertEqual(pe._ss_record_key(self.rec), pe._ss_record_key(annotated))

    def test_renaming_the_log_does_not_change_it(self):
        a = dict(self.rec, **{"_log file": "one.json"})
        b = dict(self.rec, **{"_log file": "two.json"})
        self.assertEqual(pe._ss_record_key(a), pe._ss_record_key(b))

    def test_the_done_flag_does_not_change_it(self):
        self.assertEqual(pe._ss_record_key(self.rec),
                         pe._ss_record_key(dict(self.rec, done=True)))

    def test_same_photo_same_second_still_differ(self):
        a = record(11, "2026-08-18 16:04:55", "Bob Tucker")
        b = record(11, "2026-08-18 16:04:55", "Forry Ackerman")
        self.assertNotEqual(pe._ss_record_key(a), pe._ss_record_key(b))

    def test_different_face_names_are_enough(self):
        a = record(11, "t", "same", faces=[{"number": 1, "name": "X", "box": [1, 2, 3, 4]}])
        b = record(11, "t", "same", faces=[{"number": 1, "name": "Y", "box": [1, 2, 3, 4]}])
        self.assertNotEqual(pe._ss_record_key(a), pe._ss_record_key(b))

    def test_records_without_a_photo_id_do_not_collide(self):
        self.assertNotEqual(pe._ss_record_key(record(None, "t", "one")),
                            pe._ss_record_key(record(None, "t", "two")))

    def test_key_order_does_not_matter(self):
        shuffled = {k: v for k, v in sorted(self.rec.items(), reverse=True)}
        self.assertEqual(pe._ss_record_key(self.rec), pe._ss_record_key(shuffled))


class ReadAndWrite(unittest.TestCase):

    def test_round_trip_is_byte_identical(self):
        """PE must not reformat a log it merely rewrites, or every save would
        produce a spurious diff."""
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00", [
                record(1, "t1", "a caption",
                       faces=[{"number": 1, "name": "Bob", "box": [4, 104, 26, 34]}]),
                record(2, "t2", "another"),
            ])
            before = log.read_text(encoding="utf-8")
            pe._ss_write_records(log, pe._read_ss_records(log))
            self.assertEqual(before, log.read_text(encoding="utf-8"))

    def test_face_boxes_stay_on_one_line(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00", [
                record(1, "t1", faces=[{"number": 1, "name": "", "box": [4, 104, 26, 34]}])])
            pe._ss_write_records(log, pe._read_ss_records(log))
            self.assertIn("[4, 104, 26, 34]", log.read_text(encoding="utf-8"))

    def test_internal_annotations_are_not_written_out(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00", [record(1, "t1")])
            recs = pe._read_ss_records(log)
            recs[0]["_log file"] = "should not be saved"
            pe._ss_write_records(log, recs)
            self.assertNotIn("_log file", log.read_text(encoding="utf-8"))

    def test_a_corrupt_log_is_skipped_not_fatal(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00", [record(1, "t1")])
            (d / "SlideShow Output 2026-08-02 11.00.00.json").write_text(
                "{not json", encoding="utf-8")
            self.assertEqual([r["photo id"] for r in pe._collect_ss_records(d)], [1])


class Ordering(unittest.TestCase):
    """Photos carrying several comments come first, with their records
    adjacent, so they can be dealt with together."""

    def _dir(self, d):
        write_log(d, "2026-08-01 10.00.00",
                  [record(100, "t1"), record(200, "t2"), record(400, "t3")])
        write_log(d, "2026-08-02 11.00.00",
                  [record(300, "t4"), record(200, "t5"),
                   record(300, "t6"), record(500, "t7")])

    def test_multi_record_photos_come_first_and_together(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            self._dir(d)
            got = [(r["photo id"], r["saved"]) for r in pe._collect_ss_records(d)]
            self.assertEqual(got[:4], [(200, "t2"), (200, "t5"),
                                       (300, "t4"), (300, "t6")])
            self.assertEqual(got[4:], [(100, "t1"), (400, "t3"), (500, "t7")])

    def test_done_records_are_not_offered(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            self._dir(d)
            first = pe._collect_ss_records(d)[0]
            pe._ss_mark_record_done_in_log(d, first)
            still = [(r["photo id"], r["saved"]) for r in pe._collect_ss_records(d)]
            self.assertNotIn((first["photo id"], first["saved"]), still)

    def test_records_without_a_photo_id_are_not_grouped_together(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00",
                      [record(None, "t1", "one"), record(None, "t2", "two")])
            got = pe._collect_ss_records(d)
            self.assertEqual(len(got), 2)          # two singles, not one pair


class MarkingDone(unittest.TestCase):

    def test_marks_exactly_one_record(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00",
                            [record(11, "t1", "first"), record(11, "t2", "second")])
            target = pe._collect_ss_records(d)[0]
            found, completed = pe._ss_mark_record_done_in_log(d, target)
            self.assertTrue(found)
            self.assertIsNone(completed)          # one of two still open
            self.assertEqual([r.get("done") for r in pe._read_ss_records(log)],
                             [True, None])

    def test_a_record_appended_meanwhile_is_not_lost(self):
        """SlideShow may append while a review is open; PE re-reads before it
        rewrites, so the newcomer must survive."""
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00",
                            [record(11, "t1"), record(22, "t2")])
            stale = pe._collect_ss_records(d)[0]           # read before the append
            with open(log, "a", encoding="utf-8") as f:
                f.write(json.dumps(record(99, "t9"), indent=2) + "\n\n")
            pe._ss_mark_record_done_in_log(d, stale)
            self.assertIn(99, [r["photo id"] for r in pe._read_ss_records(log)])

    def test_found_after_slideshow_renames_the_log(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            log = write_log(d, "2026-08-01 10.00.00", [record(11, "t1"), record(22, "t2")])
            rec = pe._collect_ss_records(d)[0]
            renamed = d / "SlideShow Output 2026-08-01 12.00.00.json"
            log.rename(renamed)                            # as SlideShow does on save
            found, _ = pe._ss_mark_record_done_in_log(d, rec)
            self.assertTrue(found)
            self.assertTrue(any(r.get("done") for r in pe._read_ss_records(renamed)))

    def test_an_unknown_record_reports_failure(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00", [record(11, "t1")])
            found, completed = pe._ss_mark_record_done_in_log(
                d, record(-1, "1999-01-01 00:00:00"))
            self.assertFalse(found)
            self.assertIsNone(completed)

    def test_no_temporary_files_are_left_behind(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00", [record(11, "t1")])
            pe._ss_mark_record_done_in_log(d, pe._collect_ss_records(d)[0])
            self.assertEqual(list(d.glob("*.tmp")), [])


class CompletedLogs(unittest.TestCase):

    def test_finishing_a_log_renames_it_and_drops_it_from_the_scan(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00", [record(11, "t1")])
            _, completed = pe._ss_mark_record_done_in_log(d, pe._collect_ss_records(d)[0])
            self.assertIsNotNone(completed)
            self.assertTrue(completed.name.startswith(pe.SS_COMPLETED_PREFIX))
            self.assertEqual(pe._collect_ss_records(d), [])
            # ...and the records are still in there
            self.assertEqual([r["photo id"] for r in pe._read_ss_records(completed)], [11])

    def test_a_clash_does_not_overwrite_an_existing_completed_log(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            write_log(d, "2026-08-01 10.00.00", [record(11, "t1")])
            _, first = pe._ss_mark_record_done_in_log(d, pe._collect_ss_records(d)[0])
            write_log(d, "2026-08-01 10.00.00", [record(99, "t9")])   # same name again
            _, second = pe._ss_mark_record_done_in_log(d, pe._collect_ss_records(d)[0])
            self.assertNotEqual(first, second)
            self.assertEqual([r["photo id"] for r in pe._read_ss_records(first)], [11])
            self.assertEqual([r["photo id"] for r in pe._read_ss_records(second)], [99])

    def test_renaming_an_already_prefixed_log_is_a_no_op(self):
        with TemporaryDirectory() as td:
            d = Path(td)
            p = d / (pe.SS_COMPLETED_PREFIX + "SlideShow Output 2026-08-01 10.00.00.json")
            p.write_text("", encoding="utf-8")
            self.assertIsNone(pe._ss_rename_completed_log(p))


if __name__ == "__main__":
    unittest.main()
