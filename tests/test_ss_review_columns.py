"""Turning a photo's review reports into the columns shown beside it.

Several people often identify the same faces in the same photo, so the review
screen shows every report for one photo side by side: a row per detected face,
a column per report, and each report's name for that face where they cross.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe, record                       # noqa: E402

pe = load_pe()


def face(number, name="", box=None):
    return {"number": number, "name": name,
            "box": box if box is not None else [number * 10, 20, 30, 40]}


class GroupingByPhoto(unittest.TestCase):

    def test_records_for_one_photo_come_together(self):
        recs = [record(11, "t1"), record(11, "t2"), record(22, "t3")]
        groups = pe._ss_group_by_photo(recs)
        self.assertEqual([[r["saved"] for r in g] for g in groups],
                         [["t1", "t2"], ["t3"]])

    def test_the_order_photos_arrived_in_is_kept(self):
        recs = [record(22, "t1"), record(11, "t2"), record(11, "t3")]
        groups = pe._ss_group_by_photo(recs)
        self.assertEqual([g[0]["photo id"] for g in groups], [22, 11])

    def test_records_with_no_photo_id_are_never_grouped(self):
        recs = [record(None, "t1"), record(None, "t2")]
        self.assertEqual(len(pe._ss_group_by_photo(recs)), 2)

    def test_no_records_no_groups(self):
        self.assertEqual(pe._ss_group_by_photo([]), [])


class FaceRows(unittest.TestCase):

    def test_one_row_per_detected_face_named_or_not(self):
        group = [record(11, "t1", faces=[face(1, "Bob"), face(2), face(3)])]
        rows = pe._ss_face_rows(group)
        self.assertEqual([r["number"] for r in rows], [1, 2, 3])

    def test_reports_sharing_a_detection_share_rows(self):
        """SlideShow's detection is deterministic, so two reports on one photo
        have the same boxes and must not produce duplicate rows."""
        faces = [face(1, "Bob"), face(2), face(3)]
        group = [record(11, "t1", faces=faces),
                 record(11, "t2", faces=[face(1), face(2, "Ann"), face(3)])]
        self.assertEqual(len(pe._ss_face_rows(group)), 3)

    def test_a_face_only_one_report_saw_still_gets_a_row(self):
        group = [record(11, "t1", faces=[face(1), face(2)]),
                 record(11, "t2", faces=[face(1), face(2), face(3)])]
        self.assertEqual([r["number"] for r in pe._ss_face_rows(group)], [1, 2, 3])

    def test_faces_are_matched_by_box_not_by_position(self):
        a = {"number": 1, "name": "", "box": [100, 10, 30, 40]}
        b = {"number": 2, "name": "", "box": [200, 10, 30, 40]}
        group = [record(11, "t1", faces=[a, b]),
                 record(11, "t2", faces=[b, a])]      # same faces, other order
        self.assertEqual(len(pe._ss_face_rows(group)), 2)

    def test_a_record_with_no_faces_contributes_no_rows(self):
        self.assertEqual(pe._ss_face_rows([record(11, "t1")]), [])


class ReportColumns(unittest.TestCase):

    def test_a_report_with_names_becomes_a_column(self):
        group = [record(11, "t1", faces=[face(1, "Bob Tucker"), face(2)])]
        cols = pe._ss_report_columns(group)
        self.assertEqual(len(cols), 1)
        self.assertEqual(list(cols[0]["names"].values()), ["Bob Tucker"])

    def test_a_report_with_only_a_comment_becomes_a_column(self):
        group = [record(11, "t1", comment="the man at the back is wrong")]
        self.assertEqual(len(pe._ss_report_columns(group)), 1)

    def test_a_report_saying_nothing_is_not_shown(self):
        """Someone opened the panel and saved without typing. Still has to be
        marked done, but there is nothing to put in a column."""
        group = [record(11, "t1", faces=[face(1), face(2)])]
        self.assertEqual(pe._ss_report_columns(group), [])

    def test_whitespace_only_content_counts_as_nothing(self):
        group = [record(11, "t1", comment="   ", faces=[face(1, "  ")])]
        self.assertEqual(pe._ss_report_columns(group), [])

    def test_identical_reports_collapse_into_one_column(self):
        """Real logs contain the same report saved twice a minute apart."""
        faces = [face(1, "Bob Macintosh"), face(2), face(3)]
        group = [record(11, "t1", faces=faces), record(11, "t2", faces=faces)]
        cols = pe._ss_report_columns(group)
        self.assertEqual(len(cols), 1)
        self.assertEqual(len(cols[0]["records"]), 2)      # both still get marked done

    def test_reports_that_differ_stay_apart(self):
        group = [record(11, "t1", faces=[face(1, "Bob Tucker")]),
                 record(11, "t2", faces=[face(1, "Bob Tucker"), face(2, "Ann")])]
        self.assertEqual(len(pe._ss_report_columns(group)), 2)

    def test_the_same_names_from_different_people_stay_apart(self):
        faces = [face(1, "Bob Tucker")]
        group = [record(11, "t1", faces=faces, editor="a@x"),
                 record(11, "t2", faces=faces, editor="b@x")]
        self.assertEqual(len(pe._ss_report_columns(group)), 2)

    def test_every_record_of_a_collapsed_column_is_kept(self):
        faces = [face(1, "Bob")]
        group = [record(11, f"t{i}", faces=faces) for i in range(3)]
        cols = pe._ss_report_columns(group)
        self.assertEqual([r["saved"] for r in cols[0]["records"]], ["t0", "t1", "t2"])


class ColumnHeadings(unittest.TestCase):

    def test_the_email_heads_the_column_when_given(self):
        col = {"records": [1], "editor": "mlo@x", "saved": "2026-08-28 17:30:40"}
        self.assertEqual(pe._ss_column_heading(col), "mlo@x")

    def test_the_save_time_stands_in_when_it_is_blank(self):
        """Every report in the current log has an empty editor field."""
        col = {"records": [1], "editor": "", "saved": "2026-08-28 17:30:40"}
        self.assertEqual(pe._ss_column_heading(col), "2026-08-28 17:30:40")

    def test_neither_still_gives_something_to_read(self):
        self.assertEqual(pe._ss_column_heading({"records": [1], "editor": "",
                                                "saved": ""}), "(unknown)")

    def test_collapsed_columns_say_how_many_arrived(self):
        col = {"records": [1, 2], "editor": "mlo@x", "saved": ""}
        self.assertEqual(pe._ss_column_heading(col), "mlo@x  ×2")


class AgainstTheRealLog(unittest.TestCase):
    """The shapes above, checked against a log SlideShow actually wrote."""

    @classmethod
    def setUpClass(cls):
        logs = sorted((Path(__file__).resolve().parent.parent.parent / "SlideShow")
                      .glob("*SlideShow Output *.json"))
        cls.records = pe._read_ss_records(logs[-1]) if logs else None

    def setUp(self):
        if self.records is None:
            self.skipTest("no SlideShow log on disk to check against")

    def test_photos_with_several_reports_group_correctly(self):
        groups = pe._ss_group_by_photo(self.records)
        self.assertEqual(sum(len(g) for g in groups), len(self.records))
        for g in groups:
            self.assertEqual(len({r.get("photo id") for r in g}), 1)

    def test_duplicate_submissions_collapse(self):
        multi = [g for g in pe._ss_group_by_photo(self.records) if len(g) > 1]
        if not multi:
            self.skipTest("this log has no photo with several reports")
        for group in multi:
            cols = pe._ss_report_columns(group)
            self.assertLessEqual(len(cols), len(group))


if __name__ == "__main__":
    unittest.main()
