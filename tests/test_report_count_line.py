"""The line above the matrix, when reports and columns are not the same number.

A user asked how "2 reports" could show one column, and suspected the count was
including a report already dealt with.  It was not -- done records never reach
a group -- but there was no way to tell that from the screen.  Two reports
saying the same thing share a column, and a report saying nothing gets none
while still having to be marked done.  The line now says which.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe, record                           # noqa: E402

pe = load_pe()


def face(number, name=""):
    return {"number": number, "name": name, "box": [number*10, 20, 30, 40]}


class Line:
    """_ss_set_count without a window: it only needs the columns and a var."""

    def __init__(self, group, index=0, total=1):
        class Var:
            text = ""

            def set(self, value):
                self.text = value

        self.var = Var()
        self._ss_count_var = self.var
        self._ss_group_index = index
        self._ss_groups = [None]*total
        self._ss_columns = pe._ss_report_columns(group)
        pe.PhotosEditor._ss_set_count(self, group)

    def __str__(self):
        return self.var.text


class WhenTheyAgree(unittest.TestCase):

    def test_one_report_one_column(self):
        group = [record(11, "t1", faces=[face(1, "Bob Tucker")])]
        self.assertEqual(str(Line(group, 0, 29)),
                         "Photo 1 of 29   —   1 report")

    def test_two_reports_two_columns_say_no_more(self):
        group = [record(11, "t1", faces=[face(1, "Bob Tucker")], editor="a@x"),
                 record(11, "t2", faces=[face(1, "Ann Green")], editor="b@x")]
        self.assertEqual(str(Line(group, 0, 29)),
                         "Photo 1 of 29   —   2 reports")


class WhenTheyDoNot(unittest.TestCase):

    def test_two_identical_reports_say_so(self):
        """The reported case: photo 9938 carries the same report twice."""
        faces = [face(1, "Arthur Thomson (ATom)"), face(2, "Wrai Ballard")]
        group = [record(11, "t1", faces=faces), record(11, "t2", faces=faces)]
        line = str(Line(group, 0, 29))
        self.assertIn("2 reports in 1 column", line)
        self.assertIn("identical ones share a column", line)

    def test_a_report_that_says_nothing_is_counted_out_loud(self):
        group = [record(11, "t1", faces=[face(1, "Bob Tucker")]),
                 record(11, "t2", faces=[face(1), face(2)])]
        line = str(Line(group, 0, 29))
        self.assertIn("2 reports in 1 column", line)
        self.assertIn("1 said nothing", line)

    def test_both_at_once(self):
        faces = [face(1, "Bob Tucker")]
        group = [record(11, "t1", faces=faces),
                 record(11, "t2", faces=faces),
                 record(11, "t3", faces=[face(1)])]
        line = str(Line(group, 0, 29))
        self.assertIn("3 reports in 1 column", line)
        self.assertIn("identical ones share a column", line)
        self.assertIn("1 said nothing", line)

    def test_two_silent_reports_are_counted(self):
        group = [record(11, "t1", faces=[face(1, "Bob")]),
                 record(11, "t2", faces=[face(1)]),
                 record(11, "t3", faces=[face(1)])]
        self.assertIn("2 said nothing", str(Line(group, 0, 29)))

    def test_every_report_saying_nothing_leaves_no_columns(self):
        group = [record(11, "t1", faces=[face(1)]), record(11, "t2")]
        line = str(Line(group, 0, 29))
        self.assertIn("2 reports in 0 columns", line)
        self.assertIn("2 said nothing", line)


class WhatTheCountIsOf(unittest.TestCase):
    """The user's guess was that the count included a report already dealt
    with.  It cannot: done records are dropped before a group is made."""

    def test_done_records_never_reach_a_group(self):
        recs = [record(11, "t1", faces=[face(1, "Bob")]),
                dict(record(11, "t2", faces=[face(1, "Ann")]), done=True)]
        kept = [r for r in recs if not r.get("done")]
        groups = pe._ss_group_by_photo(kept)
        self.assertEqual(len(groups[0]), 1)
        self.assertEqual(str(Line(groups[0], 0, 29)),
                         "Photo 1 of 29   —   1 report")


if __name__ == "__main__":
    unittest.main()
