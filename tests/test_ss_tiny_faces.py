"""Faces too small to identify are left out of the review rows.

SlideShow now discards them before it writes a report, by the shared rule in
FaceGeometry.  Logs written before that still carry them, and a crowd photo can
offer a column of rows cut from a dozen stray pixels each.

A small face somebody named anyway is kept: they looked at it and knew who it
was, so it is not a stray, and hiding it would hide their work with it.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe, record                           # noqa: E402

pe = load_pe()


def face(number, name="", size=100):
    """A square face of `size` across the box, placed clear of the others."""
    return {"number": number, "name": name,
            "box": [number*500, 0, size, size]}


def rows_for(group):
    rows = pe._ss_face_rows(group)
    return pe._ss_hide_tiny_unnamed_rows(rows, group)


def numbers(group):
    return [r["number"] for r in rows_for(group)]


class TheCutoffIsTheSharedOne(unittest.TestCase):

    def test_it_comes_from_facegeometry(self):
        """Not a second copy of the rule that could drift from SlideShow's."""
        from FaceGeometry import SmallFaceCutoff, SMALL_FACE_RATIO
        self.assertIs(pe.SmallFaceCutoff, SmallFaceCutoff)
        # third largest of 100,90,80,10 is 80, so the bar is 16
        self.assertAlmostEqual(
            SmallFaceCutoff([[0, 0, 100, 0], [0, 0, 90, 0],
                             [0, 0, 80, 0], [0, 0, 10, 0]]), 80*SMALL_FACE_RATIO)
        # with only two, the larger sets it
        self.assertAlmostEqual(SmallFaceCutoff([[0, 0, 100, 0], [0, 0, 10, 0]]),
                               100*SMALL_FACE_RATIO)
        self.assertEqual(SmallFaceCutoff([[0, 0, 100, 0]]), 0.0)

    def test_dropping_and_measuring_agree(self):
        from FaceGeometry import DropTinyFaces, SmallFaceCutoff, FaceSize
        boxes = [[0, 0, s, s] for s in (120, 110, 100, 60, 21, 19, 5)]
        cutoff = SmallFaceCutoff(boxes)
        self.assertEqual(DropTinyFaces(boxes),
                         [b for b in boxes if FaceSize(b) >= cutoff])


class WhichRowsAreShown(unittest.TestCase):

    def test_a_stray_nobody_named_is_hidden(self):
        group = [record(11, "t1", faces=[face(1), face(2), face(3), face(4, size=8)])]
        self.assertEqual(numbers(group), [1, 2, 3])

    def test_a_stray_somebody_named_is_kept(self):
        """They knew who it was, so it is not a stray."""
        group = [record(11, "t1", faces=[face(1), face(2), face(3),
                                         face(4, "Bob Tucker", size=8)])]
        self.assertEqual(numbers(group), [1, 2, 3, 4])

    def test_a_name_in_any_report_keeps_it(self):
        """Even one whose column is not on screen -- a collapsed duplicate, or
        a report carrying nothing else at all."""
        group = [record(11, "t1", faces=[face(1), face(2), face(3), face(4, size=8)]),
                 record(11, "t2", faces=[face(1), face(2), face(3),
                                         face(4, "Ellen Klages", size=8)])]
        self.assertEqual(numbers(group), [1, 2, 3, 4])
        # and that second report really does have no column of its own reason
        # to exist beyond the name
        self.assertEqual(len(pe._ss_report_columns(group)), 1)

    def test_whitespace_is_not_a_name(self):
        group = [record(11, "t1", faces=[face(1), face(2), face(3),
                                         face(4, "   ", size=8)])]
        self.assertEqual(numbers(group), [1, 2, 3])

    def test_several_strays_go_together(self):
        group = [record(11, "t1", faces=[face(1), face(2), face(3)]
                                        + [face(n, size=9) for n in (4, 5, 6, 7)])]
        self.assertEqual(numbers(group), [1, 2, 3])

    def test_a_photo_of_evenly_sized_faces_loses_none(self):
        group = [record(11, "t1", faces=[face(n) for n in range(1, 7)])]
        self.assertEqual(numbers(group), [1, 2, 3, 4, 5, 6])

    def test_two_faces_are_measured_against_the_larger(self):
        group = [record(11, "t1", faces=[face(1), face(2, size=5)])]
        self.assertEqual(numbers(group), [1])

    def test_a_named_stray_survives_in_a_two_face_photo_too(self):
        group = [record(11, "t1", faces=[face(1), face(2, "Bob Tucker", size=5)])]
        self.assertEqual(numbers(group), [1, 2])

    def test_a_lone_face_is_never_hidden(self):
        group = [record(11, "t1", faces=[face(1, size=5)])]
        self.assertEqual(numbers(group), [1])

    def test_one_big_face_does_not_carry_away_the_rest(self):
        """The measure is the third largest: bar is 80*0.2 = 16."""
        group = [record(11, "t1", faces=[face(1, size=400), face(2, size=90),
                                         face(3, size=80), face(4, size=20)])]
        self.assertEqual(numbers(group), [1, 2, 3, 4])

    def test_a_face_recorded_without_a_box_is_never_hidden(self):
        """It cannot be measured, so it is not for this rule to remove."""
        group = [record(11, "t1", faces=[face(1), face(2), face(3),
                                         {"number": 4, "name": ""},
                                         face(5, size=8)])]
        self.assertEqual(numbers(group), [1, 2, 3, 4])

    def test_no_faces_at_all(self):
        self.assertEqual(rows_for([record(11, "t1")]), [])


class AgainstTheRealLog(unittest.TestCase):
    """The log SlideShow actually wrote, before it filtered at detection."""

    @classmethod
    def setUpClass(cls):
        logs = sorted((Path(__file__).resolve().parent.parent.parent / "SlideShow")
                      .glob("*SlideShow Output *.json"))
        cls.records = pe._read_ss_records(logs[-1]) if logs else None

    def setUp(self):
        if not self.records:
            self.skipTest("no SlideShow log on disk to check against")

    def test_nothing_anybody_named_is_ever_hidden(self):
        for group in pe._ss_group_by_photo(self.records):
            shown = {r["key"] for r in rows_for(group)}
            for key in pe._ss_named_face_keys(group):
                with self.subTest(photo=group[0].get("photo id")):
                    self.assertIn(key, shown, "a named face was hidden")

    def test_no_photo_loses_every_face_it_had(self):
        """Whichever face sets the bar clears it, so something always survives."""
        for group in pe._ss_group_by_photo(self.records):
            if pe._ss_face_rows(group):
                with self.subTest(photo=group[0].get("photo id")):
                    self.assertTrue(rows_for(group))


if __name__ == "__main__":
    unittest.main()
