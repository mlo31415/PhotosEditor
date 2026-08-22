"""Which photos need identifying, and the arithmetic behind the face rings
and the upload size limit."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                              # noqa: E402

pe = load_pe()


class NeedsIdTagName(unittest.TestCase):
    """Download Need_IDs matches the tag however it happens to be spelled."""

    def test_accepted_spellings(self):
        for name in ("Needs-ID", "needs-id", "NEEDS ID", "needs_id", "NeedsID",
                     "Need-ID", "need id", "Need_ID", "needid"):
            self.assertTrue(pe._is_needs_id_tag_name(name), name)

    def test_rejected(self):
        for name in ("Needs-IDs", "ID", "Needs", "identified", "no id", "", None):
            self.assertFalse(pe._is_needs_id_tag_name(name), name)


class NeedsIdentification(unittest.TestCase):
    """A photo qualifies by tag or by a '??' standing in for a name."""

    IDS = {5, 9}

    def test_by_tag(self):
        self.assertTrue(pe._needs_identification({"id": 5, "comment": "Bob"}, self.IDS))

    def test_by_tag_with_a_string_id(self):
        self.assertTrue(pe._needs_identification({"id": "9", "comment": ""}, self.IDS))

    def test_by_question_marks_in_the_caption(self):
        for caption in ("Bob Tucker, ??, Ackerman", "??", "l-r: ?? and ??",
                        "Forry (seated), ???, ???"):
            self.assertTrue(
                pe._needs_identification({"id": 1, "comment": caption}, self.IDS),
                caption)

    def test_a_single_question_mark_is_just_a_question(self):
        self.assertFalse(
            pe._needs_identification({"id": 1, "comment": "Who? Tucker?"}, self.IDS))

    def test_neither(self):
        self.assertFalse(pe._needs_identification({"id": 1, "comment": "Bob"}, self.IDS))
        self.assertFalse(pe._needs_identification({"id": 1}, self.IDS))
        self.assertFalse(pe._needs_identification({"id": 1, "comment": None}, self.IDS))
        self.assertFalse(pe._needs_identification({}, self.IDS))

    def test_an_unusable_id_does_not_raise(self):
        self.assertFalse(
            pe._needs_identification({"id": "not a number", "comment": "x"}, self.IDS))


class FaceCircle(unittest.TestCase):
    """SlideShow logs face boxes in original-photo pixels; the ring is drawn on
    a canvas showing the photo scaled and letterboxed."""

    def circle(self, box, orig, rect):
        return pe._ss_face_circle_on_canvas(box, orig, rect)

    def test_drawn_one_to_one_at_the_origin(self):
        r = 0.65 * (100 ** 2 + 100 ** 2) ** 0.5
        got = self.circle((100, 100, 100, 100), (1000, 1000), (0, 0, 1000, 1000))
        for a, b in zip(got, (150 - r, 150 - r, 150 + r, 150 + r)):
            self.assertAlmostEqual(a, b, places=3)

    def test_scaled_and_letterboxed(self):
        r = 0.65 * (100 ** 2 + 100 ** 2) ** 0.5
        got = self.circle((100, 100, 100, 100), (1000, 1000), (20, 50, 520, 550))
        want = (20 + (150 - r) * .5, 50 + (150 - r) * .5,
                20 + (150 + r) * .5, 50 + (150 + r) * .5)
        for a, b in zip(got, want):
            self.assertAlmostEqual(a, b, places=3)

    def test_a_circle_stays_circular(self):
        got = self.circle((100, 100, 100, 100), (1000, 1000), (20, 50, 520, 550))
        self.assertAlmostEqual(got[2] - got[0], got[3] - got[1], places=9)

    def test_string_values_from_json_are_accepted(self):
        self.assertIsNotNone(
            self.circle(("100", "100", "100", "100"), ("1000", "1000"),
                        (0, 0, 1000, 1000)))

    def test_a_box_that_cannot_belong_to_this_photo_draws_nothing(self):
        cases = {
            "off the right":  ((900, 100, 200, 100), (1000, 1000), (0, 0, 100, 100)),
            "off the bottom": ((100, 900, 100, 200), (1000, 1000), (0, 0, 100, 100)),
            "negative":       ((-5, 10, 50, 50),     (1000, 1000), (0, 0, 100, 100)),
            "no dimensions":  ((10, 10, 50, 50),     (0, 0),       (0, 0, 100, 100)),
            "empty box":      ((10, 10, 0, 50),      (1000, 1000), (0, 0, 100, 100)),
            "nothing drawn":  ((10, 10, 50, 50),     (1000, 1000), (0, 0, 0, 0)),
        }
        for why, args in cases.items():
            self.assertIsNone(self.circle(*args), why)

    def test_a_box_exactly_at_the_corner_is_accepted(self):
        self.assertIsNotNone(
            self.circle((900, 900, 100, 100), (1000, 1000), (0, 0, 1000, 1000)))


class UploadSizeLimit(unittest.TestCase):
    """When a photo is over the configured pixel limit PE offers to reduce it;
    the offered size has to actually fit, and keep the photo's shape."""

    def test_the_reduced_size_fits_the_limit(self):
        for w, h, limit in ((2510, 1593, 1_000_000), (4000, 3000, 4_000_000),
                            (1000, 1000, 250_000)):
            tw, th = pe.PhotosEditor._fit_within_pixels(w, h, limit)
            self.assertLessEqual(tw * th, limit, (w, h, limit))

    def test_the_shape_is_preserved(self):
        tw, th = pe.PhotosEditor._fit_within_pixels(2510, 1593, 1_000_000)
        self.assertAlmostEqual(tw / th, 2510 / 1593, places=2)

    def test_never_returns_a_zero_dimension(self):
        tw, th = pe.PhotosEditor._fit_within_pixels(4000, 3000, 1)
        self.assertGreaterEqual(min(tw, th), 1)


if __name__ == "__main__":
    unittest.main()
