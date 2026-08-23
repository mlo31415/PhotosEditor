"""How a face is shown: the circle PhotosEditor rings and cuts its thumbnails
from, which must be the one SlideShow used.

Both programs call the shared FaceGeometry in HelpersPackage, and both are held
to one set of recorded numbers -- FaceGeometryGolden.json, beside it.  If this
file and SlideShow's `test_face_geometry.py` disagree, the two have drifted
apart, which is the thing the shared module exists to prevent.
"""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                 # noqa: E402

pe = load_pe()

_GOLDEN = (Path(__file__).resolve().parent.parent.parent
           / "HelpersPackage" / "FaceGeometryGolden.json")


@unittest.skipUnless(_GOLDEN.is_file(), f"the shared HelpersPackage is not beside PhotosEditor ({_GOLDEN})")
class TheRecordedCircles(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.golden = json.loads(_GOLDEN.read_text(encoding="utf-8"))

    def test_a_face_on_a_scaled_photo_lands_where_it_should(self):
        """Through PE's own function, which is what the review mode calls."""
        case = self.golden["on display"]
        drawn = pe._ss_face_circle_on_canvas(case["box"], case["original size"], case["display rect"])
        self.assertEqual([round(v, 6) for v in drawn], case["circle"])

    def test_a_face_which_cannot_belong_to_the_photo_is_refused(self):
        """Rather than ringing something at random -- a record left over from
        another photo, or from before this one was cropped."""
        for case in self.golden["refused"]:
            with self.subTest(case["what"]):
                self.assertIsNone(pe._ss_face_circle_on_canvas(
                    case["box"], case["original size"], case["display rect"]))

    def test_the_ratio_is_the_recorded_one(self):
        from FaceGeometry import FACE_CIRCLE_RATIO
        self.assertEqual(FACE_CIRCLE_RATIO, self.golden["ratio"])

    def test_the_circles_themselves_are_the_recorded_ones(self):
        from FaceGeometry import FaceCircle, FaceCircleBounds
        for case in self.golden["cases"]:
            with self.subTest(case["what"]):
                self.assertEqual([round(v, 6) for v in FaceCircle(case["box"])], case["circle"])
                self.assertEqual([round(v, 6) for v in FaceCircleBounds(case["box"])], case["bounds"])


@unittest.skipUnless(_GOLDEN.is_file(), "the shared HelpersPackage is not beside PhotosEditor")
class TheRoundPicture(unittest.TestCase):
    """The same cutting SlideShow's list shows, so a face looks the same in both."""

    @staticmethod
    def photo(centreX, centreY):
        from PIL import Image, ImageDraw
        image = Image.new("RGB", (200, 200), "white")
        ImageDraw.Draw(image).rectangle((centreX-10, centreY-10, centreX+10, centreY+10), fill="black")
        return image

    @staticmethod
    def markerAspect(thumb):
        dark = [(x, y) for y in range(thumb.height) for x in range(thumb.width)
                if sum(thumb.getpixel((x, y))) < 200]
        xs, ys = [p[0] for p in dark], [p[1] for p in dark]
        return (max(xs)-min(xs)+1)/(max(ys)-min(ys)+1)

    def test_a_face_at_the_edge_is_not_stretched(self):
        from FaceGeometry import RoundFaceThumbnail
        middle = RoundFaceThumbnail(self.photo(100, 100), [80, 80, 40, 40], "white", 64)
        edge = RoundFaceThumbnail(self.photo(20, 100), [0, 80, 40, 40], "white", 64)
        self.assertAlmostEqual(self.markerAspect(edge), self.markerAspect(middle), delta=0.05)

    def test_the_size_asked_for_is_the_size_returned(self):
        from FaceGeometry import RoundFaceThumbnail
        self.assertEqual(RoundFaceThumbnail(self.photo(100, 100), [80, 80, 40, 40], "black", 64).size,
                         (64, 64))


if __name__ == "__main__":
    unittest.main()
