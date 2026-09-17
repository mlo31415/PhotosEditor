"""Correcting a colour cast, and keeping what the file knows about itself.

Two things PhotoDefectFixer could do and PhotosEditor could not: measure a
photo's colour cast rather than have it judged by eye, and put warmth back
into a scan that came out cold.  And one thing PhotosEditor was doing wrong:
re-encoding a JPEG on upload threw away its EXIF -- the camera, the lens, the
date the photo was taken -- which for an archive is most of the point.
"""
import sys
import unittest
from io import BytesIO
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "PiwigoHelpers"))
import PhotoRestoration                                        # noqa: E402
from PIL import Image, ImageStat                               # noqa: E402


def flat(rgb, size=(60, 40)):
    return Image.new("RGB", size, rgb)


def means(img):
    return tuple(ImageStat.Stat(img.convert("RGB")).mean)


class MeasuringTheCast(unittest.TestCase):
    """grey_world_red_cast: what the Auto Colour button asks the photo."""

    def test_a_neutral_photo_needs_no_correction(self):
        self.assertEqual(PhotoRestoration.grey_world_red_cast(flat((128, 128, 128))), 0.0)

    def test_an_orange_scan_asks_to_be_cooled(self):
        """The fading these photos suffer: reds up, blues down."""
        self.assertGreater(PhotoRestoration.grey_world_red_cast(flat((180, 130, 90))), 0)

    def test_a_cold_scan_asks_to_be_warmed(self):
        """Which the slider could not do at all before: it started at zero."""
        self.assertLess(PhotoRestoration.grey_world_red_cast(flat((90, 130, 180))), 0)

    def test_the_worse_the_cast_the_larger_the_answer(self):
        mild   = PhotoRestoration.grey_world_red_cast(flat((150, 130, 120)))
        strong = PhotoRestoration.grey_world_red_cast(flat((200, 130, 70)))
        self.assertGreater(strong, mild)

    def test_it_stays_on_the_slider(self):
        for colour in ((255, 0, 0), (0, 0, 255), (0, 0, 0), (255, 255, 255)):
            got = PhotoRestoration.grey_world_red_cast(flat(colour))
            self.assertGreaterEqual(got, -100.0, colour)
            self.assertLessEqual(got, 100.0, colour)

    def test_applying_the_answer_closes_the_gap(self):
        """The measurement is only worth having if acting on it works."""
        img = flat((180, 130, 90))
        before = means(img)
        fixed = PhotoRestoration.opencv_restore(
            img, 0, 0, PhotoRestoration.grey_world_red_cast(img), 0)
        after = means(fixed)
        self.assertLess(abs(after[0] - after[2]), abs(before[0] - before[2]) / 2,
                        f"{before} -> {after}")


class TheCastGoesBothWays(unittest.TestCase):

    def test_positive_takes_red_out(self):
        r, _g, b = means(PhotoRestoration.opencv_restore(flat((150, 150, 150)),
                                                         0, 0, 60, 0))
        self.assertLess(r, 150)
        self.assertGreater(b, 150)

    def test_negative_puts_red_back(self):
        r, _g, b = means(PhotoRestoration.opencv_restore(flat((150, 150, 150)),
                                                         0, 0, -60, 0))
        self.assertGreater(r, 150)
        self.assertLess(b, 150)

    def test_zero_leaves_the_colours_alone(self):
        self.assertEqual(
            means(PhotoRestoration.opencv_restore(flat((150, 140, 130)), 0, 0, 0, 0)),
            (150.0, 140.0, 130.0))

    def test_the_slider_offers_both_directions(self):
        """A range that starts at zero cannot warm anything up."""
        source = Path(pe.__file__).read_text(encoding="utf-8")
        row = next(ln for ln in source.splitlines()
                   if '("Red cast"' in ln)
        self.assertIn("-100", row, row.strip())


class KeepingTheExif(unittest.TestCase):
    """What _exif_to_write hands to the JPEG encoder."""

    def setUp(self):
        self.app = pe.PhotosEditor.__new__(pe.PhotosEditor)   # no window needed

    def written(self, raw):
        self.app._orig_exif = raw
        return self.app._exif_to_write()

    def read_back(self, raw):
        exif = Image.Exif()
        exif.load(raw)
        return dict(exif)

    def test_a_photo_with_no_exif_writes_none(self):
        self.assertEqual(self.written(b""), b"")

    def test_the_date_taken_survives(self):
        exif = Image.Exif()
        exif[36867] = "1964:09:04 18:30:00"     # DateTimeOriginal
        exif[271]   = "FANAC"                   # Make
        got = self.read_back(self.written(exif.tobytes()))
        self.assertEqual(got.get(36867), "1964:09:04 18:30:00")
        self.assertEqual(got.get(271), "FANAC")

    def test_orientation_does_not_survive(self):
        """The pixels are written the way they are on screen, rotation and
        all, so a viewer must not turn them again."""
        exif = Image.Exif()
        exif[274] = 6                           # Orientation: rotate 90
        exif[271] = "FANAC"
        got = self.read_back(self.written(exif.tobytes()))
        self.assertNotIn(274, got)
        self.assertEqual(got.get(271), "FANAC", "the rest went with it")

    def test_rubbish_is_kept_rather_than_dropped(self):
        """If it cannot be rewritten, the original block still goes in: some
        EXIF beats none, and the orientation risk is the lesser harm."""
        self.assertEqual(self.written(b"not an exif block at all"),
                         b"not an exif block at all")

    def test_a_saved_jpeg_really_carries_it(self):
        """End to end, because the point is what lands in the file."""
        exif = Image.Exif()
        exif[36867] = "1964:09:04 18:30:00"
        out = self.written(exif.tobytes())
        buf = BytesIO()
        flat((120, 120, 120)).save(buf, format="JPEG", quality=95,
                                   subsampling=0, exif=out)
        reopened = Image.open(BytesIO(buf.getvalue()))
        self.assertEqual(self.read_back(reopened.info["exif"]).get(36867),
                         "1964:09:04 18:30:00")


if __name__ == "__main__":
    unittest.main()
