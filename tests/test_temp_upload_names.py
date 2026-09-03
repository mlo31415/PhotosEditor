"""Photos stored on Piwigo under a tempfile's name.

PhotosEditor used to save the edited image to a NamedTemporaryFile and send
that, and Piwigo keeps the name of the file it is given, so those photos are
stored as "tmp2qfmcfwp.JPG".  Their titles kept the real name.  Six of the
twenty-nine photos in the SlideShow log on disk are in this state.

Two things follow: what a person is shown must be the name that means
something, and re-uploading such a photo must not send the temp name back and
overwrite the last copy of the real one.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()


class SpottingATempName(unittest.TestCase):

    def test_the_names_seen_on_the_server(self):
        """Every one of these was really found on photos.fanac.org."""
        for name in ("tmp2qfmcfwp.JPG", "tmp3figxcg9.jpg", "tmp_9yj5dgg.jpg",
                     "tmprzsvndii.jpg", "tmp86i1nw3b.JPG", "tmp12cehr09.JPG",
                     "tmp8xzn0oi5.JPG"):
            with self.subTest(name):
                self.assertTrue(pe._looks_like_temp_upload_name(name))

    def test_real_photo_names_are_left_alone(self):
        for name in ("es-b00273.jpg", "mlo01267.jpg", "PICT0943.JPG",
                     "x15-002.jpeg", "w54m003.jpeg", "tmp.jpg",
                     "tmpanything-longer-than-eight.jpg", "temperature.jpg",
                     "tmp123.jpg"):
            with self.subTest(name):
                self.assertFalse(pe._looks_like_temp_upload_name(name))

    def test_nothing_at_all_is_not_a_temp_name(self):
        self.assertFalse(pe._looks_like_temp_upload_name(""))
        self.assertFalse(pe._looks_like_temp_upload_name(None))


class TheNameToUploadUnder(unittest.TestCase):

    def test_an_ordinary_photo_keeps_its_file_name(self):
        self.assertEqual(
            pe._real_photo_filename({"file": "es-b00273.jpg", "name": "es-b00273.jpg"}, 1),
            "es-b00273.jpg")

    def test_a_temp_named_photo_goes_back_under_its_real_name(self):
        """Otherwise the upload writes the temp name into the title as well,
        and the real name is gone for good."""
        self.assertEqual(
            pe._real_photo_filename({"file": "tmp3figxcg9.jpg", "name": "es-eb00102.jpg"}, 1),
            "es-eb00102.jpg")

    def test_the_extension_comes_from_the_stored_name(self):
        """A title often has none: id 3983 on the server is name 'x15-002'."""
        self.assertEqual(
            pe._real_photo_filename({"file": "tmp86i1nw3b.JPG", "name": "mlo00195"}, 1),
            "mlo00195.JPG")

    def test_a_title_that_is_also_a_temp_name_is_not_preferred(self):
        self.assertEqual(
            pe._real_photo_filename({"file": "tmp12cehr09.JPG", "name": "tmp8xzn0oi5.JPG"}, 1),
            "tmp12cehr09.JPG")

    def test_no_title_leaves_the_stored_name(self):
        self.assertEqual(
            pe._real_photo_filename({"file": "tmp12cehr09.JPG", "name": "  "}, 1),
            "tmp12cehr09.JPG")

    def test_a_photo_with_neither_falls_back_to_its_id(self):
        self.assertEqual(pe._real_photo_filename({}, 77), "77.jpg")


class WhatThePersonIsShown(unittest.TestCase):
    """_photo_label picks what to call the photo in a dialog."""

    class Fake:
        _photo_label = pe.PhotosEditor._photo_label

        def __init__(self, img):
            self._current_image_dict = img

    def label(self, img):
        return self.Fake(img)._photo_label()

    def test_an_ordinary_photo_is_called_by_its_file_name(self):
        self.assertEqual(self.label({"file": "mlo01267.jpg", "name": "mlo01267.jpg"}),
                         "mlo01267.jpg")

    def test_a_temp_named_photo_is_called_by_its_title(self):
        """This is the dialog that read 'For "tmp2qfmcfwp.JPG"'."""
        self.assertEqual(self.label({"file": "tmp2qfmcfwp.JPG", "name": "PICT0943.JPG"}),
                         "PICT0943.JPG")

    def test_a_photo_with_only_a_temp_name_still_says_something(self):
        self.assertEqual(self.label({"file": "tmp2qfmcfwp.JPG"}), "tmp2qfmcfwp.JPG")

    def test_no_photo_at_all(self):
        self.assertEqual(self.label(None), "this photo")


if __name__ == "__main__":
    unittest.main()
