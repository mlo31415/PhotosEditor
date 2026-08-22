"""Naming and sidecar files for downloaded photos.

Download Album writes three files per photo -- the image, an .xml of selected
Piwigo metadata, and a .txt holding the caption -- so the names have to be
safe on Windows and the XML has to carry exactly the agreed fields.
"""
import sys
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                              # noqa: E402

pe = load_pe()


class Filenames(unittest.TestCase):

    def test_characters_windows_forbids_are_replaced(self):
        self.assertEqual(pe._sanitize_filename('Bob: "Tucker"?'), 'Bob_ _Tucker__')

    def test_trailing_dots_and_spaces_go(self):
        self.assertEqual(pe._sanitize_filename("  dots... "), "dots")

    def test_a_name_that_sanitises_to_nothing_still_yields_a_name(self):
        self.assertEqual(pe._sanitize_filename(""), "unnamed")
        self.assertEqual(pe._sanitize_filename("   "), "unnamed")

    def test_photo_named_from_the_display_name_with_the_original_extension(self):
        self.assertEqual(
            pe._photo_filename({"name": "Bob Tucker at Chicon", "file": "IMG_4032.JPG"}),
            "Bob Tucker at Chicon.jpg")

    def test_falls_back_to_the_file_stem_when_unnamed(self):
        self.assertEqual(pe._photo_filename({"name": "", "file": "IMG_4032.jpg"}),
                         "IMG_4032.jpg")

    def test_extension_can_come_from_the_url(self):
        self.assertEqual(
            pe._photo_filename({"name": "NoExt", "file": "",
                                "element_url": "https://x/y/img.jpeg?p=1", "id": 7}),
            "NoExt.jpeg")


class PhotoXml(unittest.TestCase):

    INFO = {
        "id": 123, "name": "Bob & Co <test>", "file": "IMG.jpg",
        "date_creation": "1962-09-01 00:00:00", "comment": "goes in the .txt",
        "author": "mlo",
        "tags": [{"id": 5, "name": "Tucker, Bob", "url": "http://x/t5",
                  "page_url": "http://x/p5", "lastmodified": "2020-01-01"},
                 {"id": 9, "name": "Chicon III"}],
        "categories": [{"id": 42, "name": "Chicon III", "url": "http://x/c42",
                        "page_url": "http://x/pc42", "uppercats": "1,42"}],
        "derivatives": {"square": {"url": "http://x/sq.jpg"}},
        "md5sum": "deadbeef",
    }

    def setUp(self):
        self._tmp = TemporaryDirectory()
        path = Path(self._tmp.name) / "IMG.xml"
        pe._write_photo_xml(path, self.INFO)
        self.root = ET.parse(path).getroot()
        self.addCleanup(self._tmp.cleanup)

    def test_only_the_agreed_fields_appear_in_order(self):
        self.assertEqual([c.tag for c in self.root],
                         ["id", "file", "date_creation", "name", "author",
                          "tags", "categories"])

    def test_the_caption_is_not_in_the_xml(self):
        self.assertIsNone(self.root.find("comment"))     # it lives in the .txt

    def test_bulk_piwigo_fields_are_dropped(self):
        self.assertIsNone(self.root.find("derivatives"))
        self.assertIsNone(self.root.find("md5sum"))

    def test_markup_in_a_name_is_escaped(self):
        self.assertEqual(self.root.find("name").text, "Bob & Co <test>")

    def test_each_tag_keeps_only_the_agreed_item_fields(self):
        tags = self.root.find("tags")
        self.assertEqual([c.tag for c in tags[0]], ["name", "id", "url", "page_url"])
        self.assertEqual([c.tag for c in tags[1]], ["name", "id"])   # absent ones omitted

    def test_categories_are_trimmed_the_same_way(self):
        cat = self.root.find("categories")[0]
        self.assertEqual(cat.find("page_url").text, "http://x/pc42")
        self.assertIsNone(cat.find("uppercats"))


class Durations(unittest.TestCase):
    """The download estimate is read aloud to the user, so it should read like
    English rather than a number of seconds."""

    def test_seconds(self):
        self.assertEqual(pe._format_duration(9), "9 seconds")
        self.assertEqual(pe._format_duration(1), "1 second")

    def test_minutes(self):
        self.assertEqual(pe._format_duration(60), "1 minute")
        self.assertEqual(pe._format_duration(200), "3 minutes 20 seconds")

    def test_hours(self):
        self.assertEqual(pe._format_duration(3900), "1 hour 5 minutes")


if __name__ == "__main__":
    unittest.main()
