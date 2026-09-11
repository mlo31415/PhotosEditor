"""A report can outlive the photo it is about.

The reports are read from the SlideShow log on disk; the photo is fetched from
Piwigo by id.  A photo deleted since the report was written leaves the review
half-usable -- which is fine -- but the photo side must say so rather than sit
at "Loading…", which reads as a hang.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()


class TellingDeletionFromBreakage(unittest.TestCase):
    """Piwigo answers a request for a photo that has gone with a 404 and
    "image_id not found".  A network that is merely down says neither, and
    must not be reported to the user as a deletion."""

    def test_piwigos_answer_for_a_deleted_photo(self):
        """The wording as it really came back for photo 9938."""
        self.assertTrue(pe._is_missing_photo(Exception(
            "404 Client Error: image_id not found for url: "
            "https://162.246.254.99/ws.php?format=json")))

    def test_either_half_of_it_is_enough(self):
        self.assertTrue(pe._is_missing_photo(Exception("image_id not found")))
        self.assertTrue(pe._is_missing_photo(Exception("404 Client Error")))

    def test_the_case_does_not_matter(self):
        self.assertTrue(pe._is_missing_photo(Exception("Image_ID Not Found")))

    def test_a_network_failure_is_not_a_deletion(self):
        for text in ("Connection refused",
                     "HTTPSConnectionPool: Max retries exceeded",
                     "500 Server Error",
                     "timed out",
                     "401 Client Error: Unauthorized"):
            with self.subTest(text):
                self.assertFalse(pe._is_missing_photo(Exception(text)))


if __name__ == "__main__":
    unittest.main()
