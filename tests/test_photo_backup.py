"""The copy kept before a photo is changed.

Piwigo keeps no earlier version of a photo: the moment edited pixels go up,
what was there is gone.  So PhotosEditor puts a copy in "Photo Backups"
first, and the one thing that must never happen is a backup overwriting an
earlier backup -- the whole point is the photo as it was before the *first*
edit, which is the one under the plain name.
"""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()

PHOTO = b"\xff\xd8\xff\xe0 not really a jpeg, but bytes are bytes \xff\xd9"


class Naming(unittest.TestCase):
    """_backup_path: what the next copy is called."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def take(self, name):
        """Claim the next backup name, as writing one would."""
        path = pe._backup_path(self.tmp, name)
        path.write_bytes(b"x")
        return path.name

    def test_the_first_copy_has_the_photo_s_own_name(self):
        self.assertEqual(self.take("Chicon 1962.jpg"), "Chicon 1962.jpg")

    def test_the_second_is_generation_01(self):
        self.take("Chicon 1962.jpg")
        self.assertEqual(self.take("Chicon 1962.jpg"), "Chicon 1962 - Gen 01.jpg")

    def test_and_they_keep_counting(self):
        got = [self.take("p.jpg") for _ in range(4)]
        self.assertEqual(got, ["p.jpg", "p - Gen 01.jpg",
                               "p - Gen 02.jpg", "p - Gen 03.jpg"])

    def test_the_number_is_two_digits_until_it_cannot_be(self):
        for _ in range(11):
            last = self.take("p.jpg")
        self.assertEqual(last, "p - Gen 10.jpg")

    def test_the_generation_goes_before_the_extension(self):
        """So the file is still a .jpg to everything that opens it."""
        self.take("p.jpeg")
        self.assertTrue(self.take("p.jpeg").endswith(".jpeg"))

    def test_a_name_with_no_extension_is_given_one(self):
        self.assertEqual(self.take("no extension here"), "no extension here.jpg")

    def test_a_name_windows_will_not_take_is_made_safe(self):
        got = self.take('why? "this" <that>.jpg')
        self.assertNotIn("?", got)
        self.assertNotIn('"', got)
        self.assertTrue(got.endswith(".jpg"), got)

    def test_two_photos_with_different_names_do_not_collide(self):
        self.assertEqual(self.take("a.jpg"), "a.jpg")
        self.assertEqual(self.take("b.jpg"), "b.jpg")


class Writing(unittest.TestCase):

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_the_folder_is_made_if_it_is_not_there(self):
        folder = self.tmp / "Photo Backups"
        self.assertFalse(folder.exists())
        pe._write_photo_backup(folder, "p.jpg", PHOTO)
        self.assertTrue(folder.is_dir())

    def test_what_is_written_is_what_was_downloaded(self):
        """Byte for byte: a backup that has been through a JPEG encoder is not
        the photo that was there."""
        path = pe._write_photo_backup(self.tmp, "p.jpg", PHOTO)
        self.assertEqual(path.read_bytes(), PHOTO)

    def test_a_second_edit_does_not_overwrite_the_first_backup(self):
        first  = pe._write_photo_backup(self.tmp, "p.jpg", PHOTO)
        second = pe._write_photo_backup(self.tmp, "p.jpg", b"edited once")
        self.assertNotEqual(first, second)
        self.assertEqual(first.read_bytes(), PHOTO,
                         "the copy from before the first edit was lost")


class WhenItGoesWrong(unittest.TestCase):
    """_back_up_photo decides whether the upload may go ahead."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self._real_dir = pe._SCRIPT_DIR
        pe._SCRIPT_DIR = self.tmp
        self.app = pe.PhotosEditor.__new__(pe.PhotosEditor)
        self.said = []
        self.app.set_status = self.said.append
        self.app.root = None
        self.asked = []
        self._real_ask = pe.messagebox.askyesno
        pe.messagebox.askyesno = lambda t, m, **k: (self.asked.append((t, m)),
                                                    self.answer)[1]
        self.answer = False

    def tearDown(self):
        pe._SCRIPT_DIR = self._real_dir
        pe.messagebox.askyesno = self._real_ask
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_a_backup_is_written_and_the_upload_goes_ahead(self):
        self.app._orig_bytes = PHOTO
        self.assertTrue(self.app._back_up_photo("p.jpg"))
        self.assertEqual(self.asked, [], "nothing should have been asked")
        kept = self.tmp / pe.PHOTO_BACKUP_DIR / "p.jpg"
        self.assertEqual(kept.read_bytes(), PHOTO)

    def test_the_status_line_names_the_copy(self):
        self.app._orig_bytes = PHOTO
        self.app._back_up_photo("p.jpg")
        self.assertTrue(any("p.jpg" in s for s in self.said), self.said)

    def test_with_nothing_to_copy_it_asks_rather_than_assuming(self):
        """No original held means no backup is possible, and an upload that
        replaces the photo is then unrecoverable.  Worth a question."""
        self.app._orig_bytes = b""
        self.assertFalse(self.app._back_up_photo("p.jpg"))
        self.assertEqual(len(self.asked), 1)
        self.assertIn("gone", self.asked[0][1])
        self.assertIn("no longer being held", self.asked[0][1])

    def test_and_the_answer_is_obeyed(self):
        self.app._orig_bytes = b""
        self.answer = True
        self.assertTrue(self.app._back_up_photo("p.jpg"),
                        "saying yes should let the upload through")


if __name__ == "__main__":
    unittest.main()
