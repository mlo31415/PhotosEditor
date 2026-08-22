"""Which typed-in changes count as unsaved.

Exit, closing the editor and moving between SlideShow records all ask before
throwing work away.  Getting this wrong is expensive in both directions: miss a
change and the user silently loses what they typed; report one that is not
there and they learn to click through the warning.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                              # noqa: E402

pe = load_pe()
LABELS = dict(pe.CUSTOM_FIELDS)


class ChangedFields(unittest.TestCase):

    def changed(self, loaded, now):
        return pe._changed_field_labels(loaded, now, LABELS)

    def test_nothing_typed_reports_nothing(self):
        loaded = {"comments": "Bob Tucker", "tags": "Chicon"}
        self.assertEqual(self.changed(loaded, dict(loaded)), [])

    def test_an_edited_caption_is_reported_by_its_label(self):
        self.assertEqual(
            self.changed({"comments": "Bob Tucker"},
                         {"comments": "Bob Tucker and Forry Ackerman"}),
            ["Caption"])

    def test_several_fields_are_all_reported(self):
        got = self.changed(
            {"comments": "a", "tags": "b", "photo_source": "c", "date_of_photo": "d"},
            {"comments": "a!", "tags": "b", "photo_source": "c!", "date_of_photo": "d"})
        self.assertEqual(sorted(got), sorted(["Caption", "Photographer/Source"]))

    def test_clearing_a_field_counts_as_a_change(self):
        self.assertEqual(self.changed({"comments": "Bob Tucker"}, {"comments": ""}),
                         ["Caption"])

    def test_filling_an_empty_field_counts_as_a_change(self):
        self.assertEqual(self.changed({"comments": ""}, {"comments": "Bob"}),
                         ["Caption"])

    def test_no_photo_loaded_means_nothing_to_lose(self):
        """An empty baseline is 'no photo on screen', not 'everything was
        cleared' -- reporting every field there would warn on every quit."""
        self.assertEqual(self.changed({}, {"comments": "typed with no photo"}), [])

    def test_a_field_absent_from_the_baseline_is_compared_against_empty(self):
        self.assertEqual(self.changed({"comments": "x"}, {"comments": "x", "tags": ""}),
                         [])
        self.assertEqual(self.changed({"comments": "x"}, {"comments": "x", "tags": "new"}),
                         ["Tags"])

    def test_keys_without_a_label_fall_back_to_the_key(self):
        self.assertEqual(self.changed({"odd": "a"}, {"odd": "b"}), ["odd"])

    def test_every_custom_field_has_a_label_to_report(self):
        """The warning names fields; a missing label would show a bare key."""
        for key, label in pe.CUSTOM_FIELDS:
            self.assertTrue(label and not label.startswith("_"), key)


if __name__ == "__main__":
    unittest.main()
