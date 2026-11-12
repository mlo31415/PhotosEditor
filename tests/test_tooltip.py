"""Hover tooltips go away.

A thumbnail's tooltip covers three widgets -- the cell, its picture and its
name -- as one hover region.  Moving from one to another with the tooltip up
was correctly not taken as leaving, but the Enter on the second widget then
scheduled another tooltip, which replaced the first in _tip without closing
it.  The first was never destroyed: the yellow boxes that piled up in the
Move and Copy tab.

The tooltip's own methods are driven directly with made-up events, so no
pointer is needed; the windows are real.
"""
import sys
import tkinter as tk
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                                   # noqa: E402

pe = load_pe()


class _At:
    """Just enough of a Tk event: where the pointer was."""
    def __init__(self, widget):
        self.x_root = widget.winfo_rootx() + 2
        self.y_root = widget.winfo_rooty() + 2
        self.widget = widget


class _Group:
    """A thumbnail cell: picture and name in it, one tooltip over all three."""

    def setUp(self):
        self.root = tk.Tk()
        self.root.geometry("300x200+40+40")
        self.cell = tk.Frame(self.root, width=200, height=150)
        self.cell.pack()
        self.picture = tk.Label(self.cell, text="picture")
        self.picture.place(x=10, y=10, width=180, height=90)
        self.name = tk.Label(self.cell, text="name")
        self.name.place(x=10, y=110, width=180, height=30)
        self.root.update()
        self.tip = pe._Tooltip(lambda: "Chicon 1962.jpg")
        for w in (self.cell, self.picture, self.name):
            self.tip.attach(w)

    def tearDown(self):
        self.root.destroy()

    def tips_on_screen(self):
        """Every tooltip window, wherever it hangs: they are made as
        children of the widget the tooltip is attached to, not of the root."""
        found = []

        def walk(w):
            for c in w.winfo_children():
                if isinstance(c, tk.Toplevel) and c.winfo_exists():
                    found.append(c)
                walk(c)
        walk(self.root)
        return found

    def hover(self, widget):
        """The pointer comes onto widget and rests there."""
        self.tip._on_enter(_At(widget))
        if self.tip._after_id is not None:
            # Through the tooltip, which cancels on the widget that scheduled
            # it; cancelling via another widget leaves Tk a command to fail on
            self.tip._cancel()
            self.tip._show()
        self.root.update()

    def move(self, src, dst):
        """From src onto dst, which is in the same group."""
        self.tip._on_leave(_At(dst))
        self.hover(dst)


class OneRegion(_Group, unittest.TestCase):

    def test_moving_within_the_group_keeps_one_tooltip(self):
        self.hover(self.picture)
        self.move(self.picture, self.name)
        self.move(self.name, self.picture)
        self.move(self.picture, self.name)
        self.assertEqual(len(self.tips_on_screen()), 1)

    def test_and_leaving_takes_it_away(self):
        self.hover(self.picture)
        self.move(self.picture, self.name)
        self.tip._on_leave(None)
        self.root.update()
        self.assertEqual(self.tips_on_screen(), [])

    def test_a_click_takes_it_away(self):
        self.hover(self.picture)
        self.move(self.picture, self.name)
        self.tip._cancel_and_hide()
        self.root.update()
        self.assertEqual(self.tips_on_screen(), [])

    def test_a_second_show_never_orphans_the_first(self):
        """Whatever schedules it, a tooltip shown twice is still one window."""
        self.hover(self.picture)
        self.tip._show()
        self.root.update()
        self.assertEqual(len(self.tips_on_screen()), 1)
        self.tip._cancel_and_hide()
        self.root.update()
        self.assertEqual(self.tips_on_screen(), [])


class _Point:
    """A Leave event at a screen point."""
    def __init__(self, x, y):
        self.x_root, self.y_root = x, y


class OverTheTooltip(_Group, unittest.TestCase):
    """The pointer goes from the photo onto its tooltip, which lies over it.
    The photo's Leave sees a point inside the photo and rightly keeps the
    tooltip; then the pointer goes from the tooltip straight out of the
    photo, and the photo sees nothing.  The tooltip stayed up for good."""

    def on_the_tooltip(self):
        """Show the tooltip over the picture and move the pointer onto it."""
        self.hover(self.picture)
        tip = self.tips_on_screen()[0]
        # Where it appears depends on the real pointer: put it over the picture
        tip.wm_geometry(f"+{self.picture.winfo_rootx() + 100}+{self.picture.winfo_rooty() + 40}")
        self.root.update()
        self.tip._on_leave(_Point(tip.winfo_rootx() + 5, tip.winfo_rooty() + 5))
        self.root.update()
        self.assertEqual(len(self.tips_on_screen()), 1)
        return tip

    def leave_tip(self, x, y):
        """The tooltip window's own Leave, at screen point (x, y)."""
        self.tips_on_screen()[0].event_generate("<Leave>", rootx=x, rooty=y)
        self.root.update()

    def test_leaving_the_tooltip_out_of_the_photo_takes_it_away(self):
        tip = self.on_the_tooltip()
        self.leave_tip(tip.winfo_rootx() + tip.winfo_width() + 5,
                       self.root.winfo_rooty() + self.root.winfo_height() + 50)
        self.assertEqual(self.tips_on_screen(), [])

    def test_leaving_the_tooltip_back_onto_the_photo_keeps_it(self):
        self.on_the_tooltip()
        self.leave_tip(self.picture.winfo_rootx() + 5, self.picture.winfo_rooty() + 5)
        self.assertEqual(len(self.tips_on_screen()), 1)


if __name__ == "__main__":
    unittest.main()
