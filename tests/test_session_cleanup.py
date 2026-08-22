"""Every Piwigo session PhotosEditor opens must be closed, including when the
work in between fails.

An abandoned session sits on the server until it times out, and the failure
path is exactly the one where a plain `client.logout()` at the end of a
function gets skipped.  Two kinds of check here:

* a structural one, which reads PhotosEditor.py and insists no logout sits on
  the happy path only -- this is what stops the problem coming back in the next
  worker somebody writes;
* behavioural ones, which run real workers against a client that fails partway
  and confirm the session was closed anyway.  They use a stub, so no server is
  contacted and nothing is uploaded, moved or deleted.
"""
import ast
import sys
import threading
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _support import load_pe                              # noqa: E402

pe = load_pe()
SOURCE = (Path(__file__).resolve().parent.parent / "PhotosEditor.py")


class NoLogoutOnTheHappyPathOnly(unittest.TestCase):
    """Read the source and check where each logout actually sits."""

    @staticmethod
    def _logout_calls(tree):
        """(line, is_protected) for every logout in the file."""
        protected = set()

        class Walker(ast.NodeVisitor):
            def visit_Try(self, node):
                # Anything in a finally: runs whatever happened above it
                for handler in node.finalbody:
                    for sub in ast.walk(handler):
                        if isinstance(sub, ast.Call):
                            protected.add(sub.lineno)
                self.generic_visit(node)

        Walker().visit(tree)

        # The one legitimate exception is the body of the _logout helper itself:
        # wrapping that call is its entire purpose, so it is not "unprotected".
        helper = next((n for n in ast.walk(tree)
                       if isinstance(n, ast.FunctionDef) and n.name == "_logout"), None)
        inside_helper = range(helper.lineno, (helper.end_lineno or helper.lineno) + 1) \
            if helper else range(0)

        calls = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            if node.lineno in inside_helper:
                continue
            name = None
            if isinstance(node.func, ast.Attribute) and node.func.attr == "logout":
                name = "client.logout()"
            elif isinstance(node.func, ast.Name) and node.func.id == "_logout":
                name = "_logout(client)"
            if name:
                calls.append((node.lineno, name, node.lineno in protected))
        return calls

    def test_every_logout_runs_on_the_failure_path_too(self):
        tree = ast.parse(SOURCE.read_text(encoding="utf-8"))
        calls = self._logout_calls(tree)
        self.assertGreater(len(calls), 5, "expected PhotosEditor to log out somewhere")
        unprotected = [(line, what) for line, what, ok in calls if not ok]
        self.assertEqual(
            unprotected, [],
            "these logouts are skipped when the work above them raises, "
            "abandoning the Piwigo session:\n  "
            + "\n  ".join(f"line {line}: {what}" for line, what in unprotected))

    def test_the_helper_swallows_a_failing_logout(self):
        """A logout that fails must not mask the error that led to it."""
        class Grumpy:
            def logout(self):
                raise RuntimeError("server went away")
        pe._logout(Grumpy())        # must not raise


class _FailingClient:
    """Logs in, then fails on whatever it is asked to do."""

    def __init__(self, *a, **k):
        self.logged_out = False

    def login(self, *a, **k):
        pass

    def logout(self):
        self.logged_out = True

    def __getattr__(self, name):
        def boom(*a, **k):
            raise RuntimeError(f"{name} failed")
        return boom


class SessionClosedWhenTheWorkFails(unittest.TestCase):
    """Drive the workers that can be run without a window, with a client that
    fails partway, and confirm the session was closed regardless."""

    def setUp(self):
        self.made = []
        original = pe.AlbumHierarchy.PiwigoClient

        def factory(*a, **k):
            c = _FailingClient()
            self.made.append(c)
            return c

        pe.AlbumHierarchy.PiwigoClient = factory
        self.addCleanup(setattr, pe.AlbumHierarchy, "PiwigoClient", original)

    def _ran_and_closed(self):
        self.assertTrue(self.made, "no Piwigo client was created")
        for c in self.made:
            self.assertTrue(c.logged_out,
                            "the session was left open after a failure")

    def test_fetching_an_album_closes_the_session(self):
        app = pe.PhotosEditor.__new__(pe.PhotosEditor)     # no window, no __init__
        app.root = _FakeRoot()
        panel = _FakePanel()
        app._worker_fetch_photos(panel, 1, "Album", _FakeVar(),
                                 lambda *_: None, lambda *_: None,
                                 lambda *_: None, gen=panel.load_gen)
        self._ran_and_closed()

    def test_fetching_one_photo_closes_the_session(self):
        app = pe.PhotosEditor.__new__(pe.PhotosEditor)
        app.root = _FakeRoot()
        app._worker_fetch_full("http://example.invalid/x.jpg", {"id": 1})
        self._ran_and_closed()


class _FakeRoot:
    """Enough of a Tk root for a worker to marshal results back."""
    def after(self, delay, fn=None, *a):
        return "after#1"        # never actually run: the GUI is not under test


class _FakeVar:
    def set(self, *_): pass
    def get(self): return ""


class _FakePanel:
    def __init__(self):
        self.load_gen = 1
        self.album_images = []
        self.shown_album_id = None
        self.thumb_cache = {}


if __name__ == "__main__":
    unittest.main()
