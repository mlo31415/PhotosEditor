"""
PhotosEditor.py
A GUI application for browsing and editing photos from a Piwigo album.

Left panel  – Scrollable thumbnail grid of photos in the selected album.
Right panel – Photo Editor: full-size display + Custom Fields (no EXIF section),
              modeled closely on the Photo Viewer in PhotosUploader.

Requires: pip install Pillow requests
Shares DownloadAlbumStructure.py in ../PiwigoHelpers with ../PhotosUploader.
"""

import os
import re
import sys
import json
import tempfile
import threading
import logging
import warnings
import tkinter as tk
from tkinter import ttk, messagebox
from pathlib import Path
from io import BytesIO
from datetime import datetime

try:
    from PIL import Image, ImageTk, IptcImagePlugin
    PIL_AVAILABLE = True
except Exception:
    PIL_AVAILABLE = False

try:
    import requests
    import urllib3
    REQUESTS_AVAILABLE = True
except Exception:
    REQUESTS_AVAILABLE = False

try:
    import cv2
    import numpy as np
    CV2_AVAILABLE = True
except Exception:
    CV2_AVAILABLE = False


# ---------------------------------------------------------------------------
# Locate and import the shared DownloadAlbumStructure module
# ---------------------------------------------------------------------------
# When frozen by PyInstaller, __file__ is inside the read-only _MEIPASS temp
# dir.  Use sys.executable (the .exe path) to get the writable install dir.
if getattr(sys, "frozen", False):
    _SCRIPT_DIR = Path(sys.executable).resolve().parent
else:
    _SCRIPT_DIR = Path(__file__).resolve().parent

_PIWIGO_HELPERS = _SCRIPT_DIR.parent / "PiwigoHelpers"

if str(_PIWIGO_HELPERS) not in sys.path:
    sys.path.insert(0, str(_PIWIGO_HELPERS))

try:
    import DownloadAlbumStructure
    # Override the params-file path to the exe/script's own directory.
    DownloadAlbumStructure.PARAMS_FILE = _SCRIPT_DIR / "PhotosEditor Params.json"
except ImportError as _e:
    import tkinter as _tk
    import tkinter.messagebox as _mb
    _tk.Tk().withdraw()
    _mb.showerror("Startup Error",
                  f"Cannot import DownloadAlbumStructure from:\n{_PIWIGO_HELPERS}\n\n{_e}")
    sys.exit(1)
# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.WARNING,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    datefmt="%H:%M:%S",
)
logging.getLogger("urllib3").setLevel(logging.WARNING)
logger = logging.getLogger("PhotosEditor")

# ---------------------------------------------------------------------------
# Constants (mirrored from PhotosUploader)
# ---------------------------------------------------------------------------
CUSTOM_FIELDS = [
    ('photo_source',    'Photographer/Source'),
    ('date_of_photo',   'Date of Photo'),
    ('comments',        'Caption'),
    ('tags',            'Tags (comma-separated)'),
]

VIEWER_FETCH_SIZE  = "medium"        # Piwigo derivative used in the editor canvas
STATE_FILE         = _SCRIPT_DIR / "PhotosEditor State.json"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def _opencv_restore(pil_img: "Image.Image",
                    exposure: float, contrast: float,
                    red_cast: float, sharpen: float) -> "Image.Image":
    """Apply fading/redness/blur corrections using OpenCV.
    All parameters are on a −100…+100 (or 0…100) scale.
    Returns a new PIL Image."""
    img = np.array(pil_img.convert("RGB"), dtype=np.float32)

    # 1. Red-cast removal ────────────────────────────────────────────────────
    if red_cast > 0:
        t = red_cast / 100.0
        img[:, :, 0] = np.clip(img[:, :, 0] * (1.0 - t * 0.50), 0, 255)  # R ↓
        img[:, :, 1] = np.clip(img[:, :, 1] * (1.0 + t * 0.10), 0, 255)  # G ↑ slight
        img[:, :, 2] = np.clip(img[:, :, 2] * (1.0 + t * 0.40), 0, 255)  # B ↑

    # 2. Exposure + Contrast ─────────────────────────────────────────────────
    #    alpha: 0.5 … 2.5   beta: −100 … +100
    alpha = 1.0 + contrast / 100.0 * 1.5
    beta  = exposure
    if alpha != 1.0 or beta != 0.0:
        img = np.clip(img * alpha + beta, 0, 255)

    # 3. Sharpening (unsharp mask) ────────────────────────────────────────────
    if sharpen > 0 and CV2_AVAILABLE:
        t      = sharpen / 100.0
        sigma  = 1.0 + t * 2.0    # blur radius 1 → 3
        amount = t * 1.5           # blend weight 0 → 1.5
        u8     = img.astype(np.uint8)
        blurred = cv2.GaussianBlur(u8, (0, 0), sigma)
        img = cv2.addWeighted(u8, 1.0 + amount, blurred, -amount, 0).astype(np.float32)

    return Image.fromarray(np.clip(img, 0, 255).astype(np.uint8))


def _truncate(text: str, max_len: int) -> str:
    return text if len(text) <= max_len else text[: max_len - 1] + "\u2026"


def _load_state() -> dict:
    try:
        if STATE_FILE.exists():
            with open(STATE_FILE) as f:
                return json.load(f)
    except Exception:
        pass
    return {}


def _save_state(state: dict) -> None:
    try:
        tmp = STATE_FILE.with_suffix(".tmp")
        with open(tmp, "w") as f:
            json.dump(state, f, indent=2)
        tmp.replace(STATE_FILE)
    except Exception as e:
        logger.warning(f"Could not save state: {e}")


class _Tooltip:
    """Hover tooltip that treats multiple widgets as one hover region.

    On Leave, uses the event's x_root/y_root (the position at the moment the
    mouse left) to check whether it moved to another widget in the group.
    This avoids async timing issues with after()-based coordinate polling.
    """

    def __init__(self, text_fn):
        self._text_fn  = text_fn
        self._tip      = None
        self._after_id = None
        self._widgets  = []
        self._root     = None

    def attach(self, widget):
        if not self._widgets:
            self._root = widget
        self._widgets.append(widget)
        widget.bind("<Enter>",       self._on_enter,       add="+")
        widget.bind("<Leave>",       self._on_leave,       add="+")
        widget.bind("<ButtonPress>", self._cancel_and_hide, add="+")

    def _coords_inside_group(self, wx: int, wy: int) -> bool:
        """Return True if screen point (wx, wy) falls inside any attached widget."""
        for w in self._widgets:
            try:
                x  = w.winfo_rootx()
                y  = w.winfo_rooty()
                if x <= wx < x + w.winfo_width() and y <= wy < y + w.winfo_height():
                    return True
            except Exception:
                pass
        return False

    def _on_enter(self, _event=None):
        if self._after_id is None:
            if self._root:
                self._after_id = self._root.after(500, self._show)

    def _on_leave(self, event=None):
        # Use the Leave event's own coordinates — they reflect where the mouse
        # was at the instant it left, so no async delay is needed.
        if event is not None:
            try:
                if self._coords_inside_group(event.x_root, event.y_root):
                    return   # moved to a sibling widget in the group
            except Exception:
                pass
        self._cancel_and_hide()

    def _cancel(self):
        if self._after_id and self._root:
            try:
                self._root.after_cancel(self._after_id)
            except Exception:
                pass
            self._after_id = None

    def _cancel_and_hide(self, _event=None):
        self._cancel()
        if self._tip:
            try:
                self._tip.destroy()
            except Exception:
                pass
            self._tip = None

    def _show(self):
        self._after_id = None
        text = self._text_fn()
        if not text:
            return
        try:
            x, y = self._root.winfo_pointerxy()
        except Exception:
            return
        self._tip = tk.Toplevel(self._root)
        self._tip.wm_overrideredirect(True)
        self._tip.wm_geometry(f"+{x + 14}+{y + 14}")
        tk.Label(self._tip, text=text, justify="left",
                 background="#ffffe0", relief="solid", borderwidth=1,
                 font=("TkDefaultFont", 9), padx=6, pady=4).pack()


def _pick_derivative_url(img_dict: dict, preference: tuple) -> str:
    derivs = img_dict.get("derivatives", {})
    for key in preference:
        url = derivs.get(key, {}).get("url", "")
        if url:
            return url
    return ""


# ---------------------------------------------------------------------------
# ThumbnailPanel
# ---------------------------------------------------------------------------
class ThumbnailPanel:
    """A scrollable thumbnail grid with an embedded album hierarchy tree.

    Encapsulates all per-panel state: canvas, grid frame, caches, cells,
    and selected IDs.  PhotosEditor creates two instances (source / target)
    and wires them together via callbacks.
    """

    def __init__(self, parent: tk.Widget, root: tk.Tk, side: str,
                 thumb_size: tuple,
                 album_var: tk.StringVar,
                 count_var: tk.StringVar,
                 on_tree_select,        # (album_id, fullname) -> None
                 on_tree_populate,      # () -> None  (called after widget mapped)
                 on_tree_rmb,           # (event, tree, fullname_map) -> None
                 on_cell_press,         # (event, img_dict, cell, side) -> None
                 on_cell_motion,        # (event, img_dict, cell, side) -> None
                 on_cell_release,       # (event, img_dict, cell, side) -> None
                 on_cell_double,        # (img_dict) -> None
                 on_grid_drop,          # (event, side) -> None
                 on_context_menu,       # (event, iid, img_dict, cell) -> None
                 ):
        self.root        = root
        self.side        = side
        self.thumb_size  = thumb_size
        self._on_tree_select   = on_tree_select
        self._on_tree_populate = on_tree_populate
        self._on_tree_rmb      = on_tree_rmb
        self._on_cell_press    = on_cell_press
        self._on_cell_motion   = on_cell_motion
        self._on_cell_release  = on_cell_release
        self._on_cell_double   = on_cell_double
        self._on_grid_drop     = on_grid_drop
        self._on_context_menu  = on_context_menu

        # Per-panel state
        self.album_images: list[dict] = []
        self.thumb_cache:  dict = {}   # image_id → PIL Image
        self.thumb_tk:     dict = {}   # image_id → PhotoImage (GC anchor)
        self.thumb_cells:  list = []   # ordered cell widgets
        self.img_labels:   dict = {}   # image_id → tk.Label
        self.cell_by_id:   dict = {}   # image_id → tk.Frame
        self.selected_ids: set  = set()

        # Tree state (populated by PhotosEditor)
        self.tree_all_items:       list = []
        self.tree_fullname_by_iid: dict = {}

        self.frame = ttk.Frame(parent)
        self._build(album_var, count_var)

    # ── UI construction ──────────────────────────────────────────────────────

    def _build(self, album_var: tk.StringVar, count_var: tk.StringVar):
        hpane = ttk.PanedWindow(self.frame, orient="horizontal")
        hpane.pack(fill="both", expand=True)
        self.hpane = hpane

        # ── Album hierarchy tree ─────────────────────────────────────────────
        tree_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(tree_outer, weight=2)

        filter_frame = ttk.Frame(tree_outer)
        filter_frame.pack(fill="x", pady=(0, 4))
        ttk.Label(filter_frame, text="Filter:").pack(side="left", padx=(0, 4))
        self._filter_var = tk.StringVar()
        ttk.Entry(filter_frame, textvariable=self._filter_var).pack(
            side="left", fill="x", expand=True)

        tree_frame = ttk.Frame(tree_outer)
        tree_frame.pack(fill="both", expand=True)
        yscroll = ttk.Scrollbar(tree_frame, orient="vertical")
        xscroll = ttk.Scrollbar(tree_frame, orient="horizontal")
        self.tree = ttk.Treeview(
            tree_frame, selectmode="browse", show="tree",
            yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        yscroll.config(command=self.tree.yview)
        xscroll.config(command=self.tree.xview)
        yscroll.pack(side="right", fill="y")
        xscroll.pack(side="bottom", fill="x")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.column("#0", minwidth=200)

        self._filter_var.trace_add("write", self._on_filter)
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select_event)
        self.tree.bind("<Double-1>",         self._on_tree_select_event)
        self.tree.bind("<Button-3>",
            lambda e: self._on_tree_rmb(e, self.tree, self.tree_fullname_by_iid))
        self.tree.bind("<MouseWheel>",
            lambda e: self.tree.yview_scroll(-1 * (e.delta // 120), "units"))

        # ── Thumbnail grid ───────────────────────────────────────────────────
        thumb_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(thumb_outer, weight=3)

        top = ttk.Frame(thumb_outer)
        top.pack(fill="x", pady=(0, 4))
        ttk.Label(top, text="Album:").pack(side="left")
        ttk.Label(top, textvariable=album_var,
                  foreground="blue", anchor="w").pack(side="left", padx=(4, 0))
        ttk.Label(top, textvariable=count_var,
                  foreground="gray").pack(side="right", padx=4)

        container = ttk.Frame(thumb_outer)
        container.pack(fill="both", expand=True)

        self.canvas = tk.Canvas(container, bg="#2a2a2a", highlightthickness=0)
        vscroll = ttk.Scrollbar(container, orient="vertical",
                                command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=vscroll.set)
        vscroll.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)

        self.grid_frame = tk.Frame(self.canvas, bg="#2a2a2a")
        self._grid_win = self.canvas.create_window(0, 0, anchor="nw",
                                                   window=self.grid_frame)

        self.grid_frame.bind("<Configure>",   self._on_grid_resize)
        self.grid_frame.bind("<MouseWheel>",  self._on_mousewheel)
        self.canvas.bind("<Configure>",       self._on_canvas_resize)
        self.canvas.bind("<MouseWheel>",      self._on_mousewheel)
        self.canvas.bind("<ButtonRelease-1>",
                         lambda e: self._on_grid_drop(e, self.side))

        self.frame.bind("<Map>",
            lambda e: self.root.after(50, self._on_tree_populate), add="+")

    # ── Tree helpers ─────────────────────────────────────────────────────────

    def _on_tree_select_event(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        iid      = sel[0]
        album_id = int(iid)
        fullname = self.tree_fullname_by_iid.get(iid, "")
        self._on_tree_select(album_id, fullname)

    def _on_filter(self, *_):
        q = self._filter_var.get().strip().lower()
        if not q:
            self.tree.selection_remove(self.tree.selection())
            return
        for iid, name_lower, _ in self.tree_all_items:
            if q in name_lower:
                self.tree.selection_set(iid)
                self.tree.see(iid)
                return
        self.tree.selection_remove(self.tree.selection())

    # ── Grid helpers ─────────────────────────────────────────────────────────

    def _on_grid_resize(self, _event=None):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas_resize(self, event):
        self.canvas.itemconfigure(self._grid_win, width=event.width)
        self.reflow()

    def _on_mousewheel(self, event):
        self.canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def reflow(self):
        if not self.thumb_cells:
            return
        canvas_w = self.canvas.winfo_width()
        if canvas_w < 10:
            canvas_w = self.thumb_size[0] + 20
        cols = max(1, canvas_w // (self.thumb_size[0] + 16))
        for idx, cell in enumerate(self.thumb_cells):
            r, c = divmod(idx, cols)
            cell.grid(row=r, column=c, padx=4, pady=4, sticky="n")

    def clear(self):
        for cell in self.thumb_cells:
            cell.destroy()
        self.thumb_cells.clear()
        self.thumb_cache.clear()
        self.thumb_tk.clear()
        self.img_labels.clear()
        self.cell_by_id.clear()
        self.selected_ids.clear()
        self.album_images.clear()
        self.canvas.yview_moveto(0)

    # ── Cell creation ─────────────────────────────────────────────────────────

    def add_cell(self, image_id: int, img_dict: dict):
        pil = self.thumb_cache.get(image_id)
        if pil is None:
            return
        tk_img = ImageTk.PhotoImage(pil)
        self.thumb_tk[image_id] = tk_img

        name = img_dict.get("name") or img_dict.get("file") or f"#{image_id}"
        cell = tk.Frame(self.grid_frame, bg="#3a3a3a", relief="flat",
                        padx=2, pady=2, cursor="hand2")
        img_lbl = tk.Label(cell, image=tk_img, bg="#3a3a3a", cursor="hand2")
        img_lbl.pack()
        self.img_labels[image_id] = img_lbl
        self.cell_by_id[image_id] = cell
        name_lbl = tk.Label(cell, text=_truncate(name, 20),
                            bg="#3a3a3a", fg="#dddddd",
                            font=("TkDefaultFont", 8), anchor="center",
                            wraplength=self.thumb_size[0])
        name_lbl.pack(fill="x")

        def _tip_text(d=img_dict, iid=image_id):
            parts = []
            fname = (d.get("file") or d.get("name") or f"#{iid}").strip()
            if fname:
                parts.append(fname)
            caption = (d.get("comment") or "").strip()
            if caption:
                parts.append(f"Caption: {caption}")
            return "\n".join(parts)

        tip = _Tooltip(_tip_text)
        side = self.side
        for w in (cell, img_lbl, name_lbl):
            w.bind("<ButtonPress-1>",
                   lambda e, d=img_dict, c=cell: self._on_cell_press(e, d, c, side))
            w.bind("<B1-Motion>",
                   lambda e, d=img_dict, c=cell: self._on_cell_motion(e, d, c, side))
            w.bind("<ButtonRelease-1>",
                   lambda e, d=img_dict, c=cell: self._on_cell_release(e, d, c, side))
            w.bind("<Double-Button-1>",
                   lambda e, d=img_dict: self._on_cell_double(d))
            w.bind("<Enter>",
                   lambda e, iid=image_id, c=cell: self._enter(iid, c))
            w.bind("<Leave>",
                   lambda e, iid=image_id, c=cell: self._leave(iid, c))
            w.bind("<Button-3>",
                   lambda e, iid=image_id, d=img_dict, c=cell:
                       self._on_context_menu(e, iid, d, c))
            w.bind("<MouseWheel>", self._on_mousewheel)
            tip.attach(w)

        self.thumb_cells.append(cell)
        self.reflow()

    def _enter(self, image_id, cell: tk.Frame):
        if image_id not in self.selected_ids:
            cell.configure(bg="#5a5a5a", relief="raised")

    def _leave(self, image_id, cell: tk.Frame):
        if image_id not in self.selected_ids:
            cell.configure(bg="#3a3a3a", relief="flat")

    def update_thumbnail(self, image_id: int, pil, tk_img):
        """Replace the cached image and update the label in-place."""
        lbl = self.img_labels.get(image_id)
        if lbl is not None:
            self.thumb_cache[image_id] = pil
            self.thumb_tk[image_id]    = tk_img
            lbl.configure(image=tk_img)


# ---------------------------------------------------------------------------
# Main application
# ---------------------------------------------------------------------------
class PhotosEditor:
    _MONTH_MAP: dict = {
        'jan': 1, 'january': 1,   'feb': 2, 'february': 2,
        'mar': 3, 'march': 3,     'apr': 4, 'april': 4,
        'may': 5, 'jun': 6,       'june': 6,
        'jul': 7, 'july': 7,      'aug': 8, 'august': 8,
        'sep': 9, 'sept': 9,      'september': 9,
        'oct': 10, 'october': 10, 'nov': 11, 'november': 11,
        'dec': 12, 'december': 12,
    }
    _2DY_CUTOFF:    int = 35
    _DATE_MIN_YEAR: int = 1926
    _DATE_MAX_YEAR: int = 2035

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("PhotosEditor")
        self.root.geometry("1400x820")
        self.root.minsize(800, 500)

        # ── persistent state ────────────────────────────────────────────────
        self._state = _load_state()

        # 1.5-inch thumbnails sized to the actual display DPI
        _sz = max(100, int(root.winfo_fpixels('1.5i')))
        self._thumb_size = (_sz, _sz)

        # ── album state ────────────────────────────────────────────────────────
        self.current_album_id:   int | None = None
        self.current_album_name: str        = ""
        self.target_album_id:    int | None = None
        self.target_album_name:  str        = ""
        # Saved IDs from previous session (consumed by _populate_*_hierarchy_tree)
        self._saved_album_id:          int | None = None
        self._saved_album_name:        str        = ""
        self._saved_target_album_id:   int | None = None
        self._saved_target_album_name: str        = ""

        # ── drag-and-drop / selection state ─────────────────────────────────
        self._drag_batch:           list        = []     # list of img_dict being dragged
        self._drag_is_copy:         bool        = False
        self._drag_source_side:     str         = 'left' # 'left' | 'right'
        self._drag_window:          tk.Toplevel | None = None
        self._drag_tk_ref:          "ImageTk.PhotoImage | None" = None
        self._press_pos:            tuple | None = None
        self._move_undo_stack:      list        = []     # undo records for drag-and-drop ops
        self._double_click_pending: bool        = False  # suppress spurious release after dbl-click
        self._zoomed:               bool        = False
        self._unzoomed_sash:        int | None  = None   # main pane sash saved before zoom
        self._unzoomed_source_sash: int | None  = None   # source hpane sash (tree width) before zoom

        # ── editor / viewer state ───────────────────────────────────────────
        self._viewer_image:        Image.Image | None = None
        self._viewer_tk:           ImageTk.PhotoImage | None = None
        self._current_image_dict:  dict | None = None
        self._caption_editor_open: bool  = False
        self._photo_edited:        bool  = False  # unsaved edits since last load/upload
        self._crop_start:          tuple | None = None
        self._crop_rect_id:        int   | None = None
        self._photo_display_rect:  tuple | None = None  # (x0,y0,x1,y1) on canvas
        self._edit_history:        list        = []     # stack of PIL Images for undo

        # ── custom-fields state (mirrors PhotosUploader) ────────────────────
        self.custom_data:    dict = {}   # image_id → {field: value}
        self._field_links:   list = []
        self.persist_vars:   dict = {}
        self._exif_data:     dict = {}   # kept for field-link machinery
        self._field_validity = {'date': False, 'caption': False}

        # ── tk variables ────────────────────────────────────────────────────
        self.status_var           = tk.StringVar(value="Ready")
        self.album_var            = tk.StringVar(value="(none)")
        self.target_album_var     = tk.StringVar(value="(none)")
        self.photo_label_var      = tk.StringVar(value="No photo selected")
        self.photo_dim_var        = tk.StringVar(value="")
        self.url_var              = tk.StringVar(value="")
        self.thumb_count_var      = tk.StringVar(value="")
        self.target_thumb_count_var = tk.StringVar(value="")
        self.custom_vars:    dict = {}

        # ── photo restoration state ─────────────────────────────────────────
        self._restoration_base:    Image.Image | None = None
        self._restore_after_id:    str | None         = None
        self._restore_generation:  int                = 0
        self._restore_exposure_var = tk.DoubleVar(value=0.0)
        self._restore_contrast_var = tk.DoubleVar(value=0.0)
        self._restore_red_var      = tk.DoubleVar(value=0.0)
        self._restore_sharpen_var  = tk.DoubleVar(value=0.0)

        # ── editor dialog (built lazily on first double-click) ───────────────
        self._editor_dlg: tk.Toplevel | None = None

        self._build_ui()
        self._restore_state()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.bind("<F5>", self._on_f5_refresh)
        self.root.bind("<Control-z>", self._on_ctrl_z)
        self._ctrl_held: bool = False
        self.root.bind("<KeyPress-Control_L>",   lambda e: setattr(self, '_ctrl_held', True),  add="+")
        self.root.bind("<KeyPress-Control_R>",   lambda e: setattr(self, '_ctrl_held', True),  add="+")
        self.root.bind("<KeyRelease-Control_L>", lambda e: setattr(self, '_ctrl_held', False), add="+")
        self.root.bind("<KeyRelease-Control_R>", lambda e: setattr(self, '_ctrl_held', False), add="+")

        # Refresh album hierarchy from Piwigo on every startup
        self.root.after(200, self._refresh_hierarchy_on_startup)

    # -----------------------------------------------------------------------
    # UI construction
    # -----------------------------------------------------------------------
    def _build_ui(self):
        # ── toolbar ──────────────────────────────────────────────────────────
        toolbar = ttk.Frame(self.root, padding=(4, 2))
        toolbar.pack(side="top", fill="x")

        self._zoom_btn = ttk.Button(toolbar, text="Zoom",
                                    command=self._toggle_zoom)
        self._zoom_btn.pack(side="left", padx=2)

        ttk.Button(toolbar, text="Exit",
                   command=self._on_close).pack(side="right", padx=2)

        # ── main pane ─────────────────────────────────────────────────────────
        self._main_pane = ttk.PanedWindow(self.root, orient="horizontal")
        self._main_pane.pack(side="top", fill="both", expand=True, padx=4, pady=4)

        self._source_panel = ThumbnailPanel(
            parent          = self._main_pane,
            root            = self.root,
            side            = 'left',
            thumb_size      = self._thumb_size,
            album_var       = self.album_var,
            count_var       = self.thumb_count_var,
            on_tree_select  = self._on_source_album_selected_from_tree,
            on_tree_populate= self._populate_source_hierarchy_tree,
            on_tree_rmb     = self._on_tree_rmb,
            on_cell_press   = self._on_cell_press,
            on_cell_motion  = self._on_cell_motion,
            on_cell_release = self._on_cell_release,
            on_cell_double  = self._on_cell_double,
            on_grid_drop    = self._on_grid_drop,
            on_context_menu = self._on_source_context_menu,
        )
        self._main_pane.add(self._source_panel.frame, weight=2)

        self._target_panel = ThumbnailPanel(
            parent          = self._main_pane,
            root            = self.root,
            side            = 'right',
            thumb_size      = self._thumb_size,
            album_var       = self.target_album_var,
            count_var       = self.target_thumb_count_var,
            on_tree_select  = self._on_target_album_selected_from_tree,
            on_tree_populate= self._populate_hierarchy_tree,
            on_tree_rmb     = self._on_tree_rmb,
            on_cell_press   = self._on_cell_press,
            on_cell_motion  = self._on_cell_motion,
            on_cell_release = self._on_cell_release,
            on_cell_double  = self._on_cell_double,
            on_grid_drop    = self._on_grid_drop,
            on_context_menu = self._on_target_context_menu,
        )
        self._main_pane.add(self._target_panel.frame, weight=2)

        # ── status bar ───────────────────────────────────────────────────────
        status_bar = ttk.Frame(self.root, relief="sunken")
        status_bar.pack(side="bottom", fill="x")
        ttk.Label(status_bar, textvariable=self.status_var,
                  anchor="w").pack(side="left", padx=6, pady=2)

    # ── Editor dialog: opened on double-click of any thumbnail ─────────────
    def _open_editor_dialog(self, img_dict: dict):
        """Open (or bring forward) the photo-editor dialog and load img_dict."""
        dlg_alive = (self._editor_dlg is not None and
                     self._editor_dlg.winfo_exists())
        if not dlg_alive:
            self._editor_dlg = tk.Toplevel(self.root)
            self._editor_dlg.title("Photo Editor")
            self._editor_dlg.minsize(600, 400)
            self._editor_dlg.transient(self.root)   # always on top of main window
            self._build_editor_dialog_content(self._editor_dlg)
            saved_geo = self._state.get("editor_geometry", "")
            if saved_geo:
                try:
                    self._editor_dlg.geometry(saved_geo)
                except Exception:
                    saved_geo = ""
            if not saved_geo:
                # No saved size: fit all controls up to the screen limit.
                self._editor_dlg.update_idletasks()
                req_w = self._editor_dlg.winfo_reqwidth()
                req_h = self._editor_dlg.winfo_reqheight()
                scr_w = self._editor_dlg.winfo_screenwidth()
                scr_h = self._editor_dlg.winfo_screenheight()
                dlg_w = min(max(req_w, 900), scr_w - 40)
                dlg_h = min(max(req_h, 700), scr_h - 80)
                # Centre on screen
                x = (scr_w - dlg_w) // 2
                y = (scr_h - dlg_h) // 2
                self._editor_dlg.geometry(f"{dlg_w}x{dlg_h}+{x}+{y}")
            self._editor_dlg.protocol("WM_DELETE_WINDOW", self._close_editor_dialog)
            self._editor_dlg.bind("<Control-z>", lambda e: self._undo_edit())
        else:
            self._editor_dlg.deiconify()
            self._clear_editor()   # wipe previous image before new one loads
        self._editor_dlg.lift()
        self._editor_dlg.grab_set()
        self._on_thumb_click(img_dict)

    def _close_editor_dialog(self):
        if self._photo_edited:
            name = (self._current_image_dict or {}).get("file") or \
                   (self._current_image_dict or {}).get("name") or "this photo"
            if not messagebox.askyesno(
                    "Unsaved Edits",
                    f'"{name}" has been edited but not uploaded to Piwigo.\n\n'
                    "Close without uploading?",
                    icon="warning", parent=self._editor_dlg):
                return
        # Persist the dialog's current geometry so it reopens in the same spot.
        self._state["editor_geometry"] = self._editor_dlg.geometry()
        _save_state(self._state)
        self._editor_dlg.grab_release()
        self._editor_dlg.withdraw()
        # Refresh the thumbnail in whichever grid it came from.
        self._refresh_current_thumbnail()

    def _build_editor_dialog_content(self, dlg: tk.Toplevel):
        """Populate the editor Toplevel with all editor widgets."""
        # Vertical pane: photo viewer (top) / custom fields (bottom)
        vpane = ttk.PanedWindow(dlg, orient="vertical")
        vpane.pack(fill="both", expand=True)
        self._editor_vpane = vpane

        # ── Top pane: Photo display ───────────────────────────────────────────
        viewer_frame = ttk.LabelFrame(vpane, text="Photo Editor", padding=4)
        vpane.add(viewer_frame, weight=13)

        # Left column: photo name, dimensions, source URL
        left_col = ttk.Frame(viewer_frame)
        left_col.pack(side="left", fill="y", padx=(0, 6))

        _bg = ttk.Style().lookup("TFrame", "background") or "SystemButtonFace"
        tk.Entry(left_col, textvariable=self.photo_label_var,
                 font=("TkDefaultFont", 9, "italic"),
                 state="readonly", relief="flat", bd=0,
                 highlightthickness=0,
                 readonlybackground=_bg).pack(fill="x", pady=(0, 2))

        ttk.Label(left_col, textvariable=self.photo_dim_var,
                  anchor="w").pack(fill="x", pady=(0, 6))

        url_label = ttk.Label(left_col, textvariable=self.url_var,
                              font=("TkDefaultFont", 8),
                              anchor="nw", justify="left",
                              wraplength=220, foreground="gray")
        url_label.pack(fill="x")

        def _update_url_wraplength(event):
            url_label.configure(wraplength=max(event.width - 4, 50))
        url_label.bind("<Configure>", _update_url_wraplength)

        # Right column: canvas
        right_col = ttk.Frame(viewer_frame)
        right_col.pack(side="left", fill="both", expand=True)

        self.canvas = tk.Canvas(right_col, bg="#1a1a1a", cursor="crosshair",
                                height=200)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>",        self._on_canvas_resize)
        self.canvas.bind("<Control-Button-1>", self._open_caption_editor)
        self.canvas.bind("<Double-Button-1>",  self._open_caption_editor)
        self.canvas.bind("<Button-1>",         self._on_crop_start)
        self.canvas.bind("<B1-Motion>",        self._on_crop_drag)
        self.canvas.bind("<ButtonRelease-1>",  self._on_crop_release)
        self.canvas.bind("<Escape>",           self._clear_crop_rect)

        def _enforce_canvas_min_width(event):
            min_w = int(event.width * 0.60)
            if self.canvas.winfo_width() < min_w:
                self.canvas.configure(width=min_w)
        right_col.bind("<Configure>", _enforce_canvas_min_width)

        # ── Bottom pane: lower container (Custom Fields + Editing Tools) ────────
        lower_frame = ttk.Frame(vpane)
        vpane.add(lower_frame, weight=17)

        custom_frame = ttk.LabelFrame(lower_frame, text="Custom Fields", padding=6)
        custom_frame.pack(fill="x")

        # "Persist" column header
        ttk.Label(custom_frame, text="Persist", anchor="center").grid(
            row=0, column=1, sticky="ew", pady=2)

        for i, (key, label) in enumerate(CUSTOM_FIELDS):
            row = i + 1
            ttk.Label(custom_frame, text=label + ":", width=22, anchor="e").grid(
                row=row, column=0, sticky="e", pady=2, padx=(0, 4))

            persist_var = tk.BooleanVar(value=False)
            ttk.Checkbutton(custom_frame, variable=persist_var).grid(
                row=row, column=1, sticky="w", padx=4, pady=2)
            self.persist_vars[key] = persist_var

            if key == 'comments':
                txt = tk.Text(custom_frame, height=3, width=40, wrap="word",
                              font=("TkDefaultFont", 9))
                txt.grid(row=row, column=2, sticky="ew", pady=2)
                self.custom_vars[key] = txt
            else:
                var = tk.StringVar()
                if key == 'date_of_photo':
                    entry = tk.Entry(custom_frame, textvariable=var, width=40)
                    self.date_entry = entry
                else:
                    entry = ttk.Entry(custom_frame, textvariable=var, width=40)
                entry.grid(row=row, column=2, sticky="ew", pady=2)
                self.custom_vars[key] = var
        custom_frame.columnconfigure(2, weight=1)

        # ── Bidirectional field links ─────────────────────────────────────────
        self._field_links = []   # reset before registering
        self._register_field_link(
            custom_key='photo_source', exif_key='Artist',
            iptc_tag=(2, 80), validate_fn=None)
        self._register_field_link(
            custom_key='date_of_photo', exif_key='Date Created',
            iptc_tag=(2, 55), validate_fn=self._parse_date)
        self.custom_vars['date_of_photo'].trace_add(
            'write', lambda *_: self._validate_date_field())
        self._register_field_link(
            custom_key='tags', exif_key=None,
            iptc_tag=(2, 25), validate_fn=None)

        def _on_comments_changed(_event=None):
            self._validate_caption_field()
            self.custom_vars['comments'].edit_modified(False)
        self.custom_vars['comments'].bind('<<Modified>>', _on_comments_changed)

        # ── Editing Tools ─────────────────────────────────────────────────────
        tools_frame = ttk.LabelFrame(lower_frame, text="Editing Tools", padding=6)
        tools_frame.pack(fill="x", pady=(4, 0))

        # Single row – Rotate | Crop | Undo
        row1 = ttk.Frame(tools_frame)
        row1.pack(fill="x", pady=(0, 4))
        ttk.Label(row1, text="Rotate:").pack(side="left", padx=(0, 6))
        self.rotate_right_btn = ttk.Button(row1, text="↻ 90° Right",
                   command=lambda: self._rotate_photo(90), state="disabled")
        self.rotate_right_btn.pack(side="left", padx=2)
        self.rotate_left_btn = ttk.Button(row1, text="↺ 90° Left",
                   command=lambda: self._rotate_photo(-90), state="disabled")
        self.rotate_left_btn.pack(side="left", padx=2)
        self.rotate_180_btn = ttk.Button(row1, text="↷ 180°",
                   command=lambda: self._rotate_photo(180), state="disabled")
        self.rotate_180_btn.pack(side="left", padx=2)
        ttk.Label(row1, text="").pack(side="left", padx=16)   # spacer
        self.crop_btn = ttk.Button(row1, text="Crop", command=self._crop_photo,
                                   state="disabled")
        self.crop_btn.pack(side="left", padx=2)
        ttk.Label(row1, text="").pack(side="left", padx=16)   # spacer
        self.undo_btn = ttk.Button(row1, text="Undo", command=self._undo_edit,
                                   state="disabled")
        self.undo_btn.pack(side="left", padx=2)
        self.revert_btn = ttk.Button(row1, text="Revert", command=self._revert_photo,
                                     state="disabled")
        self.revert_btn.pack(side="left", padx=2)

        # ── Photo Restoration ─────────────────────────────────────────────────
        restore_frame = ttk.LabelFrame(lower_frame, text="Photo Restoration", padding=6)
        restore_frame.pack(fill="x", pady=(4, 0))

        # Left column: sliders  |  Right column: buttons
        sliders_col = ttk.Frame(restore_frame)
        sliders_col.pack(side="left", fill="x", expand=True)

        btns_col = ttk.Frame(restore_frame)
        btns_col.pack(side="left", fill="y", padx=(8, 0))

        _restore_sliders = [
            ("Exposure",  self._restore_exposure_var, -100, 100),
            ("Contrast",  self._restore_contrast_var, -100, 100),
            ("Red cast",  self._restore_red_var,         0, 100),
            ("Sharpen",   self._restore_sharpen_var,     0, 100),
        ]
        self._restore_val_vars = {}
        for label, dvar, lo, hi in _restore_sliders:
            row = ttk.Frame(sliders_col)
            row.pack(fill="x", pady=1)
            ttk.Label(row, text=f"{label}:", width=9, anchor="e").pack(
                side="left", padx=(0, 4))
            val_var = tk.StringVar(value="0")
            self._restore_val_vars[label] = val_var
            ttk.Label(row, textvariable=val_var, width=4,
                      anchor="e").pack(side="right")
            def _cmd(v, vv=val_var, dv=dvar):
                vv.set(str(int(float(v))))
                self._on_restoration_change()
            ttk.Scale(row, from_=lo, to=hi, orient="horizontal",
                      variable=dvar, command=_cmd).pack(
                          side="left", fill="x", expand=True)

        if not CV2_AVAILABLE:
            ttk.Label(btns_col, text="(requires\nopencv-python)",
                      foreground="red", justify="center").pack(pady=(0, 4))
        ttk.Button(btns_col, text="Revert\nRestoration",
                   command=self._reset_restoration).pack()

        # ── Dialog action buttons (Upload / Close) ────────────────────────────
        action_bar = ttk.Frame(dlg, padding=(8, 4))
        action_bar.pack(fill="x")

        self.upload_photo_btn = tk.Button(
            action_bar, text="⬆ Upload to Piwigo",
            command=self._upload_current_photo,
            background="#add8e6",
            font=("TkDefaultFont", 10, "bold"),
            state="disabled")
        self.upload_photo_btn.pack(side="left", padx=(0, 8))

        ttk.Button(action_bar, text="Close",
                   command=self._close_editor_dialog).pack(side="left")

        dlg.after(100, self._set_initial_sash_positions)

    # -----------------------------------------------------------------------
    # State / geometry
    # -----------------------------------------------------------------------
    def _restore_state(self):
        geo = self._state.get("geometry", "")
        if geo:
            try:
                self.root.geometry(geo)
            except Exception:
                pass
        sash = self._state.get("sash", None)
        if sash is not None:
            self.root.after(200, lambda: self._set_main_sash(sash))
        # Stash saved album IDs so tree-population methods can restore them.
        # Do NOT load photos here — _populate_*_hierarchy_tree() will trigger
        # the load after confirming the album still exists in the hierarchy.
        album_id   = self._state.get("album_id",   None)
        album_name = self._state.get("album_name", "")
        if album_id is not None:
            self._saved_album_id   = album_id
            self._saved_album_name = album_name
        target_id   = self._state.get("target_album_id",   None)
        target_name = self._state.get("target_album_name", "")
        if target_id is not None:
            self._saved_target_album_id   = target_id
            self._saved_target_album_name = target_name

    def _set_main_sash(self, pos: int):
        try:
            self._main_pane.sashpos(0, pos)
        except Exception:
            pass

    def _set_initial_sash_positions(self):
        """Give the photo viewer ~43% of the right panel height."""
        total = self._editor_vpane.winfo_height()
        if total < 50:
            self.root.after(50, self._set_initial_sash_positions)
            return
        self._editor_vpane.sashpos(0, round(total * 13 / 30))

    def _on_close(self):
        if self._photo_edited:
            name = (self._current_image_dict or {}).get("file") or \
                   (self._current_image_dict or {}).get("name") or "this photo"
            if not messagebox.askyesno(
                    "Unsaved Edits",
                    f'"{name}" has been edited but not uploaded to Piwigo.\n\n'
                    "Close without uploading?",
                    icon="warning", parent=self.root):
                return
        state: dict = dict(self._state)   # preserve keys like editor_geometry
        # Capture editor dialog size/position even if closed via app exit
        if self._editor_dlg is not None and self._editor_dlg.winfo_exists():
            state["editor_geometry"] = self._editor_dlg.geometry()
        state["geometry"] = self.root.geometry()
        # Always save the unzoomed sash position
        try:
            state["sash"] = (self._unzoomed_sash if self._zoomed
                             else self._main_pane.sashpos(0))
        except Exception:
            pass
        if self.current_album_id is not None:
            state["album_id"]   = self.current_album_id
            state["album_name"] = self.current_album_name
        if self.target_album_id is not None:
            state["target_album_id"]   = self.target_album_id
            state["target_album_name"] = self.target_album_name
        _save_state(state)
        self.root.destroy()

    def _on_ctrl_z(self, _event=None):
        self._undo_drag_drop()

    def _on_f5_refresh(self, _event=None):
        self._load_album_photos()
        if self.target_album_id is not None:
            self._load_target_album_photos()

    def _toggle_zoom(self):
        if self._zoomed:
            # Re-add right panel, force layout, restore main sash and tree width
            self._main_pane.add(self._target_panel.frame, weight=2)
            self._main_pane.update()
            if self._unzoomed_sash is not None:
                self._set_main_sash(self._unzoomed_sash)
            # Restore the source tree to its pre-zoom width
            if self._unzoomed_source_sash is not None:
                self._source_panel.hpane.update()
                try:
                    self._source_panel.hpane.sashpos(0, self._unzoomed_source_sash)
                except Exception:
                    pass
            self._zoom_btn.config(text="Zoom")
            self._zoomed = False
        else:
            # Save main sash and source tree width, then hide right panel
            try:
                self._unzoomed_sash = self._main_pane.sashpos(0)
            except Exception:
                self._unzoomed_sash = None
            try:
                self._unzoomed_source_sash = self._source_panel.hpane.sashpos(0)
            except Exception:
                self._unzoomed_source_sash = None
            self._main_pane.forget(self._target_panel.frame)
            # Keep source tree the same width; thumbnails absorb all extra space
            self._source_panel.hpane.update()
            try:
                self._source_panel.hpane.sashpos(0, self._unzoomed_source_sash)
            except Exception:
                pass
            self._zoom_btn.config(text="Unzoom")
            self._zoomed = True

    # -----------------------------------------------------------------------
    # Status
    # -----------------------------------------------------------------------
    def set_status(self, msg: str):
        self.status_var.set(msg)

    # -----------------------------------------------------------------------
    # Startup album hierarchy refresh
    # -----------------------------------------------------------------------
    def _refresh_hierarchy_on_startup(self):
        """Fetch the album list from Piwigo and save AlbumHierarchy.json.
        Runs in a background thread; status bar shows progress."""
        self.set_status("Refreshing album hierarchy…")

        def worker():
            try:
                params = DownloadAlbumStructure.load_params()
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=params.get("verify_ssl", True),
                    rate_limit_calls_per_second=params.get(
                        "rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])
                n = DownloadAlbumStructure._fetch_and_save_hierarchy(
                    client, lambda msg: self.root.after(0, lambda m=msg: self.set_status(m)))
                client.logout()
                self.root.after(0, lambda: self.set_status(
                    f"Album hierarchy refreshed ({n} albums)."))
                self.root.after(0, self._populate_source_hierarchy_tree)
                self.root.after(0, self._populate_hierarchy_tree)
            except Exception as e:
                logger.warning(f"Could not refresh album hierarchy: {e}")
                self.root.after(0, lambda e=e: self.set_status(
                    f"Hierarchy refresh failed: {e}"))

        threading.Thread(target=worker, daemon=True).start()

    # -----------------------------------------------------------------------
    # Album selection
    def _on_source_album_selected_from_tree(self, album_id: int, fullname: str):
        if album_id != self.current_album_id:
            self._on_album_selected(album_id, fullname)

    def _on_target_album_selected_from_tree(self, album_id: int, fullname: str):
        if album_id != self.target_album_id:
            self._on_target_album_selected(album_id, fullname)

    def _on_source_context_menu(self, event, iid: int, img_dict: dict, cell):
        menu = tk.Menu(cell, tearoff=0)
        if iid in self._source_panel.selected_ids and len(self._source_panel.selected_ids) > 1:
            n = len(self._source_panel.selected_ids)
            menu.add_command(
                label=f"Remove {n} selected from Album",
                command=lambda: self._remove_selection_from_album('left'))
        else:
            menu.add_command(label="Remove from Album",
                             command=lambda: self._remove_from_album(iid, img_dict, 'left'))
        menu.tk_popup(event.x_root, event.y_root)

    def _on_target_context_menu(self, event, iid: int, img_dict: dict, cell):
        menu = tk.Menu(cell, tearoff=0)
        if iid in self._target_panel.selected_ids and len(self._target_panel.selected_ids) > 1:
            n = len(self._target_panel.selected_ids)
            menu.add_command(
                label=f"Remove {n} selected from Album",
                command=lambda: self._remove_selection_from_album('right'))
        else:
            menu.add_command(label="Remove from Album",
                             command=lambda: self._remove_from_album(iid, img_dict, 'right'))
        menu.tk_popup(event.x_root, event.y_root)

    def _on_album_selected(self, album_id: int, fullname: str):
        self.current_album_id   = album_id
        self.current_album_name = fullname
        self.album_var.set(fullname)
        self.set_status(f"Album selected: {fullname}")
        self._load_album_photos()

    # -----------------------------------------------------------------------
    # Album hierarchy tree population
    # -----------------------------------------------------------------------
    def _populate_panel_hierarchy_tree(self, panel: "ThumbnailPanel",
                                       saved_id_attr: str, saved_name_attr: str,
                                       album_id_attr: str, album_name_attr: str,
                                       album_var: tk.StringVar,
                                       load_fn):
        """Load AlbumHierarchy.json into `panel`'s tree.

        `saved_id_attr` / `saved_name_attr` name the PhotosEditor instance
        attributes holding the saved-session album ID and name to restore on
        first population.  `album_id_attr` / `album_name_attr` name the
        attributes holding the currently selected album for that panel.
        """
        try:
            hier_file = DownloadAlbumStructure._album_hierarchy_file()
            if not hier_file.exists():
                return
            with open(hier_file, encoding="utf-8") as f:
                hierarchy = json.load(f)
        except Exception as e:
            logger.warning(f"Could not load hierarchy for {panel.side} tree: {e}")
            return

        tree = panel.tree
        for item in tree.get_children():
            tree.delete(item)
        panel.tree_all_items = []
        panel.tree_fullname_by_iid = {}

        def _populate(parent_iid, nodes, top_level=False):
            for node in nodes:
                iid   = str(node["id"])
                count = node.get("total_nb_images", 0)
                text  = f"{node['name']}  ({count:,})"
                tree.insert(parent_iid, "end", iid=iid, text=text, open=top_level)
                fullname = node.get("fullname", node["name"])
                panel.tree_all_items.append((iid, node["name"].lower(), fullname))
                panel.tree_fullname_by_iid[iid] = fullname
                if node.get("children"):
                    _populate(iid, node["children"])

        _populate("", hierarchy, top_level=True)

        # On first population, restore the saved album from the previous session.
        saved_id = getattr(self, saved_id_attr)
        if saved_id is not None:
            iid = str(saved_id)
            setattr(self, saved_id_attr, None)   # consume so it isn't re-applied on refresh
            if tree.exists(iid):
                setattr(self, album_id_attr,   int(iid))
                setattr(self, album_name_attr, getattr(self, saved_name_attr))
                album_var.set(getattr(self, saved_name_attr) or "(none)")
                tree.selection_set(iid)
                tree.see(iid)
                self.root.after(0, load_fn)
            # else: album was deleted — stay at default
            return

        # Re-select current album on subsequent refreshes.
        current_id = getattr(self, album_id_attr)
        if current_id is not None:
            iid = str(current_id)
            if tree.exists(iid):
                tree.selection_set(iid)
                tree.see(iid)

    def _populate_source_hierarchy_tree(self):
        """Load AlbumHierarchy.json into the source (left) embedded tree."""
        self._populate_panel_hierarchy_tree(
            self._source_panel,
            saved_id_attr   = '_saved_album_id',
            saved_name_attr = '_saved_album_name',
            album_id_attr   = 'current_album_id',
            album_name_attr = 'current_album_name',
            album_var       = self.album_var,
            load_fn         = self._load_album_photos,
        )

    def _populate_hierarchy_tree(self):
        """Load AlbumHierarchy.json into the target (right) embedded tree."""
        self._populate_panel_hierarchy_tree(
            self._target_panel,
            saved_id_attr   = '_saved_target_album_id',
            saved_name_attr = '_saved_target_album_name',
            album_id_attr   = 'target_album_id',
            album_name_attr = 'target_album_name',
            album_var       = self.target_album_var,
            load_fn         = self._load_target_album_photos,
        )

    def _on_tree_rmb(self, event, tree: ttk.Treeview, fullname_map: dict):
        """Right-click on either hierarchy tree — offer 'Add sub-album'."""
        iid = tree.identify_row(event.y)
        if not iid:
            return
        fullname = fullname_map.get(iid, iid)
        short    = fullname.rsplit(" / ", 1)[-1]
        parent_id = int(iid)

        menu = tk.Menu(tree, tearoff=0)
        menu.add_command(
            label=f"Add sub-album under \"{short}\"",
            command=lambda: self.root.after(
                50, lambda: self._add_sub_album_dialog(parent_id, short, tree)))
        menu.tk_popup(event.x_root, event.y_root)

    def _add_sub_album_dialog(self, parent_id: int, parent_name: str,
                              tree: ttk.Treeview):
        """Show a simple name-entry dialog, then create the sub-album."""
        dlg = tk.Toplevel(self.root)
        dlg.title("Add Sub-Album")
        dlg.resizable(False, False)
        dlg.grab_set()

        ttk.Label(dlg, text=f"New sub-album under \"{parent_name}\":",
                  padding=(16, 12, 16, 4)).pack()
        name_var = tk.StringVar()
        entry = ttk.Entry(dlg, textvariable=name_var, width=40)
        entry.pack(padx=16, pady=(0, 8))
        entry.focus_set()

        msg_var = tk.StringVar()
        msg_lbl = ttk.Label(dlg, textvariable=msg_var, foreground="red",
                            padding=(16, 0, 16, 4))
        msg_lbl.pack()

        btn_row = ttk.Frame(dlg, padding=(16, 0, 16, 12))
        btn_row.pack()

        def _create():
            name = name_var.get().strip()
            if not name:
                msg_var.set("Please enter a name.")
                return
            ok_btn.config(state="disabled")
            cancel_btn.config(state="disabled")
            msg_var.set("Creating…")
            dlg.update_idletasks()

            def worker():
                try:
                    params = DownloadAlbumStructure.load_params()
                    client = DownloadAlbumStructure.PiwigoClient(
                        params["url"], params["username"], params["password"],
                        verify_ssl=params.get("verify_ssl", True),
                        rate_limit_calls_per_second=params.get(
                            "rate_limit_calls_per_second", 2.0))
                    client.login(params["username"], params["password"])
                    new_id = client.create_album(name, parent_id=parent_id)
                    client.logout()
                    self.root.after(0, lambda: _done(new_id, name))
                except Exception as e:
                    self.root.after(0, lambda e=e: _error(str(e)))

            def _done(new_id: int, album_name: str):
                dlg.destroy()
                self.set_status(f"Created sub-album \"{album_name}\" (id={new_id}).")
                # Refresh both trees so the new album appears immediately
                self._refresh_hierarchy_on_startup()

            def _error(msg: str):
                msg_var.set(f"Error: {msg}")
                ok_btn.config(state="normal")
                cancel_btn.config(state="normal")

            threading.Thread(target=worker, daemon=True).start()

        ok_btn     = ttk.Button(btn_row, text="Create", command=_create)
        cancel_btn = ttk.Button(btn_row, text="Cancel", command=dlg.destroy)
        ok_btn.pack(side="left", padx=(0, 8))
        cancel_btn.pack(side="left")

        entry.bind("<Return>", lambda e: _create())
        entry.bind("<Escape>", lambda e: dlg.destroy())

        self.root.update_idletasks()
        dlg.update_idletasks()
        rw, rh = self.root.winfo_width(), self.root.winfo_height()
        rx, ry = self.root.winfo_rootx(), self.root.winfo_rooty()
        dw, dh = dlg.winfo_reqwidth(), dlg.winfo_reqheight()
        dlg.geometry(f"{dw}x{dh}+{rx+(rw-dw)//2}+{ry+(rh-dh)//2}")

    def _on_target_album_selected(self, album_id: int, fullname: str):
        self.target_album_id   = album_id
        self.target_album_name = fullname
        self.target_album_var.set(fullname)
        self.set_status(f"Target album selected: {fullname}")
        self._load_target_album_photos()

    # -----------------------------------------------------------------------
    # Progress dialog helper
    # -----------------------------------------------------------------------
    def _make_progress_dialog(self, title: str, heading: str, total: int,
                               subheading: str = "",
                               initial_stage: str = "Starting…",
                               grab: bool = False):
        """Create a centered, non-closeable progress dialog.

        total > 0  → determinate bar (0..total)
        total == 0 → indeterminate (spinning) bar

        Returns (set_stage, advance, close_dlg) — all thread-safe via root.after.
          set_stage(msg)  update the stage label
          advance(n)      set progress bar value
          close_dlg()     stop the bar and destroy the dialog
        """
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.resizable(False, False)
        if grab:
            dlg.grab_set()
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        dlg_alive = [True]
        dlg.bind("<Destroy>", lambda _e: dlg_alive.__setitem__(0, False))

        ttk.Label(dlg, text=heading, padding=(16, 12, 16, 2)).pack()
        if subheading:
            ttk.Label(dlg, text=subheading, padding=(16, 0, 16, 8)).pack()
        if total > 0:
            pbar = ttk.Progressbar(dlg, mode="determinate",
                                   maximum=total, length=380)
        else:
            pbar = ttk.Progressbar(dlg, mode="indeterminate", length=380)
        pbar.pack(padx=16, pady=(0, 4))
        if total == 0:
            pbar.start(12)
        stage_var = tk.StringVar(value=initial_stage)
        ttk.Label(dlg, textvariable=stage_var, foreground="gray",
                  padding=(16, 0, 16, 12)).pack()

        self.root.update_idletasks()
        dlg.update_idletasks()
        rw, rh = self.root.winfo_width(), self.root.winfo_height()
        rx, ry = self.root.winfo_rootx(), self.root.winfo_rooty()
        dw, dh = dlg.winfo_reqwidth(), dlg.winfo_reqheight()
        dlg.geometry(f"{dw}x{dh}+{rx+(rw-dw)//2}+{ry+(rh-dh)//2}")

        def set_stage(msg):
            self.root.after(0, lambda: stage_var.set(msg) if dlg_alive[0] else None)

        def advance(n):
            self.root.after(0, lambda: pbar.__setitem__("value", n) if dlg_alive[0] else None)

        def close_dlg():
            self.root.after(0, lambda: (pbar.stop(), dlg.destroy())
                            if dlg_alive[0] else None)

        return set_stage, advance, close_dlg

    # -----------------------------------------------------------------------
    # Load & display thumbnails
    # -----------------------------------------------------------------------
    def _load_panel_photos(self, panel: "ThumbnailPanel",
                           album_id: int, album_name: str,
                           count_var: tk.StringVar):
        panel.clear()
        self._drag_batch.clear()
        count_var.set("")
        self.set_status(f"Fetching photos from \"{album_name}\"…")

        dlg = tk.Toplevel(self.root)
        dlg.title("Downloading Photos")
        dlg.resizable(False, False)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        dlg_alive = [True]
        dlg.bind("<Destroy>", lambda _e: dlg_alive.__setitem__(0, False))

        ttk.Label(dlg, text="Downloading thumbnails from:",
                  padding=(16, 12, 16, 2)).pack()
        ttk.Label(dlg, text=album_name,
                  font=("TkDefaultFont", 9, "bold"),
                  padding=(16, 0, 16, 8)).pack()
        pbar = ttk.Progressbar(dlg, mode="indeterminate", length=360)
        pbar.pack(padx=16, pady=(0, 4))
        pbar.start(12)
        count_lbl_var = tk.StringVar(value="Connecting…")
        ttk.Label(dlg, textvariable=count_lbl_var, foreground="gray",
                  padding=(16, 0, 16, 12)).pack()

        self.root.update_idletasks()
        dlg.update_idletasks()
        rw, rh = self.root.winfo_width(),  self.root.winfo_height()
        rx, ry = self.root.winfo_rootx(),  self.root.winfo_rooty()
        dw, dh = dlg.winfo_reqwidth(),     dlg.winfo_reqheight()
        dlg.geometry(f"{dw}x{dh}+{rx+(rw-dw)//2}+{ry+(rh-dh)//2}")

        def _on_total(n):
            def _apply():
                if not dlg_alive[0]: return
                pbar.stop()
                pbar.configure(mode="determinate", maximum=max(n, 1))
                count_lbl_var.set(f"0 / {n}")
            self.root.after(0, _apply)

        def _on_progress(done, total):
            def _apply():
                if not dlg_alive[0]: return
                pbar["value"] = done
                count_lbl_var.set(f"{done} / {total}")
            self.root.after(0, _apply)

        def _on_done():
            self.root.after(0, lambda: dlg.destroy() if dlg_alive[0] else None)

        threading.Thread(
            target=self._worker_fetch_photos,
            args=(panel, album_id, album_name, count_var, _on_total, _on_progress, _on_done),
            daemon=True).start()

    def _load_album_photos(self):
        if self.current_album_id is None:
            messagebox.showinfo("No Album", "Please select an album first.")
            return
        self._load_panel_photos(self._source_panel,
                                self.current_album_id, self.current_album_name,
                                self.thumb_count_var)

    def _load_target_album_photos(self):
        if self.target_album_id is None:
            return
        self._load_panel_photos(self._target_panel,
                                self.target_album_id, self.target_album_name,
                                self.target_thumb_count_var)

    def _worker_fetch_photos(self, panel: "ThumbnailPanel",
                             album_id: int, album_name: str,
                             count_var: tk.StringVar,
                             on_total, on_progress, on_done):
        try:
            params = DownloadAlbumStructure.load_params()
            client = DownloadAlbumStructure.PiwigoClient(
                params["url"], params["username"], params["password"],
                verify_ssl=params.get("verify_ssl", True),
                rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
            client.login(params["username"], params["password"])
            images = client.get_album_images(album_id)
            client.logout()

            panel.album_images = images
            n = len(images)
            self.root.after(0, lambda: count_var.set(f"{n} photo{'s' if n != 1 else ''}"))
            on_total(n)

            verify = params.get("verify_ssl", True)
            for idx, img_dict in enumerate(images):
                self._worker_download_thumb(panel, img_dict, verify)
                on_progress(idx + 1, n)

            on_done()
            self.root.after(0, lambda: self.set_status(
                f"Loaded {n} photo{'s' if n != 1 else ''} from \"{album_name}\""))
        except Exception as e:
            logger.exception("Error fetching photos")
            on_done()
            self.root.after(0, lambda e=e: messagebox.showerror("Error", str(e)))
            self.root.after(0, lambda e=e: self.set_status(f"Error: {e}"))

    def _worker_download_thumb(self, panel: "ThumbnailPanel", img_dict: dict, verify: bool):
        if not PIL_AVAILABLE or not REQUESTS_AVAILABLE:
            return
        image_id = img_dict.get("id")
        url = _pick_derivative_url(
            img_dict,
            ("thumb", "square", "small", "2small", "xsmall", "medium", "large"))
        if not url:
            url = img_dict.get("element_url", "")
        if not url:
            logger.warning(f"Image {image_id}: no URL found. "
                           f"derivatives={list(img_dict.get('derivatives', {}).keys())}")
            return
        try:
            with warnings.catch_warnings():
                if not verify:
                    warnings.simplefilter("ignore", urllib3.exceptions.InsecureRequestWarning)
                resp = requests.get(url, verify=verify, timeout=15)
                resp.raise_for_status()
            pil = Image.open(BytesIO(resp.content))
            pil.load()
            if pil.mode not in ("RGB", "RGBA"):
                pil = pil.convert("RGB")
            pil.thumbnail(self._thumb_size, Image.Resampling.LANCZOS)
            panel.thumb_cache[image_id] = pil
            self.root.after(0, lambda iid=image_id, d=img_dict: panel.add_cell(iid, d))
        except Exception as e:
            logger.warning(f"Thumbnail {image_id} ({url}): {e}")

    # -----------------------------------------------------------------------
    # Unified thumbnail press / motion / release  (both sides, click + drag)
    # -----------------------------------------------------------------------
    _DRAG_THRESHOLD = 5   # pixels of movement before a press becomes a drag

    def _on_cell_press(self, event, img_dict: dict, cell: tk.Frame, side: str):
        self._press_pos = (event.x_root, event.y_root)
        self._drag_source_side = side
        self._drag_batch = []

    def _on_cell_motion(self, event, img_dict: dict, cell: tk.Frame, side: str):
        if self._press_pos is None:
            return
        dx = abs(event.x_root - self._press_pos[0])
        dy = abs(event.y_root - self._press_pos[1])
        if dx < self._DRAG_THRESHOLD and dy < self._DRAG_THRESHOLD:
            return
        if self._drag_window is None and not self._drag_batch:
            self._start_drag(event, img_dict, side)
        if self._drag_window:
            self._drag_window.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
            self._update_drag_hover_label(event)

    def _on_cell_release(self, event, img_dict: dict, cell: tk.Frame, side: str):
        was_drag = self._drag_window is not None
        if self._drag_window is not None:
            self._drag_window.destroy()
            self._drag_window = None
        self._press_pos = None

        if was_drag:
            self._execute_drop(event)
        elif self._double_click_pending:
            self._double_click_pending = False   # swallow the spurious 2nd release
        else:
            self._toggle_side_selection(img_dict.get("id"), cell, side)

    def _on_cell_double(self, img_dict: dict):
        """Open the photo editor dialog on double-click."""
        self._double_click_pending = True
        self._open_editor_dialog(img_dict)

    def _start_drag(self, event, img_dict: dict, side: str):
        self._drag_is_copy = self._ctrl_held
        image_id = img_dict.get("id")
        if side == 'left':
            sel_ids = self._source_panel.selected_ids
            images   = self._source_panel.album_images
            cache    = self._source_panel.thumb_cache
        else:
            sel_ids = self._target_panel.selected_ids
            images   = self._target_panel.album_images
            cache    = self._target_panel.thumb_cache

        if image_id in sel_ids:
            self._drag_batch = [d for d in images if d.get("id") in sel_ids]
        else:
            self._drag_batch = [img_dict]

        pil = cache.get(image_id)
        if pil and PIL_AVAILABLE:
            preview = pil.copy()
            preview.thumbnail((80, 80), Image.Resampling.LANCZOS)
            self._drag_tk_ref = ImageTk.PhotoImage(preview)
        else:
            self._drag_tk_ref = None
        win = tk.Toplevel(self.root)
        win.wm_overrideredirect(True)
        win.attributes("-alpha", 0.75)
        win.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
        tk.Label(win, image=self._drag_tk_ref if self._drag_tk_ref else None,
                 text="" if self._drag_tk_ref else "\u2b06",
                 bg="#add8e6", relief="solid", borderwidth=1).pack()
        n = len(self._drag_batch)
        label_text = "COPY" if self._drag_is_copy else "MOVE"
        if n > 1:
            label_text += f"  \u00d7{n}"
        tk.Label(win, text=label_text, bg="#add8e6",
                 font=("TkDefaultFont", 8, "bold")).pack()
        self._drag_hover_label = tk.Label(win, text="", bg="#fffacd",
                                          font=("TkDefaultFont", 8, "italic"),
                                          padx=4, pady=2)
        # Packed/unpacked dynamically as cursor moves over tree nodes
        self._drag_window = win

    def _execute_drop(self, event):
        """Called after drag ends; detects destination and executes immediately."""
        if not self._drag_batch:
            return

        src_side     = self._drag_source_side
        src_album_id = (self.current_album_id if src_side == 'left'
                        else self.target_album_id)
        op = 'copy' if self._drag_is_copy else 'move'

        # ── Drop on a hierarchy tree node ────────────────────────────────────
        tree_hit = self._hit_tree_node(event)
        if tree_hit is not None:
            dst_album_id, dst_album_name, dst_side = tree_hit
            if src_album_id is not None and dst_album_id == src_album_id:
                self._drag_batch = []
                return
            # Update the destination panel's selected album so the reload
            # after the operation shows the right content.
            if dst_side == 'right':
                self.target_album_id   = dst_album_id
                self.target_album_name = dst_album_name
                self.target_album_var.set(dst_album_name)
            else:
                self.current_album_id   = dst_album_id
                self.current_album_name = dst_album_name
                self.album_var.set(dst_album_name)
            batch = list(self._drag_batch)
            self._drag_batch = []
            self._execute_move_copy(batch, op, src_side, src_album_id, dst_album_id)
            return

        # ── Drop on a thumbnail grid ──────────────────────────────────────────
        widget_under = self.root.winfo_containing(event.x_root, event.y_root)
        dst_side = self._widget_side(widget_under)

        if dst_side is None or dst_side == src_side:
            self._drag_batch = []
            return

        if src_side == 'left':
            dst_album_id = self.target_album_id
            dst_images   = self._target_panel.album_images
        else:
            dst_album_id = self.current_album_id
            dst_images   = self._source_panel.album_images

        if dst_album_id is None:
            self._drag_batch = []
            self._show_over_target(
                "No Album Selected",
                "Please select an album on the destination side before moving or copying.")
            return

        dst_ids = {d.get("id") for d in dst_images}
        already    = [d for d in self._drag_batch if d.get("id") in dst_ids]
        to_process = [d for d in self._drag_batch if d.get("id") not in dst_ids]

        if already:
            names = "\n  ".join(
                d.get("file") or d.get("name") or str(d.get("id")) for d in already)
            self._show_over_target(
                "Already in Destination Album",
                f"{len(already)} photo(s) already exist in the destination "
                f"and were skipped:\n\n  {names}")

        self._drag_batch = []
        if not to_process:
            return

        self._execute_move_copy(to_process, op, src_side, src_album_id, dst_album_id)

    def _on_grid_drop(self, event, side: str):
        """ButtonRelease-1 on empty canvas area — clear selection for that side."""
        self._clear_side_selection(side)

    # -----------------------------------------------------------------------
    # Selection helpers (symmetric for both sides)
    # -----------------------------------------------------------------------
    def _toggle_side_selection(self, image_id, cell: tk.Frame, side: str):
        ids = self._source_panel.selected_ids if side == 'left' else self._target_panel.selected_ids
        if image_id in ids:
            ids.discard(image_id)
            self._apply_cell_bg(cell, selected=False)
        else:
            ids.add(image_id)
            self._apply_cell_bg(cell, selected=True)
        total = len(self._source_panel.selected_ids) + len(self._target_panel.selected_ids)
        self.set_status(f"{total} photo{'s' if total != 1 else ''} selected" if total else "Ready")

    def _apply_cell_bg(self, cell: tk.Frame, selected: bool):
        bg = "#1a6b9a" if selected else "#3a3a3a"
        fg = "#ffffff"  if selected else "#dddddd"
        try:
            for child in cell.winfo_children():
                child.configure(bg=bg)
                if isinstance(child, tk.Label) and child.cget("fg") in ("#dddddd", "#ffffff"):
                    child.configure(fg=fg)
            cell.configure(bg=bg, relief="sunken" if selected else "flat")
        except Exception:
            pass

    def _clear_side_selection(self, side: str):
        if side == 'left':
            for iid in list(self._source_panel.selected_ids):
                cell = self._source_panel.cell_by_id.get(iid)
                if cell:
                    self._apply_cell_bg(cell, selected=False)
            self._source_panel.selected_ids.clear()
        else:
            for iid in list(self._target_panel.selected_ids):
                cell = self._target_panel.cell_by_id.get(iid)
                if cell:
                    self._apply_cell_bg(cell, selected=False)
            self._target_panel.selected_ids.clear()

    def _clear_selection(self):
        self._clear_side_selection('left')
        self._clear_side_selection('right')

    def _show_over_target(self, title: str, message: str):
        """Show a warning dialog centred over the Target Album panel."""
        self.root.update_idletasks()
        tx = self._target_panel.frame.winfo_rootx()
        ty = self._target_panel.frame.winfo_rooty()
        tw = self._target_panel.frame.winfo_width()
        th = self._target_panel.frame.winfo_height()

        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.resizable(False, False)
        dlg.grab_set()

        tk.Label(dlg, text=message, wraplength=320,
                 justify="left", padx=16, pady=12).pack()
        ttk.Button(dlg, text="OK", command=dlg.destroy).pack(pady=(0, 10))

        dlg.update_idletasks()
        dw = dlg.winfo_reqwidth()
        dh = dlg.winfo_reqheight()
        x = tx + (tw - dw) // 2
        y = ty + (th - dh) // 2
        dlg.geometry(f"{dw}x{dh}+{x}+{y}")
        dlg.wait_window()

    def _widget_side(self, widget) -> str | None:
        """Return 'left', 'right', or None depending on which panel widget belongs to."""
        if widget is None:
            return None
        w = widget
        while w is not None:
            if w == self._target_panel.frame:
                return 'right'
            if w == self._source_panel.frame:
                return 'left'
            try:
                w = w.master
            except Exception:
                break
        return None

    def _update_drag_hover_label(self, event):
        """Show/hide an album-name label in the drag window based on cursor position."""
        lbl = getattr(self, '_drag_hover_label', None)
        if lbl is None:
            return
        hit = self._hit_tree_node(event)
        if hit is not None:
            _, fullname, _ = hit
            short_name = fullname.rsplit(" / ", 1)[-1]
            lbl.config(text=f"\u27a1 {short_name}")
            lbl.pack(fill="x")
        else:
            lbl.pack_forget()
        # Force the window to resize around the (possibly shown/hidden) label
        if self._drag_window:
            self._drag_window.update_idletasks()

    def _hit_tree_node(self, event) -> tuple | None:
        """Return (album_id, fullname, side) if the event lands on a tree row, else None."""
        widget = self.root.winfo_containing(event.x_root, event.y_root)
        if widget is self._source_panel.tree:
            tree = self._source_panel.tree
            side = 'left'
            fullname_map = self._source_panel.tree_fullname_by_iid
        elif widget is self._target_panel.tree:
            tree = self._target_panel.tree
            side = 'right'
            fullname_map = self._target_panel.tree_fullname_by_iid
        else:
            return None
        y = event.y_root - tree.winfo_rooty()
        iid = tree.identify_row(y)
        if not iid:
            return None
        return int(iid), fullname_map.get(iid, iid), side

    # -----------------------------------------------------------------------
    # Immediate move/copy execution
    # -----------------------------------------------------------------------
    def _execute_move_copy(self, batch: list, op: str,
                           src_side: str, src_album_id: int, dst_album_id: int):
        """Execute copy or move for all items in batch immediately in a background thread."""
        total = len(batch)

        verb = 'Moving' if op == 'move' else 'Copying'
        set_stage, advance, close_dlg = self._make_progress_dialog(
            title=f"{verb} Photos",
            heading=f"{verb} {total} photo(s)…",
            total=max(total, 1))

        def worker():
            errors    = []
            n_ok      = 0
            undo_items = []   # {image_id, name, original_cats}
            try:
                params = DownloadAlbumStructure.load_params()
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=params.get("verify_ssl", True),
                    rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])

                for i, d in enumerate(batch):
                    image_id = d.get("id")
                    name = d.get("file") or d.get("name") or str(image_id)
                    set_stage(f"{'Moving' if op == 'move' else 'Copying'}: {name}")
                    try:
                        info = client.get_image_info(image_id)
                        original_cats = [int(c["id"]) for c in info.get("categories", [])]
                        if op == 'copy':
                            if dst_album_id not in original_cats:
                                client.set_image_categories(
                                    image_id, original_cats + [dst_album_id])
                        else:
                            new_cats = [c for c in original_cats if c != src_album_id]
                            if dst_album_id not in new_cats:
                                new_cats.append(dst_album_id)
                            if new_cats != original_cats:
                                client.set_image_categories(image_id, new_cats)
                        undo_items.append({'image_id': image_id, 'name': name,
                                           'original_cats': original_cats})
                        n_ok += 1
                    except Exception as e:
                        errors.append(f"{name}: {e}")
                    advance(i + 1)

                client.logout()
            except Exception as e:
                errors.append(f"Connection error: {e}")

            def finish():
                close_dlg()
                if errors:
                    messagebox.showerror(
                        "Move/Copy Errors", "\n".join(errors), parent=self.root)
                if undo_items:
                    self._move_undo_stack.append({
                        'description': f"{op.capitalize()} {len(undo_items)} photo(s)",
                        'items': undo_items,
                    })
                self.set_status(
                    f"{op.capitalize()} complete: {n_ok} ok"
                    + (f", {len(errors)} error(s)" if errors else ".")
                    + ("  (Ctrl+Z to undo)" if undo_items else ""))
                self._load_album_photos()
                if self.target_album_id is not None:
                    self._load_target_album_photos()

            self.root.after(0, finish)

        threading.Thread(target=worker, daemon=True).start()

    # -----------------------------------------------------------------------
    # Undo last drag-and-drop operation
    # -----------------------------------------------------------------------
    def _undo_drag_drop(self, _event=None):
        if not self._move_undo_stack:
            self.set_status("Nothing to undo.")
            return
        record = self._move_undo_stack.pop()
        items  = record['items']
        desc   = record['description']
        total  = len(items)

        set_stage, advance, close_dlg = self._make_progress_dialog(
            title="Undoing…",
            heading=f"Undoing: {desc}",
            total=max(total, 1))

        def worker():
            errors = []
            n_ok   = 0
            try:
                params = DownloadAlbumStructure.load_params()
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=params.get("verify_ssl", True),
                    rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])
                for i, item in enumerate(items):
                    set_stage(f"Restoring: {item['name']}")
                    try:
                        client.set_image_categories(
                            item['image_id'], item['original_cats'])
                        n_ok += 1
                    except Exception as e:
                        errors.append(f"{item['name']}: {e}")
                    advance(i + 1)
                client.logout()
            except Exception as e:
                errors.append(f"Connection error: {e}")

            def finish():
                close_dlg()
                if errors:
                    messagebox.showerror("Undo Errors", "\n".join(errors), parent=self.root)
                self.set_status(
                    f"Undone: {desc} — {n_ok} restored"
                    + (f", {len(errors)} error(s)" if errors else "."))
                self._load_album_photos()
                if self.target_album_id is not None:
                    self._load_target_album_photos()

            self.root.after(0, finish)

        threading.Thread(target=worker, daemon=True).start()

    # -----------------------------------------------------------------------
    # Remove from album (RMB handler — both sides)
    # -----------------------------------------------------------------------
    def _remove_selection_from_album(self, side: str):
        """Remove all selected images on `side` from their album."""
        if side == 'left':
            ids    = set(self._source_panel.selected_ids)
            images = self._source_panel.album_images
        else:
            ids    = set(self._target_panel.selected_ids)
            images = self._target_panel.album_images
        if not ids:
            return
        batch = [d for d in images if d.get("id") in ids]
        # Defer so the menu can dismiss first
        self.root.after(50, lambda: self._remove_selection_confirm(batch, side))

    def _remove_selection_confirm(self, batch: list, side: str):
        album_name = self.current_album_name if side == 'left' else self.target_album_name
        album_id   = self.current_album_id   if side == 'left' else self.target_album_id
        n = len(batch)
        if not messagebox.askyesno(
                "Remove from Album",
                f'Remove {n} photo(s) from "{album_name}"?\n\n'
                "This only removes the album association — photos remain in Piwigo.",
                parent=self.root):
            return

        def worker():
            errors = []
            try:
                params = DownloadAlbumStructure.load_params()
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=params.get("verify_ssl", True),
                    rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])
                for d in batch:
                    iid  = d.get("id")
                    name = d.get("file") or d.get("name") or str(iid)
                    try:
                        info = client.get_image_info(iid)
                        current_cats = [int(c["id"]) for c in info.get("categories", [])]
                        new_cats = [c for c in current_cats if c != album_id]
                        if new_cats != current_cats:
                            client.set_image_categories(iid, new_cats)
                        self.root.after(0, lambda i=iid, nm=name: self._after_remove(i, nm, side))
                    except Exception as e:
                        errors.append(f"{name}: {e}")
                client.logout()
            except Exception as e:
                errors.append(f"Connection error: {e}")
            if errors:
                self.root.after(0, lambda: messagebox.showerror(
                    "Remove Errors", "\n".join(errors), parent=self.root))

        self.set_status(f"Removing {n} photo(s)…")
        threading.Thread(target=worker, daemon=True).start()

    def _remove_from_album(self, image_id: int, img_dict: dict, side: str):
        # Defer so the RMB menu can fully dismiss before the dialog appears.
        self.root.after(50, lambda: self._remove_from_album_confirm(image_id, img_dict, side))

    def _remove_from_album_confirm(self, image_id: int, img_dict: dict, side: str):
        album_id   = self.current_album_id   if side == 'left' else self.target_album_id
        album_name = self.current_album_name if side == 'left' else self.target_album_name
        name = img_dict.get("file") or img_dict.get("name") or str(image_id)
        if not messagebox.askyesno(
                "Remove from Album",
                f'Remove "{name}" from "{album_name}"?\n\n'
                "This only removes the album association — the photo remains in Piwigo.",
                parent=self.root):
            return

        def worker():
            try:
                params = DownloadAlbumStructure.load_params()
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=params.get("verify_ssl", True),
                    rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])
                info = client.get_image_info(image_id)
                current_cats = [int(c["id"]) for c in info.get("categories", [])]
                new_cats = [c for c in current_cats if c != album_id]
                if new_cats != current_cats:
                    client.set_image_categories(image_id, new_cats)
                client.logout()
                self.root.after(0, lambda: self._after_remove(image_id, name, side))
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror(
                    "Remove Failed", str(e), parent=self.root))

        self.set_status(f'Removing "{name}"…')
        threading.Thread(target=worker, daemon=True).start()

    def _after_remove(self, image_id: int, name: str, side: str):
        panel = self._source_panel if side == 'left' else self._target_panel
        cell = panel.cell_by_id.pop(image_id, None)
        if cell:
            panel.thumb_cells = [c for c in panel.thumb_cells if c != cell]
            cell.destroy()
        panel.selected_ids.discard(image_id)
        panel.album_images = [d for d in panel.album_images if d.get("id") != image_id]
        panel.reflow()
        self.set_status(f'Removed "{name}" from album.')

    # -----------------------------------------------------------------------
    # Thumbnail click → load photo in editor
    # -----------------------------------------------------------------------
    def _on_thumb_click(self, img_dict: dict):
        self._save_current_custom_fields()
        name = img_dict.get("name") or img_dict.get("file") or "unknown"
        url  = _pick_derivative_url(img_dict,
                                    (VIEWER_FETCH_SIZE, "large", "small",
                                     "2small", "thumb"))
        if not url:
            url = img_dict.get("element_url", "")
        if not url:
            self.set_status("No URL available for this photo.")
            return
        self.photo_label_var.set(name)
        self.photo_dim_var.set("")
        self.url_var.set(url)
        self.set_status(f"Loading \"{name}\"…")
        threading.Thread(
            target=self._worker_fetch_full,
            args=(url, img_dict),
            daemon=True).start()

    def _worker_fetch_full(self, url: str, img_dict: dict):
        if not PIL_AVAILABLE or not REQUESTS_AVAILABLE:
            return
        try:
            params = DownloadAlbumStructure.load_params()
            verify = params.get("verify_ssl", True)

            # Fetch full image metadata (includes author, tags, etc.)
            rich_dict = dict(img_dict)
            try:
                client = DownloadAlbumStructure.PiwigoClient(
                    params["url"], params["username"], params["password"],
                    verify_ssl=verify,
                    rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
                client.login(params["username"], params["password"])
                info = client.get_image_info(img_dict["id"])
                client.logout()
                rich_dict.update(info)
            except Exception as e:
                logger.warning(f"Could not fetch full image info for {img_dict.get('id')}: {e}")

            with warnings.catch_warnings():
                if not verify:
                    warnings.simplefilter("ignore", urllib3.exceptions.InsecureRequestWarning)
                resp = requests.get(url, verify=verify, timeout=30)
                resp.raise_for_status()
            pil = Image.open(BytesIO(resp.content))
            pil.load()
            self.root.after(0, lambda: self._on_photo_loaded(pil, rich_dict))
        except Exception as e:
            logger.exception(f"Failed to load {url}")
            self.root.after(0, lambda: self.set_status(
                f"Error loading \"{img_dict.get('name', '')}\": {e}"))

    def _on_photo_loaded(self, pil: "Image.Image", img_dict: dict):
        """Called on the main thread once the full image has been downloaded."""
        name = img_dict.get("name") or img_dict.get("file") or "unknown"
        self._viewer_image       = pil
        self._current_image_dict = img_dict
        self._photo_edited       = False
        self._edit_history.clear()
        self._set_restoration_base()
        self._clear_crop_rect()
        self.photo_label_var.set(name)
        self.photo_dim_var.set(
            f"{pil.width} \u00d7 {pil.height} px  |  {pil.mode}")
        self._display_photo()
        self._exif_data = {}   # reset so previous photo's values don't bleed in
        self._load_iptc_from_image(pil)
        self._load_custom_fields(img_dict.get("id"))
        self._load_piwigo_metadata(img_dict)
        self._validate_date_field()
        self._validate_caption_field()
        self.upload_photo_btn.config(state="normal")
        self.rotate_right_btn.config(state="normal")
        self.rotate_left_btn.config(state="normal")
        self.rotate_180_btn.config(state="normal")
        self.revert_btn.config(state="normal")
        self.set_status(f"Loaded: {name}")

    def _upload_current_photo(self):
        """Upload the current (possibly edited) photo back to Piwigo."""
        if self._viewer_image is None or self._current_image_dict is None:
            self.set_status("No photo loaded.")
            return
        if self.current_album_id is None:
            messagebox.showerror("No Album", "No source album is selected.", parent=self.root)
            return

        img_dict = self._current_image_dict
        image_id = img_dict.get("id")
        fname    = img_dict.get("file") or img_dict.get("name") or f"{image_id}.jpg"

        # Gather metadata from custom fields
        author       = self.custom_vars['photo_source'].get().strip()
        comment      = self.custom_vars['comments'].get('1.0', 'end').strip()
        raw_tags     = self.custom_vars['tags'].get()
        tags         = ', '.join(t for t in (t.strip() for t in raw_tags.split(',')) if t)
        raw_date     = self.custom_vars['date_of_photo'].get().strip()
        date_creation = ''
        if raw_date:
            parsed = self._parse_date(raw_date)
            if parsed:
                date_creation = parsed.strftime('%Y-%m-%d %H:%M:%S')

        # Progress dialog
        set_stage, _advance, close_dlg = self._make_progress_dialog(
            title="Uploading…",
            heading=f"Uploading  {fname}",
            subheading=f"to  \"{self.current_album_name}\"",
            total=0,
            initial_stage="Preparing…",
            grab=True)

        # Snapshot the edited image now, before the thread starts
        pil_snapshot = self._viewer_image.copy()
        album_id     = self.current_album_id
        image_id     = img_dict.get("id")   # None for brand-new uploads

        def worker():
            temp_path = None
            try:
                params = DownloadAlbumStructure.load_params()

                # Save edited PIL image to a temp JPEG
                set_stage("Saving edited image…")
                stem, ext = os.path.splitext(fname)
                suffix = ext if ext.lower() in ('.jpg', '.jpeg') else '.jpg'
                with tempfile.NamedTemporaryFile(suffix=suffix, delete=False) as tf:
                    temp_path = tf.name
                img = pil_snapshot
                if img.mode not in ('RGB', 'L'):
                    img = img.convert('RGB')
                max_pixels = params.get('max_upload_pixels')
                if max_pixels:
                    w, h = img.size
                    if w * h > max_pixels:
                        scale = (max_pixels / (w * h)) ** 0.5
                        img = img.resize(
                            (max(1, int(w * scale)), max(1, int(h * scale))),
                            Image.Resampling.LANCZOS)
                img.save(temp_path, format='JPEG', quality=92)

                client = DownloadAlbumStructure.PiwigoClient(
                    params['url'], params['username'], params['password'],
                    verify_ssl=params.get('verify_ssl', True),
                    rate_limit_calls_per_second=params.get('rate_limit_calls_per_second', 2.0))
                set_stage("Logging in…")
                client.login(params['username'], params['password'])
                set_stage(f"Uploading {fname}…")
                result = client.upload_image(
                    temp_path, album_id,
                    name=fname, author=author, comment=comment,
                    tags=tags, date_creation=date_creation,
                    image_id=image_id)
                new_image_id = int(result.get('image_id', image_id or 0))
                if params.get('sync_metadata', True):
                    set_stage("Syncing metadata…")
                    try:
                        client.sync_metadata(new_image_id)
                    except Exception as e:
                        logger.warning(f"syncMetadata failed (non-fatal): {e}")
                # Re-apply author/comment/date after sync_metadata, which may
                # have overwritten them by re-reading the (un-annotated) file.
                if author or comment or date_creation:
                    set_stage("Setting metadata…")
                    try:
                        client.set_image_metadata(
                            new_image_id,
                            author=author,
                            comment=comment,
                            date_creation=date_creation)
                    except Exception as e:
                        logger.warning(f"set_image_metadata failed (non-fatal): {e}")
                if params.get('refresh_representative', True):
                    set_stage("Refreshing album thumbnail…")
                    try:
                        client.refresh_representative(album_id)
                    except Exception as e:
                        logger.warning(f"refreshRepresentative failed (non-fatal): {e}")
                client.logout()
                set_stage("Done.")

                def finish_ok():
                    close_dlg()
                    self._photo_edited = False
                    self._refresh_current_thumbnail()
                    self.set_status(f"Uploaded: {fname}")
                    self._close_editor_dialog()
                self.root.after(0, finish_ok)

            except Exception as e:
                logger.exception("Upload failed")
                def finish_err(msg=str(e)):
                    close_dlg()
                    messagebox.showerror("Upload Failed", msg, parent=self.root)
                    self.set_status(f"Upload failed: {msg}")
                self.root.after(0, finish_err)
            finally:
                if temp_path:
                    try:
                        Path(temp_path).unlink()
                    except Exception:
                        pass

        threading.Thread(target=worker, daemon=True).start()

    def _refresh_current_thumbnail(self):
        """Regenerate thumbnails in both grids from the current editor image."""
        if self._viewer_image is None or self._current_image_dict is None:
            return
        image_id = self._current_image_dict.get("id")
        if image_id is None:
            return
        pil = self._viewer_image.copy()
        if pil.mode not in ("RGB", "RGBA"):
            pil = pil.convert("RGB")
        pil.thumbnail(self._thumb_size, Image.Resampling.LANCZOS)
        tk_img = ImageTk.PhotoImage(pil)
        self._source_panel.update_thumbnail(image_id, pil, tk_img)
        self._target_panel.update_thumbnail(image_id, pil, tk_img)

    def _revert_photo(self):
        """Reload the current photo from Piwigo, discarding unsaved edits."""
        if self._current_image_dict is None:
            return
        self._on_thumb_click(self._current_image_dict)

    # -----------------------------------------------------------------------
    # Editing tools
    # -----------------------------------------------------------------------
    def _rotate_photo(self, degrees: int):
        """Rotate the viewer image clockwise by degrees (90, -90, or 180)."""
        if self._viewer_image is None:
            return
        self._edit_history.append(self._viewer_image.copy())
        self.undo_btn.config(state="normal")
        img = self._viewer_image
        if img.mode not in ("RGB", "RGBA"):
            img = img.convert("RGB")
        # PIL rotates counter-clockwise, so negate for clockwise behaviour
        self._viewer_image = img.rotate(-degrees, expand=True)
        self._photo_edited = True
        self._set_restoration_base()
        self._clear_crop_rect()
        self._display_photo()
        direction = "right" if degrees == 90 else ("left" if degrees == -90 else "180°")
        self.set_status(f"Rotated {direction}")

    def _undo_edit(self):
        """Revert the last rotate or crop operation."""
        if not self._edit_history:
            return
        self._viewer_image = self._edit_history.pop()
        self._set_restoration_base()
        self._clear_crop_rect()
        self._display_photo()
        if not self._edit_history:
            self.undo_btn.config(state="disabled")
            self._photo_edited = False
        self.set_status("Undo applied.")

    def _on_crop_start(self, event):
        """Begin a crop drag from anywhere on the canvas (start clamped to photo bounds at draw time)."""
        if self._photo_display_rect is None:
            self._crop_start = None
            return
        self._clear_crop_rect()
        self._crop_start = (event.x, event.y)

    def _on_crop_drag(self, event):
        if self._crop_start is None:
            return
        r = self._photo_display_rect
        if r is None:
            return
        px0, py0, px1, py1 = r
        # Clamp both endpoints so the box never extends beyond the photo.
        sx = max(px0, min(self._crop_start[0], px1))
        sy = max(py0, min(self._crop_start[1], py1))
        cx = max(px0, min(event.x, px1))
        cy = max(py0, min(event.y, py1))
        if self._crop_rect_id is not None:
            self.canvas.delete(self._crop_rect_id)
        self._crop_rect_id = self.canvas.create_rectangle(
            sx, sy, cx, cy, outline="red", width=2)

    def _on_crop_release(self, event):
        if self._crop_start is None:
            return
        r = self._photo_display_rect
        if r is None:
            return
        px0, py0, px1, py1 = r
        # Clamp both endpoints to photo bounds.
        sx = max(px0, min(self._crop_start[0], px1))
        sy = max(py0, min(self._crop_start[1], py1))
        cx = max(px0, min(event.x, px1))
        cy = max(py0, min(event.y, py1))
        self._crop_start = None
        # Discard tiny drag (< 4 px in either axis)
        if abs(cx - sx) < 4 or abs(cy - sy) < 4:
            self._clear_crop_rect()
            return
        # Redraw the final, normalised rectangle
        if self._crop_rect_id is not None:
            self.canvas.delete(self._crop_rect_id)
        self._crop_rect_id = self.canvas.create_rectangle(
            min(sx, cx), min(sy, cy), max(sx, cx), max(sy, cy),
            outline="red", width=2)
        self.crop_btn.config(state="normal")
        self.set_status("Crop region selected — click Crop to apply, Esc to cancel.")

    def _clear_crop_rect(self, _event=None):
        """Delete the on-canvas crop rectangle and reset drag state."""
        if self._crop_rect_id is not None:
            self.canvas.delete(self._crop_rect_id)
            self._crop_rect_id = None
        self._crop_start = None
        self.crop_btn.config(state="disabled")

    def _crop_photo(self):
        """Apply the current crop rectangle to the viewer image."""
        if self._viewer_image is None:
            self.set_status("No photo loaded.")
            return
        if self._crop_rect_id is None:
            self.set_status("Drag on the photo to select a crop region first.")
            return
        r = self._photo_display_rect
        if r is None:
            return
        coords = self.canvas.coords(self._crop_rect_id)
        if not coords or len(coords) < 4:
            return
        cx0, cy0, cx1, cy1 = [int(v) for v in coords]
        cx0, cx1 = min(cx0, cx1), max(cx0, cx1)
        cy0, cy1 = min(cy0, cy1), max(cy0, cy1)
        px0, py0, px1, py1 = r
        pw, ph = px1 - px0, py1 - py0
        iw, ih = self._viewer_image.size
        ix0 = max(0, int((cx0 - px0) / pw * iw))
        iy0 = max(0, int((cy0 - py0) / ph * ih))
        ix1 = min(iw, int((cx1 - px0) / pw * iw))
        iy1 = min(ih, int((cy1 - py0) / ph * ih))
        if ix1 <= ix0 or iy1 <= iy0:
            self.set_status("Crop region too small.")
            return
        self._edit_history.append(self._viewer_image.copy())
        self.undo_btn.config(state="normal")
        self._viewer_image = self._viewer_image.crop((ix0, iy0, ix1, iy1))
        self._photo_edited = True
        self._set_restoration_base()
        self._clear_crop_rect()
        self._display_photo()
        self.set_status(f"Cropped to {ix1 - ix0}\u00d7{iy1 - iy0} px")

    # -----------------------------------------------------------------------
    # Photo restoration  (OpenCV)
    # -----------------------------------------------------------------------
    def _on_restoration_change(self, *_):
        """Debounce: wait 120 ms after last slider move before processing."""
        if self._restore_after_id is not None:
            self.root.after_cancel(self._restore_after_id)
        self._restore_after_id = self.root.after(120, self._apply_restoration_bg)

    def _apply_restoration_bg(self):
        """Kick off restoration in a background thread."""
        self._restore_after_id = None
        if not CV2_AVAILABLE or self._restoration_base is None:
            if not CV2_AVAILABLE:
                self.set_status("opencv-python not installed — pip install opencv-python")
            return
        self._restore_generation += 1
        gen = self._restore_generation
        exposure = self._restore_exposure_var.get()
        contrast = self._restore_contrast_var.get()
        red_cast = self._restore_red_var.get()
        sharpen  = self._restore_sharpen_var.get()
        base     = self._restoration_base.copy()

        def worker():
            result = _opencv_restore(base, exposure, contrast, red_cast, sharpen)
            self.root.after(0, lambda: self._apply_restoration_result(result, gen))

        threading.Thread(target=worker, daemon=True).start()

    def _apply_restoration_result(self, result: "Image.Image", gen: int):
        """Called on main thread when the background worker finishes."""
        if gen != self._restore_generation:
            return   # stale — a newer slider move is already in flight
        self._viewer_image = result
        self._photo_edited = True
        self._display_photo()

    def _reset_restoration(self):
        """Reset all restoration sliders and restore the base image."""
        if self._restore_after_id is not None:
            self.root.after_cancel(self._restore_after_id)
            self._restore_after_id = None
        self._restore_generation += 1   # cancel any in-flight worker
        self._restore_exposure_var.set(0.0)
        self._restore_contrast_var.set(0.0)
        self._restore_red_var.set(0.0)
        self._restore_sharpen_var.set(0.0)
        for lbl, vv in self._restore_val_vars.items():
            vv.set("0")
        if self._restoration_base is not None:
            self._viewer_image = self._restoration_base.copy()
            self._display_photo()
        self.set_status("Restoration reverted.")

    def _set_restoration_base(self):
        """Snapshot the current viewer image as the new restoration baseline
        and reset all sliders.  Call this after any geometric edit or on load."""
        if self._restore_after_id is not None:
            self.root.after_cancel(self._restore_after_id)
            self._restore_after_id = None
        self._restore_generation += 1
        self._restore_exposure_var.set(0.0)
        self._restore_contrast_var.set(0.0)
        self._restore_red_var.set(0.0)
        self._restore_sharpen_var.set(0.0)
        for vv in self._restore_val_vars.values():
            vv.set("0")
        if self._viewer_image is not None:
            self._restoration_base = self._viewer_image.copy()

    # -----------------------------------------------------------------------
    # Photo viewer (mirrors PhotosUploader._display_photo / _on_canvas_resize)
    # -----------------------------------------------------------------------
    def _display_photo(self):
        if self._viewer_image is None:
            return
        if not PIL_AVAILABLE:
            self.canvas.delete("all")
            self.canvas.create_text(10, 10, anchor="nw",
                                    text="Pillow not installed", fill="white")
            return
        try:
            cw = max(self.canvas.winfo_width(),  100)
            ch = max(self.canvas.winfo_height(), 100)
            iw, ih = self._viewer_image.size
            scale = min(cw / iw, ch / ih, 1.0)
            tw = max(1, int(iw * scale))
            th = max(1, int(ih * scale))
            thumb = self._viewer_image.resize((tw, th), Image.Resampling.LANCZOS)
            self._viewer_tk = ImageTk.PhotoImage(thumb)
            self.canvas.delete("all")
            ix = cw // 2 - tw // 2
            iy = ch // 2 - th // 2
            self._photo_display_rect = (ix, iy, ix + tw, iy + th)
            self.canvas.create_image(cw // 2, ch // 2,
                                     anchor="center", image=self._viewer_tk)
        except Exception as e:
            self.canvas.delete("all")
            self.canvas.create_text(10, 10, anchor="nw",
                                    text=f"Cannot display image:\n{e}",
                                    fill="red", font=("TkDefaultFont", 10))

    def _on_canvas_resize(self, _event=None):
        if self._viewer_image is not None:
            self._display_photo()

    def _open_caption_editor(self, _event=None):
        """Ctrl+Click on canvas — popup with larger image + editable caption."""
        if self._viewer_image is None or not PIL_AVAILABLE:
            return
        if self._caption_editor_open:
            return
        self._caption_editor_open = True

        parent = self._editor_dlg if (self._editor_dlg and
                                       self._editor_dlg.winfo_exists()) else self.root
        win = tk.Toplevel(parent)
        name = (self._current_image_dict or {}).get("name") or \
               (self._current_image_dict or {}).get("file", "")
        win.title("Caption Editor")
        win.resizable(True, True)
        win.transient(parent)
        win.lift()

        # Selectable filename heading
        heading_var = tk.StringVar(value=name)
        tk.Entry(win, textvariable=heading_var, state="readonly",
                 readonlybackground=win.cget("bg"),
                 relief="flat", font=("TkDefaultFont", 10, "bold"),
                 justify="center").pack(fill="x", padx=8, pady=(8, 2))

        # Photo canvas
        photo_canvas = tk.Canvas(win, bg="#1a1a1a", cursor="hand2")
        photo_canvas.pack(fill="both", expand=True, padx=8, pady=(2, 4))
        _popup_img_ref = [None]

        def _render_popup(event=None):
            if self._viewer_image is None:
                return
            cw = max(photo_canvas.winfo_width(),  100)
            ch = max(photo_canvas.winfo_height(), 100)
            iw, ih = self._viewer_image.size
            scale = min(cw / iw, ch / ih, 1.0)
            tw = max(1, int(iw * scale))
            th = max(1, int(ih * scale))
            thumb = self._viewer_image.resize((tw, th), Image.Resampling.LANCZOS)
            _popup_img_ref[0] = ImageTk.PhotoImage(thumb)
            photo_canvas.delete("all")
            photo_canvas.create_image(cw // 2, ch // 2, anchor="center",
                                      image=_popup_img_ref[0])

        photo_canvas.bind("<Configure>", _render_popup)

        # Caption field
        ttk.Label(win, text="Caption:").pack(anchor="w", padx=8)
        caption_txt = tk.Text(win, height=4, wrap="word")
        caption_txt.pack(fill="x", padx=8, pady=(0, 4))
        caption_txt.insert("1.0",
                           self.custom_vars["comments"].get("1.0", "end").strip())

        def _commit_and_close(_event=None):
            new_caption = caption_txt.get("1.0", "end").strip()
            w = self.custom_vars["comments"]
            w.delete("1.0", "end")
            if new_caption:
                w.insert("1.0", new_caption)
            w.edit_modified(True)
            self._caption_editor_open = False
            win.destroy()

        # Click on photo or close window to commit
        photo_canvas.bind("<Button-1>", _commit_and_close)
        win.protocol("WM_DELETE_WINDOW", _commit_and_close)
        # Safety net: if win is destroyed from outside (e.g. parent closes),
        # ensure the flag is always cleared so the editor can reopen.
        win.bind("<Destroy>",
                 lambda e: setattr(self, '_caption_editor_open', False)
                 if e.widget is win else None)

        # Size to 75% of the editor dialog, centred over it
        parent.update_idletasks()
        rw = parent.winfo_width()
        rh = parent.winfo_height()
        rx = parent.winfo_rootx()
        ry = parent.winfo_rooty()
        pw = max(500, int(rw * 0.75))
        ph = max(400, int(rh * 0.75))
        win.minsize(300, 250)
        win.geometry(f"{pw}x{ph}+{rx + (rw - pw) // 2}+{ry + (rh - ph) // 2}")

    # -----------------------------------------------------------------------
    # Custom fields (mirrors PhotosUploader)
    # -----------------------------------------------------------------------
    def _register_field_link(self, custom_key: str, exif_key: str | None,
                              iptc_tag: tuple, validate_fn=None):
        """Register a link between a custom StringVar, an EXIF key, and an IPTC tag.
        Changes to the custom field propagate into _exif_data (used by _load_iptc).
        """
        link = {
            'custom_key':  custom_key,
            'exif_key':    exif_key,
            'iptc_tag':    iptc_tag,
            'validate_fn': validate_fn,
            'syncing':     False,
        }
        self._field_links.append(link)

        def _on_custom_changed(*_):
            if link['syncing']:
                return
            value = self.custom_vars[custom_key].get().strip()
            if value and validate_fn is not None and not validate_fn(value):
                return
            link['syncing'] = True
            try:
                if exif_key is not None:
                    self._exif_data[exif_key] = value
            finally:
                link['syncing'] = False

        self.custom_vars[custom_key].trace_add('write', _on_custom_changed)

    def _load_iptc_from_image(self, pil_image: "Image.Image"):
        """Read IPTC from an already-loaded PIL Image and populate custom fields."""
        if not PIL_AVAILABLE:
            return
        iptc = {}
        try:
            iptc = IptcImagePlugin.getiptcinfo(pil_image) or {}
        except Exception as e:
            logger.debug(f"Could not read IPTC: {e}")

        for link in self._field_links:
            raw = iptc.get(link['iptc_tag'], b'')
            if isinstance(raw, list):
                parts = [bytes(r).decode('utf-8', errors='replace').replace(',', '').strip()
                         for r in raw if r]
                value = ', '.join(p for p in parts if p)
            else:
                value = bytes(raw).decode('utf-8', errors='replace').strip() if raw else ''

            if not value and link['exif_key'] is not None:
                value = self._exif_data.get(link['exif_key'], '')

            if link['exif_key'] is not None:
                self._exif_data[link['exif_key']] = value

            persist_var = self.persist_vars.get(link['custom_key'])
            if persist_var and persist_var.get():
                continue

            link['syncing'] = True
            try:
                self.custom_vars[link['custom_key']].set(value)
            finally:
                link['syncing'] = False

    def _load_piwigo_metadata(self, img_dict: dict):
        """Populate custom fields from Piwigo API metadata, but only for fields
        that _load_iptc_from_image left empty.  IPTC embedded in the file wins."""

        def _set_if_empty(custom_key: str, value: str):
            if not value:
                return
            widget = self.custom_vars.get(custom_key)
            if widget is None:
                return
            persist_var = self.persist_vars.get(custom_key)
            if persist_var and persist_var.get():
                return
            if isinstance(widget, tk.Text):
                if not widget.get('1.0', 'end').strip():
                    widget.delete('1.0', 'end')
                    widget.insert('1.0', value)
            else:
                if not widget.get().strip():
                    widget.set(value)

        # Caption / comment
        _set_if_empty('comments', (img_dict.get("comment") or "").strip())

        # Photographer / source — Piwigo stores this as 'author'
        author = (img_dict.get("author") or
                  img_dict.get("author_name") or
                  img_dict.get("img_author") or "").strip()
        _set_if_empty('photo_source', author)

        # Date — Piwigo returns date_creation as 'YYYY-MM-DD HH:MM:SS' or 'YYYY-MM-DD'
        raw_date = (img_dict.get("date_creation") or "").strip()
        if raw_date:
            # Normalise to YYYY:MM:DD so _parse_date and _validate_date_field handle it
            normalised = raw_date.replace("-", ":", 2).split(" ")[0]  # YYYY:MM:DD
            _set_if_empty('date_of_photo', normalised)

        # Tags — Piwigo returns a list of tag dicts with 'name' keys
        raw_tags = img_dict.get("tags", [])
        if isinstance(raw_tags, list) and raw_tags:
            tag_str = ", ".join(
                t.get("name", "") for t in raw_tags if t.get("name"))
            _set_if_empty('tags', tag_str)

    def _load_custom_fields(self, image_id):
        """Populate custom fields from saved data (image_id key), falling back
        to whatever _load_iptc_from_image already wrote."""
        iptc_keys = {link['custom_key'] for link in self._field_links}
        data = self.custom_data.get(image_id)

        for key, widget in self.custom_vars.items():
            if self.persist_vars[key].get():
                continue
            if data is None:
                # No saved data: clear fields that have no IPTC source
                if key not in iptc_keys:
                    if isinstance(widget, tk.Text):
                        widget.delete('1.0', "end")
                    else:
                        widget.set('')
                continue
            val = data.get(key, '')
            if isinstance(widget, tk.Text):
                widget.delete('1.0', "end")
                widget.insert('1.0', val)
            else:
                widget.set(val)

    def _save_current_custom_fields(self):
        if self._current_image_dict is None:
            return
        image_id = self._current_image_dict.get("id")
        data = {}
        for key, widget in self.custom_vars.items():
            if isinstance(widget, tk.Text):
                data[key] = widget.get('1.0', "end").strip()
            else:
                data[key] = widget.get()
        self.custom_data[image_id] = data

    def _clear_editor(self):
        self._viewer_image       = None
        self._viewer_tk          = None
        self._current_image_dict = None
        self._exif_data          = {}
        self.photo_label_var.set("No photo selected")
        self.photo_dim_var.set("")
        self.url_var.set("")
        self.canvas.delete("all")
        self.upload_photo_btn.config(state="disabled")
        self.rotate_right_btn.config(state="disabled")
        self.rotate_left_btn.config(state="disabled")
        self.rotate_180_btn.config(state="disabled")
        self.undo_btn.config(state="disabled")
        self.revert_btn.config(state="disabled")
        self._edit_history.clear()
        self._clear_crop_rect()
        for widget in self.custom_vars.values():
            if isinstance(widget, tk.Text):
                widget.delete('1.0', "end")
            else:
                widget.set('')
        self._validate_caption_field()
        self._validate_date_field()

    # -----------------------------------------------------------------------
    # Field validation (identical to PhotosUploader)
    # -----------------------------------------------------------------------
    def _validate_caption_field(self):
        widget = self.custom_vars['comments']
        # Caption is optional — only mark invalid if it contains whitespace-only text
        # (a non-empty but blank caption is a user mistake; truly empty is fine).
        value  = widget.get('1.0', "end")
        raw    = value.rstrip('\n')          # tk.Text always appends a trailing newline
        valid  = raw == '' or bool(raw.strip())
        self._field_validity['caption'] = valid
        widget.config(bg='pink' if not valid else 'white')

    def _validate_date_field(self):
        text   = self.custom_vars['date_of_photo'].get()
        parsed = self._parse_date(text)
        valid  = (parsed is not None and
                  self._DATE_MIN_YEAR <= parsed.year <= self._DATE_MAX_YEAR)
        self._field_validity['date'] = valid
        self.date_entry.config(bg='pink' if not valid else 'white')

    # -----------------------------------------------------------------------
    # Date parsing (identical to PhotosUploader)
    # -----------------------------------------------------------------------
    @staticmethod
    def _expand_year(yy: int) -> int:
        return (2000 if yy <= PhotosEditor._2DY_CUTOFF else 1900) + yy

    def _parse_date(self, text: str):
        text = re.sub(r'\s+', ' ', text.strip())
        if not text:
            return None

        def yr(s: str) -> int:
            v = int(s)
            return v if len(s) == 4 else self._expand_year(v)

        def make(year: int, month: int, day: int = 1):
            try:
                return datetime(year, month, day)
            except ValueError:
                return None

        for fmt in ('%Y:%m:%d %H:%M:%S', '%Y:%m:%d'):
            try:
                return datetime.strptime(text, fmt)
            except ValueError:
                pass

        m = re.fullmatch(r'(\d{1,2})[/\-](\d{1,2})[/\-](\d{4}|\d{2})', text)
        if m:
            a, b, y = int(m.group(1)), int(m.group(2)), yr(m.group(3))
            return make(y, a, b) or make(y, b, a)

        m = re.fullmatch(r'(\d{1,2})[/\-](\d{4}|\d{2})', text)
        if m:
            return make(yr(m.group(2)), int(m.group(1)))

        m = re.fullmatch(r'(\d{4})', text)
        if m:
            return make(int(m.group(1)), 1)

        m = re.fullmatch(r'(\d{1,2})\s+([A-Za-z]+)\s+(\d{4}|\d{2})', text)
        if m:
            month = self._MONTH_MAP.get(m.group(2).lower())
            if month:
                return make(yr(m.group(3)), month, int(m.group(1)))

        m = re.fullmatch(r'([A-Za-z]+)\s+(\d{1,2}),?\s+(\d{4}|\d{2})', text)
        if m:
            month = self._MONTH_MAP.get(m.group(1).lower())
            if month:
                return make(yr(m.group(3)), month, int(m.group(2)))

        m = re.fullmatch(r'([A-Za-z]+)\s+(\d{4}|\d{2})', text)
        if m:
            month = self._MONTH_MAP.get(m.group(1).lower())
            if month:
                return make(yr(m.group(2)), month)

        return None


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
def main():
    root = tk.Tk()
    PhotosEditor(root)
    root.mainloop()


if __name__ == "__main__":
    try:
        main()
    except Exception as _exc:
        import traceback
        _crash_log = _SCRIPT_DIR / "PhotosEditor Crash.log"
        try:
            with open(_crash_log, "w", encoding="utf-8") as _f:
                traceback.print_exc(file=_f)
        except OSError:
            pass
        try:
            import tkinter as _tk
            import tkinter.messagebox as _mb
            _tk.Tk().withdraw()
            _mb.showerror(
                "Unexpected Error",
                f"PhotosEditor crashed:\n\n{_exc}\n\n"
                f"Details written to:\n{_crash_log}")
        except Exception:
            pass
        sys.exit(1)
