"""
PhotosEditor.py
A GUI application for browsing and editing photos from a Piwigo album.

Left panel  – Scrollable thumbnail grid of photos in the selected album.
Right panel – Photo Editor: full-size display + Custom Fields (no EXIF section),
              modelled closely on the Photo Viewer in PhotosUploader.

Requires: pip install Pillow requests
Shares DownloadAlbumStructure.py with ../PhotosUploader.
"""

import os
import re
import sys
import json
import threading
import logging
import tkinter as tk
from tkinter import ttk, messagebox
from pathlib import Path
from io import BytesIO
from datetime import datetime

try:
    from PIL import Image, ImageTk, IptcImagePlugin
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False
    print("WARNING: Pillow not installed.  Run: pip install Pillow")

try:
    import requests
    import urllib3
    REQUESTS_AVAILABLE = True
except ImportError:
    REQUESTS_AVAILABLE = False
    print("WARNING: requests not installed.  Run: pip install requests")

# ---------------------------------------------------------------------------
# Locate and import the shared DownloadAlbumStructure module
# ---------------------------------------------------------------------------
_SCRIPT_DIR   = Path(__file__).resolve().parent
_UPLOADER_DIR = _SCRIPT_DIR.parent / "PhotosUploader"

if str(_UPLOADER_DIR) not in sys.path:
    sys.path.insert(0, str(_UPLOADER_DIR))

try:
    import DownloadAlbumStructure
    # Override the params-file path so it resolves relative to PhotosUploader,
    # not the current working directory.
    DownloadAlbumStructure.PARAMS_FILE = _UPLOADER_DIR / "PhotosUploader Params.json"
except ImportError as _e:
    sys.exit(f"Cannot import DownloadAlbumStructure from {_UPLOADER_DIR}:\n{_e}")

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("PhotosEditor")

# ---------------------------------------------------------------------------
# Constants (mirrored from PhotosUploader)
# ---------------------------------------------------------------------------
IMAGE_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tiff',
                    '.tif', '.webp', '.heic', '.heif'}

CUSTOM_FIELDS = [
    ('output_filename', 'Filename'),
    ('photo_source',    'Photographer/Source'),
    ('date_of_photo',   'Date of Photo'),
    ('comments',        'Caption'),
    ('tags',            'Tags (comma-separated)'),
]

THUMB_DISPLAY_SIZE = (144, 144)   # fallback; overridden at runtime to 1.5 in
VIEWER_FETCH_SIZE  = "medium"        # Piwigo derivative used in the editor canvas
STATE_FILE         = _SCRIPT_DIR / "PhotosEditor State.json"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
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
    """Hover tooltip for one or more tkinter widgets."""

    def __init__(self, text_fn):
        """text_fn() -> str  called just before the tip is shown."""
        self._text_fn  = text_fn
        self._tip      = None
        self._after_id = None
        self._widgets  = []

    def attach(self, widget):
        self._widgets.append(widget)
        widget.bind("<Enter>",       self._schedule, add="+")
        widget.bind("<Leave>",       self._cancel_and_hide, add="+")
        widget.bind("<ButtonPress>", self._cancel_and_hide, add="+")

    def _schedule(self, _event=None):
        self._cancel()
        w = self._widgets[0] if self._widgets else None
        if w:
            self._after_id = w.after(500, self._show)

    def _cancel(self):
        if self._after_id and self._widgets:
            self._widgets[0].after_cancel(self._after_id)
            self._after_id = None

    def _cancel_and_hide(self, _event=None):
        self._cancel()
        if self._tip:
            self._tip.destroy()
            self._tip = None

    def _show(self):
        text = self._text_fn()
        if not text:
            return
        if self._widgets:
            x, y = self._widgets[0].winfo_pointerxy()
        else:
            return
        self._tip = tk.Toplevel(self._widgets[0])
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
# Main application
# ---------------------------------------------------------------------------
class PhotosEditor:
    # ── class-level constants (identical to PhotosUploader) ─────────────────
    _ILLEGAL_FILENAME_CHARS: re.Pattern = re.compile(r'[\\/:*?"<>|]')
    _RESERVED_NAMES:         re.Pattern = re.compile(
        r'^(CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(\.[^.]*)?$', re.IGNORECASE)
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

        # ── album / thumbnail state ─────────────────────────────────────────
        self.current_album_id:   int | None = None
        self.current_album_name: str        = ""
        self._album_images:      list[dict] = []
        self._thumb_cache:       dict       = {}   # image_id → PIL Image
        self._thumb_tk:          dict       = {}   # image_id → PhotoImage (GC anchor)
        self._thumb_cells:       list       = []   # ordered cell widgets
        self._thumb_img_labels:  dict       = {}   # image_id → tk.Label showing the thumbnail

        # ── target album state (Photo Move Mode) ────────────────────────────
        self.target_album_id:   int | None = None
        self.target_album_name: str        = ""
        self._target_album_images: list[dict] = []
        self._target_thumb_cache:  dict       = {}
        self._target_thumb_tk:     dict       = {}
        self._target_thumb_cells:  list       = []
        self._mode: str = 'editor'   # 'editor' | 'move'
        self._tree_all_items:       list = []
        self._tree_fullname_by_iid: dict = {}
        self._source_tree_all_items:       list = []
        self._source_tree_fullname_by_iid: dict = {}

        # ── drag-and-drop / selection state ─────────────────────────────────
        self._drag_batch:       list        = []     # list of img_dict being dragged
        self._drag_is_copy:     bool        = False
        self._drag_source_side: str         = 'left' # 'left' | 'right'
        self._drag_window:      tk.Toplevel | None = None
        self._press_pos:        tuple | None = None
        self._selected_ids:     set         = set()  # selected image ids (left grid)
        self._target_selected_ids: set      = set()  # selected image ids (right grid)
        self._cell_by_id:       dict        = {}     # image_id → left cell widget
        self._target_cell_by_id: dict       = {}     # image_id → right cell widget

        # ── editor / viewer state ───────────────────────────────────────────
        self._viewer_image:        Image.Image | None = None
        self._viewer_tk:           ImageTk.PhotoImage | None = None
        self._current_image_dict:  dict | None = None
        self._caption_editor_open: bool  = False
        self._crop_start:          tuple | None = None
        self._crop_rect_id:        int   | None = None
        self._photo_display_rect:  tuple | None = None  # (x0,y0,x1,y1) on canvas
        self._edit_history:        list        = []     # stack of PIL Images for undo

        # ── custom-fields state (mirrors PhotosUploader) ────────────────────
        self.custom_data:    dict = {}   # image_id → {field: value}
        self._field_links:   list = []
        self.persist_vars:   dict = {}
        self._exif_data:     dict = {}   # kept for field-link machinery
        self._field_validity = {'date': False, 'caption': False, 'filename': False}

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

        self._build_ui()
        self._restore_state()
        # Start fields pink (empty = invalid), same as PhotosUploader
        self._validate_caption_field()
        self._validate_date_field()
        self._validate_output_filename_field()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        # Refresh album hierarchy from Piwigo on every startup
        self.root.after(200, self._refresh_hierarchy_on_startup)

    # -----------------------------------------------------------------------
    # UI construction
    # -----------------------------------------------------------------------
    def _build_ui(self):
        # ── toolbar ──────────────────────────────────────────────────────────
        toolbar = ttk.Frame(self.root, padding=(4, 2))
        toolbar.pack(side="top", fill="x")

        self._mode_btn = ttk.Button(toolbar, text="Switch to Photo Move Mode",
                                    command=self._toggle_mode)
        self._mode_btn.pack(side="left", padx=2)
        ttk.Button(toolbar, text="Exit",
                   command=self._on_close).pack(side="right", padx=2)

        # ── main pane ─────────────────────────────────────────────────────────
        self._main_pane = ttk.PanedWindow(self.root, orient="horizontal")
        self._main_pane.pack(side="top", fill="both", expand=True, padx=4, pady=4)

        left_frame = self._build_thumb_panel(self._main_pane)
        self._main_pane.add(left_frame, weight=2)

        right_container = ttk.Frame(self._main_pane)
        self._main_pane.add(right_container, weight=3)

        self._editor_frame = self._build_editor_panel(right_container)
        self._target_frame = self._build_target_panel(right_container)
        self._editor_frame.pack(fill="both", expand=True)

        # ── status bar ───────────────────────────────────────────────────────
        status_bar = ttk.Frame(self.root, relief="sunken")
        status_bar.pack(side="bottom", fill="x")
        ttk.Label(status_bar, textvariable=self.status_var,
                  anchor="w").pack(side="left", padx=6, pady=2)

    # ── left panel: thumbnail browser ───────────────────────────────────────
    def _build_thumb_panel(self, parent) -> ttk.Frame:
        frame = ttk.Frame(parent)
        self._thumb_panel_frame = frame

        # ── Horizontal pane: album tree (left) | thumbnail grid (right) ──────
        hpane = ttk.PanedWindow(frame, orient="horizontal")
        hpane.pack(fill="both", expand=True)
        self._source_hpane = hpane

        # ── Left: album hierarchy tree ────────────────────────────────────────
        tree_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(tree_outer, weight=2)

        filter_frame = ttk.Frame(tree_outer)
        filter_frame.pack(fill="x", pady=(0, 4))
        ttk.Label(filter_frame, text="Filter:").pack(side="left", padx=(0, 4))
        self._source_filter_var = tk.StringVar()
        ttk.Entry(filter_frame, textvariable=self._source_filter_var).pack(
            side="left", fill="x", expand=True)

        tree_frame = ttk.Frame(tree_outer)
        tree_frame.pack(fill="both", expand=True)
        yscroll = ttk.Scrollbar(tree_frame, orient="vertical")
        xscroll = ttk.Scrollbar(tree_frame, orient="horizontal")
        self._source_hierarchy_tree = ttk.Treeview(
            tree_frame, selectmode="browse", show="tree",
            yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        yscroll.config(command=self._source_hierarchy_tree.yview)
        xscroll.config(command=self._source_hierarchy_tree.xview)
        yscroll.pack(side="right", fill="y")
        xscroll.pack(side="bottom", fill="x")
        self._source_hierarchy_tree.pack(side="left", fill="both", expand=True)
        self._source_hierarchy_tree.column("#0", minwidth=200)

        self._source_filter_var.trace_add("write", self._on_source_tree_filter)
        self._source_hierarchy_tree.bind("<<TreeviewSelect>>", self._on_source_hierarchy_select)
        self._source_hierarchy_tree.bind("<Double-1>",         self._on_source_hierarchy_select)

        # ── Right: source album thumbnail grid ────────────────────────────────
        thumb_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(thumb_outer, weight=3)
        self._thumb_grid_frame_label = thumb_outer

        top = ttk.Frame(thumb_outer)
        top.pack(fill="x", pady=(0, 4))
        ttk.Label(top, text="Album:").pack(side="left")
        ttk.Label(top, textvariable=self.album_var,
                  foreground="blue", anchor="w").pack(side="left", padx=(4, 0))
        ttk.Label(top, textvariable=self.thumb_count_var,
                  foreground="gray").pack(side="right", padx=4)

        container = ttk.Frame(thumb_outer)
        container.pack(fill="both", expand=True)

        self._thumb_canvas = tk.Canvas(container, bg="#2a2a2a", highlightthickness=0)
        vscroll2 = ttk.Scrollbar(container, orient="vertical",
                                 command=self._thumb_canvas.yview)
        self._thumb_canvas.configure(yscrollcommand=vscroll2.set)
        vscroll2.pack(side="right", fill="y")
        self._thumb_canvas.pack(side="left", fill="both", expand=True)

        self._grid_frame = tk.Frame(self._thumb_canvas, bg="#2a2a2a")
        self._grid_win = self._thumb_canvas.create_window(
            0, 0, anchor="nw", window=self._grid_frame)

        self._grid_frame.bind("<Configure>",    self._on_grid_resize)
        self._thumb_canvas.bind("<Configure>",  self._on_thumb_canvas_resize)
        self._thumb_canvas.bind("<MouseWheel>", self._on_mousewheel)
        # Drops from right grid onto left grid
        self._thumb_canvas.bind("<ButtonRelease-1>",
                                lambda e: self._on_grid_drop(e, 'left'))

        # Populate tree once the widget is mapped
        frame.bind("<Map>", lambda e: self.root.after(50, self._populate_source_hierarchy_tree), add="+")

        return frame

    # ── right panel: photo editor (mirrors PhotosUploader center panel) ──────
    def _build_editor_panel(self, parent) -> ttk.Frame:
        frame = ttk.Frame(parent)

        # Vertical pane: photo viewer (top) / custom fields (bottom)
        vpane = ttk.PanedWindow(frame, orient="vertical")
        vpane.pack(fill="both", expand=True)
        self._editor_vpane = vpane

        # ── Top pane: Photo display ───────────────────────────────────────────
        viewer_frame = ttk.LabelFrame(vpane, text="Photo Editor", padding=4)
        vpane.add(viewer_frame, weight=13)

        # Left column: photo name, dimensions, source URL
        left_col = ttk.Frame(viewer_frame)
        left_col.pack(side="left", fill="y", padx=(0, 6))

        ttk.Label(left_col, textvariable=self.photo_label_var,
                  font=("TkDefaultFont", 9, "italic"),
                  anchor="w").pack(fill="x", pady=(0, 2))

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

        # Right column: canvas + upload button below it
        right_col = ttk.Frame(viewer_frame)
        right_col.pack(side="left", fill="both", expand=True)

        self.canvas = tk.Canvas(right_col, bg="#1a1a1a", cursor="crosshair",
                                height=200)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>",       self._on_canvas_resize)
        self.canvas.bind("<Control-Button-1>", self._open_caption_editor)
        self.canvas.bind("<Button-1>",         self._on_crop_start)
        self.canvas.bind("<B1-Motion>",        self._on_crop_drag)
        self.canvas.bind("<ButtonRelease-1>",  self._on_crop_release)
        self.canvas.bind("<Escape>",           self._clear_crop_rect)

        btn_row = ttk.Frame(right_col)
        btn_row.pack(pady=(4, 0))

        self.upload_photo_btn = tk.Button(
            btn_row, text="⬆ Upload to Piwigo",
            command=self._upload_current_photo,
            background="#add8e6",
            font=("TkDefaultFont", 10, "bold"),
            state="disabled")
        self.upload_photo_btn.pack(side="left", padx=(0, 4))

        self.revert_btn = ttk.Button(
            btn_row, text="↺ Revert",
            command=self._revert_photo,
            state="disabled")
        self.revert_btn.pack(side="left")

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

            if key != 'output_filename':
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
                elif key == 'output_filename':
                    entry = tk.Entry(custom_frame, textvariable=var, width=40,
                                     state="readonly",
                                     readonlybackground=self.root.cget("background"),
                                     relief="flat", cursor="arrow")
                    self.output_filename_entry = entry
                    def _show_filename_menu(event, _entry=entry):
                        menu = tk.Menu(_entry, tearoff=0)
                        menu.add_command(label="Copy to Caption",
                                         command=self._copy_filename_to_caption)
                        menu.tk_popup(event.x_root, event.y_root)
                    entry.bind("<Button-3>", _show_filename_menu)
                else:
                    entry = ttk.Entry(custom_frame, textvariable=var, width=40)
                entry.grid(row=row, column=2, sticky="ew", pady=2)
                self.custom_vars[key] = var
        custom_frame.columnconfigure(2, weight=1)

        # ── Bidirectional field links (mirrors PhotosUploader) ────────────────
        self._register_field_link(
            custom_key='photo_source', exif_key='Artist',
            iptc_tag=(2, 80), validate_fn=None)
        self._register_field_link(
            custom_key='date_of_photo', exif_key='Date Created',
            iptc_tag=(2, 55), validate_fn=self._parse_date)
        self.custom_vars['date_of_photo'].trace_add(
            'write', lambda *_: self._validate_date_field())
        self.custom_vars['output_filename'].trace_add(
            'write', lambda *_: self._validate_output_filename_field())
        self._register_field_link(
            custom_key='tags', exif_key=None,
            iptc_tag=(2, 25), validate_fn=None)

        def _on_comments_changed(_event=None):
            self._validate_caption_field()
            self.custom_vars['comments'].edit_modified(False)
        self.custom_vars['comments'].bind('<<Modified>>', _on_comments_changed)

        # ── Editing Tools — packed directly below Custom Fields ───────────────
        tools_frame = ttk.LabelFrame(lower_frame, text="Editing Tools", padding=6)
        tools_frame.pack(fill="x", pady=(4, 0))

        # Row 1 – Rotate
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

        # Row 2 – Crop / Undo
        row2 = ttk.Frame(tools_frame)
        row2.pack(fill="x", pady=(0, 4))
        self.crop_btn = ttk.Button(row2, text="Crop", command=self._crop_photo)
        self.crop_btn.pack(side="left", padx=2)
        self.undo_btn = ttk.Button(row2, text="Undo", command=self._undo_edit,
                                   state="disabled")
        self.undo_btn.pack(side="left", padx=2)

        # Row 3 – Color adjustment
        row3 = ttk.Frame(tools_frame)
        row3.pack(fill="x")
        ttk.Label(row3, text="Adjust color:").pack(side="left", padx=(0, 6))
        self.color_adjust_var = tk.DoubleVar(value=1.0)
        ttk.Scale(row3, from_=0.0, to=2.0, orient="horizontal",
                  variable=self.color_adjust_var,
                  command=self._on_color_adjust).pack(side="left", fill="x", expand=True)

        self.root.after(100, self._set_initial_sash_positions)
        return frame

    # ── right panel: target album (Photo Move Mode) ──────────────────────────
    def _build_target_panel(self, parent) -> ttk.Frame:
        frame = ttk.Frame(parent)

        # ── Horizontal pane: album tree (left) | thumbnail grid (right) ──────
        hpane = ttk.PanedWindow(frame, orient="horizontal")
        hpane.pack(fill="both", expand=True)
        self._target_hpane = hpane

        # ── Left: album hierarchy tree ────────────────────────────────────────
        tree_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(tree_outer, weight=2)

        filter_frame = ttk.Frame(tree_outer)
        filter_frame.pack(fill="x", pady=(0, 4))
        ttk.Label(filter_frame, text="Filter:").pack(side="left", padx=(0, 4))
        self._tree_filter_var = tk.StringVar()
        ttk.Entry(filter_frame, textvariable=self._tree_filter_var).pack(
            side="left", fill="x", expand=True)

        tree_frame = ttk.Frame(tree_outer)
        tree_frame.pack(fill="both", expand=True)
        yscroll = ttk.Scrollbar(tree_frame, orient="vertical")
        xscroll = ttk.Scrollbar(tree_frame, orient="horizontal")
        self._hierarchy_tree = ttk.Treeview(
            tree_frame, selectmode="browse", show="tree",
            yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        yscroll.config(command=self._hierarchy_tree.yview)
        xscroll.config(command=self._hierarchy_tree.xview)
        yscroll.pack(side="right", fill="y")
        xscroll.pack(side="bottom", fill="x")
        self._hierarchy_tree.pack(side="left", fill="both", expand=True)
        self._hierarchy_tree.column("#0", minwidth=200)

        self._tree_filter_var.trace_add("write", self._on_tree_filter)
        self._hierarchy_tree.bind("<<TreeviewSelect>>", self._on_hierarchy_select)
        self._hierarchy_tree.bind("<Double-1>",         self._on_hierarchy_select)

        # ── Right: target album thumbnail grid ───────────────────────────────
        thumb_outer = ttk.LabelFrame(hpane, text="", padding=4)
        hpane.add(thumb_outer, weight=3)

        top = ttk.Frame(thumb_outer)
        top.pack(fill="x", pady=(0, 4))
        ttk.Label(top, text="Album:").pack(side="left")
        ttk.Label(top, textvariable=self.target_album_var,
                  foreground="blue", anchor="w").pack(side="left", padx=(4, 0))
        ttk.Label(top, textvariable=self.target_thumb_count_var,
                  foreground="gray").pack(side="right", padx=4)

        container = ttk.Frame(thumb_outer)
        container.pack(fill="both", expand=True)

        self._target_thumb_canvas = tk.Canvas(container, bg="#2a2a2a", highlightthickness=0)
        vscroll = ttk.Scrollbar(container, orient="vertical",
                                command=self._target_thumb_canvas.yview)
        self._target_thumb_canvas.configure(yscrollcommand=vscroll.set)
        vscroll.pack(side="right", fill="y")
        self._target_thumb_canvas.pack(side="left", fill="both", expand=True)

        self._target_grid_frame = tk.Frame(self._target_thumb_canvas, bg="#2a2a2a")
        self._target_grid_win = self._target_thumb_canvas.create_window(
            0, 0, anchor="nw", window=self._target_grid_frame)

        self._target_grid_frame.bind("<Configure>",    self._on_target_grid_resize)
        self._target_thumb_canvas.bind("<Configure>",  self._on_target_canvas_resize)
        self._target_thumb_canvas.bind("<MouseWheel>", self._on_target_mousewheel)
        # Drops from left grid onto right grid
        self._target_thumb_canvas.bind("<ButtonRelease-1>",
                                       lambda e: self._on_grid_drop(e, 'right'))

        # Populate tree once the widget is mapped
        frame.bind("<Map>", lambda e: self.root.after(50, self._populate_hierarchy_tree), add="+")

        return frame

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
        album_id   = self._state.get("album_id",   None)
        album_name = self._state.get("album_name", "")
        if album_id is not None:
            self.current_album_id   = album_id
            self.current_album_name = album_name
            self.album_var.set(album_name or "(none)")
            self.root.after(300, self._load_album_photos)
        target_id   = self._state.get("target_album_id",   None)
        target_name = self._state.get("target_album_name", "")
        if target_id is not None:
            self.target_album_id   = target_id
            self.target_album_name = target_name
            self.target_album_var.set(target_name or "(none)")
            self.root.after(300, self._load_target_album_photos)

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
        self._save_current_custom_fields()
        state: dict = {}
        state["geometry"] = self.root.geometry()
        try:
            state["sash"] = self._main_pane.sashpos(0)
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

    def _toggle_mode(self):
        self._clear_selection()
        if self._mode == 'editor':
            self._mode = 'move'
            self._editor_frame.pack_forget()
            self._target_frame.pack(fill="both", expand=True)
            self._mode_btn.config(text="Switch to Photo Editor Mode")
        else:
            self._mode = 'editor'
            self._target_frame.pack_forget()
            self._editor_frame.pack(fill="both", expand=True)
            self._mode_btn.config(text="Switch to Photo Move Mode")

    # -----------------------------------------------------------------------
    # Status
    # -----------------------------------------------------------------------
    def set_status(self, msg: str):
        self.status_var.set(msg)
        self.root.update_idletasks()

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
                self.root.after(0, lambda: self.set_status(
                    f"Hierarchy refresh failed: {e}"))

        threading.Thread(target=worker, daemon=True).start()

    # -----------------------------------------------------------------------
    # Album selection
    # -----------------------------------------------------------------------
    def _pick_album(self):
        try:
            DownloadAlbumStructure.pick_album(
                self.root, self.set_status, self._on_album_selected,
                title="Select Album to Edit")
        except FileNotFoundError as e:
            messagebox.showerror("Params file missing", str(e))
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def _on_album_selected(self, album_id: int, fullname: str):
        self.current_album_id   = album_id
        self.current_album_name = fullname
        self.album_var.set(fullname)
        self.set_status(f"Album selected: {fullname}")
        self._load_album_photos()

    # -----------------------------------------------------------------------
    # Album hierarchy tree (embedded in target panel)
    # -----------------------------------------------------------------------
    def _populate_source_hierarchy_tree(self):
        """Load AlbumHierarchy.json into the source (left) embedded tree."""
        try:
            hier_file = DownloadAlbumStructure._album_hierarchy_file()
            if not hier_file.exists():
                return
            with open(hier_file, encoding="utf-8") as f:
                hierarchy = json.load(f)
        except Exception as e:
            logger.warning(f"Could not load hierarchy for source tree: {e}")
            return

        tree = self._source_hierarchy_tree
        for item in tree.get_children():
            tree.delete(item)
        self._source_tree_all_items = []
        self._source_tree_fullname_by_iid = {}

        def _populate(parent_iid, nodes, top_level=False):
            for node in nodes:
                iid   = str(node["id"])
                count = node.get("total_nb_images", 0)
                text  = f"{node['name']}  ({count:,})"
                tree.insert(parent_iid, "end", iid=iid, text=text, open=top_level)
                fullname = node.get("fullname", node["name"])
                self._source_tree_all_items.append((iid, node["name"].lower(), fullname))
                self._source_tree_fullname_by_iid[iid] = fullname
                if node.get("children"):
                    _populate(iid, node["children"])

        _populate("", hierarchy, top_level=True)

        # Re-select current source album if one is set
        if self.current_album_id is not None:
            iid = str(self.current_album_id)
            if tree.exists(iid):
                tree.selection_set(iid)
                tree.see(iid)

    def _on_source_tree_filter(self, *_):
        q = self._source_filter_var.get().strip().lower()
        tree = self._source_hierarchy_tree
        if not q:
            tree.selection_remove(tree.selection())
            return
        for iid, name_lower, _ in self._source_tree_all_items:
            if q in name_lower:
                tree.selection_set(iid)
                tree.see(iid)
                return
        tree.selection_remove(tree.selection())

    def _on_source_hierarchy_select(self, _event=None):
        sel = self._source_hierarchy_tree.selection()
        if not sel:
            return
        iid      = sel[0]
        album_id = int(iid)
        fullname = self._source_tree_fullname_by_iid.get(iid, "")
        if album_id != self.current_album_id:
            self._on_album_selected(album_id, fullname)

    def _populate_hierarchy_tree(self):
        """Load AlbumHierarchy.json into the embedded tree (non-blocking)."""
        try:
            hier_file = DownloadAlbumStructure._album_hierarchy_file()
            if not hier_file.exists():
                return
            with open(hier_file, encoding="utf-8") as f:
                hierarchy = json.load(f)
        except Exception as e:
            logger.warning(f"Could not load hierarchy for tree: {e}")
            return

        tree = self._hierarchy_tree
        # Clear existing items
        for item in tree.get_children():
            tree.delete(item)
        self._tree_all_items = []   # (iid, name_lower, fullname)
        self._tree_fullname_by_iid = {}

        def _populate(parent_iid, nodes, top_level=False):
            for node in nodes:
                iid   = str(node["id"])
                count = node.get("total_nb_images", 0)
                text  = f"{node['name']}  ({count:,})"
                tree.insert(parent_iid, "end", iid=iid, text=text, open=top_level)
                fullname = node.get("fullname", node["name"])
                self._tree_all_items.append((iid, node["name"].lower(), fullname))
                self._tree_fullname_by_iid[iid] = fullname
                if node.get("children"):
                    _populate(iid, node["children"])

        _populate("", hierarchy, top_level=True)

        # Re-select current target album if one is set
        if self.target_album_id is not None:
            iid = str(self.target_album_id)
            if tree.exists(iid):
                tree.selection_set(iid)
                tree.see(iid)

    def _on_tree_filter(self, *_):
        q = self._tree_filter_var.get().strip().lower()
        tree = self._hierarchy_tree
        if not q:
            tree.selection_remove(tree.selection())
            return
        for iid, name_lower, _ in self._tree_all_items:
            if q in name_lower:
                tree.selection_set(iid)
                tree.see(iid)
                return
        tree.selection_remove(tree.selection())

    def _on_hierarchy_select(self, _event=None):
        sel = self._hierarchy_tree.selection()
        if not sel:
            return
        iid      = sel[0]
        album_id = int(iid)
        fullname = self._tree_fullname_by_iid.get(iid, "")
        # Only reload if a different album was chosen
        if album_id != self.target_album_id:
            self._on_target_album_selected(album_id, fullname)

    def _pick_target_album(self):
        try:
            DownloadAlbumStructure.pick_album(
                self.root, self.set_status, self._on_target_album_selected,
                title="Select Target Album")
        except FileNotFoundError as e:
            messagebox.showerror("Params file missing", str(e))
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def _on_target_album_selected(self, album_id: int, fullname: str):
        self.target_album_id   = album_id
        self.target_album_name = fullname
        self.target_album_var.set(fullname)
        self.set_status(f"Target album selected: {fullname}")
        self._load_target_album_photos()

    # -----------------------------------------------------------------------
    # Load & display thumbnails
    # -----------------------------------------------------------------------
    def _load_album_photos(self):
        if self.current_album_id is None:
            messagebox.showinfo("No Album", "Please select an album first (toolbar).")
            return
        self._clear_thumbnails()
        self.thumb_count_var.set("")
        self.set_status(f"Fetching photos from \"{self.current_album_name}\"…")

        # ── Progress dialog ────────────────────────────────────────────────
        dlg = tk.Toplevel(self.root)
        dlg.title("Downloading Photos")
        dlg.resizable(False, False)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)   # block close button

        dlg_alive = [True]
        def _on_dlg_destroyed(_e=None): dlg_alive[0] = False
        dlg.bind("<Destroy>", _on_dlg_destroyed)

        ttk.Label(dlg, text="Downloading thumbnails from:",
                  padding=(16, 12, 16, 2)).pack()
        ttk.Label(dlg, text=self.current_album_name,
                  font=("TkDefaultFont", 9, "bold"),
                  padding=(16, 0, 16, 8)).pack()

        pbar = ttk.Progressbar(dlg, mode="indeterminate", length=360)
        pbar.pack(padx=16, pady=(0, 4))
        pbar.start(12)

        count_var = tk.StringVar(value="Connecting…")
        ttk.Label(dlg, textvariable=count_var, foreground="gray",
                  padding=(16, 0, 16, 12)).pack()

        # Centre over main window
        self.root.update_idletasks()
        dlg.update_idletasks()
        rw, rh = self.root.winfo_width(),   self.root.winfo_height()
        rx, ry = self.root.winfo_rootx(),   self.root.winfo_rooty()
        dw, dh = dlg.winfo_reqwidth(),      dlg.winfo_reqheight()
        dlg.geometry(f"{dw}x{dh}+{rx + (rw - dw) // 2}+{ry + (rh - dh) // 2}")

        # ── Callbacks called from the background thread via root.after() ───
        def _on_total(n: int):
            def _apply():
                if not dlg_alive[0]: return
                pbar.stop()
                pbar.configure(mode="determinate", maximum=max(n, 1))
                count_var.set(f"0 / {n}")
            self.root.after(0, _apply)

        def _on_progress(done: int, total: int):
            def _apply():
                if not dlg_alive[0]: return
                pbar["value"] = done
                count_var.set(f"{done} / {total}")
            self.root.after(0, _apply)

        def _on_done():
            def _apply():
                if dlg_alive[0]: dlg.destroy()
            self.root.after(0, _apply)

        threading.Thread(
            target=self._worker_fetch_photos,
            args=(_on_total, _on_progress, _on_done),
            daemon=True).start()

    def _worker_fetch_photos(self, on_total, on_progress, on_done):
        try:
            params = DownloadAlbumStructure.load_params()
            client = DownloadAlbumStructure.PiwigoClient(
                params["url"], params["username"], params["password"],
                verify_ssl=params.get("verify_ssl", True),
                rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
            client.login(params["username"], params["password"])
            images = client.get_album_images(self.current_album_id)
            client.logout()

            self._album_images = images
            n = len(images)
            self.root.after(0, lambda: self.thumb_count_var.set(
                f"{n} photo{'s' if n != 1 else ''}"))
            on_total(n)

            # Log the first image dict so derivative key names are visible in the console
            if images:
                logger.info(f"Sample image dict keys: {list(images[0].keys())}")
                logger.info(f"Sample derivatives: {list(images[0].get('derivatives', {}).keys())}")

            verify = params.get("verify_ssl", True)
            for idx, img_dict in enumerate(images):
                self._worker_download_thumb(img_dict, verify)
                on_progress(idx + 1, n)

            on_done()
            self.root.after(0, lambda: self.set_status(
                f"Loaded {n} photo{'s' if n != 1 else ''} "
                f"from \"{self.current_album_name}\""))
        except Exception as e:
            logger.exception("Error fetching photos")
            on_done()   # always close the dialog
            self.root.after(0, lambda: messagebox.showerror("Error", str(e)))
            self.root.after(0, lambda: self.set_status(f"Error: {e}"))

    def _worker_download_thumb(self, img_dict: dict, verify: bool):
        if not PIL_AVAILABLE or not REQUESTS_AVAILABLE:
            return
        image_id = img_dict.get("id")

        # Try every known derivative size, then fall back to the full image URL
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
            import warnings
            with warnings.catch_warnings():
                if not verify:
                    warnings.simplefilter("ignore", urllib3.exceptions.InsecureRequestWarning)
                resp = requests.get(url, verify=verify, timeout=15)
                resp.raise_for_status()
            pil = Image.open(BytesIO(resp.content))
            pil.load()   # fully decode while BytesIO is still in scope
            # Ensure a mode ImageTk can render
            if pil.mode not in ("RGB", "RGBA"):
                pil = pil.convert("RGB")
            pil.thumbnail(self._thumb_size, Image.Resampling.LANCZOS)
            self._thumb_cache[image_id] = pil
            self.root.after(0, lambda iid=image_id, d=img_dict:
                            self._add_thumb_cell(iid, d))
        except Exception as e:
            logger.warning(f"Thumbnail {image_id} ({url}): {e}")

    def _add_thumb_cell(self, image_id: int, img_dict: dict):
        pil = self._thumb_cache.get(image_id)
        if pil is None:
            return
        tk_img = ImageTk.PhotoImage(pil)
        self._thumb_tk[image_id] = tk_img   # prevent GC

        name = img_dict.get("name") or img_dict.get("file") or f"#{image_id}"

        cell = tk.Frame(self._grid_frame, bg="#3a3a3a", relief="flat",
                        padx=2, pady=2, cursor="hand2")
        img_lbl = tk.Label(cell, image=tk_img, bg="#3a3a3a", cursor="hand2")
        img_lbl.pack()
        self._thumb_img_labels[image_id] = img_lbl
        self._cell_by_id[image_id] = cell
        name_lbl = tk.Label(cell, text=_truncate(name, 20),
                            bg="#3a3a3a", fg="#dddddd",
                            font=("TkDefaultFont", 8), anchor="center",
                            wraplength=self._thumb_size[0])
        name_lbl.pack(fill="x")

        # Tooltip: filename + caption
        def _tip_text(d=img_dict):
            parts = []
            fname = d.get("file", "").strip()
            if fname:
                parts.append(fname)
            caption = d.get("comment", "").strip()
            if caption:
                parts.append(f"Caption: {caption}")
            return "\n".join(parts)

        def _show_left_menu(event, iid=image_id, d=img_dict, c=cell):
            menu = tk.Menu(c, tearoff=0)
            menu.add_command(label="Remove from Album",
                             command=lambda: self._remove_from_album(iid, d, 'left'))
            menu.tk_popup(event.x_root, event.y_root)

        tip = _Tooltip(_tip_text)
        for w in (cell, img_lbl, name_lbl):
            w.bind("<ButtonPress-1>",   lambda e, d=img_dict, c=cell: self._on_cell_press(e, d, c, 'left'))
            w.bind("<B1-Motion>",       lambda e, d=img_dict, c=cell: self._on_cell_motion(e, d, c, 'left'))
            w.bind("<ButtonRelease-1>", lambda e, d=img_dict, c=cell: self._on_cell_release(e, d, c, 'left'))
            w.bind("<Enter>",           lambda e, iid=image_id, c=cell: self._on_source_enter(iid, c))
            w.bind("<Leave>",           lambda e, iid=image_id, c=cell: self._on_source_leave(iid, c))
            w.bind("<Button-3>",        _show_left_menu)
            tip.attach(w)

        self._thumb_cells.append(cell)
        self._reflow_grid()

    def _clear_thumbnails(self):
        for cell in self._thumb_cells:
            cell.destroy()
        self._thumb_cells.clear()
        self._thumb_cache.clear()
        self._thumb_tk.clear()
        self._thumb_img_labels.clear()
        self._cell_by_id.clear()
        self._selected_ids.clear()
        self._album_images.clear()
        self._drag_batch.clear()

    # -----------------------------------------------------------------------
    # Grid layout
    # -----------------------------------------------------------------------
    def _reflow_grid(self):
        if not self._thumb_cells:
            return
        canvas_w = self._thumb_canvas.winfo_width()
        if canvas_w < 10:
            canvas_w = self._thumb_size[0] + 20
        cols = max(1, canvas_w // (self._thumb_size[0] + 16))
        for idx, cell in enumerate(self._thumb_cells):
            r, c = divmod(idx, cols)
            cell.grid(row=r, column=c, padx=4, pady=4, sticky="n")

    def _on_grid_resize(self, _event=None):
        self._thumb_canvas.configure(scrollregion=self._thumb_canvas.bbox("all"))

    def _on_thumb_canvas_resize(self, event):
        self._thumb_canvas.itemconfigure(self._grid_win, width=event.width)
        self._reflow_grid()

    def _on_mousewheel(self, event):
        self._thumb_canvas.yview_scroll(-1 * (event.delta // 120), "units")

    # -----------------------------------------------------------------------
    # Target album thumbnail loading
    # -----------------------------------------------------------------------
    def _load_target_album_photos(self):
        if self.target_album_id is None:
            return
        self._clear_target_thumbnails()
        self.target_thumb_count_var.set("")
        self.set_status(f"Fetching photos from \"{self.target_album_name}\"…")

        dlg = tk.Toplevel(self.root)
        dlg.title("Downloading Photos")
        dlg.resizable(False, False)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        dlg_alive = [True]
        dlg.bind("<Destroy>", lambda _e: dlg_alive.__setitem__(0, False))

        ttk.Label(dlg, text="Downloading thumbnails from:",
                  padding=(16, 12, 16, 2)).pack()
        ttk.Label(dlg, text=self.target_album_name,
                  font=("TkDefaultFont", 9, "bold"),
                  padding=(16, 0, 16, 8)).pack()
        pbar = ttk.Progressbar(dlg, mode="indeterminate", length=360)
        pbar.pack(padx=16, pady=(0, 4))
        pbar.start(12)
        count_var = tk.StringVar(value="Connecting…")
        ttk.Label(dlg, textvariable=count_var, foreground="gray",
                  padding=(16, 0, 16, 12)).pack()

        self.root.update_idletasks()
        dlg.update_idletasks()
        rw, rh = self.root.winfo_width(), self.root.winfo_height()
        rx, ry = self.root.winfo_rootx(), self.root.winfo_rooty()
        dw, dh = dlg.winfo_reqwidth(), dlg.winfo_reqheight()
        dlg.geometry(f"{dw}x{dh}+{rx + (rw - dw) // 2}+{ry + (rh - dh) // 2}")

        def _on_total(n):
            def _apply():
                if not dlg_alive[0]: return
                pbar.stop()
                pbar.configure(mode="determinate", maximum=max(n, 1))
                count_var.set(f"0 / {n}")
            self.root.after(0, _apply)

        def _on_progress(done, total):
            def _apply():
                if not dlg_alive[0]: return
                pbar["value"] = done
                count_var.set(f"{done} / {total}")
            self.root.after(0, _apply)

        def _on_done():
            self.root.after(0, lambda: dlg.destroy() if dlg_alive[0] else None)

        threading.Thread(
            target=self._worker_fetch_target_photos,
            args=(_on_total, _on_progress, _on_done),
            daemon=True).start()

    def _worker_fetch_target_photos(self, on_total, on_progress, on_done):
        try:
            params = DownloadAlbumStructure.load_params()
            client = DownloadAlbumStructure.PiwigoClient(
                params["url"], params["username"], params["password"],
                verify_ssl=params.get("verify_ssl", True),
                rate_limit_calls_per_second=params.get("rate_limit_calls_per_second", 2.0))
            client.login(params["username"], params["password"])
            images = client.get_album_images(self.target_album_id)
            client.logout()
            self._target_album_images = images
            n = len(images)
            self.root.after(0, lambda: self.target_thumb_count_var.set(
                f"{n} photo{'s' if n != 1 else ''}"))
            on_total(n)
            verify = params.get("verify_ssl", True)
            for idx, img_dict in enumerate(images):
                self._worker_download_target_thumb(img_dict, verify)
                on_progress(idx + 1, n)
            on_done()
            self.root.after(0, lambda: self.set_status(
                f"Loaded {n} photo{'s' if n != 1 else ''} from \"{self.target_album_name}\""))
        except Exception as e:
            logger.exception("Error fetching target photos")
            on_done()
            self.root.after(0, lambda: messagebox.showerror("Error", str(e)))

    def _worker_download_target_thumb(self, img_dict: dict, verify: bool):
        if not PIL_AVAILABLE or not REQUESTS_AVAILABLE:
            return
        image_id = img_dict.get("id")
        url = _pick_derivative_url(
            img_dict, ("thumb", "square", "small", "2small", "xsmall", "medium", "large"))
        if not url:
            url = img_dict.get("element_url", "")
        if not url:
            return
        try:
            import warnings
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
            self._target_thumb_cache[image_id] = pil
            self.root.after(0, lambda iid=image_id, d=img_dict:
                            self._add_target_thumb_cell(iid, d))
        except Exception as e:
            logger.warning(f"Target thumbnail {image_id}: {e}")

    def _add_target_thumb_cell(self, image_id: int, img_dict: dict):
        pil = self._target_thumb_cache.get(image_id)
        if pil is None:
            return
        tk_img = ImageTk.PhotoImage(pil)
        self._target_thumb_tk[image_id] = tk_img
        self._target_cell_by_id[image_id] = None  # set below after cell creation

        name = img_dict.get("name") or img_dict.get("file") or f"#{image_id}"
        cell = tk.Frame(self._target_grid_frame, bg="#3a3a3a", relief="flat",
                        padx=2, pady=2, cursor="hand2")
        self._target_cell_by_id[image_id] = cell
        img_lbl = tk.Label(cell, image=tk_img, bg="#3a3a3a", cursor="hand2")
        img_lbl.pack()
        name_lbl = tk.Label(cell, text=_truncate(name, 20),
                            bg="#3a3a3a", fg="#dddddd",
                            font=("TkDefaultFont", 8), anchor="center",
                            wraplength=self._thumb_size[0])
        name_lbl.pack(fill="x")

        def _tip_text(d=img_dict):
            parts = []
            fname = d.get("file", "").strip()
            if fname: parts.append(fname)
            caption = d.get("comment", "").strip()
            if caption: parts.append(f"Caption: {caption}")
            return "\n".join(parts)

        def _show_right_menu(event, iid=image_id, d=img_dict, c=cell):
            menu = tk.Menu(c, tearoff=0)
            menu.add_command(label="Remove from Album",
                             command=lambda: self._remove_from_album(iid, d, 'right'))
            menu.tk_popup(event.x_root, event.y_root)

        tip = _Tooltip(_tip_text)
        for w in (cell, img_lbl, name_lbl):
            w.bind("<ButtonPress-1>",   lambda e, d=img_dict, c=cell: self._on_cell_press(e, d, c, 'right'))
            w.bind("<B1-Motion>",       lambda e, d=img_dict, c=cell: self._on_cell_motion(e, d, c, 'right'))
            w.bind("<ButtonRelease-1>", lambda e, d=img_dict, c=cell: self._on_cell_release(e, d, c, 'right'))
            w.bind("<Enter>",           lambda e, c=cell, iid=image_id: self._on_target_enter(iid, c))
            w.bind("<Leave>",           lambda e, c=cell, iid=image_id: self._on_target_leave(iid, c))
            w.bind("<Button-3>",        _show_right_menu)
            tip.attach(w)

        self._target_thumb_cells.append(cell)
        self._reflow_target_grid()

    def _clear_target_thumbnails(self):
        for cell in self._target_thumb_cells:
            cell.destroy()
        self._target_thumb_cells.clear()
        self._target_thumb_cache.clear()
        self._target_thumb_tk.clear()
        self._target_cell_by_id.clear()
        self._target_selected_ids.clear()
        self._target_album_images.clear()
        self._drag_batch.clear()

    def _reflow_target_grid(self):
        if not self._target_thumb_cells:
            return
        canvas_w = self._target_thumb_canvas.winfo_width()
        if canvas_w < 10:
            canvas_w = self._thumb_size[0] + 20
        cols = max(1, canvas_w // (self._thumb_size[0] + 16))
        for idx, cell in enumerate(self._target_thumb_cells):
            r, c = divmod(idx, cols)
            cell.grid(row=r, column=c, padx=4, pady=4, sticky="n")

    def _on_target_grid_resize(self, _event=None):
        self._target_thumb_canvas.configure(
            scrollregion=self._target_thumb_canvas.bbox("all"))

    def _on_target_canvas_resize(self, event):
        self._target_thumb_canvas.itemconfigure(self._target_grid_win, width=event.width)
        self._reflow_target_grid()

    def _on_target_mousewheel(self, event):
        self._target_thumb_canvas.yview_scroll(-1 * (event.delta // 120), "units")

    # -----------------------------------------------------------------------
    # Unified thumbnail press / motion / release  (both sides, click + drag)
    # -----------------------------------------------------------------------
    _DRAG_THRESHOLD = 5   # pixels of movement before a press becomes a drag

    def _on_cell_press(self, event, img_dict: dict, cell: tk.Frame, side: str):
        self._press_pos = (event.x_root, event.y_root)
        self._drag_source_side = side
        self._drag_batch = []

    def _on_cell_motion(self, event, img_dict: dict, cell: tk.Frame, side: str):
        if self._mode != 'move' or self._press_pos is None:
            return
        dx = abs(event.x_root - self._press_pos[0])
        dy = abs(event.y_root - self._press_pos[1])
        if dx < self._DRAG_THRESHOLD and dy < self._DRAG_THRESHOLD:
            return
        if self._drag_window is None and not self._drag_batch:
            self._start_drag(event, img_dict, side)
        if self._drag_window:
            self._drag_window.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")

    def _on_cell_release(self, event, img_dict: dict, cell: tk.Frame, side: str):
        was_drag = self._drag_window is not None
        if self._drag_window is not None:
            self._drag_window.destroy()
            self._drag_window = None
        self._press_pos = None

        if was_drag:
            self._execute_drop(event)
        elif self._mode == 'move':
            self._toggle_side_selection(img_dict.get("id"), cell, side)
        elif side == 'left':
            self._on_thumb_click(img_dict)

    def _start_drag(self, event, img_dict: dict, side: str):
        self._drag_is_copy = bool(event.state & 0x0004)
        image_id = img_dict.get("id")
        if side == 'left':
            sel_ids = self._selected_ids
            images   = self._album_images
            cache    = self._thumb_cache
        else:
            sel_ids = self._target_selected_ids
            images   = self._target_album_images
            cache    = self._target_thumb_cache

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
        self._drag_window = win

    def _execute_drop(self, event):
        """Called after drag ends; detects destination and executes immediately."""
        if not self._drag_batch or self._mode != 'move':
            self._drag_batch = []
            return

        widget_under = self.root.winfo_containing(event.x_root, event.y_root)
        dst_side = self._widget_side(widget_under)
        src_side = self._drag_source_side

        if dst_side is None or dst_side == src_side:
            self._drag_batch = []
            return

        if src_side == 'left':
            src_album_id = self.current_album_id
            dst_album_id = self.target_album_id
            dst_images   = self._target_album_images
        else:
            src_album_id = self.target_album_id
            dst_album_id = self.current_album_id
            dst_images   = self._album_images

        if dst_album_id is None:
            self._drag_batch = []
            self._show_over_target(
                "No Album Selected",
                "Please select an album on the destination side before moving or copying.")
            return

        dst_ids = {d.get("id") for d in dst_images}
        already = [d for d in self._drag_batch if d.get("id") in dst_ids]
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

        op = 'copy' if self._drag_is_copy else 'move'
        self._execute_move_copy(to_process, op, src_side, src_album_id, dst_album_id)

    def _on_grid_drop(self, event, side: str):
        """ButtonRelease-1 on empty canvas area — clear selection for that side."""
        if self._mode == 'move':
            if side == 'left':
                self._clear_side_selection('left')
            else:
                self._clear_side_selection('right')

    # -----------------------------------------------------------------------
    # Selection helpers (symmetric for both sides)
    # -----------------------------------------------------------------------
    def _toggle_side_selection(self, image_id, cell: tk.Frame, side: str):
        ids = self._selected_ids if side == 'left' else self._target_selected_ids
        if image_id in ids:
            ids.discard(image_id)
            self._apply_cell_bg(cell, selected=False)
        else:
            ids.add(image_id)
            self._apply_cell_bg(cell, selected=True)
        total = len(self._selected_ids) + len(self._target_selected_ids)
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

    def _on_source_enter(self, image_id, cell: tk.Frame):
        if image_id not in self._selected_ids:
            cell.configure(bg="#5a5a5a", relief="raised")

    def _on_source_leave(self, image_id, cell: tk.Frame):
        if image_id not in self._selected_ids:
            cell.configure(bg="#3a3a3a", relief="flat")

    def _on_target_enter(self, image_id, cell: tk.Frame):
        if image_id not in self._target_selected_ids:
            cell.configure(bg="#5a5a5a", relief="raised")

    def _on_target_leave(self, image_id, cell: tk.Frame):
        if image_id not in self._target_selected_ids:
            cell.configure(bg="#3a3a3a", relief="flat")

    def _clear_side_selection(self, side: str):
        if side == 'left':
            for iid in list(self._selected_ids):
                cell = self._cell_by_id.get(iid)
                if cell:
                    self._apply_cell_bg(cell, selected=False)
            self._selected_ids.clear()
        else:
            for iid in list(self._target_selected_ids):
                cell = self._target_cell_by_id.get(iid)
                if cell:
                    self._apply_cell_bg(cell, selected=False)
            self._target_selected_ids.clear()

    def _clear_selection(self):
        self._clear_side_selection('left')
        self._clear_side_selection('right')

    def _show_over_target(self, title: str, message: str):
        """Show a warning dialog centred over the Target Album panel."""
        self.root.update_idletasks()
        tx = self._target_frame.winfo_rootx()
        ty = self._target_frame.winfo_rooty()
        tw = self._target_frame.winfo_width()
        th = self._target_frame.winfo_height()

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
            if w == self._target_frame:
                return 'right'
            if w == self._thumb_panel_frame:
                return 'left'
            try:
                w = w.master
            except Exception:
                break
        return None

    # -----------------------------------------------------------------------
    # Immediate move/copy execution
    # -----------------------------------------------------------------------
    def _execute_move_copy(self, batch: list, op: str,
                           src_side: str, src_album_id: int, dst_album_id: int):
        """Execute copy or move for all items in batch immediately in a background thread."""
        total = len(batch)

        dlg = tk.Toplevel(self.root)
        dlg.title("Moving Photos" if op == 'move' else "Copying Photos")
        dlg.resizable(False, False)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        dlg_alive = [True]
        dlg.bind("<Destroy>", lambda _e: dlg_alive.__setitem__(0, False))

        ttk.Label(dlg, text=f"{'Moving' if op == 'move' else 'Copying'} {total} photo(s)…",
                  padding=(16, 12, 16, 2)).pack()
        pbar = ttk.Progressbar(dlg, mode="determinate", maximum=max(total, 1), length=380)
        pbar.pack(padx=16, pady=(0, 4))
        stage_var = tk.StringVar(value="Starting…")
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
            self.root.after(0, lambda: dlg.destroy() if dlg_alive[0] else None)

        def worker():
            errors = []
            n_ok = 0
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
                        current_cats = [int(c["id"]) for c in info.get("categories", [])]
                        if op == 'copy':
                            # Add dst album to the image's categories
                            if dst_album_id not in current_cats:
                                current_cats.append(dst_album_id)
                                client.set_image_categories(image_id, current_cats)
                        else:
                            # Move: swap src album for dst album in categories
                            new_cats = [c for c in current_cats if c != src_album_id]
                            if dst_album_id not in new_cats:
                                new_cats.append(dst_album_id)
                            if new_cats != current_cats:
                                client.set_image_categories(image_id, new_cats)
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
                self.set_status(
                    f"{op.capitalize()} complete: {n_ok} ok"
                    + (f", {len(errors)} error(s)" if errors else "."))
                # Reload both albums to reflect the new state
                self._load_album_photos()
                if self.target_album_id is not None:
                    self._load_target_album_photos()

            self.root.after(0, finish)

        threading.Thread(target=worker, daemon=True).start()

    # -----------------------------------------------------------------------
    # Remove from album (RMB handler — both sides)
    # -----------------------------------------------------------------------
    def _remove_from_album(self, image_id: int, img_dict: dict, side: str):
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
        if side == 'left':
            cell = self._cell_by_id.pop(image_id, None)
            if cell:
                self._thumb_cells = [c for c in self._thumb_cells if c != cell]
                cell.destroy()
            self._selected_ids.discard(image_id)
            self._album_images = [d for d in self._album_images if d.get("id") != image_id]
            self._reflow_grid()
        else:
            cell = self._target_cell_by_id.pop(image_id, None)
            if cell:
                self._target_thumb_cells = [c for c in self._target_thumb_cells if c != cell]
                cell.destroy()
            self._target_selected_ids.discard(image_id)
            self._target_album_images = [
                d for d in self._target_album_images if d.get("id") != image_id]
            self._reflow_target_grid()
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
            import warnings
            with warnings.catch_warnings():
                if not verify:
                    warnings.simplefilter("ignore", urllib3.exceptions.InsecureRequestWarning)
                resp = requests.get(url, verify=verify, timeout=30)
                resp.raise_for_status()
            pil = Image.open(BytesIO(resp.content))
            pil.load()   # fully decode before leaving the thread
            self.root.after(0, lambda: self._on_photo_loaded(pil, img_dict))
        except Exception as e:
            logger.exception(f"Failed to load {url}")
            self.root.after(0, lambda: self.set_status(
                f"Error loading \"{img_dict.get('name', '')}\": {e}"))

    def _on_photo_loaded(self, pil: "Image.Image", img_dict: dict):
        """Called on the main thread once the full image has been downloaded."""
        name = img_dict.get("name") or img_dict.get("file") or "unknown"
        self._viewer_image       = pil
        self._current_image_dict = img_dict
        self._edit_history.clear()
        self._clear_crop_rect()
        self.photo_label_var.set(name)
        self.photo_dim_var.set(
            f"{pil.width} \u00d7 {pil.height} px  |  {pil.mode}")
        self._display_photo()
        self._load_iptc_from_image(pil)
        self._load_custom_fields(img_dict.get("id"))
        self._validate_date_field()
        self._validate_caption_field()
        self._validate_output_filename_field()
        self.upload_photo_btn.config(state="normal")
        self.revert_btn.config(state="normal")
        self.rotate_right_btn.config(state="normal")
        self.rotate_left_btn.config(state="normal")
        self.rotate_180_btn.config(state="normal")
        self.set_status(f"Loaded: {name}")

    def _upload_current_photo(self):
        """Upload the current photo back to Piwigo (not yet implemented)."""
        self._refresh_current_thumbnail()
        self.set_status("Upload to Piwigo: not yet implemented.")

    def _refresh_current_thumbnail(self):
        """Regenerate the left-pane thumbnail from the current editor image."""
        if self._viewer_image is None or self._current_image_dict is None:
            return
        image_id = self._current_image_dict.get("id")
        if image_id is None:
            return
        img_lbl = self._thumb_img_labels.get(image_id)
        if img_lbl is None:
            return
        pil = self._viewer_image.copy()
        if pil.mode not in ("RGB", "RGBA"):
            pil = pil.convert("RGB")
        pil.thumbnail(self._thumb_size, Image.Resampling.LANCZOS)
        self._thumb_cache[image_id] = pil
        tk_img = ImageTk.PhotoImage(pil)
        self._thumb_tk[image_id] = tk_img   # keep reference to prevent GC
        img_lbl.configure(image=tk_img)

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
        self._clear_crop_rect()
        self._display_photo()
        direction = "right" if degrees == 90 else ("left" if degrees == -90 else "180°")
        self.set_status(f"Rotated {direction}")

    def _undo_edit(self):
        """Revert the last rotate or crop operation."""
        if not self._edit_history:
            return
        self._viewer_image = self._edit_history.pop()
        self._clear_crop_rect()
        self._display_photo()
        if not self._edit_history:
            self.undo_btn.config(state="disabled")
        self.set_status("Undo applied.")

    def _on_crop_start(self, event):
        """Begin a crop drag — only if the click lands within the photo bounds."""
        r = self._photo_display_rect
        if r is None:
            self._crop_start = None
            return
        px0, py0, px1, py1 = r
        if event.x < px0 or event.x > px1 or event.y < py0 or event.y > py1:
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
        cx = max(px0, min(event.x, px1))
        cy = max(py0, min(event.y, py1))
        if self._crop_rect_id is not None:
            self.canvas.delete(self._crop_rect_id)
        sx, sy = self._crop_start
        self._crop_rect_id = self.canvas.create_rectangle(
            sx, sy, cx, cy, outline="red", width=2)

    def _on_crop_release(self, event):
        if self._crop_start is None:
            return
        r = self._photo_display_rect
        if r is None:
            return
        px0, py0, px1, py1 = r
        cx = max(px0, min(event.x, px1))
        cy = max(py0, min(event.y, py1))
        sx, sy = self._crop_start
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
        self.set_status("Crop region selected — click Crop to apply, Esc to cancel.")

    def _clear_crop_rect(self, _event=None):
        """Delete the on-canvas crop rectangle and reset drag state."""
        if self._crop_rect_id is not None:
            self.canvas.delete(self._crop_rect_id)
            self._crop_rect_id = None
        self._crop_start = None

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
        self._clear_crop_rect()
        self._display_photo()
        self.set_status(f"Cropped to {ix1 - ix0}\u00d7{iy1 - iy0} px")

    def _on_color_adjust(self, _value=None):
        """Color saturation/brightness adjustment (not yet implemented)."""
        val = round(self.color_adjust_var.get(), 2)
        self.set_status(f"Color adjust: {val:.2f}  (not yet implemented)")

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

        win = tk.Toplevel(self.root)
        name = (self._current_image_dict or {}).get("name") or \
               (self._current_image_dict or {}).get("file", "")
        win.title("Caption Editor")
        win.resizable(True, True)
        win.lift()
        win.attributes("-topmost", True)
        win.after(100, lambda: win.attributes("-topmost", False))

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

        # Click on photo to commit
        photo_canvas.bind("<Button-1>", _commit_and_close)
        win.protocol("WM_DELETE_WINDOW",
                     lambda: (setattr(self, "_caption_editor_open", False),
                              win.destroy()))

        # Size to 75% of main window, centred over it
        self.root.update_idletasks()
        rw = self.root.winfo_width()
        rh = self.root.winfo_height()
        rx = self.root.winfo_rootx()
        ry = self.root.winfo_rooty()
        pw = max(500, int(rw * 0.75))
        ph = max(400, int(rh * 0.75))
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

    def _load_custom_fields(self, image_id):
        """Populate custom fields from saved data (image_id key), falling back
        to whatever _load_iptc_from_image already wrote."""
        iptc_keys = {link['custom_key'] for link in self._field_links}
        data = self.custom_data.get(image_id)

        for key, widget in self.custom_vars.items():
            if key == 'output_filename':
                continue
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

        # Output filename: saved → photo filename → empty
        saved_fn = data.get('output_filename') if data else None
        if not saved_fn and self._current_image_dict:
            saved_fn = (self._current_image_dict.get("file") or
                        self._current_image_dict.get("name") or "")
        self.custom_vars['output_filename'].set(saved_fn or "")

    def _copy_filename_to_caption(self):
        filename = self.custom_vars['output_filename'].get().strip()
        if not filename:
            return
        caption_widget = self.custom_vars['comments']
        existing = caption_widget.get('1.0', 'end').rstrip('\n')
        if existing:
            caption_widget.insert('end', '\n' + filename)
        else:
            caption_widget.insert('end', filename)
        caption_widget.edit_modified(True)

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
        self.revert_btn.config(state="disabled")
        self.rotate_right_btn.config(state="disabled")
        self.rotate_left_btn.config(state="disabled")
        self.rotate_180_btn.config(state="disabled")
        self.undo_btn.config(state="disabled")
        self._edit_history.clear()
        self._clear_crop_rect()
        for widget in self.custom_vars.values():
            if isinstance(widget, tk.Text):
                widget.delete('1.0', "end")
            else:
                widget.set('')
        self._validate_caption_field()
        self._validate_date_field()
        self._validate_output_filename_field()

    # -----------------------------------------------------------------------
    # Field validation (identical to PhotosUploader)
    # -----------------------------------------------------------------------
    def _validate_output_filename_field(self):
        name = self.custom_vars['output_filename'].get().strip()
        _, dot_ext = os.path.splitext(name)
        ext  = dot_ext.lstrip('.').lower()
        valid = (
            bool(name)
            and not self._ILLEGAL_FILENAME_CHARS.search(name)
            and not self._RESERVED_NAMES.match(name)
            and not name.endswith('.')
            and ('.' + ext) in IMAGE_EXTENSIONS
        )
        self._field_validity['filename'] = valid

    def _validate_caption_field(self):
        widget = self.custom_vars['comments']
        value  = widget.get('1.0', "end").strip()
        valid  = len(value) > 0
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
    main()
