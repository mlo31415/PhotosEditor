# -*- mode: python ; coding: utf-8 -*-
import os

a = Analysis(
    ['PhotosEditor.py'],
    # PiwigoHelpers and HelpersPackage live one level up; tell PyInstaller to search
    # them so that DownloadAlbumStructure (imported via a runtime sys.path insert)
    # and FaceGeometry (the face circle shared with SlideShow) are found during
    # analysis and bundled into the exe.
    pathex=[os.path.join(SPECPATH, '..', 'PiwigoHelpers'),
            os.path.join(SPECPATH, '..', 'HelpersPackage')],
    binaries=[],
    # Bundle the icon so root.iconbitmap() can find it at runtime (via sys._MEIPASS)
    datas=[('PhotosEditor.ico', '.')],
    hiddenimports=['DownloadAlbumStructure'],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='PhotosEditor',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=['PhotosEditor.ico'],
)
