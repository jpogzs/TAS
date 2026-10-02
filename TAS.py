# ============================================================================
# TAS - Twister Auto Shapes
# Created and developed by PIA — members: Pogi, LT, Rona
#
# Do not edit the code without informing PIA
# PIA site: https://eagleviewcloud.sharepoint.com/sites/QualityTeam/SitePages/PIA.aspx
# ============================================================================
"""
Twister Auto Shapes: small GUI + global hotkey.  Windows only, no pip installs.

Hotkeys (only while Twister.exe is focused): F5 Gable/Hip, F6 Dormer, F7 Gambrel, F8 Cone.
The GUI (TTT look): header, description, one toggle tile per hotkey, a status box
(running tool / errors) and the footer (version, PIA link).
Rectangle-based tools (shape, dormer, arch) are drawn corner to corner:
  1) the first corner - pressing the HOTKEY counts as this click (the cursor position at
     the key press),
  2) the opposite corner.
From the first corner on, the live preview follows the cursor: width AND height depend on
where the cursor is, and the rectangle is always exactly axis-aligned.  Its FIRST EDGE is
the shorter side.  Scroll the mouse wheel at any time to cycle the shape
(Rectangle / 2-piece / 4-piece ...); the 2nd click
locks the rectangle in with whatever shape is currently shown and starts
tracing immediately (or Backspace / right-click to undo back to the 1st
point).  (The cone tool still uses its own clicks: ring vertex, then center.) The tool then focuses Twister.exe and, for each corner in order,
moves the cursor there and presses the "create point" key (b). After the
last corner it presses the "close polygon" key (y).

Shape "2-piece" splits that same rectangle into two connected rectangles along a
line through the middle of two opposite sides.  Tracing then goes:
  1st rectangle: b at each of its 4 corners, then y.
  2nd rectangle: b at its 2 new corners; at the 2 points it shares with the 1st
                 (in cyclic order), press a (re-use
                 it); then y.

Shape "4-piece" splits the rectangle into 4 polygons: a triangle at each end
(apex inset from that end by half the rectangle's width, along the centerline)
and two middle quads split by the line joining the two apexes. Tracing goes:
  left triangle: b at its 2 corners + the left apex, then y.
  top-mid quad: a at the shared corner; b at its new corner; b at the right
                apex; a at the shared left apex; then y.
  bottom-mid quad: a at the 2 shared apexes; b at its new corner; a at the
                   shared corner; then y.
  right triangle: a at all 3 (all already placed), then y.

Shapes "3-piece (triangle end)" and its inverted twin (more mouse-wheel choices on F5):
a triangle on one end of the rectangle (the 2nd-click end; the 1st-click end when
inverted) plus two quads split by a centerline that runs from the middle of the far
edge to the triangle's top corner.  Tracing goes:
  left quad: b at its 4 corners (including the far-edge middle and the triangle corner).
  right quad: b at its 2 new corners; a at the triangle corner, then at the far-edge middle.
  triangle: a at all 3 (all already placed), then y.

Dormer tool (default F6): same flow as F5, but the far end of the rectangle is
pointed like a roof.  Click 1) the top of the side edge, 2) the bottom of that
same edge, 3) a point on the opposite side to set the width; the point sits half
the width beyond the bottom edge, on the centerline.  Scroll while sighting the
3rd point to pick the split (and whether the shape is inverted - the roof point on
the 1st-click end instead, flat edge on the 2nd-click end; the wheel cycles 2-piece
inverted, 2-piece, 3-piece inverted, 3-piece):
  3-piece (Y):  a top triangle (corner, corner, junction) and left/right quads
                that meet on the centerline.
  2-piece:      two pieces split by one centerline from the top edge to the point.
Tracing uses the same keys as above: b for new corners, a (re-use) for shared ones, y.

Arch tool (default F7): same flow as the rectangle (hotkey press = corner 1, click the opposite corner).  The rectangle is cut into equal strips - the shorter side is
divided, so the cuts run parallel to the longer side.  Scroll while sighting the 3rd
point to pick the piece count: 3 (default), 4, 5, 6.  Tracing: strip 1 is b at its 4
corners then y; every following strip is b at its 2 new corners, a at the 2 shared
points, then y.

Backspace / right-click undoes the last point while you are placing them.
While placing points your physical mouse is locked so it can't knock the
cursor off target. Hold Esc to abort at any time.  If Twister.exe loses
focus, the run stops instead of typing into another app. Twister is always
refocused once the run ends, whether it finished, was aborted, or you hit Esc.
"""
import csv
import ctypes
import ctypes.wintypes as wt
import getpass
import math
import os
import queue
import socket
import threading
import time
import webbrowser
import tkinter as tk
from types import SimpleNamespace

user32 = ctypes.windll.user32
kernel32 = ctypes.windll.kernel32
ctypes.windll.shcore.SetProcessDpiAwareness(2)  # physical pixels everywhere

# ---- Win32 constants -------------------------------------------------------
MOD_ALT, MOD_CONTROL, MOD_SHIFT = 0x1, 0x2, 0x4
VK_SHIFT, VK_CONTROL, VK_MENU, VK_ESCAPE, VK_LBUTTON = 0x10, 0x11, 0x12, 0x1B, 0x01
KEYEVENTF_KEYUP = 0x0002
WH_KEYBOARD_LL, WH_MOUSE_LL = 13, 14
WM_KEYDOWN, WM_KEYUP, WM_SYSKEYDOWN, WM_SYSKEYUP = 0x0100, 0x0101, 0x0104, 0x0105
WM_LBUTTONUP = 0x0202
LLKHF_INJECTED, LLMHF_INJECTED = 0x10, 0x01
PM_REMOVE, SW_RESTORE, GW_OWNER = 0x0001, 9, 4
SW_MAXIMIZE, SW_HIDE, SW_SHOW = 3, 0, 5
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
ERROR_ALREADY_EXISTS = 183
WAIT_OBJECT_0 = 0
MUTEX_NAME = "Local\\TwisterAutoShapesSingleInstance"
REPLACE_EVENT_NAME = "Local\\TwisterAutoShapesReplace"   # a new instance sets this to make the running one exit

# ---- Tray icon constants ----------------------------------------------------
WM_USER = 0x0400
WM_TRAYICON = WM_USER + 20          # our custom callback message from Shell_NotifyIcon
WM_COMMAND = 0x0111
WM_LBUTTONDBLCLK = 0x0203
WM_RBUTTONUP = 0x0205
GWLP_WNDPROC = -4
NIM_ADD, NIM_MODIFY, NIM_DELETE = 0, 1, 2
NIF_MESSAGE, NIF_ICON, NIF_TIP, NIF_INFO = 0x1, 0x2, 0x4, 0x10
NIIF_INFO = 0x1
IDI_APPLICATION = 32512
MF_STRING = 0x0
TPM_RIGHTBUTTON = 0x0002
ID_TRAY_SHOW, ID_TRAY_EXIT = 1001, 1002
MB_ICONWARNING, MB_TOPMOST = 0x30, 0x40000

# ---- Look ------------------------------------------------------------------
KEY = "#010101"        # colour that turns fully transparent
COLOR = "#39FF14"      # neon green
BAD_COLOR = "#FF4040"  # preview colour when a corner would be off-screen
LINE_W = 1             # line thickness (px)
DOT_R = 3              # corner dot radius (px)
DIM_ALPHA = 0.3        # darkness of the selection overlay (0.1 - 0.6)
MIN_SIZE = 5           # ignore rectangles / edges smaller than this (px)

SHAPES = ["Rectangle", "2-piece (2 connected rectangles)", "4-piece (4 connected polygons)",
          "3-piece (triangle end)", "3-piece (triangle end), inverted"]
SHAPE_KEYS = ["rect", "two", "four", "tri", "tri_inv"]   # internal codes, parallel to SHAPES
DEFAULT_SHAPE_IDX = 1     # F5 starts on the 2-piece (index into SHAPE_KEYS)
DORMER_SHAPES = ["Dormer 2-piece (center split), inverted", "Dormer 2-piece (center split)",
                 "Dormer 3-piece (Y split), inverted", "Dormer 3-piece (Y split)"]
DORMER_KEYS = ["dormer_c_inv", "dormer_c", "dormer_y_inv", "dormer_y"]   # parallel to DORMER_SHAPES
SPLITS = {"Longer side": "long", "First edge (P1-P2)": "first", "Second edge (width)": "second"}
TOOLS = {                # tool code -> (name shown in the GUI, hotkey)
    "rect":   ("Gable/Hip", "F5"),
    "dormer": ("Dormer", "F6"),
    "arch":   ("Gambrel", "F7"),
    "cone":   ("Cone", "F8"),
}
VERSION = "1.10.2"
PIA_URL = "https://eagleviewcloud.sharepoint.com/sites/QualityTeam/SitePages/PIA.aspx"
CONFIG_FILE = r"P:\1_Coordinators\PIA\TAS\TAS_config.ini"   # shared on/off switch, read at every launch
USAGE_LOG = r"P:\1_Coordinators\PIA\TAS\Logs\TAS_usage.csv"   # shared usage log (one row per launch)
TARGET_EXE = "Twister.exe"   # fixed target app; no longer user-configurable in the GUI

# ---- GUI theme (same palette / look as the TTT tool) ---------------------------
UI_FONT = "Consolas"
UI_BLUE = "#0563C1"        # header, footer bar
UI_GOLD = "#FFC72C"        # "PIA" link in the footer (gold on blue)
UI_GREEN = "#1E9E3F"       # switched-on tiles
UI_GREEN_HOVER = "#27B84C" # switched-on tile under the mouse
UI_CONSOLE_BG = "#000000"  # status box background
UI_CONSOLE_OK = "#39FF14"  # status text (neon green, same as the overlay lines)
UI_CONSOLE_ERR = "#FF4040" # status text on errors
UI_LIGHT = "#E4E9F0"       # switched-off tiles (the "inactive tab" colour)
UI_LIGHT_HOVER = "#D3DBE8"
UI_BG = "#F0F0F0"          # window background
UI_PANEL = "#FFFFFF"       # panels
UI_BORDER = "#2B2B2B"      # panel outline
UI_TEXT = "#1B2A41"        # main text
UI_MUTED = "#6B7280"       # small hint text



# ---- Remote config (on/off switch) -------------------------------------------
CONFIG_REQUIRED = True    # True: TAS will not start when the config can't be read (P: unreachable,
                          # file missing/unreadable).  False: it shows the message and runs anyway.
DISABLED_WORDS = {"false", "no", "0", "off", "disabled", "disable"}


def load_config(path=None):
    """Read the shared config file.  Returns (status, cfg):
      status \"ok\"       cfg = {key: value} (keys lower-case; '#' / ';' lines are comments)
             \"no_drive\" the folder isn't reachable (P: not mapped / share down)
             \"no_file\"  the folder is there but the config file isn't
             \"error\"    the file exists but couldn't be read"""
    path = path or CONFIG_FILE
    cfg = {}
    try:
        if not os.path.isdir(os.path.dirname(path)):
            return "no_drive", {}
        if not os.path.isfile(path):
            return "no_file", {}
        with open(path, encoding="utf-8-sig") as f:
            for line in f:
                line = line.strip()
                if not line or line[0] in "#;" or "=" not in line:
                    continue
                key, _, val = line.partition("=")
                cfg[key.strip().lower()] = val.strip()
    except Exception:
        return "error", {}
    return "ok", cfg


def check_startup(path=None):
    """Decide whether TAS may start.  Returns (can_run, message, state) - show `message` in a
    message box whenever it isn't empty.  state: ok / disabled / no_drive / no_file / error."""
    path = path or CONFIG_FILE
    state, cfg = load_config(path)
    if state == "no_drive":
        msg = ("Can't reach the PIA shared folder, so TAS can't check its configuration.\n\n"
               "Make sure the P: drive is connected, then start TAS again.")
    elif state == "no_file":
        msg = "The TAS config file was not found.\n\nPlease contact PIA."
    elif state == "error":
        msg = "The TAS config file could not be read.\n\nPlease contact PIA."
    elif cfg.get("enabled", "true").strip().lower() in DISABLED_WORDS:
        return False, "TAS is disabled.\n\n" + (cfg.get("message")
                                                 or "Please contact PIA for details."), "disabled"
    else:
        return True, "", "ok"
    return (not CONFIG_REQUIRED), msg, state


# ---- Usage log ---------------------------------------------------------------
def log_usage(action="Launch", path=None):
    """Append one row (Timestamp, User, Computer, Action) to the shared usage CSV so PIA can
    see who uses TAS.  Runs in a background thread and never raises: if the P: drive isn't
    mapped, the share is slow, or someone has the CSV open in Excel, the row is skipped /
    retried a few times - logging must never block or break the tool."""
    path = path or USAGE_LOG

    def work():
        now = time.localtime()
        row = [f"{now.tm_mon}/{now.tm_mday}/{now.tm_year} {now.tm_hour:02d}:{now.tm_min:02d}",
               getpass.getuser(), socket.gethostname(), action]
        for _ in range(5):
            try:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                is_new = not os.path.exists(path) or os.path.getsize(path) == 0
                with open(path, "a", newline="", encoding="utf-8") as f:
                    w = csv.writer(f, lineterminator="\r\n")
                    if is_new:
                        w.writerow(["Timestamp", "User", "Computer", "Action"])
                    w.writerow(row)
                return
            except Exception:
                time.sleep(0.4)          # file locked / share busy: try again shortly

    threading.Thread(target=work, daemon=True).start()


def key_to_vk(name):
    return ord(name) if len(name) == 1 else 0x70 + int(name[1:]) - 1


# ---- ctypes signatures -----------------------------------------------------
HOOKPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, ctypes.c_int, wt.WPARAM, wt.LPARAM)
WNDENUMPROC = ctypes.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)

user32.SetWindowsHookExW.argtypes = [ctypes.c_int, HOOKPROC, wt.HINSTANCE, wt.DWORD]
user32.SetWindowsHookExW.restype = wt.HHOOK
user32.CallNextHookEx.argtypes = [wt.HHOOK, ctypes.c_int, wt.WPARAM, wt.LPARAM]
user32.CallNextHookEx.restype = ctypes.c_ssize_t
user32.UnhookWindowsHookEx.argtypes = [wt.HHOOK]
user32.GetForegroundWindow.restype = wt.HWND
user32.SetForegroundWindow.argtypes = [wt.HWND]
user32.IsWindow.argtypes = [wt.HWND]
user32.IsWindowVisible.argtypes = [wt.HWND]
user32.IsIconic.argtypes = [wt.HWND]
user32.ShowWindow.argtypes = [wt.HWND, ctypes.c_int]
user32.GetWindow.argtypes = [wt.HWND, wt.UINT]
user32.GetWindow.restype = wt.HWND
user32.GetWindowTextLengthW.argtypes = [wt.HWND]
user32.GetWindowThreadProcessId.argtypes = [wt.HWND, ctypes.POINTER(wt.DWORD)]
user32.EnumWindows.argtypes = [WNDENUMPROC, wt.LPARAM]
user32.VkKeyScanW.argtypes = [wt.WCHAR]
user32.VkKeyScanW.restype = ctypes.c_short
kernel32.GetModuleHandleW.argtypes = [wt.LPCWSTR]
kernel32.GetModuleHandleW.restype = wt.HMODULE
kernel32.OpenProcess.argtypes = [wt.DWORD, wt.BOOL, wt.DWORD]
kernel32.OpenProcess.restype = wt.HANDLE
kernel32.CloseHandle.argtypes = [wt.HANDLE]
kernel32.QueryFullProcessImageNameW.argtypes = [
    wt.HANDLE, wt.DWORD, wt.LPWSTR, ctypes.POINTER(wt.DWORD)]
kernel32.CreateMutexW.argtypes = [ctypes.c_void_p, wt.BOOL, wt.LPCWSTR]
kernel32.CreateMutexW.restype = wt.HANDLE
kernel32.GetLastError.restype = wt.DWORD
kernel32.CreateEventW.argtypes = [ctypes.c_void_p, wt.BOOL, wt.BOOL, wt.LPCWSTR]
kernel32.CreateEventW.restype = wt.HANDLE
kernel32.SetEvent.argtypes = [wt.HANDLE]
kernel32.WaitForSingleObject.argtypes = [wt.HANDLE, wt.DWORD]
kernel32.WaitForSingleObject.restype = wt.DWORD

shell32 = ctypes.windll.shell32
WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)

# window subclassing (GWLP_WNDPROC) needs the *Ptr variants on 64-bit Windows;
# 32-bit builds don't export them, so fall back to the plain 32-bit versions.
_SetWindowLongPtrW = getattr(user32, "SetWindowLongPtrW", user32.SetWindowLongW)
_GetWindowLongPtrW = getattr(user32, "GetWindowLongPtrW", user32.GetWindowLongW)
_SetWindowLongPtrW.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_void_p]
_SetWindowLongPtrW.restype = ctypes.c_void_p
_GetWindowLongPtrW.argtypes = [wt.HWND, ctypes.c_int]
_GetWindowLongPtrW.restype = ctypes.c_void_p
user32.CallWindowProcW.argtypes = [ctypes.c_void_p, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
user32.CallWindowProcW.restype = ctypes.c_ssize_t
user32.LoadIconW.argtypes = [wt.HINSTANCE, wt.LPCWSTR]
user32.LoadIconW.restype = wt.HICON
user32.CreatePopupMenu.restype = wt.HMENU
user32.AppendMenuW.argtypes = [wt.HMENU, wt.UINT, ctypes.c_void_p, wt.LPCWSTR]
user32.TrackPopupMenu.argtypes = [wt.HMENU, wt.UINT, ctypes.c_int, ctypes.c_int,
                                  ctypes.c_int, wt.HWND, ctypes.c_void_p]
user32.DestroyMenu.argtypes = [wt.HMENU]
user32.PostMessageW.argtypes = [wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
user32.MessageBoxW.argtypes = [wt.HWND, wt.LPCWSTR, wt.LPCWSTR, wt.UINT]


class GUID(ctypes.Structure):
    _fields_ = [("Data1", wt.DWORD), ("Data2", wt.WORD), ("Data3", wt.WORD),
                ("Data4", ctypes.c_ubyte * 8)]


class NOTIFYICONDATAW(ctypes.Structure):
    """The full modern NOTIFYICONDATA layout (Vista+, always present on any
    supported Windows). NIF_MESSAGE | NIF_ICON | NIF_TIP use the first fields;
    NIF_INFO (a tray balloon notification) additionally uses szInfo,
    szInfoTitle and dwInfoFlags."""
    _fields_ = [("cbSize", wt.DWORD), ("hWnd", wt.HWND), ("uID", wt.UINT),
                ("uFlags", wt.UINT), ("uCallbackMessage", wt.UINT),
                ("hIcon", wt.HICON), ("szTip", wt.WCHAR * 128),
                ("dwState", wt.DWORD), ("dwStateMask", wt.DWORD),
                ("szInfo", wt.WCHAR * 256), ("uTimeoutOrVersion", wt.UINT),
                ("szInfoTitle", wt.WCHAR * 64), ("dwInfoFlags", wt.DWORD),
                ("guidItem", GUID), ("hBalloonIcon", wt.HICON)]


class MSLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [("pt", wt.POINT), ("mouseData", wt.DWORD), ("flags", wt.DWORD),
                ("time", wt.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


class KBDLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [("vkCode", wt.DWORD), ("scanCode", wt.DWORD), ("flags", wt.DWORD),
                ("time", wt.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


# ---- Geometry (pure functions) ----------------------------------------------
def box_edge(p1, c):
    """Corner-to-corner drawing: the rectangle spans the 1st point `p1` and the cursor `c`
    (axis-aligned, so no edge can ever be crooked).  Its FIRST EDGE is the SHORTER side, so
    triangle ends / hip ridges / dormer points land on the short ends.  Returns the 2nd
    corner of that first edge (feed it to rect_from_points(p1, edge_end, c)), or None if the
    box is thinner than MIN_SIZE."""
    dx, dy = c[0] - p1[0], c[1] - p1[1]
    if min(abs(dx), abs(dy)) < MIN_SIZE:
        return None
    if abs(dx) <= abs(dy):
        return (c[0], p1[1])            # short side is horizontal
    return (p1[0], c[1])                # short side is vertical


def rect_from_points(p1, p2, p3):
    """Rectangle with edge p1->p2; p3 sets the width (perpendicular distance).
    Returns (corners, width) or None.  Corners are whole pixels and the width offset
    is rounded ONCE and applied to both far corners, so opposite sides are exactly
    equal and parallel (no corner is rounded independently -> no crooked edges)."""
    ux, uy = p2[0] - p1[0], p2[1] - p1[1]
    length = math.hypot(ux, uy)
    if length == 0:
        return None
    nx, ny = -uy / length, ux / length            # unit normal to the edge
    d = (p3[0] - p2[0]) * nx + (p3[1] - p2[1]) * ny
    vx, vy = int(round(nx * d)), int(round(ny * d))
    a = (int(round(p1[0])), int(round(p1[1])))
    b = (int(round(p2[0])), int(round(p2[1])))
    corners = [a, b, (b[0] + vx, b[1] + vy), (a[0] + vx, a[1] + vy)]
    return corners, abs(d)
def split_rectangle(corners, which="long"):
    """Cut rectangle A,B,C,D into two rectangles along the line joining the midpoints
    of two opposite sides.
      which="first"  : cut the first edge A-B (and D-C) in half
      which="second" : cut the second edge B-C (and A-D) in half
      which="long"   : cut whichever of the two is longer
      which="short"  : cut whichever of the two is SHORTER (same logic as the arch tool:
                       the shorter side is divided, the cut runs parallel to the longer side)
    Returns (half1, half2, (m1, m2)).  Each half is 4 corners in order around it;
    half2[0] and half2[3] are the two points shared with half1 (they are m1 and m2).
    m2 is derived from m1 by an integer offset, so the cut is exactly parallel to the
    sides and both halves are exact parallelograms."""
    a, b, c, d = corners
    cut_first = (which == "first"
                 or (which == "long" and math.dist(a, b) >= math.dist(b, c))
                 or (which == "short" and math.dist(a, b) <= math.dist(b, c)))
    if cut_first:
        vx, vy = d[0] - a[0], d[1] - a[1]
        m1 = (int(round((a[0] + b[0]) / 2)), int(round((a[1] + b[1]) / 2)))
        m2 = (m1[0] + vx, m1[1] + vy)
        return [a, m1, m2, d], [m1, b, c, m2], (m1, m2)
    ux, uy = b[0] - a[0], b[1] - a[1]
    m1 = (int(round((b[0] + c[0]) / 2)), int(round((b[1] + c[1]) / 2)))
    m2 = (m1[0] - ux, m1[1] - uy)
    return [a, b, m1, m2], [m1, c, d, m2], (m1, m2)


MIN_RIDGE = 10   # px: closer than this, the two apexes of the 4-piece shape are merged into one


def split_four(corners):
    """Split rectangle A,B,C,D into 4 polygons: a triangle at the A-D end, a
    triangle at the B-C end, and two middle quads split by the line joining
    the triangles' apexes. Each apex sits on the centerline, inset from its
    end by half the rectangle's width (so each triangle's taper is a clean
    45-degree-ish point, matching the corner-to-centerline offset).
    If the ridge L-R would be shorter than MIN_RIDGE px (first edge shorter than or
    about as long as the width), L and R are merged into ONE point at the middle -
    the 4 pieces become 4 triangles meeting there (a pyramid).  Otherwise the two
    apexes sit only a few pixels apart and the same point would be clicked / snapped
    twice, which gives a crooked or missing piece.
    Returns (L, R) - the left and right apex points - or None if the
    rectangle is too thin end-to-end for both apexes to fit."""
    a, b, c, d = corners
    length = math.hypot(b[0] - a[0], b[1] - a[1])
    if length == 0:
        return None
    ux, uy = (b[0] - a[0]) / length, (b[1] - a[1]) / length   # unit vector A->B
    wx, wy = d[0] - a[0], d[1] - a[1]                          # full width vector A->D
    width = math.hypot(wx, wy)
    offset = min(width / 2, length / 2)                        # clamp so apexes don't cross
    hwx, hwy = wx / 2, wy / 2                                  # half-width vector (to centerline)
    L = (int(round(a[0] + ux * offset + hwx)), int(round(a[1] + uy * offset + hwy)))
    R = (int(round(a[0] + ux * (length - offset) + hwx)), int(round(a[1] + uy * (length - offset) + hwy)))
    if math.dist(L, R) < MIN_RIDGE:
        L = R = (int(round(a[0] + ux * length / 2 + hwx)), int(round(a[1] + uy * length / 2 + hwy)))
    return L, R


def build_steps(corners, shape, which, vk_point, vk_close, vk_snap, vk_reuse):
    """Ordered key presses.  Each step is (position or None, virtual-key); the cursor
    is moved to `position` first when it is given."""
    if shape in ("tri", "tri_inv"):
        return build_tri_steps(corners, shape == "tri_inv", vk_point, vk_close, vk_snap, vk_reuse)
    if shape == "four":
        a, b, c, d = corners
        res = split_four(corners)
        if res is None:
            return []
        L, R = res
        if L == R:                                   # merged apex: 4 triangles around one point
            M = L
            steps = [(a, vk_point), (d, vk_point), (M, vk_point), (None, vk_close)]       # left triangle
            steps += [(b, vk_point), (M, vk_reuse),
                      (a, vk_reuse), (None, vk_close)]                    # top triangle (new point first)
            steps += [(c, vk_point), (M, vk_reuse),
                      (d, vk_reuse), (None, vk_close)]                    # bottom triangle (new point first)
            steps += [(b, vk_reuse), (c, vk_reuse),
                      (M, vk_reuse), (None, vk_close)]                    # right triangle
            return steps
        steps = [(a, vk_point), (d, vk_point), (L, vk_point), (None, vk_close)]           # left triangle
        steps += [(b, vk_point), (R, vk_point),
                  (L, vk_reuse), (a, vk_reuse), (None, vk_close)]         # top-mid quad (new points first)
        steps += [(c, vk_point), (d, vk_reuse),
                  (L, vk_reuse), (R, vk_reuse), (None, vk_close)]         # bottom-mid quad (new point first)
        steps += [(b, vk_reuse), (c, vk_reuse),
                  (R, vk_reuse), (None, vk_close)]                        # right triangle
        return steps
    if shape != "two":
        return [(pt, vk_point) for pt in corners] + [(None, vk_close)]
    half1, half2, _ = split_rectangle(corners, which)
    steps = [(pt, vk_point) for pt in half1] + [(None, vk_close)]
    m1, c, d, m2 = half2                      # m1/m2 are shared with the 1st rectangle
    for pt in (c, d):                         # new corners first
        steps.append((pt, vk_point))
    for pt in (m2, m1):                       # then the shared points, in cyclic order
        steps += [(pt, vk_reuse)]
    steps.append((None, vk_close))
    return steps


def split_tri_end(corners, inverted=False):
    """Rectangle A,B,C,D cut into 3 pieces: a triangle on the B-C end (the 2nd-click end;
    the A-D end when `inverted`), and two quads split by a centerline running from the
    middle of the far edge to the triangle's top corner.
      frame = the corner order used (ends swapped when inverted), t = middle of the far
      edge, m = the triangle's top corner, on the centerline half the width in from the
      triangle's edge (clamped to the rectangle).  t and m share one rounding, so the
      centerline is exactly parallel to the sides.
    If the centerline would be shorter than MIN_RIDGE px, m is merged into t and the
    pieces become three triangles fanning out from that one point (fan=True).
    Returns {frame, t, m, fan, lines} or None for a flat rectangle."""
    a, b, c, d = corners
    if inverted:
        a, b, c, d = b, a, d, c                                   # swap the two ends
    length = math.hypot(b[0] - a[0], b[1] - a[1])
    wx, wy = d[0] - a[0], d[1] - a[1]
    width = math.hypot(wx, wy)
    if length == 0 or width == 0:
        return None
    ux, uy = (b[0] - a[0]) / length, (b[1] - a[1]) / length       # unit vector A->B
    t = (int(round(a[0] + wx / 2)), int(round(a[1] + wy / 2)))    # middle of the far edge A-D
    run = length - min(width / 2, length)                         # t -> m, along A->B
    m = (t[0] + int(round(ux * run)), t[1] + int(round(uy * run)))
    fan = math.dist(t, m) < MIN_RIDGE
    if fan:
        m = t
    return {"frame": [a, b, c, d], "t": t, "m": m, "fan": fan,
            "lines": [(t, m), (m, b), (m, c)]}


def build_tri_steps(corners, inverted, vk_point, vk_close, vk_snap, vk_reuse):
    """Ordered key presses for the triangle-end shape (same step format as build_steps).
      left quad  [A, T, M, B]: b at all 4, then y.
      right quad [T, D, C, M]: b at D and C, a at M then T (already placed), y.
      triangle   [B, C, M]:    a at all 3, then y.
    Merged-apex case (fan): left [A, T, B] b at all 3; right [T, D, C] b at D and C,
    a at T; triangle [B, C, T] a at all 3."""
    g = split_tri_end(corners, inverted)
    if g is None:
        return []
    a, b, c, d = g["frame"]
    t, m = g["t"], g["m"]
    if g["fan"]:
        steps = [(a, vk_point), (t, vk_point), (b, vk_point), (None, vk_close)]
        steps += [(d, vk_point), (c, vk_point), (t, vk_reuse), (None, vk_close)]
    else:
        steps = [(a, vk_point), (t, vk_point), (m, vk_point), (b, vk_point), (None, vk_close)]
        steps += [(d, vk_point), (c, vk_point), (m, vk_reuse), (t, vk_reuse), (None, vk_close)]
    steps += [(b, vk_reuse), (c, vk_reuse), (m, vk_reuse), (None, vk_close)]
    return steps


def dormer_geometry(corners, shape):
    """Pointed dormer on rectangle A,B,C,D (A->B is the 1st/2nd click edge, A-D the top).
    The B-C end gets a roof point: `apex` on the centerline, half the width beyond B-C.
    `m` is the junction on the centerline: the top-middle of A-D for the 2-piece split
    (\"dormer_c\"), or half the width below A-D for the 3-piece Y split (\"dormer_y\") -
    exactly where the two arms A-m and D-m (and the hips B-apex, C-apex) run at 45 degrees.  All three points share one rounding, so they stay
    exactly on one line.  Returns {outline, m, apex, lines} or None for a flat rectangle.
    outline = [A, B, apex, C, D]; lines = the dashed inner cuts (point pairs).
    A shape code ending in "_inv" is the same dormer turned around: the roof point is on
    the 1st-click end instead (the A-D / B-C ends swap roles), so the flat edge is the 2nd
    click's edge.  `frame` is the corner order actually used, `y` says whether it is the Y split."""
    inverted = shape.endswith("_inv")
    if inverted:
        shape = shape[:-4]
        corners = [corners[1], corners[0], corners[3], corners[2]]   # swap the two ends
    a, b, c, d = corners
    length = math.hypot(b[0] - a[0], b[1] - a[1])
    wx, wy = d[0] - a[0], d[1] - a[1]
    width = math.hypot(wx, wy)
    if length == 0 or width == 0:
        return None
    ux, uy = (b[0] - a[0]) / length, (b[1] - a[1]) / length    # unit vector A->B (toward the point)
    t = (int(round(a[0] + wx / 2)), int(round(a[1] + wy / 2)))  # top-middle, on edge A-D

    def along(dist):
        return (t[0] + int(round(ux * dist)), t[1] + int(round(uy * dist)))

    hw = math.hypot(t[0] - a[0], t[1] - a[1])      # half the width, as the whole-pixel distance A->t
    apex = along(length + hw)                       # B->apex runs at 45 degrees
    y_split = shape == "dormer_y"
    if y_split:
        m = along(hw)                               # A->m and D->m run at 45 degrees too
        lines = [(a, m), (d, m), (m, apex)]
    else:
        m = t
        lines = [(m, apex)]
    return {"outline": [a, b, apex, c, d], "m": m, "apex": apex, "lines": lines,
            "frame": [a, b, c, d], "y": y_split}


def build_dormer_steps(corners, shape, vk_point, vk_close, vk_snap, vk_reuse):
    """Ordered key presses for a dormer (same step format as build_steps).
      left piece  [A, B, apex, m]: b at all 4 corners, then y.
      right piece [m, apex, C, D]: b at C and D, a at m then apex (already placed), y.
      Y split only - top triangle [A, m, D]: a at all 3, then y."""
    g = dormer_geometry(corners, shape)
    if g is None:
        return []
    a, b, c, d = g["frame"]
    m, apex = g["m"], g["apex"]
    steps = [(a, vk_point), (b, vk_point), (apex, vk_point), (m, vk_point), (None, vk_close)]
    steps += [(c, vk_point), (d, vk_point),
              (m, vk_reuse), (apex, vk_reuse), (None, vk_close)]
    if g["y"]:
        steps += [(a, vk_reuse), (m, vk_reuse),
                  (d, vk_reuse), (None, vk_close)]
    return steps


ARCH_SIDES = [3, 4, 5, 6]   # piece-count options for the arch tool (mouse wheel list)


def split_arch(corners, n):
    """Cut rectangle A,B,C,D into `n` equal strips.  The SHORTER side is divided, so the
    cuts run parallel to the longer side (long thin strips, whichever edge was clicked first).
    P[0..n] are the division points on one side, Q[0..n] the matching points on the opposite
    side (Q[i] = P[i] + one integer offset, so every cut is exactly parallel to the sides).
    Strip i (1..n) is the quad P[i-1], P[i], Q[i], Q[i-1].
    Returns {"P": [...], "Q": [...]} or None if a strip would be thinner than 2 px."""
    a, b, c, d = corners
    if math.dist(a, b) <= math.dist(a, d):        # AB is the short side: divide it
        end, off = b, (d[0] - a[0], d[1] - a[1])
    else:                                         # AD is the short side: divide it
        end, off = d, (b[0] - a[0], b[1] - a[1])
    def rnd(v):
        return int(math.floor(v + 0.5))           # round half up (Python's round() is half-to-even)
    P = [(rnd(a[0] + (end[0] - a[0]) * i / n),
          rnd(a[1] + (end[1] - a[1]) * i / n)) for i in range(n + 1)]
    Q = [(x + off[0], y + off[1]) for x, y in P]
    if any(math.dist(P[i - 1], P[i]) < 2 for i in range(1, n + 1)):
        return None
    return {"P": P, "Q": Q}


def build_arch_steps(corners, n, vk_point, vk_close, vk_snap, vk_reuse):
    """Ordered key presses for the arch (same step format as build_steps).
      strip 1:   b at P0, P1, Q1, Q0, then y.
      strip i>1: b at its 2 new points P[i], Q[i]; a at the 2 shared points
                 (Q[i-1], P[i-1], in cyclic order); then y."""
    g = split_arch(corners, n)
    if g is None:
        return []
    P, Q = g["P"], g["Q"]
    steps = [(P[0], vk_point), (P[1], vk_point), (Q[1], vk_point), (Q[0], vk_point),
             (None, vk_close)]
    for i in range(2, n + 1):
        steps += [(P[i], vk_point), (Q[i], vk_point),
                  (Q[i - 1], vk_reuse), (P[i - 1], vk_reuse), (None, vk_close)]
    return steps


CONE_SIDES = [4, 6, 8, 12]   # piece-count options for the cone tool


def polygon_from_points(center, p2, sides):
    """Regular polygon with `sides` vertices around `center`; p2 sets the radius
    and rotation (it becomes the first vertex). Returns a list of vertices, or
    None if center and p2 coincide."""
    dx, dy = p2[0] - center[0], p2[1] - center[1]
    radius = math.hypot(dx, dy)
    if radius == 0:
        return None
    start_ang = math.atan2(dy, dx)
    verts = []
    for i in range(sides):
        ang = start_ang + 2 * math.pi * i / sides
        verts.append((int(round(center[0] + radius * math.cos(ang))),
                     int(round(center[1] + radius * math.sin(ang)))))
    return verts


def build_cone_steps(center, verts, vk_point, vk_close, vk_snap, vk_reuse):
    """Ordered key presses for a cone: N triangular wedges fanning out from
    `center`, each wedge being (center, verts[i], verts[i+1]).  Points shared
    with an earlier wedge (the center, and the previous wedge's outer vertex)
    are snapped + reused instead of re-clicked."""
    n = len(verts)
    steps = [(center, vk_point), (verts[0], vk_point), (verts[1], vk_point),
             (None, vk_close)]
    for i in range(1, n):
        j = (i + 1) % n
        last = i == n - 1
        steps += [(center, vk_reuse), (verts[i], vk_reuse)]
        if last:
            steps += [(verts[j], vk_reuse)]
        else:
            steps.append((verts[j], vk_point))
        steps.append((None, vk_close))
    return steps
# ---- end geometry ------------------------------------------------------------


# ---- Window / process helpers ---------------------------------------------
def exe_of_hwnd(hwnd):
    """Lower-case exe file name (e.g. 'twister.exe') that owns a window, or ''."""
    if not hwnd:
        return ""
    pid = wt.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    if not pid.value:
        return ""
    h = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid.value)
    if not h:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(1024)
        size = wt.DWORD(1024)
        if kernel32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(size)):
            return buf.value.rsplit("\\", 1)[-1].lower()
    finally:
        kernel32.CloseHandle(h)
    return ""


def find_windows(exe_name):
    """Visible top-level windows (with a title) owned by exe_name, top of z-order first."""
    found = []

    def cb(hwnd, _):
        try:
            if (user32.IsWindowVisible(hwnd) and not user32.GetWindow(hwnd, GW_OWNER)
                    and user32.GetWindowTextLengthW(hwnd) > 0
                    and exe_of_hwnd(hwnd) == exe_name):
                found.append(hwnd)
        except Exception:
            pass
        return True

    proc = WNDENUMPROC(cb)
    user32.EnumWindows(proc, 0)
    return found


def focus_window(hwnd, maximize=False):
    """Bring a window to the foreground.  Returns True once it is the foreground window.
    With maximize=True, also maximizes it once focus is confirmed."""
    if user32.IsIconic(hwnd):
        user32.ShowWindow(hwnd, SW_RESTORE)
    for attempt in range(2):
        if attempt == 1:   # fallback: tap Alt so Windows allows the focus change
            user32.keybd_event(VK_MENU, 0, 0, 0)
            user32.keybd_event(VK_MENU, 0, KEYEVENTF_KEYUP, 0)
        user32.SetForegroundWindow(hwnd)
        for _ in range(10):
            time.sleep(0.03)
            if user32.GetForegroundWindow() == hwnd:
                if maximize:
                    user32.ShowWindow(hwnd, SW_MAXIMIZE)
                return True
    return False


# ---- Tracing speed (seconds) -------------------------------------------------
# Total time per point is roughly MOVE_POLL + MOVE_SETTLE + KEY_HOLD + STEP_INTERVAL_MS.
# If Twister ever misses a point, raise MOVE_SETTLE / KEY_HOLD a little (e.g. 0.05).
MOVE_POLL = 0.03          # wait after SetCursorPos before checking the cursor arrived
MOVE_SETTLE = 0.03        # let Twister see the mouse move before the key is pressed
KEY_HOLD = 0.03           # how long each key stays down (cursor is held still meanwhile)
PRE_KEY_DWELL = 0.03      # extra time the cursor rests on the exact spot BEFORE the key goes down
POST_KEY_DWELL = 0.03     # time the cursor keeps resting there AFTER the key is released
STEP_INTERVAL_MS = 30     # gap between steps
CLOSE_PAUSE_MS = 30       # extra wait after the close key: Twister is busy finishing the piece
REUSE_APPROACH_PX = 3     # a re-used point is approached from this many px away, then the cursor
                          # lands exactly on it, so Twister gets a fresh hover on that point (0 = off)


# ---- Input helpers ---------------------------------------------------------
def char_to_vk(ch):
    if not ch:
        return None
    r = user32.VkKeyScanW(ch)
    return None if r == -1 else r & 0xFF


def send_key(vk, pos=None):
    """Press and release `vk`.  With `pos`, the cursor is kept ON that exact pixel the whole
    time: it rests there before the key goes down, stays put while the key is held, and
    rests there again after the release - so the app can't create the point while the cursor
    is already on its way to the next one.  Returns (cursor at key-down, cursor after the
    final dwell)."""
    scan = user32.MapVirtualKeyW(vk, 0)
    if pos is not None:
        time.sleep(PRE_KEY_DWELL)
        if not cursor_near(*pos):                 # nudged during the dwell: put it back
            move_to(*pos)
            time.sleep(MOVE_SETTLE)
    at_press = cursor_pos()
    user32.keybd_event(vk, scan, 0, 0)
    time.sleep(KEY_HOLD)
    user32.keybd_event(vk, scan, KEYEVENTF_KEYUP, 0)
    if pos is not None:
        time.sleep(POST_KEY_DWELL)
    return at_press, cursor_pos()


def modifiers_down():
    return any(user32.GetAsyncKeyState(vk) & 0x8000 for vk in (VK_SHIFT, VK_CONTROL, VK_MENU))


def mods_now():
    m = 0
    if user32.GetAsyncKeyState(VK_CONTROL) & 0x8000:
        m |= MOD_CONTROL
    if user32.GetAsyncKeyState(VK_MENU) & 0x8000:
        m |= MOD_ALT
    if user32.GetAsyncKeyState(VK_SHIFT) & 0x8000:
        m |= MOD_SHIFT
    return m


def cursor_pos():
    pt = wt.POINT()
    user32.GetCursorPos(ctypes.byref(pt))
    return pt.x, pt.y


def move_to(x, y):
    """Move the cursor onto the EXACT pixel and confirm it arrived; retry if something
    pushed it away.  Only if the exact pixel can't be held after 5 tries is a +-1 px
    miss accepted (the miss is reported in the placement log)."""
    x, y = int(round(x)), int(round(y))
    for _ in range(5):
        user32.SetCursorPos(x, y)
        time.sleep(MOVE_POLL)
        if cursor_pos() == (x, y):
            return True
    cx, cy = cursor_pos()
    return abs(cx - x) <= 1 and abs(cy - y) <= 1


def cursor_near(x, y, tol=0):
    cx, cy = cursor_pos()
    return abs(cx - int(round(x))) <= tol and abs(cy - int(round(y))) <= tol


# ---- Mouse hook: capture clicks / lock the mouse ----------------------------
BUTTON_DOWN = {0x0201: "left", 0x0204: "right", 0x0207: "middle", 0x020B: "x"}
BUTTON_UP = {0x0202: 0x0201, 0x0205: 0x0204, 0x0208: 0x0207, 0x020C: 0x020B}  # up -> its down
WM_MOUSEWHEEL, WM_MOUSEHWHEEL = WHEEL_MSGS = (0x020A, 0x020E)


class MouseLock:
    """Low-level mouse hook that keeps *physical* mouse input away from other apps.

    mode "capture": buttons and wheel are swallowed, so no app (Twister included) ever
                    sees your clicks; left/right presses are reported through click_q.
                    Movement passes through so you can still aim.
    mode "lock":    every physical mouse event is swallowed.
    mode "off":     nothing new is swallowed; the release of a press we already swallowed
                    is still swallowed (no stray release reaches an app), then the hook
                    removes itself.
    Input injected by this script (SetCursorPos) always passes through.
    A deadline removes the hook automatically as a safety net."""

    def __init__(self):
        self.click_q = queue.Queue()
        self.mode = "off"
        self._stop = threading.Event()
        self._ready = threading.Event()
        self._thread = None
        self._proc = None
        self._deadline = 0.0
        self._pending = set()      # presses we swallowed whose release we still owe a swallow

    def engage(self, mode, timeout):
        self.release()
        self._stop.clear()
        self._ready.clear()
        self._pending.clear()
        self.mode = mode
        self._deadline = time.time() + timeout
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        self._ready.wait(1.0)

    def set_mode(self, mode, timeout):
        self.mode = mode
        self._deadline = time.time() + timeout

    def release(self):
        self._stop.set()
        t, self._thread = self._thread, None
        if t is not None and t is not threading.current_thread():
            t.join(1.0)
        self.mode = "off"

    def drain(self):
        try:
            while True:
                self.click_q.get_nowait()
        except queue.Empty:
            pass

    def _run(self):
        def proc(n_code, w_param, l_param):
            try:
                if n_code >= 0:
                    info = ctypes.cast(l_param, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                    if not (info.flags & LLMHF_INJECTED):
                        mode = self.mode
                        if w_param in BUTTON_UP:
                            down = BUTTON_UP[w_param]
                            if down in self._pending:      # we ate the press, eat the release
                                self._pending.discard(down)
                                return 1
                            # otherwise the press wasn't ours: let the release through
                        elif mode == "lock":
                            if w_param in BUTTON_DOWN:
                                self._pending.add(w_param)
                            return 1
                        elif mode == "capture":
                            if w_param in BUTTON_DOWN:
                                self._pending.add(w_param)
                                if w_param == 0x0201:
                                    self.click_q.put(("left", info.pt.x, info.pt.y))
                                elif w_param == 0x0204:
                                    self.click_q.put(("right", info.pt.x, info.pt.y))
                                return 1
                            if w_param in WHEEL_MSGS:
                                if w_param == WM_MOUSEWHEEL:
                                    delta = ctypes.c_short((info.mouseData >> 16) & 0xFFFF).value
                                    direction = 1 if delta > 0 else -1
                                    self.click_q.put(("wheel", direction, info.pt.x, info.pt.y))
                                return 1
            except Exception:
                pass
            return user32.CallNextHookEx(None, n_code, w_param, l_param)

        self._proc = HOOKPROC(proc)   # keep a reference so it isn't garbage collected
        hook = user32.SetWindowsHookExW(
            WH_MOUSE_LL, self._proc, kernel32.GetModuleHandleW(None), 0)
        self._ready.set()
        if not hook:
            return
        msg = wt.MSG()
        try:
            while (not self._stop.is_set() and time.time() < self._deadline
                   and not (self.mode == "off" and not self._pending)):
                if user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, PM_REMOVE):
                    user32.TranslateMessage(ctypes.byref(msg))
                    user32.DispatchMessageW(ctypes.byref(msg))
                else:
                    time.sleep(0.005)
        finally:
            user32.UnhookWindowsHookEx(hook)


# ---- Hotkey (context-aware) ------------------------------------------------
class HotkeyListener(threading.Thread):
    """Low-level keyboard hook.  Unlike RegisterHotKey it can leave the key alone
    when the target app is NOT focused, so Shift+R still types a capital R
    everywhere else.  Injected keys (our own b / y presses) are ignored.
    Supports several independently-named hotkeys sharing one hook (e.g. one for
    rectangles, one for cones)."""

    def __init__(self, ui_q):
        super().__init__(daemon=True)
        self.ui_q = ui_q
        self.combos = {"rect": (0, key_to_vk("F5")), "cone": (0, key_to_vk("F8")),
                       "dormer": (0, key_to_vk("F6")), "arch": (0, key_to_vk("F7"))}
        self.target_exe = TARGET_EXE.lower()
        self.only_focused = True
        self.enabled = set(self.combos)   # hotkeys that are switched on (GUI checkboxes)
        self._held = {name: False for name in self.combos}
        self._quit = False
        self._proc = None

    def set_hotkey(self, name, mods, vk):
        self.combos[name] = (mods, vk)
        self._held[name] = False
        self.ui_q.put(("hk_set", name))

    def set_enabled(self, name, on):
        (self.enabled.add if on else self.enabled.discard)(name)
        self._held[name] = False

    def stop(self):
        self._quit = True

    def _on_key(self, n_code, w_param, l_param):
        try:
            if n_code >= 0:
                info = ctypes.cast(l_param, ctypes.POINTER(KBDLLHOOKSTRUCT)).contents
                if not (info.flags & LLKHF_INJECTED):
                    for name, (mods, vk) in self.combos.items():
                        if info.vkCode != vk or name not in self.enabled:
                            continue
                        if w_param in (WM_KEYDOWN, WM_SYSKEYDOWN):
                            if self._held[name]:                # auto-repeat: keep swallowing
                                return 1
                            if mods_now() == mods and (
                                    not self.only_focused
                                    or exe_of_hwnd(user32.GetForegroundWindow()) == self.target_exe):
                                self._held[name] = True
                                pt = wt.POINT()
                                user32.GetCursorPos(ctypes.byref(pt))
                                self.ui_q.put(("trigger", (name, (pt.x, pt.y))))
                                return 1
                        elif w_param in (WM_KEYUP, WM_SYSKEYUP) and self._held[name]:
                            self._held[name] = False
                            return 1
        except Exception:
            pass
        return user32.CallNextHookEx(None, n_code, w_param, l_param)

    def run(self):
        self._proc = HOOKPROC(self._on_key)
        hook = user32.SetWindowsHookExW(
            WH_KEYBOARD_LL, self._proc, kernel32.GetModuleHandleW(None), 0)
        if not hook:
            self.ui_q.put(("hk_failed", None))
            return
        msg = wt.MSG()
        try:
            while not self._quit:
                if user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, PM_REMOVE):
                    user32.TranslateMessage(ctypes.byref(msg))
                    user32.DispatchMessageW(ctypes.byref(msg))
                else:
                    time.sleep(0.005)
        finally:
            user32.UnhookWindowsHookEx(hook)


# ---- Tray icon --------------------------------------------------------------
class TrayIcon:
    """Puts an icon in the system tray for a Tk toplevel by subclassing its
    window procedure (no pip installs - just Shell_NotifyIcon + ctypes).
    Double-click or the "Show window" menu item calls on_show(); "Exit"
    calls on_exit()."""

    def __init__(self, hwnd, tip, on_show, on_exit):
        self.hwnd = hwnd
        self.on_show = on_show
        self.on_exit = on_exit
        self._new_proc = WNDPROC(self._wnd_proc)
        self._old_proc = _GetWindowLongPtrW(hwnd, GWLP_WNDPROC)
        _SetWindowLongPtrW(hwnd, GWLP_WNDPROC,
                           ctypes.cast(self._new_proc, ctypes.c_void_p))
        self._nid = NOTIFYICONDATAW()
        self._nid.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
        self._nid.hWnd = hwnd
        self._nid.uID = 1
        self._nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP
        self._nid.uCallbackMessage = WM_TRAYICON
        self._nid.hIcon = user32.LoadIconW(0, ctypes.cast(IDI_APPLICATION, wt.LPCWSTR))
        self._nid.szTip = tip
        shell32.Shell_NotifyIconW(NIM_ADD, ctypes.byref(self._nid))

    def notify(self, title, msg, timeout_ms=4000):
        """Pop a balloon tip from the tray icon (e.g. to say the tool has started,
        since the GUI itself stays hidden)."""
        self._nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP | NIF_INFO
        self._nid.szInfo = msg
        self._nid.szInfoTitle = title
        self._nid.uTimeoutOrVersion = timeout_ms
        self._nid.dwInfoFlags = NIIF_INFO
        shell32.Shell_NotifyIconW(NIM_MODIFY, ctypes.byref(self._nid))

    def _wnd_proc(self, hwnd, msg, wparam, lparam):
        if msg == WM_TRAYICON:
            if lparam == WM_LBUTTONDBLCLK:
                self.on_show()
            elif lparam == WM_RBUTTONUP:
                self._show_menu()
            return 0
        if msg == WM_COMMAND:
            cmd = wparam & 0xFFFF
            if cmd == ID_TRAY_SHOW:
                self.on_show()
            elif cmd == ID_TRAY_EXIT:
                self.on_exit()
            return 0
        return user32.CallWindowProcW(self._old_proc, hwnd, msg, wparam, lparam)

    def _show_menu(self):
        pt = wt.POINT()
        user32.GetCursorPos(ctypes.byref(pt))
        menu = user32.CreatePopupMenu()
        user32.AppendMenuW(menu, MF_STRING, ID_TRAY_SHOW, "Show window")
        user32.AppendMenuW(menu, MF_STRING, ID_TRAY_EXIT, "Exit")
        user32.SetForegroundWindow(self.hwnd)   # so the menu closes if it loses focus
        user32.TrackPopupMenu(menu, TPM_RIGHTBUTTON, pt.x, pt.y, 0, self.hwnd, None)
        user32.PostMessageW(self.hwnd, 0, 0, 0)
        user32.DestroyMenu(menu)

    def remove(self):
        try:
            shell32.Shell_NotifyIconW(NIM_DELETE, ctypes.byref(self._nid))
        except Exception:
            pass
        try:
            _SetWindowLongPtrW(self.hwnd, GWLP_WNDPROC, self._old_proc)
        except Exception:
            pass


# ---- App -------------------------------------------------------------------
class App:
    HINTS = [
        "Click the first corner of the rectangle   (Esc = cancel)",
        "Click the opposite corner - width and height follow the cursor   (scroll = change shape, Backspace / right-click = undo)",
    ]
    DORMER_HINTS = [
        "Click point 1 - the top of the side edge   (Esc = cancel)",
        "Click the opposite corner - width and height follow the cursor   (scroll = change shape, Backspace / right-click = undo)",
    ]
    CONE_HINTS = [
        "Click a point on the outer ring of the cone (a vertex)   (Esc = cancel)",
    ]

    def __init__(self, root):
        self.root = root
        self.busy = False
        self.ui_q = queue.Queue()
        self.lock = MouseLock()
        self.selecting = False
        self.ov = self.dw = None
        self.exe = TARGET_EXE.lower()
        self.target_hwnd = None
        self.vk_point = self.vk_close = self.vk_snap = self.vk_reuse = None
        self.mode = "rect"        # "rect", "cone", "dormer" or "arch" - which tool is currently active
        self.cur_shape, self.cur_split, self.steps = "rect", "short", []
        self.shape_idx = 0
        self.cone_idx = CONE_SIDES.index(8)   # default piece-count: octagon
        self.dormer_idx = 0
        self.arch_idx = 0      # default piece-count: 3
        self.last_pt = None    # last click / cursor position - where the tooltip anchors
        self.was_visible = False   # was the window shown before the current draw?
        self.auto_first = None     # cursor position at hotkey press = automatic 1st point
        self.place_log = []        # (step, key, intended pos, actual cursor pos) of the current run

        # -- fixed settings (no longer exposed in the GUI)
        self.point_key = "b"
        self.close_key = "y"
        self.snap_key = "s"
        self.reuse_key = "a"
        self.delay = 0            # seconds before placing starts
        self.interval = STEP_INTERVAL_MS   # ms between steps (see tracing-speed constants)
        self.lock_mouse = True
        self.dry = False
        self.snap = True          # snap near-horizontal/vertical edges

        root.title(f"TAS - Twister Auto Shapes v{VERSION}")
        root.attributes("-topmost", True)
        root.resizable(False, False)
        # the window is shown at start (not minimized); the tray icon is added at the end of __init__

        # hidden settings (no widgets): fixed values the drawing code still reads
        self.cone_sides = tk.IntVar(value=8)
        self.only_focused = tk.BooleanVar(value=True)
        self.show_tooltips = tk.BooleanVar(value=False)
        self.status = tk.StringVar(value="")      # last message (errors are shown in a message box)

        # -- layout (styled like the TTT tool): blue header, a "Tools" group with the
        # description and one toggle tile per hotkey, a "Status" group, and a blue footer bar.
        root.configure(bg=UI_BG)
        self.enabled_vars = {name: tk.BooleanVar(value=True) for name in TOOLS}
        self.tiles = {}

        header = tk.Frame(root, bg=UI_BLUE)
        header.pack(side="top", fill="x")
        tk.Label(header, text="TAS - Twister Auto Shapes", bg=UI_BLUE, fg="white",
                 font=(UI_FONT, 15, "bold"), anchor="w", padx=16, pady=12).pack(fill="x")

        footer = tk.Frame(root, bg=UI_BLUE)
        footer.pack(side="bottom", fill="x")
        foot_font = ("Segoe UI Symbol", 9)     # one font for star + text -> same baseline
        link = tk.Label(footer, text="\u2605 PIA", bg=UI_BLUE, fg=UI_GOLD, cursor="hand2",
                        font=(foot_font[0], foot_font[1], "bold"), padx=10, pady=3)
        link.pack(side="left")
        tk.Label(footer, text=f"Version {VERSION}", bg=UI_BLUE, fg="white",
                 font=foot_font, padx=10, pady=3).pack(side="right")
        link.bind("<Button-1>", lambda _e: webbrowser.open(PIA_URL))

        body = tk.Frame(root, bg=UI_BG, padx=14, pady=12)
        body.pack(side="top", fill="both", expand=True)

        def group(title, **pack):
            g = tk.LabelFrame(body, text=f" {title} ", bg=UI_BG, fg=UI_TEXT,
                              font=(UI_FONT, 9), bd=1, relief="groove", padx=10, pady=8)
            g.pack(fill="x", **pack)
            return g

        tools = group("Tools")
        panel = tk.Frame(tools, bg=UI_PANEL, highlightbackground=UI_BORDER,
                         highlightthickness=1, padx=16, pady=14)
        panel.pack(fill="x")
        tk.Label(panel, bg=UI_PANEL, fg=UI_TEXT, font=(UI_FONT, 9), wraplength=400,
                 justify="left", anchor="w", text=(
                     "Draws gable/hip, dormer, gambrel and cone shapes in Twister.exe for you: "
                     "press the key while Twister is focused, then click the opposite corner."
                 )).pack(fill="x")
        grid = tk.Frame(panel, bg=UI_PANEL)
        grid.pack(fill="x", pady=(12, 6))
        grid.columnconfigure((0, 1), weight=1, uniform="tile")
        for i, (name, (title, key)) in enumerate(TOOLS.items()):
            tile = tk.Label(grid, text=f"{key} - {title}", font=(UI_FONT, 10, "bold"),
                            pady=9, cursor="hand2")
            tile.grid(row=i // 2, column=i % 2, sticky="ew", pady=3,
                      padx=(0, 4) if i % 2 == 0 else (4, 0))
            tile.bind("<Button-1>", lambda _e, n=name: self.flip_hotkey(n))
            tile.bind("<Enter>", lambda _e, n=name: self.refresh_tile(n, hover=True))
            tile.bind("<Leave>", lambda _e, n=name: self.refresh_tile(n))
            self.tiles[name] = tile
            self.refresh_tile(name)
        tk.Label(panel, text="Click a tile to switch its hotkey on / off.", bg=UI_PANEL,
                 fg=UI_MUTED, font=(UI_FONT, 8), anchor="w").pack(fill="x")

        stat = group("Status", pady=(10, 0))
        sbox = tk.Frame(stat, bg=UI_CONSOLE_BG, highlightbackground=UI_BORDER, highlightthickness=1)
        sbox.pack(fill="x")
        self.status_accent = tk.Frame(sbox, bg=UI_CONSOLE_OK, width=5)   # turns red on errors
        self.status_accent.pack(side="left", fill="y")
        self.status_lbl = tk.Label(sbox, textvariable=self.status, bg=UI_CONSOLE_BG, fg=UI_CONSOLE_OK,
                                   anchor="w", justify="left", wraplength=385, height=2,
                                   font=(UI_FONT, 9), padx=10, pady=8)
        self.status_lbl.pack(side="left", fill="x", expand=True)
        self.set_status("Ready - press " + ", ".join(k for _, k in TOOLS.values())
                        + " while Twister is focused.")

        # -- hotkey listener
        self.hk = HotkeyListener(self.ui_q)
        self.hk.start()
        # a newer instance sets this event to ask us to exit (see acquire_single_instance_lock)
        self.replace_evt = kernel32.CreateEventW(None, False, False, REPLACE_EVENT_NAME)
        root.after(50, self.poll)
        root.protocol("WM_DELETE_WINDOW", self.quit)

        # -- tray icon: the window starts visible; the tray icon lets you bring it back
        # ("Show window" / double-click) if it was hidden, and exit from there.
        root.update_idletasks()   # make sure the win32 window actually exists
        main_hwnd = user32.GetParent(root.winfo_id()) or root.winfo_id()
        self.tray = TrayIcon(main_hwnd, "Twister Auto Shapes",
                             self.show_from_tray, self.exit_from_tray)
        self.tray.notify("Twister Auto Shapes",
                         "Ready. In " + TARGET_EXE + ": "
                         + ", ".join(f"{k} = {n}" for n, k in TOOLS.values()) + ".")

        # bring Twister to the front, maximized, as soon as the tool starts -
        # best-effort: does nothing if Twister.exe isn't running yet
        root.after(300, self.focus_target_at_startup)

        log_usage("Launch")      # who started TAS (shared usage log)

    def focus_target_at_startup(self):
        wins = find_windows(self.exe)
        if wins:
            self.target_hwnd = wins[0]
            focus_window(self.target_hwnd, maximize=True)

    # ---- tray ---------------------------------------------------------------
    def show_from_tray(self):
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    def exit_from_tray(self):
        self.quit()

    # ---- helpers -----------------------------------------------------------
    def set_status(self, text, error=False):
        self.status.set(text)
        lbl = getattr(self, "status_lbl", None)
        if lbl is not None:
            col = UI_CONSOLE_ERR if error else UI_CONSOLE_OK     # green normally, red on errors
            lbl.config(fg=col)
            self.status_accent.config(bg=col)

    def refresh_tile(self, name, hover=False):
        """Repaint a hotkey tile: green = switched on, light grey = switched off."""
        on = self.enabled_vars[name].get()
        if on:
            bg, fg = (UI_GREEN_HOVER if hover else UI_GREEN), "white"
        else:
            bg, fg = (UI_LIGHT_HOVER if hover else UI_LIGHT), UI_MUTED
        self.tiles[name].config(bg=bg, fg=fg)

    def flip_hotkey(self, name):
        """A tile was clicked: flip its switch, then apply it."""
        self.enabled_vars[name].set(not self.enabled_vars[name].get())
        self.toggle_hotkey(name)

    def toggle_hotkey(self, name):
        on = self.enabled_vars[name].get()
        self.refresh_tile(name, hover=True)    # the mouse is still over the tile
        self.hk.set_enabled(name, on)
        keys = [k for n, (_, k) in TOOLS.items() if self.enabled_vars[n].get()]
        self.set_status(("Ready - press " + ", ".join(keys) + " while Twister is focused.")
                        if keys else "All hotkeys are switched off.")

    def tool_title(self):
        name, key = TOOLS[self.mode]
        return f"{name} ({key})"

    def current_shape_name(self):
        if self.mode == "cone":
            return f"{CONE_SIDES[self.cone_idx]}-piece"
        if self.mode == "arch":
            return f"{ARCH_SIDES[self.arch_idx]}-piece"
        if self.mode == "dormer":
            return DORMER_SHAPES[self.dormer_idx]
        return SHAPES[self.shape_idx]

    def drawing_status(self):
        if self.mode == "cone":
            prompt = ("click a point on the outer ring" if not self.pts
                      else "click the center")
        else:
            prompt = "click the first corner" if not self.pts else "click the opposite corner"
        return f"Running: {self.tool_title()} - {self.current_shape_name()} - {prompt}."

    def show_error(self, msg):
        self.set_status("Error: " + msg, error=True)
        user32.MessageBoxW(0, msg, "Twister Auto Shapes", MB_ICONWARNING | MB_TOPMOST)

    def run_tool(self, fn, first_pt=None):
        """Call fn() (a start_draw*), but never let an exception kill polling or
        leave self.busy stuck True - that would silently disable every hotkey."""
        if fn.__name__.startswith("start_draw") and not self.busy:
            self.auto_first = first_pt   # hotkey press doubles as the 1st click
        try:
            fn()
        except Exception as ex:
            self.busy = False
            self.set_status(f"Error starting the tool: {ex}", error=True)

    def poll(self):
        if self.replace_evt and kernel32.WaitForSingleObject(self.replace_evt, 0) == WAIT_OBJECT_0:
            self.quit()          # a newer instance was started: make room for it
            return
        while True:
            try:
                kind, val = self.ui_q.get_nowait()
            except queue.Empty:
                break
            if kind == "hk_failed":
                self.show_error("Could not install the keyboard hook - the F5-F8 keys won't work.")
            elif kind == "trigger":
                name, pos = val
                self.run_tool({"cone": self.start_draw_cone,
                               "dormer": self.start_draw_dormer,
                               "arch": self.start_draw_arch}.get(name, self.start_draw),
                              first_pt=pos)
        self.root.after(50, self.poll)

    # ---- drawing flow ------------------------------------------------------
    def start_draw(self):
        if self.busy:
            return
        exe = TARGET_EXE
        self.exe = exe.lower()
        self.mode = "rect"
        self.shape_idx = DEFAULT_SHAPE_IDX
        self.cur_shape = SHAPE_KEYS[self.shape_idx]
        self.cur_split = "short"
        self.vk_point = char_to_vk(self.point_key)
        self.vk_close = char_to_vk(self.close_key)
        self.vk_snap = char_to_vk(self.snap_key)
        self.vk_reuse = char_to_vk(self.reuse_key)
        wins = find_windows(self.exe)
        if not wins and not self.dry:
            self.show_error(f"{exe} window not found. Start it first.")
            return
        self.target_hwnd = wins[0] if wins else None
        self.busy = True
        if self.target_hwnd:
            focus_window(self.target_hwnd, maximize=True)   # bring it forward, maximized,
                                                             # so you can see what you're drawing on
        self.was_visible = self.root.state() != "withdrawn"
        self.root.withdraw()
        self.root.after(200, lambda: self.run_tool(self.open_overlay))   # let the GUI vanish first

    def start_draw_dormer(self):
        if self.busy:
            return
        exe = TARGET_EXE
        self.exe = exe.lower()
        self.mode = "dormer"
        self.dormer_idx = 0
        self.cur_shape = DORMER_KEYS[self.dormer_idx]
        self.vk_point = char_to_vk(self.point_key)
        self.vk_close = char_to_vk(self.close_key)
        self.vk_snap = char_to_vk(self.snap_key)
        self.vk_reuse = char_to_vk(self.reuse_key)
        wins = find_windows(self.exe)
        if not wins and not self.dry:
            self.show_error(f"{exe} window not found. Start it first.")
            return
        self.target_hwnd = wins[0] if wins else None
        self.busy = True
        if self.target_hwnd:
            focus_window(self.target_hwnd, maximize=True)
        self.was_visible = self.root.state() != "withdrawn"
        self.root.withdraw()
        self.root.after(200, lambda: self.run_tool(self.open_overlay))

    def start_draw_arch(self):
        if self.busy:
            return
        exe = TARGET_EXE
        self.exe = exe.lower()
        self.mode = "arch"
        self.arch_idx = 0
        self.cur_shape = "arch"
        self.vk_point = char_to_vk(self.point_key)
        self.vk_close = char_to_vk(self.close_key)
        self.vk_snap = char_to_vk(self.snap_key)
        self.vk_reuse = char_to_vk(self.reuse_key)
        wins = find_windows(self.exe)
        if not wins and not self.dry:
            self.show_error(f"{exe} window not found. Start it first.")
            return
        self.target_hwnd = wins[0] if wins else None
        self.busy = True
        if self.target_hwnd:
            focus_window(self.target_hwnd, maximize=True)
        self.was_visible = self.root.state() != "withdrawn"
        self.root.withdraw()
        self.root.after(200, lambda: self.run_tool(self.open_overlay))

    def start_draw_cone(self):
        if self.busy:
            return
        exe = TARGET_EXE
        self.exe = exe.lower()
        self.mode = "cone"
        self.cone_idx = (CONE_SIDES.index(self.cone_sides.get())
                         if self.cone_sides.get() in CONE_SIDES else CONE_SIDES.index(8))
        self.vk_point = char_to_vk(self.point_key)
        self.vk_close = char_to_vk(self.close_key)
        self.vk_snap = char_to_vk(self.snap_key)
        self.vk_reuse = char_to_vk(self.reuse_key)
        wins = find_windows(self.exe)
        if not wins and not self.dry:
            self.show_error(f"{exe} window not found. Start it first.")
            return
        self.target_hwnd = wins[0] if wins else None
        self.busy = True
        if self.target_hwnd:
            focus_window(self.target_hwnd, maximize=True)
        self.was_visible = self.root.state() != "withdrawn"
        self.root.withdraw()
        self.root.after(200, lambda: self.run_tool(self.open_overlay))

    def open_overlay(self):
        W, H = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.W, self.H = W, H

        # Layer 1: dim layer that catches your clicks (semi-transparent)
        ov = tk.Toplevel(self.root)
        self.ov = ov
        ov.overrideredirect(True)
        ov.attributes("-topmost", True)
        ov.attributes("-alpha", DIM_ALPHA)
        ov.geometry(f"{W}x{H}+0+0")
        catcher = tk.Canvas(ov, bg="black", highlightthickness=0, cursor="crosshair")
        catcher.pack(fill="both", expand=True)
        self.catcher = catcher

        # Layer 2: drawing layer on top - fully opaque lines, click-through
        dw = tk.Toplevel(self.root)
        self.dw = dw
        dw.overrideredirect(True)
        dw.attributes("-topmost", True)
        dw.attributes("-transparentcolor", KEY)
        dw.geometry(f"{W}x{H}+0+0")
        self.canvas = tk.Canvas(dw, bg=KEY, highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.make_click_through(dw)

        self.pts = []
        self.corners = []
        self.last_pt = None
        first, self.auto_first = self.auto_first, None
        if first is not None and 0 <= first[0] < W and 0 <= first[1] < H:
            self.pts.append(first)          # hotkey press counts as the first click
            self.last_pt = first
        self.draw_hint()

        catcher.bind("<Button-1>", self.on_click)
        catcher.bind("<Motion>", self.on_motion)
        catcher.bind("<Button-3>", self.undo)
        catcher.bind("<MouseWheel>", lambda e: self.on_wheel(1 if e.delta > 0 else -1))
        ov.bind("<BackSpace>", self.undo)
        ov.bind("<Escape>", lambda e: self.cancel_draw())
        ov.focus_force()

        # Take over the mouse buttons at system level: your 3 clicks are read here and
        # never reach Twister (or any other app) while you draw the rectangle.
        self.lock.drain()
        self.lock.engage("capture", 300)
        self.selecting = True
        if self.pts:
            self.on_motion(SimpleNamespace(x=self.pts[0][0], y=self.pts[0][1]))
        self.pump_clicks()

    @staticmethod
    def make_click_through(win):
        win.update()
        hwnd = user32.GetParent(win.winfo_id())
        GWL_EXSTYLE, WS_EX_LAYERED, WS_EX_TRANSPARENT = -20, 0x80000, 0x20
        style = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
        user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style | WS_EX_LAYERED | WS_EX_TRANSPARENT)

    def hint_text(self):
        """What the tooltip should say for the current step."""
        if self.mode == "cone":
            if len(self.pts) == 1:
                return (f"Click the center point to set the radius & rotation - "
                        f"{CONE_SIDES[self.cone_idx]}-piece cone\n"
                        "(scroll = change piece count, Backspace = undo)")
            return self.CONE_HINTS[len(self.pts)]
        if self.mode == "arch":
            if len(self.pts) == 2:
                return (f"Click a point on the opposite side to set the width - "
                        f"{ARCH_SIDES[self.arch_idx]}-piece gambrel\n"
                        "(scroll = change piece count, Backspace = undo)")
            return self.HINTS[len(self.pts)]
        if self.mode == "dormer":
            if len(self.pts) == 2:
                return (f"Click a point on the opposite side to set the width - "
                        f"{DORMER_SHAPES[self.dormer_idx]}\n"
                        "(scroll = change shape, Backspace = undo)")
            return self.DORMER_HINTS[len(self.pts)]
        if len(self.pts) == 2:
            return (f"Click a point on the opposite side to set the width - "
                    f"{SHAPES[self.shape_idx]}\n"
                    "(scroll = change shape, Backspace = undo)")
        return self.HINTS[len(self.pts)]

    def show_tooltip(self, x, y, text, tag="hint", offset=18):
        """Small dark tooltip box with `text`, anchored just off point (x, y) and
        kept fully on-screen."""
        c = self.canvas
        c.delete(tag)
        font = ("Segoe UI", 10)
        pad_x, pad_y = 8, 6
        tmp = c.create_text(0, 0, text=text, font=font, anchor="nw")
        x1, y1, x2, y2 = c.bbox(tmp)
        c.delete(tmp)
        w, h = x2 - x1, y2 - y1
        tx, ty = x + offset, y + offset
        if tx + w + pad_x * 2 > self.W:
            tx = x - offset - w - pad_x * 2
        if ty + h + pad_y * 2 > self.H:
            ty = y - offset - h - pad_y * 2
        tx, ty = max(0, tx), max(0, ty)
        c.create_rectangle(tx, ty, tx + w + pad_x * 2, ty + h + pad_y * 2,
                           fill="#202020", outline=COLOR, width=1, tags=tag)
        c.create_text(tx + pad_x, ty + pad_y, anchor="nw", fill="white",
                      font=font, text=text, tags=tag)

    def draw_hint(self):
        self.set_status(self.drawing_status())
        if not self.show_tooltips.get():
            self.canvas.delete("hint")
            return
        anchor = self.last_pt or (self.W // 2, self.H // 2)
        self.show_tooltip(*anchor, self.hint_text())

    def on_screen(self, corners):
        return all(0 <= x < self.W and 0 <= y < self.H for x, y in corners)

    def draw_split(self, corners, color, tag):
        _, _, (m1, m2) = split_rectangle(corners, self.cur_split)
        self.canvas.create_line(*m1, *m2, fill=color, width=LINE_W, dash=(6, 4), tags=tag)

    def draw_four(self, corners, color, tag):
        res = split_four(corners)
        if not res:
            return
        L, R = res
        a, b, c, d = corners
        for p1, p2 in ((a, L), (d, L), (b, R), (c, R), (L, R)):
            self.canvas.create_line(*p1, *p2, fill=color, width=LINE_W, dash=(6, 4), tags=tag)

    def draw_arch(self, corners, color, tag):
        g = split_arch(corners, ARCH_SIDES[self.arch_idx])
        if g:
            for p1, p2 in list(zip(g["P"], g["Q"]))[1:-1]:
                self.canvas.create_line(*p1, *p2, fill=color, width=LINE_W, dash=(6, 4), tags=tag)

    def draw_tri(self, corners, color, tag):
        g = split_tri_end(corners, self.cur_shape == "tri_inv")
        if g:
            for p1, p2 in g["lines"]:
                self.canvas.create_line(*p1, *p2, fill=color, width=LINE_W, dash=(6, 4), tags=tag)

    def draw_dormer_lines(self, g, color, tag):
        for p1, p2 in g["lines"]:
            self.canvas.create_line(*p1, *p2, fill=color, width=LINE_W, dash=(6, 4), tags=tag)

    def dot(self, x, y, tag):
        self.canvas.create_oval(x - DOT_R, y - DOT_R, x + DOT_R, y + DOT_R,
                                fill=COLOR, outline="", tags=tag)

    def draw_cone_spokes(self, center, verts, color, tag):
        for v in verts:
            self.canvas.create_line(*center, *v, fill=color, width=LINE_W, tags=tag)

    def on_wheel(self, direction):
        # incoming direction: +1 = wheel up, -1 = wheel down.
        # Wheel DOWN cycles to the NEXT shape, wheel UP goes back to the previous one.
        direction = -direction
        if self.mode == "cone" and len(self.pts) == 1:
            # pick the piece-count while sighting the center, live in the preview
            self.cone_idx = (self.cone_idx + direction) % len(CONE_SIDES)
            if self.last_pt:
                self.on_motion(SimpleNamespace(x=self.last_pt[0], y=self.last_pt[1]))
            return
        if self.mode == "dormer" and len(self.pts) in (1, 2):
            self.dormer_idx = (self.dormer_idx + direction) % len(DORMER_KEYS)
            self.cur_shape = DORMER_KEYS[self.dormer_idx]
            if self.last_pt:
                self.on_motion(SimpleNamespace(x=self.last_pt[0], y=self.last_pt[1]))
            return
        if self.mode == "arch" and len(self.pts) in (1, 2):
            # pick the piece count (3 / 4 / 5 / 6) while sighting the width
            self.arch_idx = (self.arch_idx + direction) % len(ARCH_SIDES)
            if self.last_pt:
                self.on_motion(SimpleNamespace(x=self.last_pt[0], y=self.last_pt[1]))
            return
        if self.mode == "rect" and len(self.pts) in (1, 2):
            # pick the shape (Rectangle / 2-piece / 4-piece) while sighting the
            # width, live in the preview - same idea as the cone's piece-count
            self.shape_idx = (self.shape_idx + direction) % len(SHAPE_KEYS)
            self.cur_shape = SHAPE_KEYS[self.shape_idx]
            if self.last_pt:
                self.on_motion(SimpleNamespace(x=self.last_pt[0], y=self.last_pt[1]))

    def on_click(self, e):
        p = (e.x, e.y)
        self.last_pt = p
        if self.mode == "cone":
            if len(self.pts) == 0:
                self.pts.append(p)   # 1st click: a vertex on the outer ring
            else:  # 2nd click: center point - locks in and starts tracing right away
                vertex = self.pts[0]
                center = p
                verts = polygon_from_points(center, vertex, CONE_SIDES[self.cone_idx])
                if verts and self.on_screen(verts) and self.on_screen([center]):
                    self.finish((center, verts))
                return
            self.draw_hint()
            self.on_motion(e)
            return
        if len(self.pts) == 0:
            self.pts.append(p)
        else:  # 2nd click = opposite corner: the shape is locked in and tracing starts right away
            box = box_edge(self.pts[0], p)
            if box:
                res = rect_from_points(self.pts[0], box, p)
                if res and res[1] >= MIN_SIZE and self.shape_fits(res[0]):
                    self.pts.append(box)
                    self.finish(res[0])
            return
        self.draw_hint()
        self.on_motion(e)

    def pump_clicks(self):
        """Feed the clicks captured by the mouse hook into the drawing logic."""
        if not self.selecting:
            return
        if user32.GetAsyncKeyState(VK_ESCAPE) & 0x8000:   # Esc cancels, focus or not
            self.cancel_draw()
            return
        try:
            while self.selecting:
                item = self.lock.click_q.get_nowait()
                kind = item[0]
                if kind == "left":
                    _, x, y = item
                    self.on_click(SimpleNamespace(x=x, y=y))
                elif kind == "right":
                    _, x, y = item
                    self.undo(SimpleNamespace(x=x, y=y))
                elif kind == "wheel":
                    _, direction, x, y = item
                    self.on_wheel(direction)
        except queue.Empty:
            pass
        if self.selecting:
            self.root.after(10, self.pump_clicks)

    def undo(self, e=None):
        if self.pts:
            self.pts.pop()
        self.draw_hint()
        if e is not None:
            self.on_motion(e)

    def on_motion(self, e):
        self.last_pt = (e.x, e.y)
        self.draw_hint()
        c = self.canvas
        c.delete("preview")
        for x, y in self.pts:
            self.dot(x, y, "preview")
        p = (e.x, e.y)
        if self.mode == "cone":
            if len(self.pts) == 1:
                verts = polygon_from_points(p, self.pts[0], CONE_SIDES[self.cone_idx])
                if verts:
                    ok = self.on_screen(verts)
                    c.create_polygon([v for pt in verts for v in pt],
                                     outline=COLOR if ok else BAD_COLOR, fill="",
                                     width=LINE_W, tags="preview")
                    self.draw_cone_spokes(p, verts, COLOR if ok else BAD_COLOR, "preview")
            return
        if len(self.pts) == 1:
            # the cursor is the opposite corner: width AND height follow it
            box = box_edge(self.pts[0], p)
            if box:
                res = rect_from_points(self.pts[0], box, p)
                if res:
                    self.draw_shape_preview(res[0], None)

    def shape_fits(self, corners):
        """Is the current tool's shape on screen (and, for the arch, not too thin)?"""
        if self.mode == "dormer":
            g = dormer_geometry(corners, self.cur_shape)
            return bool(g and self.on_screen(g["outline"]))       # the roof point must fit too
        return self.on_screen(corners) and (
            self.mode != "arch" or bool(split_arch(corners, ARCH_SIDES[self.arch_idx])))

    def draw_shape_preview(self, corners, color):
        """Draw the current tool's shape (outline + cut lines) as a preview.  `color` None =
        normal (red when it would leave the screen); a colour = provisional preview."""
        c = self.canvas
        if self.mode == "dormer":
            g = dormer_geometry(corners, self.cur_shape)
            if not g:
                return
            ok = self.on_screen(g["outline"])
            col = (color if color and ok else None) or (COLOR if ok else BAD_COLOR)
            c.create_polygon([v for pt in g["outline"] for v in pt],
                             outline=col, fill="", width=LINE_W, tags="preview")
            self.draw_dormer_lines(g, col, "preview")
            return
        ok = self.on_screen(corners)
        col = (color if color and ok else None) or (COLOR if ok else BAD_COLOR)
        c.create_polygon([v for pt in corners for v in pt],
                         outline=col, fill="", width=LINE_W, tags="preview")
        if self.mode == "arch":
            self.draw_arch(corners, col, "preview")
        elif self.cur_shape == "two":
            self.draw_split(corners, col, "preview")
        elif self.cur_shape == "four":
            self.draw_four(corners, col, "preview")
        elif self.cur_shape in ("tri", "tri_inv"):
            self.draw_tri(corners, col, "preview")

    def finish(self, corners):
        self.selecting = False
        # No more input on the catcher layer
        self.catcher.unbind("<Button-1>")
        self.catcher.unbind("<Motion>")
        self.catcher.unbind("<Button-3>")
        self.catcher.unbind("<MouseWheel>")

        self.canvas.delete("all")
        if self.mode == "cone":
            center, verts = corners
            self.corners = verts
            self.canvas.create_polygon([v for pt in verts for v in pt],
                                       outline=COLOR, fill="", width=LINE_W)
            self.draw_cone_spokes(center, verts, COLOR, "final")
            self.dot(*center, "final")
            for x, y in verts:
                self.dot(x, y, "final")
            self.steps = build_cone_steps(center, verts, self.vk_point, self.vk_close,
                                          self.vk_snap, self.vk_reuse)
        elif self.mode == "dormer":
            g = dormer_geometry(corners, self.cur_shape)
            self.corners = corners
            self.canvas.create_polygon([v for pt in g["outline"] for v in pt],
                                       outline=COLOR, fill="", width=LINE_W)
            self.draw_dormer_lines(g, COLOR, "final")
            for x, y in g["outline"] + [g["m"]]:
                self.dot(x, y, "final")
            self.steps = build_dormer_steps(corners, self.cur_shape, self.vk_point,
                                            self.vk_close, self.vk_snap, self.vk_reuse)
        elif self.mode == "arch":
            n = ARCH_SIDES[self.arch_idx]
            g = split_arch(corners, n)
            self.corners = corners
            self.canvas.create_polygon([v for pt in corners for v in pt],
                                       outline=COLOR, fill="", width=LINE_W)
            self.draw_arch(corners, COLOR, "final")
            for x, y in g["P"] + g["Q"]:
                self.dot(x, y, "final")
            self.steps = build_arch_steps(corners, n, self.vk_point, self.vk_close,
                                          self.vk_snap, self.vk_reuse)
        else:
            self.corners = corners
            self.canvas.create_polygon([v for pt in corners for v in pt],
                                       outline=COLOR, fill="", width=LINE_W)
            pts = list(corners)
            if self.cur_shape == "two":
                self.draw_split(corners, COLOR, "final")
                pts += list(split_rectangle(corners, self.cur_split)[2])
            elif self.cur_shape == "four":
                self.draw_four(corners, COLOR, "final")
                res = split_four(corners)
                if res:
                    pts += list(res)
            elif self.cur_shape in ("tri", "tri_inv"):
                self.draw_tri(corners, COLOR, "final")
                g = split_tri_end(corners, self.cur_shape == "tri_inv")
                if g:
                    pts += [g["t"], g["m"]]
            for x, y in pts:
                self.dot(x, y, "final")

            self.steps = build_steps(corners, self.cur_shape, self.cur_split,
                                     self.vk_point, self.vk_close, self.vk_snap, self.vk_reuse)

        # Lock the physical mouse right now and keep it locked until every
        # point (and the close key) has been sent.  Dry runs press nothing, so no lock.
        if self.lock_mouse and not self.dry:
            delay_s = self.delay
            interval = STEP_INTERVAL_MS
            per_step = (MOVE_POLL + 3 * MOVE_SETTLE + PRE_KEY_DWELL + KEY_HOLD + POST_KEY_DWELL
                        + (interval + CLOSE_PAUSE_MS) / 1000)
            timeout = delay_s + (len(self.steps) + 1) * per_step + 15          # safety auto-release
            self.lock.set_mode("lock", timeout)
            if self.show_tooltips.get():
                anchor = self.last_pt or (self.W // 2, self.H // 2)
                self.show_tooltip(*anchor,
                                  "Mouse locked until all points are placed\n(hold Esc to abort)",
                                  tag="lockmsg")
        else:
            self.lock.set_mode("off", 5)   # no lock wanted: just finish swallowing this click's release

        self.wait_release()

    def wait_release(self, tries=0):
        """Wait until you let go of the left button before dropping the catcher
        layer, so the release doesn't leak into the app underneath."""
        if user32.GetAsyncKeyState(VK_LBUTTON) & 0x8000 and tries < 100:
            self.root.after(20, self.wait_release, tries + 1)
            return
        try:
            self.ov.destroy()          # dim layer gone; only the click-through drawing stays
        except tk.TclError:
            pass
        self.begin_placing()

    # ---- placing points in the target app ----------------------------------
    def begin_placing(self):
        self.place_log = []
        self.t_start = time.time()
        self.set_status(f"Running: {self.tool_title()} - tracing the shape in Twister...")
        if self.dry:
            self.root.after(3000, self.close_overlay)
            return
        delay_s = self.delay
        self.root.after(delay_s * 1000, self.place_next, 0)

    def target_focused(self):
        return exe_of_hwnd(user32.GetForegroundWindow()) == self.exe

    def ensure_focus(self):
        if self.target_focused():
            return True
        hwnd = self.target_hwnd
        if not hwnd or not user32.IsWindow(hwnd):
            wins = find_windows(self.exe)
            hwnd = self.target_hwnd = wins[0] if wins else None
        if hwnd and focus_window(hwnd):
            return True
        return self.target_focused()

    def abort(self, msg):
        self.set_status(msg, error=not msg.startswith("Aborted"))
        self.close_overlay()

    def place_next(self, i, tries=0):
        n = len(self.steps)
        if user32.GetAsyncKeyState(VK_ESCAPE) & 0x8000:   # global abort
            self.abort("Aborted (Esc).")
            return
        if i >= n:                                         # every key has been sent
            self.set_status(f"Done: {self.tool_title()} traced in {time.time() - self.t_start:.1f} s."
                            + self.write_place_log())
            self.root.after(300, self.close_overlay)
            return
        if modifiers_down():                               # a held Shift would turn "b" into "B"
            if tries > 100:
                self.abort("Release Shift/Ctrl/Alt and try again.")
                return
            self.root.after(50, self.place_next, i, tries + 1)
            return
        if not self.ensure_focus():
            self.abort(f"{TARGET_EXE} is not focused - stopped without sending keys.")
            return
        pos, vk = self.steps[i]
        if pos is not None:
            if vk == self.vk_reuse and REUSE_APPROACH_PX:
                user32.SetCursorPos(int(pos[0]) + REUSE_APPROACH_PX, int(pos[1]) + REUSE_APPROACH_PX)
                time.sleep(MOVE_POLL)
            for _ in range(3):                             # aim, settle, verify - until EXACT
                if not move_to(*pos):
                    self.abort("Couldn't hold the cursor in place - stopped.")
                    return
                time.sleep(MOVE_SETTLE)                    # let the app see the mouse move
                if cursor_near(*pos):                      # (re-aims if pushed away, e.g. by a snap)
                    break
        at_press, after = send_key(vk, pos)
        if pos is not None:
            self.place_log.append((i, chr(vk) if 32 <= vk < 127 else vk, pos, at_press, after))
        interval = STEP_INTERVAL_MS + (CLOSE_PAUSE_MS if vk == self.vk_close else 0)
        self.root.after(interval, self.place_next, i + 1)

    def write_place_log(self):
        """Dump intended vs. actual cursor position of every key press next to the script
        (twister_placement.log) and return a short summary for the status line."""
        worst = 0
        try:
            path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "twister_placement.log")
            with open(path, "w", encoding="utf-8") as f:
                f.write("step key intended at-key-press after-dwell error\n")
                for i, key, want, got, after in self.place_log:
                    err = max(abs(want[0] - got[0]), abs(want[1] - got[1]),
                              abs(want[0] - after[0]), abs(want[1] - after[1]))
                    worst = max(worst, err)
                    f.write(f"{i:3d}  {key}  {want}  {got}  {after}  "
                            f"{'OFF by ' + str(err) if err else 'ok'}\n")
        except Exception:
            return ""
        return f" Cursor was off by up to {worst} px (see twister_placement.log)." if worst else ""

    def refocus_target(self):
        """Best-effort: put Twister back in the foreground, no matter how we got here
        (finished, aborted, dry run, or the overlay was just closed)."""
        hwnd = self.target_hwnd
        if not hwnd or not user32.IsWindow(hwnd):
            wins = find_windows(self.exe)
            hwnd = wins[0] if wins else None
        if hwnd:
            focus_window(hwnd)

    def cancel_draw(self):
        self.set_status(f"Cancelled: {self.tool_title()}.")
        self.close_overlay()

    def close_overlay(self):
        self.selecting = False
        self.lock.release()
        for w in (self.ov, self.dw):
            try:
                if w is not None:
                    w.destroy()
            except tk.TclError:
                pass
        self.ov = self.dw = None
        if getattr(self, "was_visible", False):
            self.root.deiconify()
        self.refocus_target()      # bring Twister back to the front, not our own GUI
        self.busy = False

    def quit(self):
        self.lock.release()
        self.hk.stop()
        if getattr(self, "tray", None):
            self.tray.remove()
        self.root.destroy()


def acquire_single_instance_lock():
    """Returns a mutex handle to keep for the life of the process.  If another instance
    is already running, this one REPLACES it: it asks the running instance to exit (via
    a named event) and waits for it to let go of the mutex.  Returns None (after a
    message box) only if the old instance doesn't exit in time - e.g. an older build
    that doesn't listen for the request, which then has to be closed by hand once."""
    handle = kernel32.CreateMutexW(None, False, MUTEX_NAME)
    if not handle or kernel32.GetLastError() != ERROR_ALREADY_EXISTS:
        return handle
    kernel32.CloseHandle(handle)
    evt = kernel32.CreateEventW(None, False, False, REPLACE_EVENT_NAME)
    if evt:
        kernel32.SetEvent(evt)                       # "please exit"
        kernel32.CloseHandle(evt)
    deadline = time.time() + 8
    while time.time() < deadline:
        time.sleep(0.2)
        handle = kernel32.CreateMutexW(None, False, MUTEX_NAME)
        if handle and kernel32.GetLastError() != ERROR_ALREADY_EXISTS:
            return handle                            # the old instance is gone: we own it now
        if handle:
            kernel32.CloseHandle(handle)
    user32.MessageBoxW(0, "Twister Auto Shapes is already running and did not close. "
                          "Close it from the system tray (right-click > Exit) or Task "
                          "Manager, then start this again.", "Twister Auto Shapes",
                       MB_ICONWARNING | MB_TOPMOST)
    return None


if __name__ == "__main__":
    # PIA's on/off switch (TAS_config.ini on the P: drive) is checked on every launch, BEFORE
    # the instance lock, so a blocked launch never replaces an instance that is already running.
    can_run, why, state = check_startup()
    if why:
        if state == "disabled":
            log_usage("Blocked (disabled)")
        user32.MessageBoxW(0, why, "Twister Auto Shapes", MB_ICONWARNING | MB_TOPMOST)
    if not can_run:
        raise SystemExit(0)
    _instance_lock = acquire_single_instance_lock()
    if _instance_lock is None:
        raise SystemExit(0)
    root = tk.Tk()
    App(root)
    root.mainloop()
