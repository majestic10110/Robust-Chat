import sys
import io
import os
import datetime
import traceback
import threading
import time
import queue
import json
import math
import re
import tkinter as tk
from tkinter import ttk, messagebox
import tkinter.font as tkfont

def enable_dark_titlebar(window):
    """
    Try to enable a dark immersive title bar on Windows 10/11 for this Tk window only.
    No effect on other applications or system-wide theme.
    """
    try:
        import sys
        if sys.platform != "win32":
            return
        import ctypes

        hwnd = window.winfo_id()
        if not hwnd:
            return

        # Known values for DWMWA_USE_IMMERSIVE_DARK_MODE
        DWMWA_USE_IMMERSIVE_DARK_MODE = 20
        DWMWA_USE_IMMERSIVE_DARK_MODE_BEFORE_20 = 19

        def _set_dark(h, attr):
            value = ctypes.c_int(1)
            return ctypes.windll.dwmapi.DwmSetWindowAttribute(
                h,
                attr,
                ctypes.byref(value),
                ctypes.sizeof(value),
            )

        # Try modern attribute first, then fallback
        res = _set_dark(hwnd, DWMWA_USE_IMMERSIVE_DARK_MODE)
        if res != 0:
            _set_dark(hwnd, DWMWA_USE_IMMERSIVE_DARK_MODE_BEFORE_20)
    except Exception:
        # If anything fails (old Windows, missing API, etc), just ignore.
        pass

try:
    import serial
    import serial.tools.list_ports
except ImportError:
    serial = None


FEND = 0xC0
FESC = 0xDB
TFEND = 0xDC
TFESC = 0xDD
def logmsg(*a):
    """Safe fallback logger for early startup errors."""
    try:
        print("[LOG]", *a)
    except Exception:
        pass

def app_path(name: str) -> str:
    """
    Resolve a file path relative to the running program:
      - If frozen as an .exe, use the folder containing the .exe
      - Otherwise, use the folder containing this .py file
    This keeps settings/log/messages beside the visible program file.
    """
    try:
        if getattr(sys, "frozen", False):
            base = os.path.dirname(sys.executable)
        else:
            base = os.path.dirname(os.path.abspath(__file__))
    except Exception:
        base = os.getcwd()
    return os.path.join(base, name)

def grid_to_latlon(grid: str):
    """
    Convert Maidenhead locator (e.g. IO91WM) to (lat, lon) in decimal degrees
    using the centre of the square. Supports 4- or 6-character locators.
    """
    if not grid:
        raise ValueError("Empty grid")
    g = grid.strip().upper()
    if len(g) < 4:
        raise ValueError("Grid too short")

    # Field (A-R)
    lon = (ord(g[0]) - ord('A')) * 20 - 180
    lat = (ord(g[1]) - ord('A')) * 10 - 90

    # Square (0-9)
    lon += (ord(g[2]) - ord('0')) * 2
    lat += (ord(g[3]) - ord('0')) * 1

    # Centre of that square
    lon += 1.0
    lat += 0.5

    # Subsquare (AA-XX) for 6-char
    if len(g) >= 6:
        lon += (ord(g[4]) - ord('A')) * (5.0 / 60.0)
        lat += (ord(g[5]) - ord('A')) * (2.5 / 60.0)
        lon += (2.5 / 60.0)
        lat += (1.25 / 60.0)

    return float(lat), float(lon)







# Amateur radio prefix -> (country, placeholder_flag) mapping
# (Flag value unused in this textflags build, but kept for compatibility.)
PREFIX_COUNTRY_FLAG = {
    "G": ("United Kingdom", ""),
    "M": ("United Kingdom", ""),
    "2": ("United Kingdom", ""),
    "K": ("United States", ""),
    "N": ("United States", ""),
    "W": ("United States", ""),
    "AA": ("United States", ""),
    "AB": ("United States", ""),
    "AC": ("United States", ""),
    "AD": ("United States", ""),
    "AE": ("United States", ""),
    "AF": ("United States", ""),
    "AG": ("United States", ""),
    "AH": ("United States", ""),
    "DL": ("Germany", ""),
    "D": ("Germany", ""),
    "F": ("France", ""),
    "I": ("Italy", ""),
    "EA": ("Spain", ""),
    "EB": ("Spain", ""),
    "VK": ("Australia", ""),
    "VE": ("Canada", ""),
    "VA": ("Canada", ""),
    "JA": ("Japan", ""),
    "JR": ("Japan", ""),
    "ZL": ("New Zealand", ""),
    "ZS": ("South Africa", ""),
    # Fallbacks/others can be extended here
}

class RobustChatSimpleV16:
    def __init__(self, master: tk.Tk):
        self.master = master
        self.master.title("Robust Chat v2.09")
        self.master.configure(bg="#0b141a")
        self.master.geometry("980x600")
        self.master.minsize(800, 480)

        # Serial / KISS
        self.ser = None
        self.read_thread = None
        self.read_running = False
        self.kiss_mode = False  # True only after successful preflight KISS init

        # GPS serials
        self.gps_ser = None
        self.gps_thread = None
        self.gps_running = False
        self.gps_last_update = 0.0  # 10-min throttle

        self.link500_ser = None  # for %AZ polling

        # Data
        self.conversations = {"All": [], "Settings": []}
        self.active_chat = "All"

        # Beacons / link graph
        self.beacons = {}   # { parent: {"last": ts, "children": {child: ts}} }
        self.links = {}     # { call: last_ts } where beacon contained MYCALL as child

        # Files
        self.messages_file = app_path("messages_v1.json")
        self.link_graph_file = app_path("link_graph.json")
        self.settings_file = app_path("settings.json")
        self.positions_file = app_path("positions.json")

        # Positions: { call: { "lat": float, "lon": float, "epoch": float } }
        self.positions = {}

        # Current own position source tag
        self._beacon_pos_source = None

        # UI infra
        self.ui_queue: "queue.SimpleQueue" = queue.SimpleQueue()

        # ACK / reliability state
        self.pending_acks = {}      # ack_id -> entry
        self.seen_ack_ids = {}      # (from_base, ack_id) -> {"ts": float, "ack_sent": bool}
        self.ack_lock = threading.Lock()
        self.ack_id_counter = 0

        # Fonts
                # Global emoji-capable font configuration (Option A)
        try:
            emoji_family = "Segoe UI Emoji"
            self.font_main = tkfont.Font(family=emoji_family, size=11)
            self.font_meta = tkfont.Font(family=emoji_family, size=10)
            self.font_fixed = tkfont.Font(family=emoji_family, size=11)
        except Exception:
            try:
                emoji_family = "Noto Color Emoji"
                self.font_main = tkfont.Font(family=emoji_family, size=11)
                self.font_meta = tkfont.Font(family=emoji_family, size=10)
                self.font_fixed = tkfont.Font(family=emoji_family, size=11)
            except Exception:
                emoji_family = "Segoe UI"
                self.font_main = tkfont.Font(family=emoji_family, size=11)
                self.font_meta = tkfont.Font(family=emoji_family, size=10)
                self.font_fixed = tkfont.Font(family=emoji_family, size=11)

        print(f"[Fonts] Using global font family: {emoji_family}")
        self.font_day = tkfont.Font(family="Segoe UI", size=9, weight="bold")
        try:
            self.font_small = tkfont.Font(family=self.font_main.actual("family"), size=9)
        except Exception:
            self.font_small = self.font_main

        self.speed_var = tk.StringVar(value="R300")
        self.current_page = "Main"

        # GPS tab vars
        self.fixed_name_var = tk.StringVar()
        self.fixed_lat_var = tk.StringVar()
        self.fixed_lon_var = tk.StringVar()
        self.mygrid_var = tk.StringVar()

        self.gps_port_var = tk.StringVar()
        self.gps_lat_var = tk.StringVar()
        self.gps_lon_var = tk.StringVar()

        self.link500_port_var = tk.StringVar()
        self.link500_lat_var = tk.StringVar()
        self.link500_lon_var = tk.StringVar()

        self.locator_canvas = None  # locator compass canvas

        # Beacon timing
        self.beacon_interval_var = tk.IntVar(value=10)  # default 10 min; persisted in settings if changed
        self.beacon_job = None

        # Track last successful beacon time for UI
        self.last_beacon_epoch = None

        self.settings = {}

        self._load_settings()

        # AI Assistant (LM Studio) settings
        self.ai_autoreply_enabled = self.settings.get("ai_autoreply_enabled", False)
        self.ai_endpoint = self.settings.get(
            "ai_endpoint",
            "http://127.0.0.1:1234/v1/chat/completions",
        )
        self.ai_model = self.settings.get("ai_model", "")
        self.ai_personality = self.settings.get(
            "ai_personality",
            "You are a Ham radio operator, will adhere to the general rules around amateur radio, "
            "you are communicating with other hams, you are to keep answers helpful, factual and to the point, "
            "when asked about first aid issues or survival issues follow triage rules."
        )
        self.ai_max_words = int(self.settings.get("ai_max_words", 200))
        self._load_messages()
        self._load_positions()
        self._build_ui()
        self._apply_settings_to_ui()
        self._apply_ai_mode()
        self._load_link_graph(prune_only=True)
        self._prune_beacons(save=True)

        self._refresh_chat_listbox()
        self._refresh_beacon_listbox()
        self._render_active_chat()
        self.show_page("Main")

        self.log("Set MyCall, choose COM, Connect. R300 default on startup.")
        self.log("Beacon link dots: green/amber/red = freshness of stations that hear you & you hear them.")
        self.log("Locator: compass centered on MyCall; stations with positions will be plotted.")

        self.master.after(50, self._process_ui_queue)
        self.master.protocol("WM_DELETE_WINDOW", self.on_close)

        # Periodic positions.json refresh / prune (every 30 min)
        self.master.after(30 * 60 * 1000, self._positions_maintenance)


        # Rebuild ACK state from persisted messages and start cleanup timers
        self._rebuild_ack_state_from_messages()
        self._schedule_seen_ack_prune()

    # ----- Settings -----

    def _load_settings(self):
        try:
            if os.path.exists(self.settings_file):
                with open(self.settings_file, "r", encoding="utf-8", errors="replace") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    self.settings = data
        except Exception as e:
            logmsg(f"Failed to load settings.json (ignored): {e}")
            self.settings = {}

    def _save_settings(self):
        try:
            mycall = (getattr(self, "call_var", tk.StringVar()).get() or "").strip().upper()
            last_port = (getattr(self, "port_var", tk.StringVar()).get() or "").strip()
            speed = (self.speed_var.get() or "R300").strip().upper()
            if speed not in ("R300", "R600"):
                speed = "R300"

            data = {

                "mycall": mycall,
                "last_port": last_port,
                "speed": speed,
                # Fixed pos
                "fixed_name": self.fixed_name_var.get(),
                "fixed_lat": self.fixed_lat_var.get(),
                "fixed_lon": self.fixed_lon_var.get(),
                # GPS row
                "gps_port": self.gps_port_var.get(),
                "gps_lat": self.gps_lat_var.get(),
                "gps_lon": self.gps_lon_var.get(),
                # LiNK500 row
                "link500_port": self.link500_port_var.get(),
                "link500_lat": self.link500_lat_var.get(),
                "link500_lon": self.link500_lon_var.get(),
                # Beacon timing
                "beacon_interval": int(self.beacon_interval_var.get()) if hasattr(self, "beacon_interval_var") else 0,

                "mygrid": (self.mygrid_var.get() or "").strip().upper(),

                # AI Assistant
                "ai_autoreply_enabled": bool(getattr(self, "ai_autoreply_enabled", False)),
                "ai_endpoint": getattr(self, "ai_endpoint", ""),
                "ai_model": getattr(self, "ai_model", ""),
                "ai_personality": getattr(self, "ai_personality", ""),
                "ai_max_words": int(getattr(self, "ai_max_words", 200)),
            }

            with open(self.settings_file, "w", encoding="utf-8", errors="replace") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logmsg(f"Failed to save settings.json: {e}")
    def _apply_settings_to_ui(self):
        s = self.settings

        my = (s.get("mycall") or "").strip().upper()
        if my:
            self.call_var.set(my)

        mygrid = (s.get("mygrid", "") or "")[:10]
        if hasattr(self, "mygrid_var"):
            self.mygrid_var.set(mygrid)

        last = (s.get("last_port") or "").strip()
        if last:
            ports = list(self.port_combo["values"])
            if last in ports:
                self.port_var.set(last)
                self.port_combo.set(last)

        # Always default to R300 on startup
        self.speed_var.set("R300")

        # Fixed position
        self.fixed_name_var.set((s.get("fixed_name", ""))[:10])
        self.fixed_lat_var.set((s.get("fixed_lat", ""))[:10])
        self.fixed_lon_var.set((s.get("fixed_lon", ""))[:10])

        # GPS
        self.gps_port_var.set(s.get("gps_port", ""))
        self.gps_lat_var.set((s.get("gps_lat", ""))[:10])
        self.gps_lon_var.set((s.get("gps_lon", ""))[:10])

        # LiNK500
        self.link500_port_var.set(s.get("link500_port", ""))
        self.link500_lat_var.set((s.get("link500_lat", ""))[:10])
        self.link500_lon_var.set((s.get("link500_lon", ""))[:10])

        # Beacon interval
        try:
            bi = int(s.get("beacon_interval", 0))
        except Exception:
            bi = 0
        if hasattr(self, "beacon_interval_var"):
            self.beacon_interval_var.set(bi)

        # Locator centre text
        self._draw_locator_compass()
    # ----- Positions -----

    def _load_positions(self):
        try:
            if os.path.exists(self.positions_file):
                with open(self.positions_file, "r", encoding="utf-8", errors="replace") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    self.positions = data
        except Exception as e:
            logmsg(f"Failed to load positions.json (ignored): {e}")
            self.positions = {}

    def _save_positions(self):
        try:
            with open(self.positions_file, "w", encoding="utf-8", errors="replace") as f:
                json.dump(self.positions or {}, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logmsg(f"Failed to save positions.json: {e}")

    def _positions_maintenance(self):
        # Refresh / prune old positions every 30 minutes
        now = time.time()
        ttl = 24 * 3600  # keep for 24h; can be tuned
        changed = False
        for call in list(self.positions.keys()):
            if now - float(self.positions[call].get("epoch", 0.0)) > ttl:
                self.positions.pop(call, None)
                changed = True
        if changed:
            self._save_positions()
            self._enqueue_ui(self._draw_locator_compass)
        try:
            self.master.after(30 * 60 * 1000, self._positions_maintenance)
        except Exception:
            pass
    # ===== ACK HELPERS =====================================================

    def _generate_ack_id(self) -> str:
        """Generate a short pseudo-unique ACK ID (2–12 chars)."""
        with self.ack_lock:
            self.ack_id_counter = (self.ack_id_counter + 1) & 0xFFFF
            base = int(time.time() * 10) ^ (self.ack_id_counter << 8)
        alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        out = []
        v = base & 0xFFFFFFFF
        if v == 0:
            out.append("0")
        else:
            while v > 0 and len(out) < 8:
                out.append(alphabet[v % 36])
                v //= 36
        s = "".join(out) or "00"
        if len(s) < 2:
            s = (s + "0")[:2]
        return s[:12]

    def _is_to_me(self, dst: str) -> bool:
        my = self._callsign_base(self.call_var.get() or "")
        if not my:
            return False
        dstb = self._callsign_base(dst or "")
        return bool(dstb and dstb == my)

    def _compute_ack_timeout(self, wire_len_bytes: int) -> float:
        # TX time + guard as per spec
        speed = (self.speed_var.get() or "R300").upper()
        air_bps = 300 if speed != "R600" else 600
        bits = float(wire_len_bytes) * 10.0
        tx_time_raw = bits / float(air_bps or 300)
        preamble = 0.25
        rig_latency = 0.15
        tx_time = (tx_time_raw + preamble + rig_latency) * 1.2
        ack_timeout = max(4.0, tx_time * 2.0 + 3.0)
        return ack_timeout

    def _has_pending_ack_blocker(self) -> bool:
        # Courtesy: avoid stacking ACKable frames on slow links
        with self.ack_lock:
            for e in self.pending_acks.values():
                if e.get("status") == "pending":
                    return True
        return False

    def _register_pending_ack(self, ack_id: str, src: str, dst: str, text: str,
                              ack_timeout: float, sent_at: float):
        entry = {
            "id": ack_id,
            "from": self._callsign_base(src),
            "to": self._callsign_base(dst),
            "text": text,
            "sent_at": sent_at,
            "attempts": 1,
            "status": "pending",
            "max_attempts": 3,
            "backoff_factor": 1.3,
            "ack_timeout": ack_timeout,
        }
        with self.ack_lock:
            self.pending_acks[ack_id] = entry
        try:
            self.master.after(
                int(ack_timeout * 1000),
                lambda aid=ack_id: self._check_ack_timeout(aid)
            )
        except Exception:
            pass

    def _check_ack_timeout(self, ack_id: str):
        with self.ack_lock:
            entry = self.pending_acks.get(ack_id)
        if not entry or entry.get("status") != "pending":
            return

        now = time.time()
        if now - entry["sent_at"] < entry["ack_timeout"]:
            # Timer fired before effective deadline (e.g. adjusted); ignore.
            return

        if entry["attempts"] >= entry.get("max_attempts", 3):
            entry["status"] = "failed"
            self.log(f"[ACK] No ACK for {ack_id} after {entry['attempts']} attempts.")
            self._mark_message_ack_status(ack_id, "failed")
            return

        self._resend_ack_message(ack_id)

    def _resend_ack_message(self, ack_id: str):
        with self.ack_lock:
            entry = self.pending_acks.get(ack_id)
        if not entry or entry.get("status") != "pending":
            return
        if not self.kiss_mode or not self.ser:
            entry["status"] = "failed"
            self._mark_message_ack_status(ack_id, "failed")
            return

        src = entry["from"]
        dst = entry["to"]
        text = entry["text"]
        wire_text = f"{text} [ACK:{ack_id}]"

        try:
            frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=wire_text)
            self._write_bytes(frame)
        except Exception as e:
            self.log(f"[ACK] Retry send failed for {ack_id}: {e}")
            entry["status"] = "failed"
            self._mark_message_ack_status(ack_id, "failed")
            return

        now = time.time()
        entry["attempts"] += 1
        entry["sent_at"] = now
        entry["ack_timeout"] = entry["ack_timeout"] * entry.get("backoff_factor", 1.3)
        self.log(f"[ACK] Retrying {ack_id} (attempt {entry['attempts']})")

        try:
            self.master.after(
                int(entry["ack_timeout"] * 1000),
                lambda aid=ack_id: self._check_ack_timeout(aid)
            )
        except Exception:
            pass

    def _handle_incoming_ack(self, src: str, ack_id: str):
        srcb = self._callsign_base(src)
        with self.ack_lock:
            entry = self.pending_acks.get(ack_id)
        if not entry or entry.get("status") != "pending":
            return
        if srcb != entry.get("to"):
            return

        entry["status"] = "ok"
        entry["acked_at"] = time.time()
        self.log(f"[ACK] Received ACK {ack_id} from {srcb}")
        self._mark_message_ack_status(ack_id, "ok")

    def _mark_message_ack_status(self, ack_id: str, status: str):
        def do():
            changed = False
            for _, msgs in self.conversations.items():
                for m in msgs:
                    if m.get("ack_id") == ack_id:
                        if m.get("ack_status") != status:
                            m["ack_status"] = status
                            changed = True
            if changed:
                self._save_messages()
                self._render_active_chat()
        self._enqueue_ui(do)

    def _send_ack_response(self, dst_call: str, ack_id: str):
        if not self.kiss_mode or not self.ser:
            return
        my = (self.call_var.get() or "").strip().upper()
        if not my:
            return
        try:
            text = f"[ACK:{ack_id}]"
            frame = self._build_kiss_ui_frame(src_call=my, dst_call=dst_call, text=text)
            self._write_bytes(frame)
            self.log(f"[ACK] Sent ACK {ack_id} to {dst_call}")
        except Exception as e:
            self.log(f"[ACK] Failed to send ACK {ack_id} to {dst_call}: {e}")

    def _record_seen_ack_id(self, from_call: str, ack_id: str, ack_sent: bool):
        key = (self._callsign_base(from_call), ack_id)
        self.seen_ack_ids[key] = {
            "ts": time.time(),
            "ack_sent": bool(ack_sent),
        }

    def _schedule_seen_ack_prune(self):
        # Purge old seen IDs every 15 minutes
        now = time.time()
        cutoff = now - 30 * 60  # 30 min
        for key, info in list(self.seen_ack_ids.items()):
            if info.get("ts", 0) < cutoff:
                self.seen_ack_ids.pop(key, None)
        try:
            self.master.after(15 * 60 * 1000, self._schedule_seen_ack_prune)
        except Exception:
            pass

    def _rebuild_ack_state_from_messages(self):
        # On startup: re-arm outgoing messages that were waiting for ACK
        now = time.time()
        for _, msgs in self.conversations.items():
            for m in msgs:
                ack_id = m.get("ack_id")
                if not ack_id:
                    continue
                if not m.get("ack_is_request"):
                    continue
                status = m.get("ack_status") or "pending"
                if status != "pending":
                    continue
                src = m.get("src") or ""
                dst = m.get("dst") or ""
                text = m.get("text") or ""
                wire_len = len((text + f" [ACK:{ack_id}]").encode("ascii", "ignore"))
                ack_timeout = self._compute_ack_timeout(wire_len)
                age = max(0.0, now - float(m.get("epoch", now)))
                if age > ack_timeout * 3.0:
                    m["ack_status"] = "failed"
                    continue
                remaining = max(1.0, ack_timeout - age)
                self.pending_acks[ack_id] = {
                    "id": ack_id,
                    "from": self._callsign_base(src),
                    "to": self._callsign_base(dst),
                    "text": text,
                    "sent_at": now - (ack_timeout - remaining),
                    "attempts": 1,
                    "status": "pending",
                    "max_attempts": 3,
                    "backoff_factor": 1.3,
                    "ack_timeout": remaining,
                }
                try:
                    self.master.after(
                        int(remaining * 1000),
                        lambda aid=ack_id: self._check_ack_timeout(aid)
                    )
                except Exception:
                    pass


    # ----- UI Build -----

    def _build_ui(self):
        style = ttk.Style()
        # Styles for Connect button state
        style.configure("ConnectOn.TButton", foreground="#39ff14")
        style.configure("ConnectOff.TButton", foreground="#ffffff")
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure("Sidebar.TFrame", background="#111b21")
        style.configure("Chat.TFrame", background="#0b141a")

        # Dark treeview style for sidebar lists
        style.configure(
            "Sidebar.Treeview",
            background="#111b21",
            fieldbackground="#111b21",
            foreground="#e9edef",
            borderwidth=0,
            rowheight=20,
        )
        style.map(
            "Sidebar.Treeview",
            background=[("selected", "#202c33")],
            foreground=[("selected", "#e9edef")],
        )
        style.configure("Header.TFrame", background="#202c33")
        style.configure(
            "SidebarHeader.TLabel",
            background="#111b21",
            foreground="#e9edef",
            font=("Segoe UI", 11, "bold"),
        )
        style.configure(
            "Header.TLabel",
            background="#202c33",
            foreground="#e9edef",
            font=("Segoe UI", 10),
        )

        self.master.columnconfigure(0, weight=0, minsize=260)
        self.master.columnconfigure(1, weight=1)
        self.master.rowconfigure(1, weight=1)


        # Connection row buttons (dark theme)
        style.configure(
            "Conn.TButton",
            background="#1E2A30",
            foreground="#FFFFFF",
            padding=4,
        )
        style.map(
            "Conn.TButton",
            background=[("active", "#30444B")],
            foreground=[("active", "#FFFFFF")],
        )

        # Speed radio buttons (dark theme)
        style.configure(
            "Speed.TRadiobutton",
            background="#202c33",
            foreground="#FFFFFF",
        )
        style.map(
            "Speed.TRadiobutton",
            background=[("active", "#30444B")],
            foreground=[("active", "#FFFFFF")],
        )
        # Header
        header = ttk.Frame(self.master, style="Header.TFrame")
        header.grid(row=0, column=0, columnspan=2, sticky="nsew")
        header.columnconfigure(0, weight=1)

        # Toolbar tabs
        toolbar = ttk.Frame(header, style="Header.TFrame")
        toolbar.grid(row=0, column=0, sticky="w", padx=6, pady=(4, 0))

        def make_tab(name):
            return tk.Button(
                toolbar,
                text=name,
                command=lambda n=name: self.show_page(n),
                bg="#1E2A30",
                fg="#FFFFFF",
                activebackground="#30444B",
                activeforeground="#FFFFFF",
                bd=0,
                padx=10,
                pady=3,
                highlightthickness=0,
            )

        self.btn_tab_main = make_tab("Main")
        self.btn_tab_gps = make_tab("GPS")
        self.btn_tab_beacon = make_tab("Beacon")
        self.btn_tab_locator = make_tab("Locator")
        self.btn_tab_cat = make_tab("CAT")
        self.btn_tab_misc = make_tab("Misc")

        self.btn_tab_main.grid(row=0, column=0, padx=2)
        self.btn_tab_gps.grid(row=0, column=1, padx=2)
        self.btn_tab_beacon.grid(row=0, column=2, padx=2)
        self.btn_tab_locator.grid(row=0, column=3, padx=2)
        self.btn_tab_cat.grid(row=0, column=4, padx=2)
        self.btn_tab_misc.grid(row=0, column=5, padx=2)

        # Connection row
        conn = ttk.Frame(header, style="Header.TFrame")
        conn.grid(row=1, column=0, sticky="nsew", pady=(2, 4))
        conn.columnconfigure(13, weight=1)

        ttk.Label(conn, text="COM:", style="Header.TLabel").grid(row=0, column=0, padx=(8, 4))
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(conn, textvariable=self.port_var, width=9, state="readonly")
        self.port_combo.grid(row=0, column=1, padx=(0, 4))
        self._populate_ports()
        ttk.Button(conn, text="↻", width=3, command=self._populate_ports, style="Conn.TButton").grid(
            row=0, column=2, padx=(0, 8)
        )

        self.connect_btn = ttk.Button(conn, text="Connect", command=self.connect_port, style="ConnectOff.TButton")
        self.connect_btn.grid(row=0, column=3, padx=(0, 4))
        self.disconnect_btn = ttk.Button(
            conn, text="Disconnect", command=self.disconnect_port, state="disabled", style="Conn.TButton"
        )
        self.disconnect_btn.grid(row=0, column=4, padx=(0, 8))

        ttk.Label(conn, text="MyCall:", style="Header.TLabel").grid(
            row=0, column=5, padx=(0, 4)
        )
        self.call_var = tk.StringVar()

        self.call_entry = ttk.Entry(conn, textvariable=self.call_var, width=12)
        self.call_entry.grid(row=0, column=6, padx=(0, 8))

        # Grid square (Maidenhead) for locator/beacons
        ttk.Label(conn, text="Grid:", style="Header.TLabel").grid(
            row=0, column=7, padx=(0, 4)
        )
        self.grid_entry = ttk.Entry(conn, textvariable=self.mygrid_var, width=8)
        self.grid_entry.grid(row=0, column=8, padx=(0, 8))

        def mycall_trace(*_):
            self._save_settings()
            self._draw_locator_compass()

        self.call_var.trace_add("write", mycall_trace)

        ttk.Label(conn, text="Speed:", style="Header.TLabel").grid(
            row=0, column=9, padx=(0, 4)
        )
        self.r300_btn = ttk.Radiobutton(
            conn,
            text="R300",
            value="R300",
            variable=self.speed_var,
            command=self.on_speed_change,
            style="Speed.TRadiobutton",
        )
        self.r300_btn.grid(row=0, column=10, padx=(0, 2))
        self.r600_btn = ttk.Radiobutton(
            conn,
            text="R600",
            value="R600",
            variable=self.speed_var,
            command=self.on_speed_change,
            style="Speed.TRadiobutton",
        )
        self.r600_btn.grid(row=0, column=11, padx=(0, 8))

        self.clear_btn = ttk.Button(conn, text="Clear Messages", command=self.clear_messages, style="Conn.TButton")
        self.clear_btn.grid(row=0, column=12, padx=(0, 8))

        # Frequency quick-select dropdown (reference frequencies)
        self.freq_var = tk.StringVar()
        self.freq_combo = ttk.Combobox(
            conn,
            textvariable=self.freq_var,
            state="readonly",
            values=[
                "(30m) 10.148.3 MHz",
                "(20m) 14.109 MHz",
                "(40m) 7.090 MHz",
            ],
            width=18,
        )
        self.freq_combo.set("Freq")
        self.freq_combo.grid(row=0, column=13, padx=(0, 8))

        
        # Sidebar
        sidebar = ttk.Frame(self.master, style="Sidebar.TFrame")
        sidebar.grid(row=1, column=0, sticky="nsew")
        sidebar.rowconfigure(1, weight=2)
        sidebar.rowconfigure(4, weight=1)
        sidebar.columnconfigure(0, weight=1)

        ttk.Label(sidebar, text="CHATS", style="SidebarHeader.TLabel").grid(
            row=0, column=0, sticky="w", padx=8, pady=(8, 2)
        )

        self.chat_tree = ttk.Treeview(
            sidebar,
            show="tree",
            selectmode="browse",
            style="Sidebar.Treeview"
        )
        self.chat_tree.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 6))
        self.chat_tree.bind("<<TreeviewSelect>>", self.on_chat_select)

        # Last beacon status directly under chat list
        self.last_beacon_label = tk.Label(
            sidebar,
            text="Last beacon: —",
            bg="#0b141a",
            fg="#8696a0",
            font=self.font_meta,
            anchor="w",
        )
        self.last_beacon_label.grid(row=2, column=0, sticky="w", padx=8, pady=(0, 4))

        # "Beacons Heard" title immediately above the beacon list
        ttk.Label(sidebar, text="BEACONS HEARD", style="SidebarHeader.TLabel").grid(
            row=3, column=0, sticky="w", padx=8, pady=(0, 2)
        )

        self.beacon_tree = ttk.Treeview(
            sidebar,
            show="tree",
            selectmode="browse",
            style="Sidebar.Treeview"
        )
        self.beacon_tree.grid(row=4, column=0, sticky="nsew", padx=6, pady=(0, 8))

# Page container
        self.page_container = ttk.Frame(self.master, style="Chat.TFrame")
        self.page_container.grid(row=1, column=1, sticky="nsew")
        self.master.rowconfigure(1, weight=1)
        self.master.columnconfigure(1, weight=1)
        self.page_container.rowconfigure(0, weight=1)
        self.page_container.columnconfigure(0, weight=1)

        self.page_main = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_gps = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_beacon = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_locator = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_cat = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_misc = ttk.Frame(self.page_container, style="Chat.TFrame")

        for p in (self.page_main, self.page_gps, self.page_beacon, self.page_locator, self.page_cat, self.page_misc):
            p.grid(row=0, column=0, sticky="nsew")

        # Main chat page
        self.page_main.rowconfigure(0, weight=1)
        self.page_main.columnconfigure(0, weight=1)

        chat_wrapper = ttk.Frame(self.page_main, style="Chat.TFrame")
        chat_wrapper.grid(row=0, column=0, sticky="nsew")
        chat_wrapper.rowconfigure(0, weight=1)
        chat_wrapper.columnconfigure(0, weight=1)

        self.chat_text = tk.Text(
            chat_wrapper,
            bg="#0b141a",
            fg="#e9edef",
            wrap="word",
            state="disabled",
            bd=0,
            padx=10,
            pady=8,
            font=self.font_main,
        )
        self.chat_text.tag_config("ai_flag", foreground="#00ff00")

        self.chat_text.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(chat_wrapper, command=self.chat_text.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.chat_text.config(yscrollcommand=scroll.set)

        self.chat_text.tag_configure("sys_msg", foreground="#8696a0")
        self.chat_text.tag_configure("in_msg", foreground="#e9edef")
        self.chat_text.tag_configure(
            "out_msg", foreground="#e9edef", background="#005c4b"
        )
        self.chat_text.tag_configure(
            "meta", foreground="#c4ced4", font=self.font_meta
        )
        self.chat_text.tag_configure(
            "day_header",
            foreground="#8696a0",
            font=self.font_day,
            justify="center",
        )
        self.chat_text.tag_configure(
            "in_to_me",
            foreground="#FFA500",
        )

        # Input bar
        input_bar = ttk.Frame(self.page_main, style="Chat.TFrame")
        input_bar.grid(row=1, column=0, sticky="nsew")
        input_bar.columnconfigure(2, weight=1)

        tk.Label(
            input_bar,
            text="To:",
            bg="#0b141a",
            fg="#e9edef",
        ).grid(row=0, column=0, padx=(8, 4), pady=6)
        self.to_var = tk.StringVar(value="CQ")
        self.to_entry = ttk.Entry(
            input_bar,
            textvariable=self.to_var,
            width=10,
            font=self.font_main,
        )
        self.to_entry.grid(row=0, column=1, padx=(0, 8), pady=6)

        self.tx_var = tk.StringVar()
        self.tx_entry = ttk.Entry(
            input_bar,
            textvariable=self.tx_var,
            font=self.font_main,
        )
        self.tx_entry.grid(
            row=0,
            column=2,
            padx=(0, 4),
            pady=6,
            sticky="ew",
        )
        self.tx_entry.bind("<Return>", self._on_enter_pressed)

        self.clip_label = tk.Label(
            input_bar,
            text="📎",
            bg="#0b141a",
            fg="#FFFFFF",
            font=("Segoe UI Emoji", 11),
        )
        self.clip_label.grid(row=0, column=3, padx=(0, 4), pady=6)
        self.clip_label.bind("<Button-1>", lambda e: self.on_attach_file())
        self.clip_label.bind("<Enter>", lambda e: self._clip_hover(True))
        self.clip_label.bind("<Leave>", lambda e: self._clip_hover(False))

        self.lock_label = tk.Label(
            input_bar,
            text="🔒",
            bg="#0b141a",
            fg="#FFFFFF",
            font=("Segoe UI Emoji", 11),
        )
        self.lock_label.grid(row=0, column=4, padx=(0, 4), pady=6)
        self.lock_label.bind("<Button-1>", lambda e: self.on_padlock_click())
        self.lock_label.bind("<Enter>", lambda e: self._lock_hover(True))
        self.lock_label.bind("<Leave>", lambda e: self._lock_hover(False))

        self.send_btn = tk.Button(
            input_bar,
            text="Send",
            command=self.send_message,
            state="disabled",
            bg="#0A84FF",
            fg="#FFFFFF",
            activebackground="#3b9dff",
            activeforeground="#FFFFFF",
            bd=0,
            padx=12,
            pady=4,
            highlightthickness=0,
        )
        self.send_btn.grid(row=0, column=5, padx=(0, 8), pady=6)

        # GPS page content
        self._build_gps_page()

        # Beacon page content
        self._build_beacon_page()

        # Locator page
        self._build_locator_page()

        # CAT Control page
        self._build_cat_page()

        # Misc / Frequencies page
        self._build_misc_page()

        self._update_tab_styles()
        self._apply_ai_mode()
        self._update_ai_tab_label()
        # Start periodic refresh of last beacon label
        self._update_last_beacon_label()


    def _build_cat_page(self):
        """Placeholder CAT Control page (for future rig CAT integration)."""
        f = self.page_cat
        f.rowconfigure(0, weight=1)
        f.columnconfigure(0, weight=1)

        frame = ttk.Frame(f, style="Chat.TFrame")
        frame.grid(row=0, column=0, sticky="nsew", padx=16, pady=16)
        frame.columnconfigure(0, weight=1)

        lbl = ttk.Label(
            frame,
            text="CAT Control",
            style="Header.TLabel"
        )
        lbl.grid(row=0, column=0, sticky="w", pady=(0, 4))

        desc = ttk.Label(
            frame,
            text="Future rig CAT control settings will appear here (IC-703 / IC-705 / etc.).",
            style="Header.TLabel",
            wraplength=520,
            justify="left"
        )
        desc.grid(row=1, column=0, sticky="w")

    def _build_misc_page(self):
        """Misc page: show suggested operating frequencies, etc."""
        f = self.page_misc
        f.rowconfigure(0, weight=1)
        f.columnconfigure(0, weight=1)

        frame = ttk.Frame(f, style="Chat.TFrame")
        frame.grid(row=0, column=0, sticky="nw", padx=16, pady=16)
        frame.columnconfigure(0, weight=1)

        title = ttk.Label(
            frame,
            text="Suggested Robust Chat Frequencies",
            style="Header.TLabel"
        )
        title.grid(row=0, column=0, sticky="w", pady=(0, 6))

        # Frequencies list (simple text, user can QSY manually)
        ttk.Label(
            frame,
            text="(30m) 10.148.3 MHz",
            style="Header.TLabel"
        ).grid(row=1, column=0, sticky="w", pady=1)

        ttk.Label(
            frame,
            text="(20m) 14.109 MHz",
            style="Header.TLabel"
        ).grid(row=2, column=0, sticky="w", pady=1)

        ttk.Label(
            frame,
            text="(40m) 7.090 MHz",
            style="Header.TLabel"
        ).grid(row=3, column=0, sticky="w", pady=1)


        # --- AI Assistant (LM Studio Integration) ---
        sep = ttk.Separator(frame, orient="horizontal")
        sep.grid(row=10, column=0, columnspan=2, sticky="ew", pady=(12, 6))

        ttk.Label(
            frame,
            text="AI Assistant (LM Studio Integration)",
            style="Header.TLabel",
        ).grid(row=11, column=0, sticky="w", pady=(0, 4))


        instructions = (
            "1. Open LM Studio\n"
            "2. Download an AI model (e.g. Grok3-Reasoning-Gemma3)\n"
            "3. Go to the Developer page\n"
            "4. Turn on 'Status: Running'\n"
            "5. Confirm reachable at 127.0.0.1:1234\n"
            "6. Go to My Models, click \u22ef and 'Copy Default Identifier'\n"
            "7. Paste into Model Identifier below\n"
            "8. Leave Endpoint unless you changed the port\n"
            "9. Adjust Personality and Max Words\n"
            "10. Tick 'Activate AI Auto-Reply' to enable"
        )
        ttk.Label(
            frame,
            text=instructions,
            style="Hint.TLabel",
            wraplength=560,
            justify="left",
        ).grid(row=12, column=0, sticky="w", pady=(0, 6))

        self.ai_enabled_var = tk.BooleanVar(value=self.ai_autoreply_enabled)
        ttk.Checkbutton(
            frame,
            text="Activate AI Auto-Reply",
            variable=self.ai_enabled_var,
            command=self._toggle_ai_autoreply,
            style="Switch.TCheckbutton",
        ).grid(row=13, column=0, sticky="w", pady=(0, 8))

        # Endpoint
        ttk.Label(
            frame,
            text="Endpoint:",
            style="Hint.TLabel",
        ).grid(row=14, column=0, sticky="w")
        self.ai_endpoint_var = tk.StringVar(value=self.ai_endpoint)
        ttk.Entry(
            frame,
            textvariable=self.ai_endpoint_var,
            width=60,
        ).grid(row=15, column=0, sticky="w", pady=(0, 4))

        # Model Identifier
        ttk.Label(
            frame,
            text="Model Identifier:",
            style="Hint.TLabel",
        ).grid(row=16, column=0, sticky="w")
        self.ai_model_var = tk.StringVar(value=self.ai_model)
        ttk.Entry(
            frame,
            textvariable=self.ai_model_var,
            width=60,
        ).grid(row=17, column=0, sticky="w", pady=(0, 4))

        # Personality / Guidance
        ttk.Label(
            frame,
            text="Personality / Guidance:",
            style="Hint.TLabel",
        ).grid(row=18, column=0, sticky="w")
        self.ai_personality_box = tk.Text(
            frame,
            height=4,
            width=60,
            wrap="word",
        )
        self.ai_personality_box.insert(
            "1.0",
            self.ai_personality,
        )
        self.ai_personality_box.grid(row=19, column=0, sticky="w", pady=(0, 4))

        # Max reply words
        max_row = ttk.Frame(frame)
        max_row.grid(row=20, column=0, sticky="w", pady=(0, 8))
        ttk.Label(
            max_row,
            text="Max Reply Length (words):",
            style="Hint.TLabel",
        ).pack(side="left")
        self.ai_max_words_var = tk.StringVar(value=str(self.ai_max_words))
        ttk.Entry(
            max_row,
            textvariable=self.ai_max_words_var,
            width=8,
        ).pack(side="left", padx=(4, 0))

        # Status label for AI settings / activation
        self.ai_status_var = tk.StringVar(value="")
        self.ai_status_label = tk.Label(
            frame,
            textvariable=self.ai_status_var,
            bg="#0b141a",
            fg="#ffffff",
            font=self.font_small,
        )
        self.ai_status_label.grid(row=21, column=0, sticky="w", pady=(2, 0))

        # Save button for AI settings
        self.ai_save_btn = tk.Button(
            frame,
            text="💾 Save AI Settings",
            command=self._save_ai_settings,
            bg="#0b141a",
            fg="#ffffff",
            activebackground="#1e2a33",
            activeforeground="#ffffff",
            bd=1,
            padx=8,
            pady=2,
            highlightthickness=0,
        )
        self.ai_save_btn.grid(row=22, column=0, sticky="w", pady=(4, 4))

    def _build_gps_page(self):
        f = self.page_gps
        for i in range(3):
            f.rowconfigure(i, weight=0)
        f.rowconfigure(3, weight=1)
        for j in range(10):
            f.columnconfigure(j, weight=0)
        f.columnconfigure(9, weight=1)

        # Row 0: Fixed Position
        tk.Label(
            f,
            text="Send Fixed Position",
            bg="#0b141a",
            fg="#e9edef",
            font=self.font_main,
        ).grid(row=0, column=0, padx=(16, 6), pady=(16, 6), sticky="w")

        tk.Label(f, text="Name", bg="#0b141a", fg="#8696a0").grid(
            row=0, column=1, padx=(0, 2), pady=(16, 6), sticky="w"
        )
        ttk.Entry(f, textvariable=self.fixed_name_var, width=10).grid(
            row=0, column=2, padx=(0, 8), pady=(16, 6), sticky="w"
        )

        tk.Label(f, text="Lat", bg="#0b141a", fg="#8696a0").grid(
            row=0, column=3, padx=(0, 2), pady=(16, 6), sticky="w"
        )
        ttk.Entry(f, textvariable=self.fixed_lat_var, width=10).grid(
            row=0, column=4, padx=(0, 8), pady=(16, 6), sticky="w"
        )

        tk.Label(f, text="Lon", bg="#0b141a", fg="#8696a0").grid(
            row=0, column=5, padx=(0, 2), pady=(16, 6), sticky="w"
        )
        ttk.Entry(f, textvariable=self.fixed_lon_var, width=10).grid(
            row=0, column=6, padx=(0, 8), pady=(16, 6), sticky="w"
        )

        tk.Button(
            f,
            text="SEND",
            command=self._gps_fixed_send,
            bg="#005c4b",
            fg="#ffffff",
            bd=0,
            padx=10,
            pady=3,
            highlightthickness=0,
        ).grid(row=0, column=7, padx=(0, 8), pady=(16, 6), sticky="w")

        for var in (self.fixed_name_var, self.fixed_lat_var, self.fixed_lon_var):
            var.trace_add("write", lambda *_: self._save_settings())

        # Row 1: External GPS from COM (NMEA)
        tk.Label(
            f,
            text="External GPS",
            bg="#0b141a",
            fg="#e9edef",
            font=self.font_main,
        ).grid(row=1, column=0, padx=(16, 6), pady=6, sticky="w")

        self.gps_port_combo = ttk.Combobox(
            f, textvariable=self.gps_port_var, width=9, state="readonly"
        )
        self.gps_port_combo.grid(row=1, column=1, padx=(0, 4), pady=6, sticky="w")

        btn_gps_conn = tk.Button(
            f,
            text="Connect",
            command=self._gps_connect_toggle,
            bg="#30444B",
            fg="#ffffff",
            bd=0,
            padx=8,
            pady=3,
            highlightthickness=0,
        )
        btn_gps_conn.grid(row=1, column=2, padx=(0, 8), pady=6, sticky="w")
        self.gps_connect_btn = btn_gps_conn

        tk.Label(f, text="Lat", bg="#0b141a", fg="#8696a0").grid(
            row=1, column=3, padx=(0, 2), pady=6, sticky="w"
        )
        ttk.Entry(f, textvariable=self.gps_lat_var, width=10).grid(
            row=1, column=4, padx=(0, 8), pady=6, sticky="w"
        )

        tk.Label(f, text="Lon", bg="#0b141a", fg="#8696a0").grid(
            row=1, column=5, padx=(0, 2), pady=6, sticky="w"
        )
        ttk.Entry(f, textvariable=self.gps_lon_var, width=10).grid(
            row=1, column=6, padx=(0, 8), pady=6, sticky="w"
        )

        tk.Button(
            f,
            text="SEND",
            command=self._gps_nmea_send,
            bg="#005c4b",
            fg="#ffffff",
            bd=0,
            padx=10,
            pady=3,
            highlightthickness=0,
        ).grid(row=1, column=7, padx=(0, 8), pady=6, sticky="w")

        for var in (self.gps_port_var, self.gps_lat_var, self.gps_lon_var):
            var.trace_add("write", lambda *_: self._save_settings())

        # Row 2: LiNK500/TEENSY TNC via %AZ
        tk.Label(
            f,
            text="LiNK500/TEENSY TNC",
            bg="#0b141a",
            fg="#e9edef",
            font=self.font_main,
        ).grid(row=2, column=0, padx=(16, 6), pady=6, sticky="w")

        self.link500_port_combo = ttk.Combobox(
            f, textvariable=self.link500_port_var, width=9, state="readonly"
        )
        self.link500_port_combo.grid(row=2, column=1, padx=(0, 4), pady=6, sticky="w")

        btn_l5_conn = tk.Button(
            f,
            text="Connect",
            command=self._link500_connect_toggle,
            bg="#30444B",
            fg="#ffffff",
            bd=0,
            padx=8,
            pady=3,
            highlightthickness=0,
        )
        btn_l5_conn.grid(row=2, column=2, padx=(0, 8), pady=6, sticky="w")
        self.link500_connect_btn = btn_l5_conn

        tk.Label(f, text="Lat", bg="#0b141a", fg="#8696a0").grid(
            row=2, column=3, padx=(0, 2), pady=6, sticky="w"
        )
        ttk.Entry(f, textvariable=self.link500_lat_var, width=10).grid(
            row=2, column=4, padx=(0, 8), pady=6, sticky="w"
        )

        tk.Label(f, text="Lon", bg="#0b141a", fg="#8696a0").grid(
            row=2, column=5, padx=(0, 2), pady=6, sticky="w"
        )
        ttk.Entry(f, textvariable=self.link500_lon_var, width=10).grid(
            row=2, column=6, padx=(0, 8), pady=6, sticky="w"
        )

        btn_l5_get = tk.Button(
            f,
            text="GET POSITION",
            command=self._link500_get_position,
            bg="#202c33",
            fg="#ffffff",
            bd=0,
            padx=8,
            pady=3,
            highlightthickness=0,
        )
        btn_l5_get.grid(row=2, column=7, padx=(0, 4), pady=6, sticky="w")
        self.link500_get_btn = btn_l5_get

        tk.Button(
            f,
            text="SEND",
            command=self._link500_gps_send,
            bg="#005c4b",
            fg="#ffffff",
            bd=0,
            padx=10,
            pady=3,
            highlightthickness=0,
        ).grid(row=2, column=8, padx=(0, 8), pady=6, sticky="w")

        for var in (self.link500_port_var, self.link500_lat_var, self.link500_lon_var):
            var.trace_add("write", lambda *_: self._save_settings())

        # Once both combos exist, populate port lists
        self._populate_gps_ports()

        tk.Label(
            f,
            text="All three GPS sections persist. LiNK500/TEENSY GET POSITION: KISS-off → ESC SP %AZ → KISS-on → update fields.",
            bg="#0b141a",
            fg="#8696a0",
            font=self.font_meta,
            justify="left",
        ).grid(row=3, column=0, columnspan=9, padx=16, pady=(8, 4), sticky="w")

    # ----- Beacon page -----


    def _build_beacon_page(self):
        f = self.page_beacon
        f.configure(style="Chat.TFrame")

        for c in range(5):
            f.columnconfigure(c, weight=0)
        f.columnconfigure(5, weight=1)
        f.rowconfigure(0, weight=0)
        f.rowconfigure(1, weight=1)

        label = tk.Label(
            f,
            text="Beacon Timing",
            bg="#0b141a",
            fg="#e9edef",
            font=self.font_main,
            justify="left",
        )
        label.grid(row=0, column=0, padx=(16, 10), pady=(16, 8), sticky="w")

        # Radio buttons: Off, 5, 10, 15 minutes
        def make_rb(text, minutes, col):
            rb = tk.Radiobutton(
                f,
                text=text,
                value=minutes,
                variable=self.beacon_interval_var,
                command=self._on_beacon_interval_changed,
                bg="#0b141a",
                fg="#e9edef",
                selectcolor="#202c33",
                activebackground="#202c33",
                activeforeground="#ffffff",
                highlightthickness=0,
            )
            rb.grid(row=0, column=col, padx=(4, 4), pady=(16, 8), sticky="w")

        make_rb("Off", 0, 1)
        make_rb("Every 5 min", 5, 2)
        make_rb("Every 10 min", 10, 3)
        make_rb("Every 15 min", 15, 4)

        hint = tk.Label(
            f,
            text=(
                "Select an interval to start automatic beacons.\n"
                "On each change, one beacon is transmitted immediately, then repeated at the chosen interval.\n"
                "Beacon format: **MYCALL /... [Lat nn.nnnnn Lon nn.nnnnn] if valid position is available."
            ),
            bg="#0b141a",
            fg="#8696a0",
            font=self.font_meta,
            justify="left",
        )
        hint.grid(row=1, column=0, columnspan=6, padx=16, pady=(0, 12), sticky="nw")
    # ----- Beacon timing helpers -----

    def _build_beacon_string(self):
        my = self._callsign_base(self.call_var.get() or "")
        if not my:
            return None
        # Keep link view current
        self._prune_beacons(save=False)
        child_calls = sorted(self.links.keys())
        parts = [f"**{my}"]
        for c in child_calls:
            parts.append(f"/{c}")
        # Append position if we have one (LiNK500 -> GPS -> Fixed)
        lat, lon = self._get_own_position()
        if lat is not None and lon is not None:
            parts.append(f"Lat {lat:.5f} Lon {lon:.5f}")
        # Append A.I flag when enabled
        if self._ai_flag_active():
            parts.append("[A.I]")
        return " ".join(parts)


    def _send_beacon_now(self):
        """Transmit a network beacon now, respecting KISS mode if active."""
        beacon = self._build_beacon_string()
        if not beacon:
            self.log("[Beacon] Cannot send beacon: set MyCall first.")
            return
        if not self.ser:
            self.log("[Beacon] Not connected: beacon not sent.")
            return

        src = (self.call_var.get() or "").strip().upper() or "ME"
        dst = "CQ"
        now = time.time()
        ts = time.strftime("%H:%M:%S", time.localtime(now))
        msg = {
            "ts": ts,
            "epoch": now,
            "direction": "out",
            "text": beacon,
            "src": src,
            "dst": dst,
        }

        try:
            if self.kiss_mode:
                # Use the same KISS UI frame path as manual sends.
                frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=beacon)
                self._write_bytes(frame)
            else:
                # Fallback: legacy raw beacon for non-KISS / CLI scenarios.
                wire = (beacon + "\r\n").encode("utf-8", errors="replace")
                self.ser.write(wire)
                self.ser.flush()
        except Exception as e:
            self.log(f"[Beacon] TX error: {e}")
            return

        # Record last beacon time for UI
        self.last_beacon_epoch = now

        def do():
            # Beacons run in the background: do not append to chat view.
            # Only update beacon/link graph + "Beacons Heard" panel.
            if hasattr(self, "_update_beacons_from_text"):
                self._update_beacons_from_text(beacon, now)
                self._refresh_beacon_listbox()
            # Refresh "Last beacon" label immediately
            if hasattr(self, "last_beacon_label"):
                try:
                    self._update_last_beacon_label()
                except Exception:
                    pass

        self._enqueue_ui(do)
        self.log(f"[Beacon] Sent: {beacon}")

    def _cancel_beacon_timer(self):
        if getattr(self, "beacon_job", None):
            try:
                self.master.after_cancel(self.beacon_job)
            except Exception:
                pass
            self.beacon_job = None

    def _on_beacon_interval_changed(self):
        minutes = int(self.beacon_interval_var.get())
        # Stop any existing timer
        self._cancel_beacon_timer()
        if minutes <= 0:
            self.log("[Beacon] Automatic beacons disabled.")
            return
        # Immediate beacon on change
        self._send_beacon_now()
        # Schedule next
        self._schedule_next_beacon(minutes)
        # Persist user preference for interval
        self._save_settings()

    def _schedule_next_beacon(self, minutes):
        if minutes <= 0:
            return
        ms = max(1, int(minutes * 60 * 1000))
        self.beacon_job = self.master.after(ms, self._beacon_timer_fire)

    def _beacon_timer_fire(self):
        minutes = int(self.beacon_interval_var.get())
        if minutes <= 0:
            self.beacon_job = None
            return
        self._send_beacon_now()
        self._schedule_next_beacon(minutes)


    def _apply_beacon_interval_on_connect(self):
        """
        Apply the stored beacon interval when TNC/KISS becomes ready.
        Uses the Beacon tab radio selection:
        - 0 = Off  -> do not start auto beacons
        - 5/10/15  -> start automatic beacons at that interval
        """
        # Always cancel any previous timer when (re)connecting
        try:
            self._cancel_beacon_timer()
        except Exception:
            pass

        # Require active serial + KISS to avoid firing beacons into nothing
        if not getattr(self, "ser", None) or not getattr(self, "kiss_mode", False):
            return

        try:
            minutes = int(self.beacon_interval_var.get())
        except Exception:
            minutes = 0

        if minutes <= 0:
            # Respect "Off" selection: no auto beacon on connect
            self.log("[Beacon] Auto beacon is OFF (per Beacon tab).")
            return

        # Start automatic beacons using the stored interval
        self.log(f"[Beacon] Auto beacon interval {minutes} min (per Beacon tab).")
        self._send_beacon_now()
        self._schedule_next_beacon(minutes)



    def _update_last_beacon_label(self):
        """
        Periodically refresh the "Last beacon" label based on last_beacon_epoch.
        Runs in the UI thread; safe to call via after().
        """
        try:
            if not hasattr(self, "last_beacon_label"):
                return
            if not self.last_beacon_epoch:
                self.last_beacon_label.config(text="Last beacon: —")
            else:
                delta = max(0, int(time.time() - float(self.last_beacon_epoch)))
                if delta < 60:
                    txt = f"Last beacon: {delta}s ago"
                else:
                    mins = delta // 60
                    txt = f"Last beacon: {mins} min ago"
                self.last_beacon_label.config(text=txt)
        except Exception:
            pass
        try:
            # Refresh every 5 seconds while UI is alive
            self.master.after(5000, self._update_last_beacon_label)
        except Exception:
            pass
    # ----- Locator page -----

    def _build_locator_page(self):
        self.page_locator.rowconfigure(1, weight=1)
        self.page_locator.columnconfigure(0, weight=1)

        hint = tk.Label(
            self.page_locator,
            text=(
                "Locator Compass — MyCall at centre. Stations with valid positions plotted.\n"
                "Ranges scaled to 0–1000 miles; lines clamp at 1000 (internally up to 1500)."
            ),
            bg="#0b141a",
            fg="#8696a0",
            font=self.font_meta,
            justify="left",
        )
        hint.grid(row=0, column=0, sticky="w", padx=16, pady=(14, 4))

        self.locator_canvas = tk.Canvas(
            self.page_locator,
            bg="#0b141a",
            highlightthickness=0,
            bd=0,
        )
        self.locator_canvas.grid(
            row=1, column=0, sticky="nsew", padx=40, pady=20
        )
        self.locator_canvas.bind(
            "<Configure>", lambda e: self._draw_locator_compass()
        )

        self._draw_locator_compass()

    # ----- Locator compass drawing & plotting -----

    
    def _get_own_position(self):
            """
            Return (lat, lon) for own station using:
            1) GPS NMEA
            2) LiNK500 GPS
            3) Fixed Lat/Lon
            4) My Grid Square (Maidenhead)
            Also sets self._beacon_pos_source to:
            "GPS" | "LINK500" | "FIXED" | "GRID" | None
            """
            # 1) GPS NMEA
            try:
                lat = float(self.gps_lat_var.get())
                lon = float(self.gps_lon_var.get())
                self._beacon_pos_source = "GPS"
                return lat, lon
            except Exception:
                pass

            # 2) LiNK500 GPS
            try:
                lat = float(self.link500_lat_var.get())
                lon = float(self.link500_lon_var.get())
                self._beacon_pos_source = "LINK500"
                return lat, lon
            except Exception:
                pass

            # 3) Fixed manual Lat/Lon
            try:
                lat = float(self.fixed_lat_var.get())
                lon = float(self.fixed_lon_var.get())
                self._beacon_pos_source = "FIXED"
                return lat, lon
            except Exception:
                pass

            # 4) Maidenhead grid
            grid = (self.mygrid_var.get() or "").strip().upper()
            if grid:
                try:
                    lat, lon = grid_to_latlon(grid)
                    self._beacon_pos_source = "GRID"
                    return lat, lon
                except Exception:
                    pass

            self._beacon_pos_source = None
            return None, None

    def _has_any_position_source(self):
        """
        True if any usable position is configured:
        GPS, LiNK500, Fixed Lat/Lon or Grid.
        """
        # GPS
        try:
            if float(self.gps_lat_var.get()) and float(self.gps_lon_var.get()):
                return True
        except Exception:
            pass

        # LiNK500
        try:
            if float(self.link500_lat_var.get()) and float(self.link500_lon_var.get()):
                return True
        except Exception:
            pass

        # Fixed
        try:
            if float(self.fixed_lat_var.get()) and float(self.fixed_lon_var.get()):
                return True
        except Exception:
            pass

        # Grid
        if (self.mygrid_var.get() or "").strip():
            return True

        return False



    def _draw_locator_compass(self):
        if not self.locator_canvas:
            return
        c = self.locator_canvas
        c.delete("all")

        w = c.winfo_width()
        h = c.winfo_height()
        if w < 80 or h < 80:
            return

        cx = w / 2
        cy = h / 2
        radius = min(w, h) * 0.4  # 1000-mile circle

        line = "#39ff14"
        faint = "#1f3f20"
        text_col = "#39ff14"

        # Outer circle
        c.create_oval(
            cx - radius,
            cy - radius,
            cx + radius,
            cy + radius,
            outline=line,
            width=1,
        )

        # Crosshairs
        c.create_line(cx, cy - radius, cx, cy + radius, fill=line)
        c.create_line(cx - radius, cy, cx + radius, cy, fill=line)

        # Degree ticks every 30°
        for deg in range(0, 360, 30):
            ang = math.radians(deg)
            inner = radius * 0.92
            outer = radius
            x1 = cx + inner * math.sin(ang)
            y1 = cy - inner * math.cos(ang)
            x2 = cx + outer * math.sin(ang)
            y2 = cy - outer * math.cos(ang)
            c.create_line(x1, y1, x2, y2, fill=faint)

        # Mile rings 50–1000; labels every 200
        max_miles = 1000.0
        for miles in range(50, 1001, 50):
            r = radius * (miles / max_miles)
            if r < 4:
                continue
            c.create_oval(
                cx - r,
                cy - r,
                cx + r,
                cy + r,
                outline=faint,
                width=1,
            )
            if miles % 200 == 0:
                c.create_text(
                    cx,
                    cy - r - 6,
                    text=str(miles),
                    fill="#3f7f40",
                    font=("Segoe UI", 7),
                )

        # Cardinal labels
        label_offset = radius + 14
        c.create_text(
            cx,
            cy - label_offset,
            text="N",
            fill=text_col,
            font=("Segoe UI", 11, "bold"),
        )
        c.create_text(
            cx,
            cy + label_offset,
            text="S",
            fill=text_col,
            font=("Segoe UI", 11, "bold"),
        )
        c.create_text(
            cx + label_offset,
            cy,
            text="E",
            fill=text_col,
            font=("Segoe UI", 11, "bold"),
        )
        c.create_text(
            cx - label_offset,
            cy,
            text="W",
            fill=text_col,
            font=("Segoe UI", 11, "bold"),
        )

        # Determine my position and source
        my = (self.call_var.get() or "").strip().upper()
        my_base = self._callsign_base(my) if my else "MYCALL"
        my_lat, my_lon = self._get_own_position()
        src = getattr(self, "_beacon_pos_source", None)

        # Choose center marker style based on source
        if src in ("GPS", "LINK500"):
            center_color = "#ff4d4d"  # red
            src_label = "[GPS]" if src == "GPS" else "[LINK500]"
        elif src == "FIXED":
            center_color = "#00b7ff"  # blue
            src_label = "[Fixed]"
        elif src == "GRID":
            center_color = "#cccccc"  # grey
            src_label = "[Maidenhead]"
        else:
            center_color = text_col
            src_label = ""

        # Draw my marker at centre
        c.create_oval(
            cx - 5,
            cy - 5,
            cx + 5,
            cy + 5,
            fill=center_color,
            outline="",
        )
        c.create_text(
            cx,
            cy - 12,
            text=my_base,
            fill=text_col,
            font=("Segoe UI", 11, "bold"),
        )
        if src_label:
            c.create_text(
                cx,
                cy + 10,
                text=src_label,
                fill=center_color,
                font=("Segoe UI", 8),
            )

        # If no valid position, stop here
        if my_lat is None or my_lon is None:
            return

        def bearing_and_range(lat1, lon1, lat2, lon2):
            """Return (bearing_deg, distance_miles). Bearing: 0=N, 90=E."""
            r_earth = 3958.8  # miles
            phi1 = math.radians(lat1)
            phi2 = math.radians(lat2)
            dphi = math.radians(lat2 - lat1)
            dlambda = math.radians(lon2 - lon1)

            a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlambda / 2) ** 2
            cang = 2 * math.atan2(math.sqrt(a), max(1e-12, math.sqrt(1 - a)))
            dist = r_earth * cang

            y = math.sin(dlambda) * math.cos(phi2)
            x = math.cos(phi1) * math.sin(phi2) - math.sin(phi1) * math.cos(phi2) * math.cos(dlambda)
            brg = (math.degrees(math.atan2(y, x)) + 360.0) % 360.0
            return brg, dist

        def bearing_to_compass(brg):
            """Convert bearing in degrees to 16-wind compass label."""
            dirs = [
                "N", "NNE", "NE", "ENE",
                "E", "ESE", "SE", "SSE",
                "S", "SSW", "SW", "WSW",
                "W", "WNW", "NW", "NNW",
            ]
            idx = int((brg + 11.25) // 22.5) % 16
            return dirs[idx]

        # Plot each known station from positions
        for call, pos in (self.positions or {}).items():
            try:
                lat2 = float(pos.get("lat"))
                lon2 = float(pos.get("lon"))
            except Exception:
                continue

            if call == my_base:
                continue

            brg, dist = bearing_and_range(my_lat, my_lon, lat2, lon2)

            # Clamp distance for drawing
            dist_clamped = min(dist, 1500.0)
            if dist_clamped <= max_miles:
                r = radius * (dist_clamped / max_miles)
            else:
                r = radius

            ang = math.radians(brg)
            x = cx + r * math.sin(ang)
            y = cy - r * math.cos(ang)

            # Radial line & marker
            c.create_line(cx, cy, x, y, fill="#2aff70", width=1)
            c.create_oval(
                x - 2,
                y - 2,
                x + 2,
                y + 2,
                fill="#39ff14",
                outline="",
            )

            # Label with CALL, distance, and compass point
            compass_pt = bearing_to_compass(brg)
            label = f"{call} {int(dist)}mi {compass_pt}"
            c.create_text(
                x + 6,
                y,
                text=label,
                anchor="w",
                fill="#39ff14",
                font=("Segoe UI", 8),
            )
    # ----- Tabs -----

    def _update_tab_styles(self):
        inactive_bg = "#1E2A30"
        active_bg = "#30444B"
        inactive_fg = "#FFFFFF"
        for btn in (
            self.btn_tab_main,
            self.btn_tab_gps,
            self.btn_tab_beacon,
            self.btn_tab_locator,
            getattr(self, 'btn_tab_cat', None),
            getattr(self, 'btn_tab_misc', None),
        ):
            if btn is not None:
                btn.configure(bg=inactive_bg, fg=inactive_fg)

        if self.current_page == "Main":
            self.btn_tab_main.configure(bg=active_bg)
        elif self.current_page == "GPS":
            self.btn_tab_gps.configure(bg=active_bg)
        elif self.current_page == "Beacon":
            self.btn_tab_beacon.configure(bg=active_bg)
        elif self.current_page == "Locator":
            self.btn_tab_locator.configure(bg=active_bg)
        elif self.current_page == "CAT" and hasattr(self, 'btn_tab_cat'):
            self.btn_tab_cat.configure(bg=active_bg)
        elif self.current_page == "Misc" and hasattr(self, 'btn_tab_misc'):
            self.btn_tab_misc.configure(bg=active_bg)

    def show_page(self, name: str):
        self.current_page = name
        if name == "Main":
            self.page_main.tkraise()
        elif name == "GPS":
            self.page_gps.tkraise()
        elif name == "Beacon":
            self.page_beacon.tkraise()
        elif name == "Locator":
            self.page_locator.tkraise()
        elif name == "CAT":
            self.page_cat.tkraise()
        elif name == "Misc":
            self.page_misc.tkraise()
        else:
            self.page_main.tkraise()
            self.current_page = "Main"

        self._update_tab_styles()
        try:
            self._update_ai_tab_label()
        except Exception:
            pass

        if name == "Locator":
            self._draw_locator_compass()

    

    
    
    def _toggle_ai_autoreply(self):
        """Toggle AI auto-reply when the checkbox changes."""
        enabled = bool(self.ai_enabled_var.get()) if hasattr(self, "ai_enabled_var") else False
        self.ai_autoreply_enabled = enabled

        # Save all current AI settings (fields + flag)
        self._save_ai_settings(show_status=False)

        # Log + inline status on Misc page
        if enabled:
            self.log("[AI] Auto-Reply ENABLED — monitoring messages addressed to your callsign.")
            if hasattr(self, "ai_status_var"):
                self.ai_status_var.set("A.I Auto-Reply is now ACTIVE")
                self._schedule_clear_ai_status()
        else:
            self.log("[AI] Auto-Reply DISABLED — manual sending restored.")
            if hasattr(self, "ai_status_var"):
                self.ai_status_var.set("A.I Auto-Reply is now DISABLED")
                self._schedule_clear_ai_status()

        # Apply UI lock/unlock on Main page
        self._apply_ai_mode()

    def _save_ai_settings(self, show_status: bool = True):
        """Read AI fields from UI, persist to settings.json, and optionally show confirmation."""
        # Endpoint
        if hasattr(self, "ai_endpoint_var"):
            self.ai_endpoint = self.ai_endpoint_var.get().strip()
        # Model
        if hasattr(self, "ai_model_var"):
            self.ai_model = self.ai_model_var.get().strip()
        # Personality
        if hasattr(self, "ai_personality_box"):
            self.ai_personality = self.ai_personality_box.get("1.0", "end").strip()
        # Max words
        if hasattr(self, "ai_max_words_var"):
            try:
                self.ai_max_words = int(self.ai_max_words_var.get().strip())
            except Exception:
                self.ai_max_words = 200
        # Enabled flag (from checkbox)
        if hasattr(self, "ai_enabled_var"):
            self.ai_autoreply_enabled = bool(self.ai_enabled_var.get())

        # Persist
        self.settings["ai_autoreply_enabled"] = self.ai_autoreply_enabled
        self.settings["ai_endpoint"] = self.ai_endpoint
        self.settings["ai_model"] = self.ai_model
        self.settings["ai_personality"] = self.ai_personality
        self.settings["ai_max_words"] = self.ai_max_words
        self._save_settings()

        # UI confirmation
        if show_status and hasattr(self, "ai_status_var"):
            self.ai_status_var.set("AI settings saved successfully.")
            self._schedule_clear_ai_status()

    def _schedule_clear_ai_status(self, delay_ms: int = 3000):
        """Clear the AI status label after a short delay."""
        if not hasattr(self, "ai_status_var"):
            return

        def _clear():
            try:
                self.ai_status_var.set("")
            except Exception:
                pass

        try:
            self.master.after(delay_ms, _clear)
        except Exception:
            pass

    def _apply_ai_mode(self):
        """Visually enforce AI mode lockout on Main page."""
        # Main page must already be built
        page = self.pages.get("Main") if hasattr(self, "pages") else None
        if not page:
            return

        send_entry = getattr(self, "tx_entry", None)
        send_button = getattr(self, "send_btn", None)

        if self.ai_autoreply_enabled:
            if send_entry is not None:
                send_entry.config(state="disabled")
            if send_button is not None:
                send_button.config(state="disabled")

            # Create or show banner
            if not hasattr(self, "ai_banner"):
                self.ai_banner = tk.Label(
                    page,
                    text="A.I mode is activated, deactivate to enable manual sending",
                    bg="#00ff00",
                    fg="#000000",
                    font=self.font_small,
                    pady=4,
                )
            # Ensure visible
            self.ai_banner.pack(side="bottom", fill="x")
        else:
            # Re-enable manual sending
            if send_entry is not None:
                send_entry.config(state="normal")
            if send_button is not None:
                send_button.config(state="normal")
            # Hide banner if present
            if hasattr(self, "ai_banner"):
                self.ai_banner.pack_forget()

        # Update AI tab label according to current AI mode
        try:
            self._update_ai_tab_label()
        except Exception:
            pass

    # ==============================================================
    # === A.I. AUTO-REPLY SYSTEM (LOCKED SECTION — DO NOT MODIFY) ===
    # ==============================================================

    def _ai_process_incoming(self, src: str, dst: str, body_text: str):
        """Handle AI auto-reply when a message is addressed to our MYCALL."""
        # Basic guards
        if not getattr(self, "ai_autoreply_enabled", False):
            return

        mycall = (self.call_var.get() or "").strip().upper()
        if not mycall:
            return

                # Only react if message is addressed to us or explicitly mentions our call
        try:
            addressed_to_me = bool(self._is_to_me(dst))
        except Exception:
            addressed_to_me = (dst or "").upper().startswith(mycall)

        mentions_me = mycall in (body_text or "").upper()

        if not (addressed_to_me or mentions_me):
            return

        # Allow ACK / protocol housekeeping to complete before AI reply
        try:
            self.log("[AI] Waiting 1.0s post-ACK before generating reply.")
        except Exception:
            pass
        try:
            import time as _ai_time
            _ai_time.sleep(1.0)
        except Exception:
            pass

        # Avoid loops: ignore if source is us
        if self._callsign_base(src) == self._callsign_base(mycall):
            return

        endpoint = (getattr(self, "ai_endpoint", "") or "").strip()
        model = (getattr(self, "ai_model", "") or "").strip()
        personality = (getattr(self, "ai_personality", "") or "").strip()
        try:
            max_words = int(getattr(self, "ai_max_words", 200) or 200)
        except Exception:
            max_words = 200

        # Normalize endpoint: if user only set host:port, append LM Studio chat path.
        if endpoint and "/v1/" not in endpoint:
            if endpoint.endswith("/"):
                endpoint = endpoint[:-1]
            endpoint = endpoint + "/v1/chat/completions"

        if not endpoint or not model:
            self.log("[AI] Missing endpoint or model; cannot auto-reply.")
            return

        # Build prompt so AI replies as our station (MYCALL) to the caller (src)
        user_msg = f"Message from {src} to {dst} (you are {mycall}): {body_text}"
        system_text = personality or "You are a concise, factual ham radio operator who follows amateur radio rules."
        if mycall:
            system_text += (
                f" You are station {mycall}. Always reply in first person as {mycall}, "
                f"addressing the calling station ({src}) directly. Do not pretend to be the other station."
            )
        messages = [
            {
                "role": "system",
                "content": system_text,
            },
            {
                "role": "user",
                "content": user_msg,
            },
        ]


        # Log that we are about to request an AI reply for visibility
        try:
            self.log(f"[AI] Requesting auto-reply for message from {src} to {dst}")
        except Exception:
            pass

        try:
            import requests  # type: ignore
        except Exception:
            self.log("[AI] 'requests' module not available; cannot contact LM Studio.")
            return

        payload = {
            "model": model,
            "messages": messages,
            "temperature": 0.7,
        }

        try:
            try:
                self.log(f"[AI] Calling LM Studio at: {endpoint}")
            except Exception:
                pass
            # Separate connect/read timeouts for robustness.
            resp = requests.post(endpoint, json=payload, timeout=(10, 90))
            resp.raise_for_status()
            data = resp.json()
            reply = (
                data.get("choices", [{}])[0]
                .get("message", {})
                .get("content", "")
            ).strip()
        except requests.exceptions.ReadTimeout:
            self.log("[AI] LM Studio took too long to respond (read timeout). Check the model is loaded or reduce request size.")
            return
        except requests.exceptions.ConnectionError:
            self.log("[AI] Cannot reach LM Studio. Ensure 'Status: Running' is enabled and endpoint is correct.")
            return
        except Exception as e:
            self.log(f"[AI] Error contacting LM Studio: {e}")
            return

        if not reply:
            return

        # Strip out any <think>...</think> reasoning blocks to save on-air time
        try:
            import re as _re_ai
            reply = _re_ai.sub(r"(?is)<think>.*?</think>", "", reply)
        except Exception:
            # If regex fails for any reason, continue with original reply
            pass

        reply = reply.strip()
        if not reply:
            return

        # Enforce max word limit
        words = reply.split()
        if len(words) > max_words:
            reply = " ".join(words[:max_words])

        # Stage and send reply using existing send path
        try:
            if hasattr(self, "to_var"):
                self.to_var.set(src)
            if hasattr(self, "tx_var"):
                self.tx_var.set(reply)

            # Log where we're sending the auto-reply
            try:
                self.log(f"[AI] Auto-reply to {src}")
            except Exception:
                pass

            # Call canonical send method
            if hasattr(self, "send_message"):
                self.send_message()
            elif hasattr(self, "_send_message"):
                self._send_message()
        except Exception as e:
            self.log(f"[AI] Failed to send AI reply: {e}")



    def _ai_process_incoming_async(self, src: str, dst: str, body_text: str):
        """Fire-and-forget AI handler so LM Studio latency never blocks RX/UI."""
        if not getattr(self, "ai_autoreply_enabled", False):
            return

        def _worker():
            try:
                self._ai_process_incoming(src, dst, body_text)
            except Exception as e:
                try:
                    self.log(f"[AI] Handler error: {e}")
                except Exception:
                    pass

        try:
            t = threading.Thread(target=_worker, daemon=True)
            t.start()
        except Exception as e:
            try:
                self.log(f"[AI] Failed to start AI thread: {e}")
            except Exception:
                pass

    
    # === END A.I. AUTO-REPLY SYSTEM (LOCKED) ======================
    def _ai_flag_active(self) -> bool:
        """Return True if A.I auto-reply is active."""
        return bool(getattr(self, "ai_autoreply_enabled", False))

    def _tag_ai_flag_in_line(self, widget, line_start_index: str, line: str):
        """Apply lime-green color to [A.I] flags within a given inserted line."""
        try:
            flag = "[A.I]"
            start = 0
            while True:
                idx = line.find(flag, start)
                if idx == -1:
                    break
                tag_start = f"{line_start_index}+{idx}c"
                tag_end = f"{line_start_index}+{idx + len(flag)}c"
                widget.tag_add("ai_flag", tag_start, tag_end)
                start = idx + len(flag)
        except Exception:
            pass


    
    def _update_ai_tab_label(self):
        """Update the [A.I] top toolbar tab label colour based on AI mode."""
        try:
            btn = getattr(self, "btn_tab_misc", None)
            if not btn:
                return
            active = bool(getattr(self, "ai_autoreply_enabled", False))
            btn.configure(
                text="[A.I]",
                fg="#00ff00" if active else "#ff0000",
                activeforeground="#00ff00" if active else "#ff0000",
            )
        except Exception as e:
            if hasattr(self, "log"):
                self.log(f"[AI] Tab label update error: {e}")
# ----- Misc UI -----

    def on_attach_file(self):
        messagebox.showinfo(
            "File transfer",
            "File transfer not implemented yet in this build.",
        )

    def _clip_hover(self, hover: bool):
        self.clip_label.configure(bg="#12212c" if hover else "#0b141a")

    def _lock_hover(self, hover: bool):
        self.lock_label.configure(bg="#12212c" if hover else "#0b141a")

    def on_padlock_click(self):
        messagebox.showinfo(
            "Encryption",
            "Encryption not implemented yet in this build.",
        )

    # ----- UI queue -----

    def _enqueue_ui(self, fn):
        try:
            self.ui_queue.put_nowait(fn)
        except Exception:
            pass

    def _process_ui_queue(self):
        while True:
            try:
                fn = self.ui_queue.get_nowait()
            except Exception:
                break
            try:
                fn()
            except Exception as e:
                logmsg(f"UI callback error: {e}")
        self.master.after(50, self._process_ui_queue)

    # ----- Persistence: messages & beacons -----

    def _load_messages(self):
        """
        Load message history from messages_v1.json.

        Supports two layouts:
        1) New (current) format:
           {
             "conversations": {
               "All": [...],
               "CALL1": [...],
               ...
             }
           }

        2) Legacy format (no wrapper):
           {
             "All": [...],
             "CALL1": [...],
             ...
           }

        In both cases we normalise into self.conversations.
        """
        try:
            if not os.path.exists(self.messages_file):
                return

            with open(self.messages_file, "r", encoding="utf-8", errors="replace") as f:
                data = json.load(f)

            conv = None

            # Preferred: wrapped format
            if isinstance(data, dict) and "conversations" in data:
                maybe = data.get("conversations")
                if isinstance(maybe, dict):
                    conv = maybe

            # Fallback: legacy direct mapping
            if conv is None and isinstance(data, dict):
                # Heuristic: if all values are lists/dicts, treat as conversations map
                if all(isinstance(v, (list, dict)) for v in data.values()):
                    conv = data

            if isinstance(conv, dict):
                # Merge into existing structure
                for key, msgs in conv.items():
                    if not isinstance(msgs, list):
                        continue
                    self.conversations.setdefault(key, [])
                    # Shallow copy each message dict to be safe
                    for m in msgs:
                        if isinstance(m, dict):
                            self.conversations[key].append(dict(m))

        except Exception as e:
            logmsg(f"Failed to load messages_v1.json (ignored): {e}")

    def _save_messages(self):
        try:
            with open(self.messages_file, "w", encoding="utf-8", errors="replace") as f:
                json.dump(
                    {"conversations": self.conversations},
                    f,
                    ensure_ascii=False,
                    indent=2,
                )
        except Exception as e:
            logmsg(f"Failed to save messages_v1.json: {e}")

    def _load_link_graph(self, prune_only: bool = False):
        try:
            if os.path.exists(self.link_graph_file):
                with open(self.link_graph_file, "r", encoding="utf-8", errors="replace") as f:
                    data = json.load(f)
                beacons = data.get("beacons", {})
                if isinstance(beacons, dict):
                    self.beacons = beacons
        except Exception as e:
            logmsg(f"Failed to load link_graph.json (ignored): {e}")
        self._prune_beacons(save=not prune_only)

    def _save_link_graph(self):
        try:
            with open(self.link_graph_file, "w", encoding="utf-8", errors="replace") as f:
                json.dump(
                    {"beacons": self.beacons},
                    f,
                    ensure_ascii=False,
                    indent=2,
                )
        except Exception as e:
            logmsg(f"Failed to save link_graph.json: {e}")

    # ----- Clear -----

    def clear_messages(self):
        if not messagebox.askyesno(
            "Clear messages",
            "Delete all stored messages/beacons/positions (keep settings)?",
        ):
            return
        self.conversations = {"All": [], "Settings": []}
        self.active_chat = "All"
        self.beacons = {}
        self.links = {}
        self.positions = {}
        for p in (
            self.messages_file,
            self.link_graph_file,
            self.positions_file,
        ):
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception as e:
                logmsg(f"Failed to remove {p}: {e}")
        self._save_messages()
        self._save_link_graph()
        self._save_positions()
        self._refresh_chat_listbox()
        self._refresh_beacon_listbox()
        self._render_active_chat()
        self._draw_locator_compass()

    # ----- Link dot helper -----

    def _link_dot_for_call(self, call: str) -> str:
        ts = self.links.get(call)
        if not ts:
            return ""
        age = time.time() - ts
        if age < 300:
            return "🟢"
        elif age < 600:
            return "🟠"
        elif age < 900:
            return "🔴"
        else:
            self.links.pop(call, None)
            return ""

    # ----- Sidebar refresh -----



    def _refresh_chat_listbox(self):
        # Treeview with text labels including [Country]
        if not hasattr(self, "chat_tree"):
            return
        self.chat_tree.delete(*self.chat_tree.get_children())

        keys = ["All", "Settings"] + sorted(
            k for k in self.conversations.keys()
            if k not in ("All", "Settings")
        )

        active = self.active_chat
        if active not in keys:
            active = "All"
            self.active_chat = "All"

        selected_iid = None
        for name in keys:
            if name in ("All", "Settings"):
                label = name
            else:
                country = self._lookup_country_for_call(name)
                label = f"{name} [{country}]" if country else name
            iid = self.chat_tree.insert("", "end", text=label)
            if name == active:
                selected_iid = iid

        if selected_iid:
            self.chat_tree.selection_set(selected_iid)
            self.chat_tree.see(selected_iid)


    

    def _refresh_beacon_listbox(self):
        if not hasattr(self, "beacon_tree"):
            return
        self.beacon_tree.delete(*self.beacon_tree.get_children())
        # Lime-green style for AI-capable stations in Beacon Heard
        try:
            self.beacon_tree.tag_configure("ai_flag", foreground="#00ff00")
        except Exception:
            pass
        self._prune_beacons(save=True)

        my = (self.call_var.get() or "").strip().upper()

        # Collect parents with their latest-heard timestamp
        parents = []
        for parent, pdata in self.beacons.items():
            if parent == my:
                continue
            if isinstance(pdata, dict):
                last_ts = pdata.get("last", 0) or 0
            else:
                last_ts = pdata or 0
            parents.append((last_ts, parent))

        # Newest-first: sort by last_ts descending
        for _, parent in sorted(parents, key=lambda x: x[0], reverse=True):
            pdata = self.beacons.get(parent, {}) or {}
            pcountry = self._lookup_country_for_call(parent)

            # Check if this parent has a stored position
            pos = self.positions.get(parent) or {}
            has_pos = isinstance(pos, dict) and "lat" in pos and "lon" in pos

            # Build label: CALL 📍 [Country]
            if has_pos:
                base_label = f"{parent} 📍"
            else:
                base_label = parent

            if pcountry:
                plabel = f"{base_label} [{pcountry}]"
            else:
                plabel = base_label

            # Append [A.I] when this parent has ai flag from its beacons
            ai_flag = isinstance(pdata, dict) and pdata.get("ai")
            if ai_flag:
                plabel = f"{plabel} [A.I]"
                p_iid = self.beacon_tree.insert("", "end", text=plabel, tags=("ai_flag",))
            else:
                p_iid = self.beacon_tree.insert("", "end", text=plabel)

            # Within each parent, sort children newest-first
            children = {}
            if isinstance(pdata, dict):
                children = pdata.get("children", {}) or {}

            child_rows = []
            for child, cdata in children.items():
                if child == my:
                    continue
                if isinstance(cdata, dict):
                    last_c = cdata.get("last", 0) or 0
                else:
                    last_c = cdata or 0
                child_rows.append((last_c, child))

            for _, child in sorted(child_rows, key=lambda x: x[0], reverse=True):
                ccountry = self._lookup_country_for_call(child)
                clabel = f"{child} [{ccountry}]" if ccountry else child
                # Children: no 📍; pin reserved for parent that carried Lat/Lon
                self.beacon_tree.insert(p_iid, "end", text=clabel)


    def on_chat_select(self, event=None):
        if not hasattr(self, "chat_tree"):
            return
        sel = self.chat_tree.selection()
        if not sel:
            return
        iid = sel[0]
        label = (self.chat_tree.item(iid, "text") or "").strip()
        if not label:
            return

        # Strip map pin and any country/extra tags for key resolution
        label = label.replace("📍", "").strip()
        if "[" in label:
            label = label.split("[", 1)[0].strip()
        if " [" in label:
            label = label.split(" [", 1)[0].strip()

        base = label

        if base not in self.conversations:
            self.conversations[base] = []
        self.active_chat = base
        if base not in ("All", "Settings"):
            self.to_var.set(base)
        self._render_active_chat()

    # ----- Logging into Settings -----

    def log(self, msg: str):
        now = time.time()
        ts = time.strftime("%H:%M:%S", time.localtime(now))

        def do():
            m = {
                "ts": ts,
                "epoch": now,
                "direction": "sys",
                "text": msg,
                "src": "",
                "dst": "",
            }
            self._append_message("Settings", m, save=False)
            self._save_messages()
            if self.active_chat == "Settings":
                self._render_active_chat()

        if threading.current_thread() is threading.main_thread():
            do()
        else:
            self._enqueue_ui(do)

    # ----- Render messages -----

    def _append_message(self, chat_key: str, msg: dict, save: bool = True):
        self.conversations.setdefault(chat_key, []).append(dict(msg))
        if save:
            self._save_messages()
        self._refresh_chat_listbox()

    def _callsign_base(self, call: str) -> str:
        call = (call or "").strip().upper()
        return call.split("-", 1)[0] if "-" in call else call

    def _lookup_flag_for_call(self, call: str) -> str:
        """Return a Unicode flag based on the callsign prefix (longest match)."""
        if not call:
            return ""
        base = self._callsign_base(call).upper()
        # strip portable etc like M0OLI/P
        if "/" in base:
            base = base.split("/", 1)[0]
        best_flag = ""
        best_len = 0
        for prefix, (_country, flag) in PREFIX_COUNTRY_FLAG.items():
            if base.startswith(prefix) and len(prefix) > best_len:
                best_len = len(prefix)
                best_flag = flag
        return best_flag

    def _lookup_country_for_call(self, call: str) -> str:
        """
        Return the country name for the callsign based on PREFIX_COUNTRY_FLAG.
        Uses longest-prefix match, same as flag lookup.
        """
        if not call:
            return ""
        base = self._callsign_base(call).upper()
        base = base.split("/", 1)[0]
        best_name = ""
        best_len = 0
        for prefix, (country, _flag) in PREFIX_COUNTRY_FLAG.items():
            if base.startswith(prefix) and len(prefix) > best_len:
                best_len = len(prefix)
                best_name = country
        return best_name

    
    
    def _render_active_chat(self):
        self.chat_text.configure(state="normal")
        self.chat_text.delete("1.0", tk.END)

        msgs = self.conversations.get(self.active_chat, [])
        my = (self.call_var.get() or "").strip().upper()
        my_base = self._callsign_base(my) or "ME"

        segments = []
        last_date = None

        # Walk from newest to oldest so newest day + newest messages are at the top
        for m in reversed(msgs):
            epoch = m.get("epoch", time.time())
            try:
                dt = datetime.datetime.fromtimestamp(epoch)
            except Exception:
                dt = datetime.datetime.now()
            date_str = dt.strftime("%a %d %b %Y")

            # New date header when date changes
            if date_str != last_date:
                if last_date is not None:
                    segments.append(("\n", ()))
                segments.append((f"── {date_str} ──\n", ("day_header",)))
                last_date = date_str

            direction = m.get("direction", "in")
            text = m.get("text", "")
            src = m.get("src", "")
            dst = m.get("dst", "")
            ts = m.get("ts", dt.strftime("%H:%M:%S"))

            if direction == "sys":
                segments.append((f"{ts}  {text}\n", ("system",)))
            elif direction == "out":
                # Apply ACK tick system for outgoing messages
                ack_status = m.get("ack_status")
                if ack_status == "pending":
                    tick = " ✓"
                elif ack_status == "ok":
                    tick = " ✓✓"
                elif ack_status == "failed":
                    tick = " !"
                else:
                    tick = ""
                meta = f"{ts}  {my_base} → {dst or 'CQ'}{tick}"
                segments.append((text + "\n", ("out_msg",)))
                segments.append((meta + "\n", ("meta", "out_msg")))
            else:
                # Incoming
                src_base = self._callsign_base(src)
                dst_base = self._callsign_base(dst)
                is_to_me = bool(my_base and dst_base == my_base)
                if is_to_me:
                    ttag = "in_to_me"
                    mtag = ("meta", "in_to_me")
                else:
                    ttag = "in_msg"
                    mtag = ("meta", "in_msg")
                meta = f"{ts}  {src or '??'} → {dst or ''}"
                segments.append((text + "\n", (ttag,)))
                segments.append((meta + "\n", mtag))

            segments.append(("\n", ()))

        # Paint in order so visual matches: newest day + newest messages at top
        for text, tags in segments:
            if tags:
                self.chat_text.insert(tk.END, text, tags)
            else:
                self.chat_text.insert(tk.END, text)

        self.chat_text.configure(state="disabled")
        # Apply [A.I] highlight for any occurrences in rendered text
        try:
            text = self.chat_text.get("1.0", "end-1c")
            idx = "1.0"
            flag = "[A.I]"
            while True:
                idx = self.chat_text.search(flag, idx, tk.END)
                if not idx:
                    break
                end = f"{idx}+{len(flag)}c"
                self.chat_text.tag_add("ai_flag", idx, end)
                idx = end
        except Exception:
            pass


    # ----- Beacons & links -----

    def _prune_beacons(self, save: bool = False):
        now = time.time()
        cutoff = now - 900  # 15 min
        my = (self.call_var.get() or "").strip().upper()
        for parent in list(self.beacons.keys()):
            pdata = self.beacons[parent]
            children = pdata.get("children", {})
            for c in list(children.keys()):
                if c == my or children[c] < cutoff:
                    children.pop(c, None)
            if parent == my or (pdata.get("last", 0) < cutoff and not children):
                self.beacons.pop(parent, None)
        for call in list(self.links.keys()):
            if self.links[call] < cutoff or call not in self.beacons:
                self.links.pop(call, None)
        if save:
            self._save_link_graph()

    def _record_beacon_with_position(self, parent, child_calls, lat, lon):
        now = time.time()
        parent = self._callsign_base(parent)
        child_calls = [self._callsign_base(c) for c in child_calls if c]

        be = self.beacons.setdefault(parent, {"last": now, "children": {}})
        be["last"] = now
        for c in child_calls:
            be["children"][c] = now

        my = self._callsign_base(self.call_var.get() or "")
        if my and my in child_calls:
            self.links[parent] = now

        self._save_link_graph()
        self._refresh_beacon_listbox()

        self.positions[parent] = {
            "lat": float(lat),
            "lon": float(lon),
            "epoch": now,
        }
        self._save_positions()
        self._enqueue_ui(self._draw_locator_compass)

        self.log(f"[BEACON] {parent} children={child_calls} Lat {lat:.5f} Lon {lon:.5f}")

    def _parse_beacon_line(self, line: str):
        """
        Backwards-compatible ASCII beacon parser.
        Delegates into _update_beacons_from_text so:
          - parent/children always recorded
          - Lat/Lon optional
        """
        txt = (line or "").strip()
        if not txt.startswith("**"):
            return
        try:
            self._update_beacons_from_text(txt)
        except Exception as e:
            self.log(f"[BEACON] parse error: {e}")

    
    def _update_beacons_from_text(self, txt: str, now: float = None):
        """
        Unified beacon parser for both ASCII and KISS sources.

        Accepts:
          **PARENT /CHILD1 /CHILD2 ... [Lat .. Lon ..]

        Behaviour:
          - Always records parent + children in self.beacons
          - Always writes link_graph.json via _save_link_graph()
          - Marks self.links[parent] if MYCALL is one of the children
          - If Lat/Lon present, also updates positions.json + locator
          - Works even if no Lat/Lon is present (graph still updated)
        """
        if not txt:
            return
        txt = txt.strip()
        if not txt.startswith("**"):
            return

        if now is None:
            now = time.time()

        s = txt

        # Optional Lat/Lon block
        lat = lon = None
        mpos = re.search(
            r"Lat\s+([-+]?\d+\.\d+)\s+Lon\s+([-+]?\d+\.\d+)",
            s,
            flags=re.IGNORECASE,
        )
        if mpos:
            try:
                lat = float(mpos.group(1))
                lon = float(mpos.group(2))
            except Exception:
                lat = lon = None
            s_nopos = s[: mpos.start()].strip()
        else:
            s_nopos = s

        tokens = s_nopos.split()
        if not tokens:
            return
        if not tokens[0].startswith("**"):
            return

        parent_raw = tokens[0].lstrip("*").strip()
        if not parent_raw:
            return

        parent = self._callsign_base(parent_raw)
        if not parent:
            return

        # Collect children (may be empty; still track parent)
        child_bases = []
        for tok in tokens[1:]:
            tok = tok.strip()
            if tok.startswith("/") and len(tok) > 1:
                c = self._callsign_base(tok[1:])
                if c:
                    child_bases.append(c)

        be = self.beacons.setdefault(parent, {"last": now, "children": {}})
        be["last"] = now
        for c in child_bases:
            be["children"][c] = now

        # Link if MYCALL appears in children
        my = self._callsign_base(self.call_var.get() or "")
        if my and my in child_bases:
            self.links[parent] = now

                # Track remote A.I usage flag from beacon text.
        # If a station includes the explicit [A.I] marker in its beacon,
        # mark it in our beacons dict so link_graph.json and UI can show it.
        ai_active = "[A.I]" in (txt or "")
        be = self.beacons.get(parent)
        if isinstance(be, dict):
            if ai_active:
                be["ai"] = True
            else:
                be.pop("ai", None)

# Persist link graph regardless of position
        try:
            self._save_link_graph()
        except Exception:
            pass

        # If position present, update positions + locator
        if lat is not None and lon is not None:
            try:
                self.positions[parent] = {
                    "lat": float(lat),
                    "lon": float(lon),
                    "epoch": float(now),
                }
                self._save_positions()
                self._enqueue_ui(self._draw_locator_compass)
            except Exception:
                pass

        # Refresh Beacon Heard UI
        try:
            self._refresh_beacon_listbox()
        except Exception:
            pass

# ----- Serial / connect -----


    def _populate_ports(self):
        ports = []
        if serial is not None:
            try:
                ports = [p.device for p in serial.tools.list_ports.comports()]
            except Exception as e:
                logmsg(f"Port enumeration failed: {e}")
        else:
            logmsg("PySerial not available: no COM ports enumerated.")
        self.port_combo["values"] = ports
        if ports and not self.port_var.get():
            self.port_combo.current(0)

    def _populate_gps_ports(self):
        try:
            ports = [p.device for p in serial.tools.list_ports.comports()]
        except Exception:
            ports = []
        # Only update combos that already exist to avoid init races
        if hasattr(self, "gps_port_combo"):
            self.gps_port_combo["values"] = ports
        if hasattr(self, "link500_port_combo"):
            self.link500_port_combo["values"] = ports

        # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — CORE CONNECT + PREFLIGHT WIRING
    # ---------------------------------------------------------------
    # CONNECT:
    #   - Opens serial port to TNC at 38400 baud.
    #   - Requires MyCall to be set.
    #   - Starts reader thread.
    #   - Schedules preflight 1 second after successful connect.
    # Any changes here risk breaking KISS init and PTT behaviour.
    # ================================================================
    def connect_port(self):
        if self.ser:
            return

        port = (self.port_var.get() or "").strip()
        if not port:
            messagebox.showerror("Error", "Select a COM port first.")
            return

        callsign = (self.call_var.get() or "").strip().upper()
        if not callsign:
            self.log("[WARN] Set MyCall before connecting TNC.")
            messagebox.showwarning(
                "Set MyCall",
                "Please enter your callsign in the MyCall box before connecting the TNC.",
            )
            return

        if not self._has_any_position_source():
            messagebox.showwarning(
                "Missing Position",
                "Please set your Grid Square or GPS / LiNK500 / Fixed position before connecting.\n"
                "This ensures the Locator and beacons have a valid reference.",
            )
            return

        try:
            if serial is None:
                raise RuntimeError("pyserial not available")
            self.ser = serial.Serial(port, baudrate=38400, timeout=0.2)
        except Exception as e:
            self.log(f"[ERR] Could not open {port}: {e}")
            self.ser = None
            return

        self.log(f"[INFO] Connected to {port}")
        self.connect_btn.config(state="disabled")
        self.disconnect_btn.config(state="normal")

        # Not yet in KISS until preflight completes
        self.kiss_mode = False
        self.send_btn.config(state="disabled")

        self._save_settings()

        # Start reader loop
        self.read_running = True
        self.read_thread = threading.Thread(
            target=self.reader_loop,
            daemon=True,
        )
        self.read_thread.start()

        # Auto-run preflight 1 second after connect
        self.master.after(1000, self.start_preflight)

        # Visual state: indicate connected
        if hasattr(self, "connect_btn"):
            self.connect_btn.configure(style="ConnectOn.TButton")
    def disconnect_port(self):
        self.read_running = False
        if self.read_thread:
            try:
                self.read_thread.join(timeout=0.5)
            except Exception:
                pass
            self.read_thread = None
        if self.ser:
            try:
                self.ser.close()
            except Exception:
                pass
            self.ser = None
        self.log("[INFO] Disconnected.")
        self.kiss_mode = False
        self.connect_btn.config(state="normal")
        self.disconnect_btn.config(state="disabled")
        self.send_btn.config(state="disabled")
        # Visual state: indicate disconnected
        if hasattr(self, "connect_btn"):
            self.connect_btn.configure(style="ConnectOff.TButton")
        # Stop any pending automatic beacons when disconnected
        try:
            self._cancel_beacon_timer()
        except Exception:
            pass
        self._save_settings()


    # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — CORE TNC PREFLIGHT SEQUENCE
    # ---------------------------------------------------------------
    # Runs automatically 1s after CONNECT (see connect_port) and may
    # also be invoked manually via start_preflight().
    #
    # Sequence (per Teensy-RPR-TNC manual):
    #   1) KISS OFF reset  : FEND 0xFF FEND 0x0D
    #   2) ESC %ZK         : reset / defaults
    #   3) ESC X 1         : host mode on
    #   4) ESC I <MYCALL>  : set callsign
    #   5) ESC %B R300     : set robust 300 speed
    #   6) ESC %ZS         : store settings
    #   7) ESC @K          : enter KISS mode
    #
    # On success:
    #   - self.kiss_mode = True
    #   - Speed selector forced to R300
    #   - Send button enabled
    #   - Log: "[PRE] Done. Now in KISS mode (R300). Ready to chat."
    #
    # If this sequence is altered or removed, manual TX/PTT WILL BREAK.
    # ================================================================
    def start_preflight(self):
        if not self.ser:
            self.log("[ERR] Not connected.")
            return

        callsign = (self.call_var.get() or "").strip().upper()
        if not callsign:
            self.log("[ERR] Enter your callsign before PRE-FLIGHT.")
            return

        t = threading.Thread(target=self._preflight_worker, args=(callsign,), daemon=True)
        t.start()

    def _preflight_worker(self, callsign: str):
        try:
            self.log("[PRE] Running preflight + KISS...")

            # 1) KISS OFF reset sequence
            self._write_bytes(bytes([FEND, 0xFF, FEND, 0x0D]))
            time.sleep(0.2)

            # 2) Reset / clean
            self._send_esc_command("%ZK")
            time.sleep(0.2)

            # 3) Host mode on
            self._send_esc_command("X 1")
            time.sleep(0.2)

            # 4) Set callsign
            self._send_esc_command(f"I {callsign}")
            time.sleep(0.2)

            # 5) Set R300
            self._send_esc_command("%B R300")
            time.sleep(0.2)

            # 6) Store settings
            self._send_esc_command("%ZS")
            time.sleep(0.2)

            # 7) Enter KISS
            self._send_esc_command("@K")
            time.sleep(0.3)

            def done():
                self.kiss_mode = True
                try:
                    self.speed_var.set("R300")
                except Exception:
                    pass
                self.send_btn.config(state="normal")
                self.log("[PRE] Done. Now in KISS mode (R300). Ready to chat.")
                # Apply stored beacon interval preference now that KISS is ready
                self._apply_beacon_interval_on_connect()

            self._enqueue_ui(done)
        except Exception as e:
            self.log(f"[ERR] Preflight failed: {e}")

    # Low-level helpers used by preflight + KISS TX
    def _write_bytes(self, data: bytes):
        if not self.ser:
            return
        try:
            self.ser.write(data)
            self.ser.flush()
        except Exception as e:
            self.log(f"[ERR] Serial write failed: {e}")

    def _send_esc_command(self, body: str):
        if not self.ser:
            return
        try:
            cmd = b"\x1b" + body.encode("ascii", "ignore") + b"\r"
            self._write_bytes(cmd)
            self.log(f"[TX-CMD] ESC {body}")
        except Exception as e:
            self.log(f"[ERR] ESC command failed ({body}): {e}")

    def _tnc_set_speed(self, mode: str):
        """
        Switch Teensy RPR TNC between R300 and R600.

        Sequence:
          - KISS OFF (FEND, 0xFF, FEND, 0x0D)
          - ESC %B <mode>
          - ESC %ZS
          - ESC @K   (back to KISS mode)
        """
        mode = (mode or "R300").strip().upper()
        if mode not in ("R300", "R600"):
            mode = "R300"

        # Update UI selection early so it always reflects requested state
        if hasattr(self, "speed_var"):
            self.speed_var.set(mode)

        if not getattr(self, "ser", None):
            self.log(f"[SPEED] No serial port open; UI set to {mode} only (no TNC command).")
            return

        try:
            self.log(f"[SPEED] Switching TNC to {mode}...")

            # 1) KISS OFF (leave KISS back to command/host mode)
            # Use explicit KISS OFF sequence per Teensy-RPR-TNC manual
            self._write_bytes(b"\xC0\xFF\xC0\x0D")
            time.sleep(0.2)

            # 2) Ensure host/command mode alive
            self._send_esc_command("X 1")
            time.sleep(0.2)

            # 3) Set RPR mode via %B (R300 / R600 per manual)
            self._send_esc_command(f"%B {mode}")
            time.sleep(0.2)

            # 4) Store settings
            self._send_esc_command("%ZS")
            time.sleep(0.2)

            # 5) Back into KISS
            self._send_esc_command("@K")
            time.sleep(0.3)

            self.kiss_mode = True
            self.log(f"[SPEED] TNC now set to {mode} and back in KISS mode.")
        except Exception as e:
            self.log(f"[SPEED] Failed to switch to {mode}: {e}")


    def _kiss_escape(self, data: bytes) -> bytes:
        out = bytearray()
        for b in data:
            if b == FEND:
                out.extend((FESC, TFEND))
            elif b == FESC:
                out.extend((FESC, TFESC))
            else:
                out.append(b)
        return bytes(out)


    def _kiss_unescape(self, data: bytes) -> bytes:
        """Reverse KISS escaping for a single frame payload (without FEND)."""
        out = bytearray()
        i = 0
        while i < len(data):
            b = data[i]
            if b == FESC and i + 1 < len(data):
                nb = data[i + 1]
                if nb == TFEND:
                    out.append(FEND)
                elif nb == TFESC:
                    out.append(FESC)
                else:
                    out.append(nb)
                i += 2
            else:
                out.append(b)
                i += 1
        return bytes(out)

    def _parse_ax25(self, ax: bytes):
        """Parse AX.25 UI frame, return (dst, src, info)."""
        idx = 0
        addrs = []
        while True:
            if idx + 7 > len(ax):
                raise ValueError("AX.25 addr truncated")
            block = ax[idx: idx + 7]
            idx += 7
            call = "".join(chr(b >> 1) for b in block[:6]).strip()
            ssid = (block[6] >> 1) & 0x0F
            last = block[6] & 0x01
            if ssid:
                call = f"{call}-{ssid}"
            addrs.append(call)
            if last:
                break
            if len(addrs) > 10:
                raise ValueError("Too many addr fields")

        if len(ax) < idx + 2:
            raise ValueError("No ctrl/PID")
        control = ax[idx]
        pid = ax[idx + 1]
        info = ax[idx + 2:]
        if control != 0x03 or pid != 0xF0:
            raise ValueError("Unsupported ctrl/pid")

        dst = addrs[0]
        src = addrs[1] if len(addrs) > 1 else "?"
        return dst, src, info

    # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — CORE KISS RX FRAME HANDLER
    # ---------------------------------------------------------------
    # This method is called by reader_loop() for each complete KISS
    # frame (port 0) after preflight has put the TNC into KISS mode.
    # It is responsible for:
    #   - Unescaping the KISS payload
    #   - Parsing AX.25 UI frames
    #   - Routing beacons into the beacon/link logic
    #   - Routing chat frames into All + per-station chats
    # If this logic is changed, RX of chat/beacon frames WILL BREAK.
    # ================================================================
    
    def _handle_kiss_frame(self, raw: bytes):
        if not raw:
            return

        data = self._kiss_unescape(raw)
        if not data:
            return

        # Only handle port 0 data frames
        if (data[0] & 0x0F) != 0x00:
            return

        ax = data[1:]
        if len(ax) < 16:
            return

        # Decode AX.25 address field (dest + src + digis)
        try:
            idx = 0
            addr_blocks = []
            while True:
                if idx + 7 > len(ax):
                    return
                block = ax[idx:idx + 7]
                addr_blocks.append(block)
                idx += 7
                # LSB=1 in last addr byte marks end of address field
                if block[6] & 0x01:
                    break

            if len(addr_blocks) < 2:
                return

            ctrl = ax[idx] if idx < len(ax) else None
            pid = ax[idx + 1] if idx + 1 < len(ax) else None
            info = ax[idx + 2:] if idx + 2 <= len(ax) else b""
        except Exception:
            return

        if not info:
            return

        dst = self._decode_ax25_addr(addr_blocks[0])
        src = self._decode_ax25_addr(addr_blocks[1])

        try:
            txt = info.decode("ascii", errors="ignore")
        except Exception:
            return
        txt = txt.replace("\r", "").strip()
        if not txt:
            return

        now = time.time()
        stripped = txt.strip()

        # Pure ACK frame: [ACK:ID]
        m_ack_only = re.fullmatch(r"\[ACK:([A-Za-z0-9]{2,12})\]", stripped)
        if m_ack_only:
            ack_id = m_ack_only.group(1)
            self._handle_incoming_ack(src, ack_id)
            return

        # Check for ACK tag at end of message
        m_ack_tag = re.search(r"\[ACK:([A-Za-z0-9]{2,12})\]\s*$", txt)
        ack_id = m_ack_tag.group(1) if m_ack_tag else None
        body_text = txt[:m_ack_tag.start()].rstrip() if m_ack_tag else txt

        # If this is an ACKable message to us, handle duplicate suppression + ACK
        if ack_id and self._is_to_me(dst):
            my = self._callsign_base(self.call_var.get() or "")
            fromb = self._callsign_base(src)
            if fromb == my:
                # Self-echo; ignore ACK semantics
                ack_id = None
            else:
                key = (fromb, ack_id)
                seen = self.seen_ack_ids.get(key)
                if seen:
                    # Duplicate: optionally resend ACK once, do not display again
                    if not seen.get("ack_sent"):
                        self._send_ack_response(fromb, ack_id)
                        seen["ack_sent"] = True
                    return
                # First time seeing this ACKable message
                self._record_seen_ack_id(fromb, ack_id, ack_sent=False)
                # Send ACK
                self._send_ack_response(fromb, ack_id)
                self.seen_ack_ids[(fromb, ack_id)]["ack_sent"] = True

        # Prepare message object
        ts = time.strftime("%H:%M:%S", time.localtime(now))
        msg = {
            "ts": ts,
            "epoch": now,
            "direction": "in",
            "text": body_text,
            "src": src,
            "dst": dst,
        }
        if ack_id and self._is_to_me(dst):
            msg["ack_id"] = ack_id
            msg["ack_is_request"] = False

        def do_msg():
            try:
                my = (self.call_var.get() or "").strip().upper()
            except Exception:
                my = ""
            my_base = self._callsign_base(my)
            src_base = self._callsign_base(src)
            dst_base = self._callsign_base(dst)

            # Pick thread key: conversation with "other" side
            if my_base and src_base == my_base:
                other = dst
            else:
                other = src

            is_beacon = body_text.startswith("**")
            # Append to All + per-station convo (skip for beacons)
            if not is_beacon and hasattr(self, "_append_message"):
                self._append_message("All", msg)
                if other:
                    self._append_message(other, msg)

            # Feed text into beacon/link parser if available
            try:
                if hasattr(self, "_update_beacons_from_text"):
                    self._update_beacons_from_text(body_text, now)
            except Exception as e:
                self.log(f"[KISS] Beacon-from-chat update error: {e}")

            # Refresh visible chat if relevant
            try:
                if getattr(self, "active_chat", "All") in ("All", other):
                    self._render_active_chat()
            except Exception as e:
                self.log(f"[KISS] Render error: {e}")


        self._enqueue_ui(do_msg)

        # Kick off AI auto-reply in background so RX/UI are never blocked
        try:
            self._ai_process_incoming_async(src, dst, body_text)
        except Exception as e:
            self.log(f"[AI] Handler error: {e}")



    def _decode_ax25_addr(self, block: bytes) -> str:
        if not block or len(block) != 7:
            return ""
        call = "".join(
            chr((b >> 1) & 0x7F).strip()
            for b in block[:6]
        ).strip()
        ssid = (block[6] >> 1) & 0x0F
        if ssid:
            return f"{call}-{ssid}"
        return call


    def _encode_ax25_addr(self, call: str, last: bool) -> bytes:
        if not call:
            call = "NOCALL"
        if "-" in call:
            base, ssid_str = call.split("-", 1)
            try:
                ssid = int(ssid_str)
            except Exception:
                ssid = 0
        else:
            base = call
            ssid = 0
        base = base.upper().ljust(6)[:6]
        addr = bytearray((ord(c) << 1) for c in base)
        ssid_byte = 0b01100000 | ((ssid & 0x0F) << 1)
        if last:
            ssid_byte |= 0x01
        addr.append(ssid_byte)
        return bytes(addr)

    def _build_kiss_ui_frame(self, src_call: str, dst_call: str, text: str) -> bytes:
        # Build AX.25 UI frame wrapped in KISS (port 0)
        info = (text + "\r").encode("ascii", "ignore")
        addr = (
            self._encode_ax25_addr(dst_call, last=False)
            + self._encode_ax25_addr(src_call, last=True)
        )
        ctrl = bytes([0x03])  # UI frame
        pid = bytes([0xF0])   # no layer 3
        ax = addr + ctrl + pid + info
        kiss = bytes([0x00]) + ax
        esc = self._kiss_escape(kiss)
        return bytes([FEND]) + esc + bytes([FEND])


    def on_speed_change(self):
        # Called when R300/R600 radio button changes
        new_speed = (self.speed_var.get() or "R300").strip().upper()

        if new_speed == "R600":
            # Confirm with user before switching
            ok = messagebox.askyesno(
                "Switch to R600",
                "Your contact must also be using R600 to hear you.\n\nProceed?"
            )
            if not ok:
                # Revert to R300 and do nothing else
                self.speed_var.set("R300")
                return

            # Proceed with KISS OFF -> %B R600 -> %ZS -> @K
            self._tnc_set_speed("R600")
        else:
            # Any other selection falls back to R300
            self._tnc_set_speed("R300")

        self._save_settings()

    # ----- Reader loop with simple beacon-line tap -----

    
    # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — CORE KISS READER LOOP
    # ---------------------------------------------------------------
    # This loop is responsible for:
    #   - Reading bytes from the TNC.
    #   - In pre-KISS mode: showing raw/banner text and feeding beacon parser.
    #   - In KISS mode: assembling KISS frames and forwarding them to
    #     _handle_kiss_frame for AX.25/UI message decode.
    # If this logic is changed, RX of chat/beacon frames WILL BREAK.
    # ================================================================
    def reader_loop(self):
        buf = bytearray()
        while self.read_running and self.ser:
            try:
                data = self.ser.read(256)
            except Exception as e:
                self.log(f"[ERR] Read error: {e}")
                break

            if not data:
                continue

            if not self.kiss_mode:
                # Pre-KISS: treat as ASCII text, show raw, and let beacon parser see it.
                try:
                    s = data.decode("ascii", errors="ignore")
                except Exception:
                    s = ""
                s = s.replace("\r", "")
                for line in s.split("\n"):
                    line = line.strip()
                    if not line:
                        continue
                    # Existing v1.5 beacon/position parser hook
                    if hasattr(self, "_parse_beacon_line"):
                        self._parse_beacon_line(line)
                    self.log("[RAW] " + line)
                continue

            # In KISS mode: parse KISS frames byte-by-byte.
            for b in data:
                if b == FEND:
                    if buf:
                        raw = bytes(buf)
                        buf.clear()
                        self._handle_kiss_frame(raw)
                    else:
                        buf.clear()
                else:
                    buf.append(b)

        self.read_running = False

    def _gps_fixed_send(self):
        name = (self.fixed_name_var.get() or "").strip()
        lat = (self.fixed_lat_var.get() or "").strip()
        lon = (self.fixed_lon_var.get() or "").strip()
        if not (name and lat and lon):
            messagebox.showerror("Fixed Position", "Fill Name, Lat and Lon.")
            return
        msg = f"Fixed Position [{name}] Latitude [{lat}] Longitude [{lon}]"
        self.tx_var.set(msg)
        self.show_page("Main")
        self._save_settings()

    def _gps_connect_toggle(self):
        if self.gps_running:
            self._gps_stop()
        else:
            self._gps_start()

    def _gps_start(self):
        port = (self.gps_port_var.get() or "").strip()
        if not port:
            messagebox.showerror("GPS", "Select a GPS COM port.")
            return
        try:
            self.gps_ser = serial.Serial(port, baudrate=4800, timeout=1.0)
        except Exception as e:
            self.log(f"[GPS] Could not open {port}: {e}")
            self.gps_ser = None
            return
        self.gps_running = True
        self.gps_connect_btn.config(text="Stop")
        self._save_settings()
        self.gps_thread = threading.Thread(target=self._gps_read_loop, daemon=True)
        self.gps_thread.start()
        self.log(f"[GPS] Listening on {port} for NMEA (5-min position updates).")

    def _gps_stop(self):
        self.gps_running = False
        if self.gps_thread:
            try:
                self.gps_thread.join(timeout=0.5)
            except Exception:
                pass
            self.gps_thread = None
        if self.gps_ser:
            try:
                self.gps_ser.close()
            except Exception:
                pass
            self.gps_ser = None
        self.gps_connect_btn.config(text="Connect")
        self.log("[GPS] Stopped.")

    def _gps_read_loop(self):
        buf = b""
        while self.gps_running and self.gps_ser:
            try:
                chunk = self.gps_ser.read(256)
            except Exception as e:
                self.log(f"[GPS] Read error: {e}")
                break
            if not chunk:
                continue
            buf += chunk
            while b"\n" in buf:
                line, buf = buf.split(b"\n", 1)
                try:
                    s = line.decode("ascii", errors="ignore").strip()
                except Exception:
                    continue
                if not s.startswith(("$GPGGA", "$GPRMC", "$GNRMC", "$GNGGA")):
                    continue
                lat, lon = self._parse_nmea_latlon(s)
                if lat is None or lon is None:
                    continue
                now = time.time()
                if now - self.gps_last_update < 300:
                    continue
                self.gps_last_update = now
                self._enqueue_ui(
                    lambda la=lat, lo=lon: self._update_gps_position(la, lo)
                )
        self.gps_running = False
        self._enqueue_ui(lambda: self.gps_connect_btn.config(text="Connect"))

    def _parse_nmea_latlon(self, sentence: str):
        try:
            parts = sentence.split(",")
            if sentence.startswith(("$GPGGA", "$GNGGA")):
                lat_s, lat_h = parts[2], parts[3]
                lon_s, lon_h = parts[4], parts[5]
            elif sentence.startswith(("$GPRMC", "$GNRMC")):
                lat_s, lat_h = parts[3], parts[4]
                lon_s, lon_h = parts[5], parts[6]
            else:
                return None, None
            if not (lat_s and lat_h and lon_s and lon_h):
                return None, None

            def dm_to_deg(dm, hemi, is_lat):
                if is_lat:
                    if len(dm) < 4:
                        return None
                    d = float(dm[:2])
                    m = float(dm[2:])
                else:
                    if len(dm) < 5:
                        return None
                    d = float(dm[:3])
                    m = float(dm[3:])
                v = d + m / 60.0
                if hemi in ("S", "W"):
                    v = -v
                return v

            lat = dm_to_deg(lat_s, lat_h, True)
            lon = dm_to_deg(lon_s, lon_h, False)
            return lat, lon
        except Exception:
            return None, None

    def _update_gps_position(self, lat: float, lon: float):
        self.gps_lat_var.set(f"{lat:.5f}"[:10])
        self.gps_lon_var.set(f"{lon:.5f}"[:10])
        self._save_settings()
        my = self._callsign_base(self.call_var.get() or "")
        if my:
            self.positions[my] = {
                "lat": float(f"{lat:.5f}"),
                "lon": float(f"{lon:.5f}"),
                "epoch": time.time(),
            }
            self._save_positions()
            self._draw_locator_compass()

    def _gps_nmea_send(self):
        lat = (self.gps_lat_var.get() or "").strip()
        lon = (self.gps_lon_var.get() or "").strip()
        if not (lat and lon):
            messagebox.showerror("GPS", "No GPS coordinates present.")
            return
        msg = f"My GPS position is lat {lat} lon {lon}"
        self.tx_var.set(msg)
        self.show_page("Main")
        self._save_settings()

    # ----- LiNK500 GPS logic -----

    def _link500_connect_toggle(self):
        if self.link500_ser:
            self._link500_close()
        else:
            self._link500_open()

    def _link500_open(self):
        port = (self.link500_port_var.get() or "").strip()
        if not port:
            messagebox.showerror("LiNK500", "Select a LiNK500 COM port.")
            return
        try:
            self.link500_ser = serial.Serial(port, baudrate=38400, timeout=1.0)
        except Exception as e:
            self.log(f"[LiNK500] Could not open {port}: {e}")
            self.link500_ser = None
            return
        self.link500_connect_btn.config(text="Close")
        self._save_settings()
        self.log(f"[LiNK500] Connected on {port} for %AZ GPS polling.")

    def _link500_close(self):
        if self.link500_ser:
            try:
                self.link500_ser.close()
            except Exception:
                pass
            self.link500_ser = None
        self.link500_connect_btn.config(text="Connect")
        self.log("[LiNK500] Disconnected.")

    
    def _extract_latlon_from_text(self, text: str):
        """Extract latitude and longitude from NMEA or APRS %AZ text."""
        import re

        # --- Try APRS-style: '* APRS Current GPS position: 5041.53N 00117.45W *'
        m = re.search(r'(\d{4,5}\.\d{2}[NS])\s+(\d{5}\.\d{2}[EW])', text)
        if m:
            lat_raw, lon_raw = m.groups()

            def to_decimal(val):
                if val[-1] in 'NS':
                    deg = int(val[0:2])
                    mins = float(val[2:-1])
                    sign = 1 if val[-1] == 'N' else -1
                    return sign * (deg + mins / 60)
                else:
                    deg = int(val[0:3])
                    mins = float(val[3:-1])
                    sign = 1 if val[-1] == 'E' else -1
                    return sign * (deg + mins / 60)

            lat = to_decimal(lat_raw)
            lon = to_decimal(lon_raw)
            self.log(f"[Parser] Parsed APRS-style coords -> {lat:.5f}, {lon:.5f}")
            return lat, lon

        # --- Fallback: existing NMEA extraction ---
        try:
            gga = None
            for line in text.splitlines():
                if line.startswith(("$GPGGA", "$GNGGA", "$GPRMC", "$GNRMC")):
                    gga = line
                    break
            if not gga:
                return None, None

            parts = gga.split(",")
            if len(parts) < 6:
                return None, None

            lat = parts[3]
            lat_dir = parts[4]
            lon = parts[5]
            lon_dir = parts[6]

            if not lat or not lon:
                return None, None

            lat_deg = int(float(lat) / 100)
            lat_min = float(lat) - lat_deg * 100
            lon_deg = int(float(lon) / 100)
            lon_min = float(lon) - lon_deg * 100

            lat_dec = lat_deg + lat_min / 60
            lon_dec = lon_deg + lon_min / 60
            if lat_dir == "S":
                lat_dec = -lat_dec
            if lon_dir == "W":
                lon_dec = -lon_dec
            self.log(f"[Parser] Parsed NMEA coords -> {lat_dec:.5f}, {lon_dec:.5f}")
            return lat_dec, lon_dec
        except Exception as e:
            self.log(f"[Parser] Exception in _extract_latlon_from_text: {e}")
            return None, None

    def _link500_get_position(self):
        """Use the already-open LiNK500/TEENSY TNC port to fetch GPS position.
        Sequence: KISS OFF -> ESC %AZ -> read -> KISS ON.
        Does not open/close the port.
        """
        ser = getattr(self, "link500_ser", None)
        if not ser or not ser.is_open:
            messagebox.showerror("LiNK500/TEENSY TNC", "Port not connected. Use Connect first.")
            return

        self.log("[LiNK500] GET POSITION: using open port, KISS OFF -> ESC %AZ -> read -> KISS ON.")
        resp = ""
        try:
            # KISS OFF: FEND 0xFF FEND CR
            ser.write(b'\xC0\xFF\xC0\x0D')
            ser.flush()
            time.sleep(0.15)

            # ESC %AZ + CR (new GPS command)
            ser.write(b'\x1b%AZ\r')
            ser.flush()
            time.sleep(0.4)
            buf = ser.read(512)
            try:
                resp = buf.decode("utf-8", errors="ignore")
            except Exception:
                resp = ""

            # KISS ON: ESC @K + CR
            ser.write(b'\x1b@K\r')
            ser.flush()
            time.sleep(0.1)
        except Exception as e:
            self.log(f"[LiNK500] %AZ error: {e}")

        if not resp:
            self.log("[LiNK500] No response to %AZ.")
            messagebox.showerror("LiNK500/TEENSY TNC", "No response from TNC for %AZ request.")
            return

        lat, lon = self._extract_latlon_from_text(resp)
        if lat is None or lon is None:
            self.log(f"[LiNK500] Could not parse %AZ response: {resp!r}")
            messagebox.showerror("LiNK500/TEENSY TNC", "Could not parse GPS position from %AZ response.")
            return

        self.link500_lat_var.set(f"{lat:.5f}"[:10])
        self.link500_lon_var.set(f"{lon:.5f}"[:10])
        self._save_settings()

        my = self._callsign_base(self.call_var.get() or "")
        if my:
            self.positions[my] = {
                "lat": float(f"{lat:.5f}"),
                "lon": float(f"{lon:.5f}"),
                "epoch": time.time(),
            }
            self._save_positions()
            self._draw_locator_compass()

        self.log(f"[LiNK500] %AZ OK -> lat={lat:.5f}, lon={lon:.5f} (fields updated).")

    def _link500_gps_send(self):
        """Stage a message using the LiNK500/TEENSY Lat/Lon fields.
        Does not talk to the TNC; assumes GET POSITION already populated the fields.
        """
        lat = (self.link500_lat_var.get() or '').strip()
        lon = (self.link500_lon_var.get() or '').strip()
        if not (lat and lon):
            messagebox.showerror('LiNK500/TEENSY TNC', 'No coordinates present. Use GET POSITION first.')
            return
        msg = f'My GPS position is lat {lat} lon {lon}'
        self.tx_var.set(msg)
        self.show_page('Main')
        self._save_settings()

    # ----- Send -----

        # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — ENTER KEY SEND WIRING
    # ---------------------------------------------------------------
    # Pressing [Enter] in the message field MUST call send_message().
    # If this binding is changed, manual TX (KISS UI frames) will break.
    # ================================================================
    def _on_enter_pressed(self, event):
        self.send_message()
        return "break"


    # ================================================================
    # ⚠️ DO NOT MODIFY OR REMOVE — CORE SEND MESSAGE / PTT WIRING
    # ---------------------------------------------------------------
    # This function is the *only* path for manual TX:
    #   - Called by [Enter] key and Send button.
    #   - If in KISS mode: builds AX.25 UI frame, wraps in KISS, keys TNC.
    #   - If not in KISS: falls back to raw text (for manual TNC commands).
    # Any refactor that bypasses this will stop PTT / RF from working.
    # ================================================================
    
    def send_message(self):
        if not self.ser:
            self.log("[ERR] Not connected.")
            return

        text = (self.tx_var.get() or "").strip()
        if not text:
            return

        # KISS mode: send proper AX.25 UI frame so TNC keys PTT.
        if self.kiss_mode:
            src = (self.call_var.get() or "").strip().upper()
            if not src:
                self.log("[ERR] Set MyCall before sending.")
                return

            dst = (self.to_var.get() or "").strip().upper()

            # If no explicit "To:", infer from active chat or default to CQ.
            if not dst:
                if getattr(self, "active_chat", "All") not in ("All", "Settings", "Beacon", "", None):
                    dst = str(self.active_chat).upper()
                else:
                    dst = "CQ"

            is_beacon = text.startswith("**")
            ack_id = None
            wire_text = text

            # Decide if this message should request an ACK
            ack_applicable = (not is_beacon and dst not in ("", "CQ", "ALL"))

            if ack_applicable:
                if self._has_pending_ack_blocker():
                    # Courtesy: avoid stacking ACK-demanding frames
                    self.log("[ACK] Pending ACK in-flight; sending without [ACK:...]")
                else:
                    ack_id = self._generate_ack_id()
                    wire_text = f"{text} [ACK:{ack_id}]"
                    wire_len = len(wire_text.encode("ascii", "ignore"))
                    ack_timeout = self._compute_ack_timeout(wire_len)
            else:
                ack_timeout = 0.0

            try:
                frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=wire_text)
                self._write_bytes(frame)
            except Exception as e:
                self.log(f"[ERR] Failed to send (KISS): {e}")
                return

            now = time.time()
            ts = time.strftime("%H:%M:%S", time.localtime(now))
            msg = {
                "ts": ts,
                "epoch": now,
                "direction": "out",
                "text": text,
                "src": src,
                "dst": dst,
            }
            if ack_id:
                msg["ack_id"] = ack_id
                msg["ack_status"] = "pending"
                msg["ack_attempts"] = 1
                msg["ack_is_request"] = True

            def do():
                # Normal messages: log to All + per-dst thread
                if not is_beacon:
                    self._append_message("All", msg)
                    if dst not in ("CQ", "ALL"):
                        self._append_message(dst, msg)
                    if self.active_chat in ("All", dst):
                        self._render_active_chat()

                # Beacons feed link/position logic
                if text.startswith("**") and hasattr(self, "_update_beacons_from_text"):
                    self._update_beacons_from_text(text, now)
                    try:
                        self._refresh_beacon_listbox()
                    except Exception:
                        pass

                self.tx_var.set("")

            self._enqueue_ui(do)

            if ack_id:
                self._register_pending_ack(ack_id, src, dst, text, ack_timeout, now)

        else:
            # Raw / pre-KISS mode: just dump ASCII, still track basic log
            try:
                wire = (text + "\r").encode("ascii", "ignore")
                self.ser.write(wire)
                self.ser.flush()
            except Exception as e:
                self.log(f"[ERR] TX error: {e}")
                return

            now = time.time()
            ts = time.strftime("%H:%M:%S", time.localtime(now))
            dst = (self.to_var.get() or "").strip().upper() or "RAW"
            src = (self.call_var.get() or "").strip().upper()

            msg = {
                "ts": ts,
                "epoch": now,
                "direction": "out",
                "text": text,
                "src": src,
                "dst": dst,
            }

            def do():
                self._append_message("All", msg)
                if dst not in ("CQ", "ALL", "RAW"):
                    self._append_message(dst, msg)
                if self.active_chat in ("All", dst):
                    self._render_active_chat()
                self.tx_var.set("")

            self._enqueue_ui(do)



    # ----- Close -----

    def on_close(self):
        self.read_running = False
        self.gps_running = False
        # Stop any pending beacon timer
        try:
            self._cancel_beacon_timer()
        except Exception:
            pass
        if self.gps_thread:
            try:
                self.gps_thread.join(timeout=0.5)
            except Exception:
                pass
        if self.read_thread:
            try:
                self.read_thread.join(timeout=0.5)
            except Exception:
                pass
        for s in (self.ser, self.gps_ser, self.link500_ser):
            if s:
                try:
                    s.close()
                except Exception:
                    pass
        self._save_settings()
        self.master.destroy()


def main():
    had_error = False
    try:
        root = tk.Tk()
        enable_dark_titlebar(root)
        app = RobustChatSimpleV16(root)
        root.mainloop()
    except Exception:
        had_error = True
        logmsg("Unhandled exception in main():")
        traceback.print_exc()
    finally:
        logmsg("===== Robust Chat Simple v1.8 shutdown =====")
        try:
            _lf = globals().get("_log_file", None)
            if _lf:
                _lf.close()
        except Exception:
            pass
        # Hold console open on error when run via double-click
        if had_error:
            try:
                input("\nPress Enter to close...")
            except Exception:
                pass

if __name__ == "__main__":
    main()