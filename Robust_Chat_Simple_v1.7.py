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
    Resolve a file path relative to this script's directory.
    Used for settings/log/messages files to keep them beside the .py.
    """
    try:
        base = os.path.dirname(os.path.abspath(__file__))
    except Exception:
        base = os.getcwd()
    return os.path.join(base, name)






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
        self.master.title("Robust Chat Simple v1.7.1")
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

        # UI infra
        self.ui_queue: "queue.SimpleQueue" = queue.SimpleQueue()

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

        self.speed_var = tk.StringVar(value="R300")
        self.current_page = "Main"

        # GPS tab vars
        self.fixed_name_var = tk.StringVar()
        self.fixed_lat_var = tk.StringVar()
        self.fixed_lon_var = tk.StringVar()

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

        self.settings = {}

        self._load_settings()
        self._load_messages()
        self._load_positions()
        self._build_ui()
        self._apply_settings_to_ui()
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

    # ----- UI Build -----

    def _build_ui(self):
        style = ttk.Style()
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

        self.btn_tab_main.grid(row=0, column=0, padx=2)
        self.btn_tab_gps.grid(row=0, column=1, padx=2)
        self.btn_tab_beacon.grid(row=0, column=2, padx=2)
        self.btn_tab_locator.grid(row=0, column=3, padx=2)

        # Connection row
        conn = ttk.Frame(header, style="Header.TFrame")
        conn.grid(row=1, column=0, sticky="nsew", pady=(2, 4))
        conn.columnconfigure(10, weight=1)

        ttk.Label(conn, text="COM:", style="Header.TLabel").grid(row=0, column=0, padx=(8, 4))
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(conn, textvariable=self.port_var, width=9, state="readonly")
        self.port_combo.grid(row=0, column=1, padx=(0, 4))
        self._populate_ports()
        ttk.Button(conn, text="↻", width=3, command=self._populate_ports).grid(
            row=0, column=2, padx=(0, 8)
        )

        self.connect_btn = ttk.Button(conn, text="Connect", command=self.connect_port)
        self.connect_btn.grid(row=0, column=3, padx=(0, 4))
        self.disconnect_btn = ttk.Button(
            conn, text="Disconnect", command=self.disconnect_port, state="disabled"
        )
        self.disconnect_btn.grid(row=0, column=4, padx=(0, 8))

        ttk.Label(conn, text="MyCall:", style="Header.TLabel").grid(
            row=0, column=5, padx=(0, 4)
        )
        self.call_var = tk.StringVar()

        self.call_entry = ttk.Entry(conn, textvariable=self.call_var, width=12)
        self.call_entry.grid(row=0, column=6, padx=(0, 8))

        def mycall_trace(*_):
            self._save_settings()
            self._draw_locator_compass()

        self.call_var.trace_add("write", mycall_trace)

        ttk.Label(conn, text="Speed:", style="Header.TLabel").grid(
            row=0, column=7, padx=(0, 4)
        )
        self.r300_btn = ttk.Radiobutton(
            conn,
            text="R300",
            value="R300",
            variable=self.speed_var,
            command=self.on_speed_change,
        )
        self.r300_btn.grid(row=0, column=8, padx=(0, 2))
        self.r600_btn = ttk.Radiobutton(
            conn,
            text="R600",
            value="R600",
            variable=self.speed_var,
            command=self.on_speed_change,
        )
        self.r600_btn.grid(row=0, column=9, padx=(0, 8))

        self.clear_btn = ttk.Button(conn, text="Clear Messages", command=self.clear_messages)
        self.clear_btn.grid(row=0, column=10, padx=(0, 8))

        # Sidebar
        sidebar = ttk.Frame(self.master, style="Sidebar.TFrame")
        sidebar.grid(row=1, column=0, sticky="nsew")
        sidebar.rowconfigure(1, weight=1)
        sidebar.rowconfigure(3, weight=1)
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

        ttk.Label(sidebar, text="BEACONS HEARD", style="SidebarHeader.TLabel").grid(
            row=2, column=0, sticky="w", padx=8, pady=(4, 2)
        )
        
        self.beacon_tree = ttk.Treeview(
            sidebar,
            show="tree",
            selectmode="browse",
            style="Sidebar.Treeview"
        )
        self.beacon_tree.grid(row=3, column=0, sticky="nsew", padx=6, pady=(0, 8))

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

        for p in (self.page_main, self.page_gps, self.page_beacon, self.page_locator):
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

        self._update_tab_styles()

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

        # Row 1: GPS from COM (NMEA)
        tk.Label(
            f,
            text="GPS",
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

        # Row 2: LiNK500 GPS via %AZ
        tk.Label(
            f,
            text="LiNK500 GPS",
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
        ).grid(row=2, column=7, padx=(0, 8), pady=6, sticky="w")

        for var in (self.link500_port_var, self.link500_lat_var, self.link500_lon_var):
            var.trace_add("write", lambda *_: self._save_settings())

        # Once both combos exist, populate port lists
        self._populate_gps_ports()

        tk.Label(
            f,
            text="All three GPS sections persist. LiNK500 SEND: KISS-off → %AZ → KISS-on → stage position message.",
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

        def do():
            self._append_message("All", msg)
            if self.active_chat in ("All",):
                self._render_active_chat()
            # Keep beacon list fresh if parser is present
            if hasattr(self, "_update_beacons_from_text"):
                self._update_beacons_from_text(beacon, now)
                self._refresh_beacon_listbox()

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
        # Priority: LiNK500 -> GPS -> Fixed
        for lat_var, lon_var in (
            (self.link500_lat_var, self.link500_lon_var),
            (self.gps_lat_var, self.gps_lon_var),
            (self.fixed_lat_var, self.fixed_lon_var),
        ):
            try:
                lat = float(lat_var.get())
                lon = float(lon_var.get())
                return lat, lon
            except Exception:
                continue
        return None, None

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

        # Centre label = MyCall base
        my = (self.call_var.get() or "").strip().upper()
        my_base = self._callsign_base(my) if my else "MYCALL"
        c.create_text(
            cx,
            cy,
            text=my_base,
            fill=text_col,
            font=("Segoe UI", 12, "bold"),
        )

        # Plot stations with known positions
        my_lat, my_lon = self._get_own_position()
        if my_lat is None or my_lon is None:
            return

        def bearing_and_range(lat1, lon1, lat2, lon2):
            r_earth = 3958.8  # miles
            phi1 = math.radians(lat1)
            phi2 = math.radians(lat2)
            dphi = math.radians(lat2 - lat1)
            dlambda = math.radians(lon2 - lon1)

            a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(
                dlambda / 2
            ) ** 2
            cang = 2 * math.atan2(math.sqrt(a), max(1e-12, math.sqrt(1 - a)))
            dist = r_earth * cang

            y = math.sin(dlambda) * math.cos(phi2)
            x = math.cos(phi1) * math.sin(phi2) - math.sin(phi1) * math.cos(
                phi2
            ) * math.cos(dlambda)
            brg = (math.degrees(math.atan2(y, x)) + 360.0) % 360.0
            return brg, dist

        for call, pos in self.positions.items():
            try:
                lat2 = float(pos.get("lat"))
                lon2 = float(pos.get("lon"))
            except Exception:
                continue
            if call == my_base:
                continue
            brg, dist = bearing_and_range(my_lat, my_lon, lat2, lon2)
            dist_clamped = min(dist, 1500.0)
            if dist_clamped <= 1000.0:
                r = radius * (dist_clamped / 1000.0)
            else:
                r = radius

            ang = math.radians(brg)
            x = cx + r * math.sin(ang)
            y = cy - r * math.cos(ang)

            c.create_line(cx, cy, x, y, fill="#2aff70", width=1)
            c.create_oval(x - 2, y - 2, x + 2, y + 2, fill="#39ff14", outline="")
            label = f"{call} {int(dist)}mi {int(brg)}°"
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
        ):
            btn.configure(bg=inactive_bg, fg=inactive_fg)

        if self.current_page == "Main":
            self.btn_tab_main.configure(bg=active_bg)
        elif self.current_page == "GPS":
            self.btn_tab_gps.configure(bg=active_bg)
        elif self.current_page == "Beacon":
            self.btn_tab_beacon.configure(bg=active_bg)
        elif self.current_page == "Locator":
            self.btn_tab_locator.configure(bg=active_bg)

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
        else:
            self.page_main.tkraise()
            self.current_page = "Main"
        self._update_tab_styles()
        if name == "Locator":
            self._draw_locator_compass()

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
        try:
            if os.path.exists(self.messages_file):
                with open(self.messages_file, "r", encoding="utf-8", errors="replace") as f:
                    data = json.load(f)
                conv = data.get("conversations", {})
                if isinstance(conv, dict):
                    self.conversations.update(conv)
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
        self._prune_beacons(save=True)

        my = (self.call_var.get() or "").strip().upper()

        for parent in sorted(self.beacons.keys()):
            if parent == my:
                continue
            pcountry = self._lookup_country_for_call(parent)
            plabel = f"{parent} [{pcountry}]" if pcountry else parent
            p_iid = self.beacon_tree.insert("", "end", text=plabel)

            children = self.beacons[parent].get("children", {})
            for child in sorted(children.keys()):
                if child == my:
                    continue
                ccountry = self._lookup_country_for_call(child)
                clabel = f"{child} [{ccountry}]" if ccountry else child
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
        if " [" in label:
            base = label.split(" [", 1)[0].strip()
        else:
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

            # When we hit a new date (going backwards), start a new block with its header
            if date_str != last_date:
                if last_date is not None:
                    segments.append(("\n", ()))  # blank line between date blocks
                segments.append((f"── {date_str} ──\n", ("day_header",)))
                last_date = date_str

            ts = m.get("ts", dt.strftime("%H:%M:%S"))
            text = m.get("text", "")
            direction = m.get("direction", "sys")
            src = m.get("src") or ""
            dst = m.get("dst") or ""

            if direction == "sys":
                segments.append((f"{ts}  {text}\n", ("sys_msg",)))
            elif direction == "out":
                meta = f"{ts}  {my_base} → {dst or 'CQ'}"
                segments.append((text + "\n", ("out_msg",)))
                segments.append((meta + "\n", ("meta", "out_msg")))
            elif direction == "in":
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

        try:
            dst, src, info = self._parse_ax25(ax)
        except Exception as e:
            self.log(f"[KISS] AX.25 parse error: {e}")
            return

        try:
            txt = info.decode("ascii", errors="ignore").strip()
        except Exception:
            txt = ""
        if not txt:
            return

        now = time.time()

        # Beacon frames (start with **): update beacon/link/positions
        if txt.startswith("**"):
            def do_beacon():
                try:
                    self._update_beacons_from_text(txt, now)
                except Exception as e:
                    self.log(f"[KISS] Beacon update error: {e}")
            self._enqueue_ui(do_beacon)
            return

        # Normal chat frame
        ts = time.strftime("%H:%M:%S", time.localtime(now))
        msg = {
            "ts": ts,
            "epoch": now,
            "direction": "in",
            "text": txt,
            "src": src,
            "dst": dst,
        }

        def do_msg():
            try:
                my = (self.call_var.get() or "").strip().upper()
            except Exception:
                my = ""
            other = dst if src.upper() == my else src

            # Always log to All
            if hasattr(self, "_append_message"):
                self._append_message("All", msg)
                if other:
                    self._append_message(other, msg)

            # Keep beacon/link logic fed if text contains patterns we care about
            try:
                if hasattr(self, "_update_beacons_from_text"):
                    self._update_beacons_from_text(txt, now)
            except Exception as e:
                self.log(f"[KISS] Beacon-from-chat update error: {e}")

            # Refresh visible chat if relevant
            try:
                if getattr(self, "active_chat", "All") in ("All", other):
                    self._render_active_chat()
            except Exception as e:
                self.log(f"[KISS] Render error: {e}")

        self._enqueue_ui(do_msg)


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
        self.log(f"[GPS] Listening on {port} for NMEA (10-min position updates).")

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
                if now - self.gps_last_update < 600:
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
        for line in text.splitlines():
            if line.startswith(("$GPGGA", "$GPRMC", "$GNRMC", "$GNGGA")):
                lat, lon = self._parse_nmea_latlon(line.strip())
                if lat is not None and lon is not None:
                    return lat, lon
        m = re.search(
            r"Lat\s+([\-\d\.]+)\s+Lon\s+([\-\d\.]+)", text, flags=re.IGNORECASE
        )
        if m:
            try:
                return float(m.group(1)), float(m.group(2))
            except Exception:
                pass
        return None, None

    def _link500_gps_send(self):
        if not self.link500_ser:
            messagebox.showerror("LiNK500", "LiNK500 is not connected.")
            return
        try:
            # KISS OFF placeholder
            self.link500_ser.write(bytes([FEND, FESC, FEND]))
            self.link500_ser.flush()
            time.sleep(0.1)

            # ESC + %AZ
            self.link500_ser.write(b"\x1B%AZ\r")
            self.link500_ser.flush()
            time.sleep(0.5)
            resp = self.link500_ser.read(512).decode("utf-8", errors="ignore")

            # KISS ON placeholder
            self.link500_ser.write(bytes([FEND, 0x00]))
            self.link500_ser.flush()
        except Exception as e:
            self.log(f"[LiNK500] %AZ error: {e}")
            return

        lat, lon = self._extract_latlon_from_text(resp)
        if lat is None or lon is None:
            self.log(f"[LiNK500] Could not parse %AZ response: {resp!r}")
            messagebox.showerror("LiNK500", "Could not parse GPS from %AZ response.")
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

        msg = f"My GPS position is lat {lat:.5f} lon {lon:.5f}"
        self.tx_var.set(msg)
        self.show_page("Main")

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
                if hasattr(self, "active_chat") and self.active_chat not in ("All", "Settings", "Beacon", ""):
                    dst = self.active_chat.upper()
                else:
                    dst = "CQ"

            is_beacon = text.startswith("**")

            try:
                frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=text)
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

            def do():
                # Normal messages: log to All + per-dst thread
                if not is_beacon:
                    self._append_message("All", msg)
                    if dst not in ("CQ", "ALL"):
                        self._append_message(dst, msg)
                    if self.active_chat in ("All", dst):
                        self._render_active_chat()

                # Beacons + any "**" content feed link/position logic
                if text.startswith("**") and hasattr(self, "_update_beacons_from_text"):
                    self._update_beacons_from_text(text, now)
                    self._refresh_beacon_listbox()

                self.tx_var.set("")

            self._enqueue_ui(do)

        else:
            # Not yet in KISS mode:
            # Behave like original v1.4.9 for compatibility with
            # manual TNC/CLI use. This path does NOT guarantee PTT.
            src = (self.call_var.get() or "").strip().upper() or "ME"
            dst = (self.to_var.get() or "").strip().upper() or "CQ"
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

            try:
                wire = (text + "\r\n").encode("utf-8", errors="replace")
                self.ser.write(wire)
                self.ser.flush()
            except Exception as e:
                self.log(f"[ERR] TX error: {e}")

            def do():
                self._append_message("All", msg)
                if dst not in ("CQ", "ALL"):
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
        app = RobustChatSimpleV16(root)
        root.mainloop()
    except Exception:
        had_error = True
        logmsg("Unhandled exception in main():")
        traceback.print_exc()
    finally:
        logmsg("===== Robust Chat Simple v1.6 shutdown =====")
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
