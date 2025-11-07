"""
Robust_Chat_Simple_v1_PATCHED.py

- Saves startup_log.txt, messages_v1.json, link_graph.json in the same folder as this .py
- Keeps console open on error / non-interactive launch
- WhatsApp-style layout with Chats + Beacons Heard
- Newest messages at top; each day's header appears above that day's messages
- Beacon frames (**PARENT /CHILD ...) are NOT shown in chat:
    - They only update link_graph.json
    - "Beacons Heard" renders from link_graph.json:
        PARENT on its own line, children indented underneath (no ** or / in UI)
"""

import sys
import io
import os
import datetime
import traceback
import threading
import time
import queue
import json
import tkinter as tk
from tkinter import ttk, messagebox

# -----------------------------------------------------
# Paths pinned to script directory
# -----------------------------------------------------

try:
    SCRIPT_PATH = os.path.abspath(sys.argv[0])
except Exception:
    SCRIPT_PATH = os.path.abspath(__file__) if "__file__" in globals() else os.getcwd()

BASE_DIR = os.path.dirname(SCRIPT_PATH)

def app_path(name: str) -> str:
    return os.path.join(BASE_DIR, name)

# KISS special characters
FEND = 0xC0
FESC = 0xDB
TFEND = 0xDC
TFESC = 0xDD

# =========================================================
# Startup logging
# =========================================================

LOGFILE = app_path("startup_log.txt")

_orig_out = sys.stdout
_orig_err = sys.stderr

_log_file = None
try:
    _log_file = open(LOGFILE, "a", encoding="utf-8")
except Exception:
    _log_file = None


class Tee(io.TextIOBase):
    def __init__(self, *streams):
        self.streams = [s for s in streams if s is not None]

    def write(self, s):
        for st in self.streams:
            try:
                st.write(s)
                st.flush()
            except Exception:
                pass
        return len(s)

    def flush(self):
        for st in self.streams:
            try:
                st.flush()
            except Exception:
                pass


if _log_file is not None:
    sys.stdout = sys.stderr = Tee(_orig_out, _orig_err, _log_file)
else:
    sys.stdout = sys.stderr = Tee(_orig_out, _orig_err)


def logmsg(msg: str) -> None:
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{ts}] {msg}")


logmsg("===== Robust Chat Simple v1 startup =====")
logmsg(f"Python executable: {sys.executable}")
logmsg(f"Script file: {SCRIPT_PATH}")
logmsg(f"Working directory: {os.getcwd()}")
logmsg(f"Python version: {sys.version.split()[0]}")

# =========================================================
# pyserial import
# =========================================================

try:
    import serial
    import serial.tools.list_ports
except ModuleNotFoundError as e:
    logmsg(f"Missing module: {e.name}")
    if e.name == "serial":
        logmsg("Install pyserial into this Python with:")
        logmsg("    python -m pip install pyserial")
    if _log_file:
        _log_file.close()
    try:
        if os.name == "nt":
            import msvcrt
            print("\n[Press any key to close]")
            msvcrt.getch()
        else:
            input("\n[Press Enter to close]")
    except Exception:
        pass
    sys.exit(1)


# =========================================================
# Main Application
# =========================================================


class RobustChatSimpleV1:
    def __init__(self, master: tk.Tk):
        self.master = master
        self.master.title("Robust Chat Simple v1")

        # Serial / KISS
        self.ser = None
        self.read_thread = None
        self.read_running = False
        self.kiss_mode = False

        # Conversations & beacons
        self.conversations = {"All": [], "Settings": []}
        self.active_chat = "All"
        # beacons: {parent: {"last": ts, "children": {child: ts}}}
        self.beacons = {}

        # Files (script directory)
        self.messages_file = app_path("messages_v1.json")
        self.link_graph_file = app_path("link_graph.json")

        # UI queue & timers
        self.ui_queue: "queue.SimpleQueue" = queue.SimpleQueue()
        self.beacon_job = None

        # Load data (no UI calls)
        self._load_messages()
        self._load_link_graph(prune_only=True)

        # Build UI
        self._build_ui()

        # Now widgets exist → final prune + refresh
        self._prune_beacons(save=True)
        self._refresh_chat_listbox()
        self._refresh_beacon_listbox()
        self._render_active_chat()

        # Initial messages
        self.log("Wire TX↔RX audio between Teensy RPR TNCs.")
        self.log("Set MyCall, then Connect. Preflight + KISS run automatically.")
        self.log("Messages: newest at top, per-day headers. Beacons shown on left.")

        # Start queue pump & close handler
        self.master.after(50, self._process_ui_queue)
        self.master.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------- UI layout ----------

    def _build_ui(self):
        self.master.geometry("980x600")
        self.master.minsize(800, 480)
        self.master.configure(bg="#0b141a")

        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure("Sidebar.TFrame", background="#111b21")
        style.configure("Chat.TFrame", background="#0b141a")
        style.configure("Header.TFrame", background="#202c33")
        style.configure("SidebarHeader.TLabel", background="#111b21", foreground="#e9edef")
        style.configure("Header.TLabel", background="#202c33", foreground="#e9edef")

        self.master.columnconfigure(0, weight=0, minsize=260)
        self.master.columnconfigure(1, weight=1)
        self.master.rowconfigure(1, weight=1)

        # Top bar
        top = ttk.Frame(self.master, style="Header.TFrame")
        top.grid(row=0, column=0, columnspan=2, sticky="nsew")
        top.columnconfigure(8, weight=1)

        ttk.Label(top, text="COM:", style="Header.TLabel").grid(row=0, column=0, padx=(8, 4), pady=6)
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(top, textvariable=self.port_var, width=8, state="readonly")
        self.port_combo.grid(row=0, column=1, padx=(0, 4), pady=6)
        self._populate_ports()
        ttk.Button(top, text="↻", width=3, command=self._populate_ports).grid(row=0, column=2, padx=(0, 8), pady=6)

        self.connect_btn = ttk.Button(top, text="Connect", command=self.connect_port)
        self.connect_btn.grid(row=0, column=3, padx=(0, 4), pady=6)
        self.disconnect_btn = ttk.Button(top, text="Disconnect", command=self.disconnect_port, state="disabled")
        self.disconnect_btn.grid(row=0, column=4, padx=(0, 8), pady=6)

        ttk.Label(top, text="MyCall:", style="Header.TLabel").grid(row=0, column=5, padx=(0, 4))
        self.call_var = tk.StringVar()
        self.call_entry = ttk.Entry(top, textvariable=self.call_var, width=12)
        self.call_entry.grid(row=0, column=6, padx=(0, 8))

        self.clear_btn = ttk.Button(top, text="Clear Messages", command=self.clear_messages)
        self.clear_btn.grid(row=0, column=7, padx=(0, 8), pady=6)

        # Sidebar
        sidebar = ttk.Frame(self.master, style="Sidebar.TFrame")
        sidebar.grid(row=1, column=0, sticky="nsew")
        sidebar.rowconfigure(1, weight=1)
        sidebar.rowconfigure(3, weight=1)
        sidebar.columnconfigure(0, weight=1)

        ttk.Label(sidebar, text="Chats", style="SidebarHeader.TLabel").grid(
            row=0, column=0, sticky="w", padx=8, pady=(8, 2)
        )

        self.chat_listbox = tk.Listbox(
            sidebar,
            bg="#111b21",
            fg="#e9edef",
            selectbackground="#202c33",
            selectforeground="#e9edef",
            activestyle="none",
            highlightthickness=0,
            bd=0,
        )
        self.chat_listbox.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 6))
        self.chat_listbox.bind("<<ListboxSelect>>", self.on_chat_select)

        ttk.Label(sidebar, text="Beacons Heard", style="SidebarHeader.TLabel").grid(
            row=2, column=0, sticky="w", padx=8, pady=(4, 2)
        )

        self.beacon_listbox = tk.Listbox(
            sidebar,
            bg="#111b21",
            fg="#e9edef",
            selectbackground="#202c33",
            selectforeground="#e9edef",
            activestyle="none",
            highlightthickness=0,
            bd=0,
        )
        self.beacon_listbox.grid(row=3, column=0, sticky="nsew", padx=6, pady=(0, 8))

        # Chat area
        chat_wrapper = ttk.Frame(self.master, style="Chat.TFrame")
        chat_wrapper.grid(row=1, column=1, sticky="nsew")
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
        )
        self.chat_text.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(chat_wrapper, command=self.chat_text.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.chat_text.config(yscrollcommand=scroll.set)

        self.chat_text.tag_configure("sys_msg", foreground="#8696a0")
        self.chat_text.tag_configure("in_msg", foreground="#e9edef")
        self.chat_text.tag_configure("out_msg", foreground="#e9edef")
        self.chat_text.tag_configure("meta", foreground="#8696a0", font=("Segoe UI", 7))
        self.chat_text.tag_configure("day_header", foreground="#8696a0", font=("Segoe UI", 8, "bold"), justify="center")

        # Bottom input
        input_bar = ttk.Frame(self.master, style="Chat.TFrame")
        input_bar.grid(row=2, column=0, columnspan=2, sticky="nsew")
        input_bar.columnconfigure(2, weight=1)

        ttk.Label(input_bar, text="To:").grid(row=0, column=0, padx=(8, 4), pady=6)
        self.to_var = tk.StringVar(value="CQ")
        self.to_entry = ttk.Entry(input_bar, textvariable=self.to_var, width=10)
        self.to_entry.grid(row=0, column=1, padx=(0, 8), pady=6)

        self.tx_var = tk.StringVar()
        self.tx_entry = ttk.Entry(input_bar, textvariable=self.tx_var)
        self.tx_entry.grid(row=0, column=2, padx=(0, 8), pady=6, sticky="ew")
        self.tx_entry.bind("<Return>", self._on_enter_pressed)

        self.send_btn = ttk.Button(input_bar, text="Send", command=self.send_message, state="disabled")
        self.send_btn.grid(row=0, column=3, padx=(0, 8), pady=6)

    # ---------- UI queue ----------

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

    # ---------- Persistence ----------

    def _load_messages(self):
        try:
            if os.path.exists(self.messages_file):
                with open(self.messages_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                conv = data.get("conversations", {})
                if isinstance(conv, dict):
                    self.conversations.update(conv)
        except Exception as e:
            logmsg(f"Failed to load messages_v1.json: {e}")

    def _load_link_graph(self, prune_only: bool = False):
        try:
            if os.path.exists(self.link_graph_file):
                with open(self.link_graph_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                beacons = data.get("beacons", {})
                if isinstance(beacons, dict):
                    self.beacons = beacons
        except Exception as e:
            logmsg(f"Failed to load link_graph.json: {e}")
        self._prune_beacons(save=not prune_only)

    def _save_messages(self):
        try:
            with open(self.messages_file, "w", encoding="utf-8") as f:
                json.dump({"conversations": self.conversations}, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logmsg(f"Failed to save messages_v1.json: {e}")

    def _save_link_graph(self):
        try:
            with open(self.link_graph_file, "w", encoding="utf-8") as f:
                json.dump({"beacons": self.beacons}, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logmsg(f"Failed to save link_graph.json: {e}")

    # ---------- Clear messages ----------

    def clear_messages(self):
        if not messagebox.askyesno(
            "Clear messages",
            "This will delete all stored messages and beacons from this app,\n"
            "messages_v1.json and link_graph.json.\n\nAre you sure?",
        ):
            return

        self.conversations = {"All": [], "Settings": []}
        self.active_chat = "All"
        self.beacons = {}

        for p in (self.messages_file, self.link_graph_file):
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception as e:
                logmsg(f"Failed to remove {p}: {e}")

        self._save_messages()
        self._save_link_graph()
        self._refresh_chat_listbox()
        self._refresh_beacon_listbox()
        self._render_active_chat()

    # ---------- Sidebar / selection ----------

    def _refresh_chat_listbox(self):
        self.chat_listbox.delete(0, tk.END)
        keys = ["All", "Settings"] + sorted(
            k for k in self.conversations.keys() if k not in ("All", "Settings")
        )
        for name in keys:
            self.chat_listbox.insert(tk.END, name)
        try:
            idx = keys.index(self.active_chat)
        except ValueError:
            idx = 0
            self.active_chat = keys[0]
        self.chat_listbox.selection_set(idx)
        self.chat_listbox.activate(idx)

    def _refresh_beacon_listbox(self):
        if not hasattr(self, "beacon_listbox"):
            return

        self.beacon_listbox.delete(0, tk.END)

        # Ensure pruning (also writes link_graph.json)
        self._prune_beacons(save=True)

        for parent in sorted(self.beacons.keys()):
            # Parent as plain callsign
            self.beacon_listbox.insert(tk.END, parent)
            children = self.beacons[parent].get("children", {})
            for child in sorted(children.keys()):
                # Child indented under parent
                self.beacon_listbox.insert(tk.END, f"   {child}")

    def on_chat_select(self, event=None):
        idxs = self.chat_listbox.curselection()
        if not idxs:
            return
        name = self.chat_listbox.get(idxs[0]).strip()
        if not name:
            return
        if name not in self.conversations:
            self.conversations[name] = []
        self.active_chat = name
        if name not in ("All", "Settings"):
            self.to_var.set(name)
        self._render_active_chat()

    # ---------- Log into Settings ----------

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

    # ---------- Messages view (newest at top, proper day headers) ----------

    def _append_message(self, chat_key: str, msg: dict, save: bool = True):
        self.conversations.setdefault(chat_key, []).append(dict(msg))
        if save:
            self._save_messages()
        self._refresh_chat_listbox()

    def _render_active_chat(self):
        self.chat_text.configure(state="normal")
        self.chat_text.delete("1.0", tk.END)

        msgs = self.conversations.get(self.active_chat, [])
        mycall = (self.call_var.get() or "").strip().upper() or "Me"

        # Build segments in chronological order, then reverse-insert
        segments = []
        last_date = None

        for m in msgs:
            epoch = m.get("epoch") or time.time()
            dt = datetime.datetime.fromtimestamp(epoch)
            date_str = dt.strftime("%a %d %b %Y")

            # New day header appears ABOVE that day's first message
            if date_str != last_date:
                if last_date is not None:
                    segments.append(("\n", ()))
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
                meta = f"{ts}  {mycall} → {dst or 'CQ'}"
                segments.append((text + "\n", ("out_msg",)))
                segments.append((meta + "\n", ("meta", "out_msg")))
            elif direction == "in":
                meta = f"{ts}  {src or '??'} → {dst or ''}"
                segments.append((text + "\n", ("in_msg",)))
                segments.append((meta + "\n", ("meta", "in_msg")))
            segments.append(("\n", ()))

        # Insert from newest to oldest so newest is at top
        for text, tags in reversed(segments):
            if tags:
                self.chat_text.insert("1.0", text, tags)
            else:
                self.chat_text.insert("1.0", text)

        self.chat_text.configure(state="disabled")

    # ---------- Serial / KISS ----------

    def _populate_ports(self):
        ports = [p.device for p in serial.tools.list_ports.comports()]
        self.port_combo["values"] = ports
        if ports:
            cur = self.port_var.get()
            if cur in ports:
                self.port_combo.set(cur)
            else:
                self.port_combo.current(0)

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
            self.ser = serial.Serial(port, baudrate=38400, timeout=0.1)
        except Exception as e:
            self.log(f"[ERR] Could not open {port}: {e}")
            self.ser = None
            return

        self.log(f"[INFO] Connected to {port}")
        self.connect_btn.config(state="disabled")
        self.disconnect_btn.config(state="normal")

        self.read_running = True
        self.read_thread = threading.Thread(target=self.reader_loop, daemon=True)
        self.read_thread.start()

        self.master.after(1000, self.start_preflight)

    def disconnect_port(self):
        self.read_running = False
        self.kiss_mode = False

        if self.beacon_job is not None:
            try:
                self.master.after_cancel(self.beacon_job)
            except Exception:
                pass
            self.beacon_job = None

        if self.read_thread:
            self.read_thread.join(timeout=0.5)
            self.read_thread = None

        if self.ser:
            try:
                self.ser.close()
            except Exception:
                pass
            self.ser = None

        self.log("[INFO] Disconnected.")
        self.connect_btn.config(state="normal")
        self.disconnect_btn.config(state="disabled")
        self.send_btn.config(state="disabled")

    # ---------- Preflight + KISS ----------

    def start_preflight(self):
        if not self.ser:
            self.log("[ERR] Not connected.")
            return

        callsign = (self.call_var.get() or "").strip().upper()
        if not callsign:
            self.log("[ERR] Enter your callsign before START.")
            return

        self.log("[PRE] Running preflight + KISS...")
        t = threading.Thread(target=self._preflight_worker, args=(callsign,), daemon=True)
        t.start()

    def _preflight_worker(self, callsign: str):
        try:
            # KISS OFF, reset, set params, then KISS ON
            self._write_bytes(bytes([FEND, 0xFF, FEND, 0x0D]))
            time.sleep(0.2)
            self._send_esc_command("%ZK")
            time.sleep(0.2)
            self._send_esc_command("X 1")
            time.sleep(0.2)
            self._send_esc_command(f"I {callsign}")
            time.sleep(0.2)
            self._send_esc_command("%B R300")
            time.sleep(0.2)
            self._send_esc_command("%ZS")
            time.sleep(0.2)
            self._send_esc_command("@K")
            time.sleep(0.3)

            def done():
                self.kiss_mode = True
                self.send_btn.config(state="normal")
                self.log("[PRE] Done. Now in KISS mode (R300). Ready to chat.")
                self._schedule_beacon(first=True)

            self._enqueue_ui(done)
        except Exception as e:
            self.log(f"[ERR] Preflight failed: {e}")

    def _send_esc_command(self, body: str):
        if not self.ser:
            return
        cmd = ("\x1b" + body + "\r").encode("ascii", "ignore")
        self._write_bytes(cmd)
        self.log(f"[TX-CMD] ESC {body}")

    def _write_bytes(self, data: bytes):
        if not self.ser:
            return
        try:
            self.ser.write(data)
        except Exception as e:
            self.log(f"[ERR] Serial write failed: {e}")

    # ---------- Auto beacon ----------

    def _schedule_beacon(self, first: bool = False):
        if self.beacon_job is not None:
            try:
                self.master.after_cancel(self.beacon_job)
            except Exception:
                pass
            self.beacon_job = None

        if not (self.kiss_mode and self.read_running and self.ser):
            return

        delay = 60_000 if first else 600_000  # 1 min then every 10 min
        self.beacon_job = self.master.after(delay, self._send_auto_beacon)

    def _send_auto_beacon(self):
        self.beacon_job = None
        if not (self.kiss_mode and self.read_running and self.ser):
            return

        my = (self.call_var.get() or "").strip().upper()
        if not my:
            self._schedule_beacon(first=False)
            return

        # Gather heard calls from current beacons (parents and children) except self
        calls = set()
        for parent, pdata in self.beacons.items():
            if parent and parent != my:
                calls.add(parent)
            for child in pdata.get("children", {}):
                if child and child != my:
                    calls.add(child)

        text = f"**{my}" + "".join(f" /{c}" for c in sorted(calls))

        try:
            frame = self._build_kiss_ui_frame(src_call=my, dst_call="CQ", text=text)
            self._write_bytes(frame)
        except Exception as e:
            self.log(f"[ERR] Auto-beacon send failed: {e}")
            self._schedule_beacon(first=False)
            return

        now = time.time()

        # Beacon is housekeeping only: update beacons, not chat
        def do():
            self._update_beacons_from_text(text, now)
            self._refresh_beacon_listbox()

        self._enqueue_ui(do)
        self._schedule_beacon(first=False)

    # ---------- Beacons tracking ----------

    def _update_beacons_from_text(self, txt: str, now: float):
        if not txt.startswith("**"):
            return
        rest = txt[2:].strip()
        if not rest:
            return
        tokens = rest.split()
        if not tokens:
            return

        parent = tokens[0].lstrip("/").upper()
        if not parent:
            return

        entry = self.beacons.setdefault(parent, {"last": 0.0, "children": {}})
        entry["last"] = float(now)
        children = entry.setdefault("children", {})

        for tok in tokens[1:]:
            tok = tok.strip()
            if not tok:
                continue
            if tok.startswith("/"):
                child = tok[1:]
            else:
                child = tok
            child = child.upper()
            if child and child != parent:
                children[child] = float(now)

        self._prune_beacons(save=True)

    def _prune_beacons(self, save: bool = False):
        now = time.time()
        cutoff = now - 15 * 60
        to_del = []

        for parent, pdata in list(self.beacons.items()):
            children = pdata.get("children", {})
            # Prune stale children
            for c, ts in list(children.items()):
                try:
                    ts_val = float(ts)
                except Exception:
                    ts_val = 0.0
                if ts_val < cutoff:
                    del children[c]

            # Prune parent if stale and no children
            try:
                last_ts = float(pdata.get("last", 0.0))
            except Exception:
                last_ts = 0.0

            if last_ts < cutoff and not children:
                to_del.append(parent)
            else:
                pdata["last"] = last_ts
                pdata["children"] = children

        for p in to_del:
            del self.beacons[p]

        if save:
            self._save_link_graph()

    # ---------- Reader / frames ----------

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
                # Pre-KISS: show raw banner etc in Settings
                try:
                    s = data.decode("ascii", errors="ignore")
                except Exception:
                    s = ""
                s = s.replace("\r", "")
                for line in s.split("\n"):
                    line = line.strip()
                    if line:
                        self.log("[RAW] " + line)
                continue

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

    def _handle_kiss_frame(self, raw: bytes):
        if not raw:
            return
        data = self._kiss_unescape(raw)
        if not data:
            return
        if (data[0] & 0x0F) != 0x00:
            return  # not a data frame

        ax = data[1:]
        if len(ax) < 16:
            return

        try:
            dst, src, info = self._parse_ax25(ax)
        except Exception as e:
            self.log(f"[KISS] Parse error: {e}")
            return

        try:
            txt = info.decode("ascii", errors="ignore").strip()
        except Exception:
            txt = ""
        if not txt:
            return

        now = time.time()

        # Beacon frames: only update beacon graph, not chat
        if txt.startswith("**"):
            def do_beacon():
                self._update_beacons_from_text(txt, now)
                self._refresh_beacon_listbox()
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
            my = (self.call_var.get() or "").strip().upper()
            other = dst if src.upper() == my else src

            self._append_message("All", msg)
            if other:
                self._append_message(other, msg)

            if self.active_chat in ("All", other):
                self._render_active_chat()

        self._enqueue_ui(do_msg)

    # ---------- AX.25 / KISS helpers ----------

    def _parse_ax25(self, ax: bytes):
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

    def _kiss_unescape(self, data: bytes) -> bytes:
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

    def _encode_ax25_addr(self, call: str, last: bool) -> bytes:
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
        info = (text + "\r").encode("ascii", "ignore")
        addr = self._encode_ax25_addr(dst_call, last=False) + self._encode_ax25_addr(src_call, last=True)
        ctrl = bytes([0x03])
        pid = bytes([0xF0])
        ax = addr + ctrl + pid + info
        kiss = bytes([0x00]) + ax
        esc = self._kiss_escape(kiss)
        return bytes([FEND]) + esc + bytes([FEND])

    # ---------- Send ----------

    def _on_enter_pressed(self, event):
        self.send_message()
        return "break"

    def send_message(self):
        if not self.ser:
            self.log("[ERR] Not connected.")
            return
        if not self.kiss_mode:
            self.log("[ERR] Not in KISS mode yet.")
            return

        text = (self.tx_var.get() or "").strip()
        if not text:
            return

        src = (self.call_var.get() or "").strip().upper()
        if not src:
            self.log("[ERR] Set MyCall first.")
            return

        dst = (self.to_var.get() or "").strip().upper()
        if not dst:
            if self.active_chat not in ("All", "Settings"):
                dst = self.active_chat.upper()
            else:
                dst = "CQ"

        is_beacon = text.startswith("**")

        try:
            frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=text)
            self._write_bytes(frame)
        except Exception as e:
            self.log(f"[ERR] Failed to send: {e}")
            return

        now = time.time()
        ts = time.strftime("%H:%M:%S", time.localtime(now))

        def do():
            if is_beacon:
                # Beacon: only update beacons, no chat message
                self._update_beacons_from_text(text, now)
                self._refresh_beacon_listbox()
            else:
                msg = {
                    "ts": ts,
                    "epoch": now,
                    "direction": "out",
                    "text": text,
                    "src": src,
                    "dst": dst,
                }
                self._append_message("All", msg)
                key = dst if dst not in ("CQ", "ALL") else "All"
                self._append_message(key, msg)
                # Beacons in normal text still parsed if they match format,
                # but they will be handled via _update_beacons_from_text if needed.
                self._update_beacons_from_text(text, now)
                if self.active_chat in ("All", key):
                    self._render_active_chat()
            self.tx_var.set("")

        self._enqueue_ui(do)

    # ---------- Cleanup ----------

    def on_close(self):
        self.disconnect_port()
        self.master.destroy()


# =========================================================
# Main entry
# =========================================================

if __name__ == "__main__":
    had_error = False
    try:
        logmsg("Creating Tk root and launching GUI...")
        root = tk.Tk()
        app = RobustChatSimpleV1(root)
        logmsg("GUI created. Entering mainloop.")
        root.mainloop()
        logmsg("GUI closed normally.")
    except Exception:
        had_error = True
        logmsg("Unhandled exception in main:")
        traceback.print_exc()
    finally:
        logmsg("===== Robust Chat Simple v1 shutdown =====")
        try:
            if _log_file:
                _log_file.close()
        except Exception:
            pass

        # Hold console on error or non-interactive (double-click) so user can read it
        try:
            if had_error or not sys.stdout.isatty():
                if os.name == "nt":
                    import msvcrt
                    print("\n[Press any key to close this window]")
                    msvcrt.getch()
                else:
                    input("\n[Press Enter to close this window]")
        except Exception:
            pass
