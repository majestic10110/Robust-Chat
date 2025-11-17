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
import base64
import hashlib
import secrets
import socket
import http.server
import urllib.parse


REMOTE_DEFAULT_PORT = 9798  # Default TCP port for remote tablet/phone control

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    HAVE_AESGCM = True
except Exception:
    HAVE_AESGCM = False


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

def _derive_key(password: str, salt: bytes) -> bytes:
    """
    Derive a 256-bit key from the given password and salt using PBKDF2-HMAC-SHA256.
    """
    if not isinstance(password, str):
        password = str(password or "")
    # 200k iterations: sensible balance; adjust if needed
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200000, dklen=32)


def encrypt_text(password: str, plaintext: str) -> str:
    """
    Encrypt plaintext with password using AES-256-GCM.
    Returns ASCII-safe payload: [ENC]ENC1:salt:iv:cipher:tag
    """
    if not HAVE_AESGCM:
        raise RuntimeError("Encryption unavailable: 'cryptography' package not installed.")
    if not plaintext:
        raise ValueError("No plaintext provided.")
    salt = secrets.token_bytes(16)
    iv = secrets.token_bytes(12)
    key = _derive_key(password, salt)
    aesgcm = AESGCM(key)
    ct = aesgcm.encrypt(iv, plaintext.encode("utf-8"), None)
    # Split out tag (last 16 bytes for GCM)
    if len(ct) < 16:
        raise RuntimeError("Ciphertext too short.")
    cipher_bytes = ct[:-16]
    tag_bytes = ct[-16:]
    salt_b64 = base64.b64encode(salt).decode("ascii")
    iv_b64 = base64.b64encode(iv).decode("ascii")
    cipher_b64 = base64.b64encode(cipher_bytes).decode("ascii")
    tag_b64 = base64.b64encode(tag_bytes).decode("ascii")
    return f"[ENC]ENC1:{salt_b64}:{iv_b64}:{cipher_b64}:{tag_b64}"


def decrypt_text(password: str, payload: str) -> str:
    """
    Decrypt payload of form [ENC]ENC1:salt:iv:cipher:tag with the given password.
    Returns plaintext string.
    """
    if not HAVE_AESGCM:
        raise RuntimeError("Decryption unavailable: 'cryptography' package not installed.")
    if not payload.startswith("[ENC]ENC1:"):
        raise ValueError("Not a recognised encrypted payload.")
    try:
        body = payload[len("[ENC]ENC1:"):]
        parts = body.split(":")
        if len(parts) != 4:
            raise ValueError("Malformed encrypted payload.")
        salt_b64, iv_b64, cipher_b64, tag_b64 = parts
        salt = base64.b64decode(salt_b64)
        iv = base64.b64decode(iv_b64)
        cipher_bytes = base64.b64decode(cipher_b64)
        tag_bytes = base64.b64decode(tag_b64)
        key = _derive_key(password, salt)
        ct = cipher_bytes + tag_bytes
        aesgcm = AESGCM(key)
        pt = aesgcm.decrypt(iv, ct, None)
        return pt.decode("utf-8", errors="replace")
    except Exception as e:
        raise ValueError("Decryption failed.") from e


def is_encrypted_payload(text: str) -> bool:
    return isinstance(text, str) and text.startswith("[ENC]ENC1:")

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
    
    # ----- Radios loader -----
    def _load_radios(self):
        """
        Load REQUIRED radio models and settings from radios.json.
        Supports keys:
          - "model" or "Radio Model"
          - "protocol" or "Protocol" (values: "CI-V", "Kenwood", "YaesuBinary", "Yaesu", "Elecraft")
          - "civ" or "CI-V Address" (hex string)
          - "baud" or "Default Baud Rate"
          - optional: "parity", "stopbits", "bytesize", "kenwood_fa_supported"
        Normalizes to:
          self.radios_data[model] = {
              "protocol": "CIV" | "KENWOOD" | "YAESU",
              "baud": int,
              "civ": hex str or "",
              "parity": "N/E/O",
              "stopbits": 1|2,
              "bytesize": 7|8,
              "kenwood_fa_supported": bool
          }
          self.radio_models = list of model names
        No fallback defaults. If none loaded, radio_models is empty.
        """
        self.radios_data = {}
        self.radio_models = []
        path = app_path("radios.json")
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                data = json.load(f)
        except Exception as e:
            self.log(f"[CAT] radios.json load error: {e}")
            data = None

        def norm_protocol(p):
            p = (p or "").strip().lower()
            if p in ("ci-v", "civ", "icom"):
                return "CIV"
            if p in ("kenwood", "elecraft"):
                return "KENWOOD"
            if p in ("yaesubinary", "yaesu", "ft"):
                return "YAESU"
            return ""

        try:
            if isinstance(data, list):
                for d in data:
                    if not isinstance(d, dict):
                        continue
                    model = (d.get("model") or d.get("Radio Model") or d.get("name") or "").strip()
                    if not model:
                        continue
                    proto = norm_protocol(d.get("protocol") or d.get("Protocol"))
                    baud = d.get("baud", d.get("Default Baud Rate"))
                    try:
                        baud = int(baud) if baud is not None else None
                    except Exception:
                        baud = None
                    civ = (d.get("civ") or d.get("CI-V Address") or "").strip()
                    parity = (d.get("parity") or "N").strip().upper()
                    stopbits = d.get("stopbits", 1)
                    try:
                        stopbits = int(stopbits)
                    except Exception:
                        stopbits = 1
                    bytesize = d.get("bytesize", 8)
                    try:
                        bytesize = int(bytesize)
                    except Exception:
                        bytesize = 8
                    fa_ok = bool(d.get("kenwood_fa_supported", False))

                    if not proto or not baud:
                        # skip incomplete entries
                        self.log(f"[CAT] Skipping radio '{model}' due to missing protocol/baud")
                        continue

                    self.radios_data[model] = {
                        "protocol": proto,
                        "baud": baud,
                        "civ": civ,
                        "parity": parity,
                        "stopbits": stopbits,
                        "bytesize": bytesize,
                        "kenwood_fa_supported": fa_ok,
                    }

            self.radio_models = list(self.radios_data.keys())
            self.log(f"[CAT] Loaded {len(self.radio_models)} radios from radios.json")
        except Exception as e:
            self.log(f"[CAT] radios.json parse error: {e}")
            self.radios_data = {}
            self.radio_models = []

    # ----- CAT helpers -----

    def _to_bcd5_lsb(self, hz: int) -> bytes:
        s = f"{int(hz):010d}"
        pairs = [s[-2:], s[-4:-2], s[-6:-4], s[-8:-6], s[-10:-8]]
        out = bytearray()
        for p in pairs:
            hi = ord(p[0]) - 48
            lo = ord(p[1]) - 48
            out.append((hi << 4) | lo)
        return bytes(out)

    def _civ_set_freq(self, hz: int) -> bool:
        try:
            to_addr_hex = (self.cat_civ_addr or "").strip()
            to_addr = int(to_addr_hex, 16) if to_addr_hex else 0x00
        except Exception:
            to_addr = 0x00
        if to_addr == 0x00:
            self.log("[CAT:CIV] Missing/invalid CIV address; set a valid 'civ' in radios.json.")
            return False
        try:
            frame = bytearray()
            frame += b'\xFE\xFE'
            frame.append(to_addr)      # To radio
            frame.append(0xE0)         # From controller
            frame.append(0x05)         # Set frequency
            frame += self._to_bcd5_lsb(int(hz))
            frame.append(0xFD)
            self.log("[CAT:CIV] TX: " + " ".join(f"{b:02X}" for b in frame))
            self.cat_ser.write(frame)
            self.cat_ser.flush()
            return True
        except Exception as e:
            self.log(f"[CAT:CIV] Write failed: {e}")
            return False

    def _yaesu_set_freq(self, hz: int, vfo: str = "A") -> bool:
        cmd = "FA" if (vfo.upper() == "A") else "FB"
        try:
            payload = f"{int(hz):011d}"
            self.log(f"[CAT:{cmd}] TX: {cmd}{payload};")
            self.cat_ser.write(wire)
            self.cat_ser.flush()
            return True
        except Exception as e:
            self.log(f"[CAT:YAESU] Write failed: {e}")
            return False

    def _kenwood_set_freq(self, hz: int) -> bool:
        """Set VFO A frequency on Kenwood-style CAT (e.g. TX-500MP)."""
        try:
            payload = f"{int(hz):011d}"
            wire = f"FA{payload};".encode("ascii", "strict")
            self.log(f"[CAT:KENWOOD] TX: {wire!r}")
            self.cat_ser.write(wire)
            self.cat_ser.flush()
            return True
        except Exception as e:
            self.log(f"[CAT:KENWOOD] Write failed: {e}")
            return False

    # ----- TX-500MP helpers (Lab599) -----

    def _tx500mp_is_active(self) -> bool:
        """Return True if the currently selected CAT radio is TX-500MP."""
        try:
            model = (self.cat_radio_var.get() or "").strip().upper()
        except Exception:
            model = ""
        return model == "TX-500MP"

    def _tx500mp_send_raw(self, wire: bytes, label: str = ""):
        """Low-level helper: send raw CAT bytes only when TX-500MP is active."""
        if not self._tx500mp_is_active():
            return
        if not getattr(self, "cat_ser", None):
            return
        try:
            tag = "[CAT:TX-500MP]"
            if label:
                tag = f"{tag} {label}"
            self.log(f"{tag} TX: {wire!r}")
            self.cat_ser.write(wire)
            self.cat_ser.flush()
        except Exception as e:
            self.log(f"[CAT:TX-500MP] send failed ({label}): {e}")

    def _tx500mp_set_digital_mode(self):
        """Ensure TX-500MP is in DIG (Data-U) mode (MD6;)."""
        if not self._tx500mp_is_active():
            return
        self._tx500mp_send_raw(b"MD6;", "MD6; (DIG/Data-U)")

    def _tx500mp_tune(self, delay_ms: int = 0):
        """Fire the internal ATU via AC011; (AT ON + start tune)."""
        if not self._tx500mp_is_active():
            return

        def _do():
            self._tx500mp_send_raw(b"AC011;", "AC011; (Tune)")

        if delay_ms and hasattr(self, "master"):
            try:
                self.master.after(int(delay_ms), _do)
                return
            except Exception:
                pass
        _do()

    def _tx500mp_after_qsy(self, mhz: float = 0.0):
        """Called after a successful QSY so TX-500MP is in DIG/Data-U and tuned."""
        if not self._tx500mp_is_active():
            return
        try:
            self._tx500mp_set_digital_mode()
        except Exception:
            pass
        try:
            # Let rig settle on the new frequency before tuning
            self._tx500mp_tune(delay_ms=1500)
        except Exception:
            pass


    def _populate_cat_ports(self):
        ports = []
        try:
            if serial and hasattr(serial.tools, "list_ports"):
                ports = [p.device for p in serial.tools.list_ports.comports()]
        except Exception:
            ports = []
        try:
            self.cat_port_combo["values"] = ports
            # Try to keep selection if still present; otherwise clear
            current = (self.cat_port_var.get() or "").strip()
            if current and current in ports:
                self.cat_port_combo.set(current)
            elif ports:
                # don't auto-select; leave blank unless previously chosen
                pass
        except Exception:
            pass

    def _cat_connect_toggle(self):
        # Toggle connect/disconnect of CAT control port
        if self.cat_connected:
            try:
                if self.cat_ser:
                    try:
                        self.cat_ser.close()
                    except Exception:
                        pass
                self.cat_ser = None
            finally:
                self.cat_connected = False
                self.log("[CAT] Disconnected")
                try:
                    self.cat_status_var.set("CAT: Disconnected")
                except Exception:
                    pass
                try:
                    self.cat_connect_btn.configure(text="Connect")
                except Exception:
                    pass
                self._cat_update_controls_state()
                # Stop auto-qsy timer
                self._auto_qsy_scheduler_start(False)
            return

        port = (self.cat_port_var.get() or "").strip()
        if not port:
            self.log("[CAT] Choose a Control COM port first.")
            return
        try:
            # Generic 9600-8N1 placeholder unless radio-specific set later
            if serial is None:
                raise RuntimeError("pyserial not available")
            # Pull radio config defaults
            model = (self.cat_radio_var.get() or "Generic")
            cfg = getattr(self, "radios_data", {}).get(model)
            if not cfg:
                self.log(f"[CAT] Unknown radio model: {model}. Check radios.json.")
                return
            baud = int(cfg.get("baud"))
            parity = (cfg.get("parity") or "N").upper()
            stopbits = int(cfg.get("stopbits") or 1)
            bytesize = int(cfg.get("bytesize") or 8)
            self.cat_protocol = (cfg.get("protocol") or "").upper()
            self.cat_civ_addr = (cfg.get("civ") or "").strip()
            self.cat_ser = serial.Serial(port=port, baudrate=baud, bytesize=bytesize, parity=parity, stopbits=stopbits, timeout=0.5, rtscts=False, dsrdtr=False)
            self.cat_connected = True
            extra = f", CIV=0x{self.cat_civ_addr}" if self.cat_civ_addr else ""
            
            try:
                self.cat_ser.setRTS(False)
                self.cat_ser.setDTR(False)
                if hasattr(self.cat_ser, "break_condition"):
                    self.cat_ser.break_condition = False
            except Exception:
                pass
            self.log(f"[CAT] Connected on {port} · {model} @ {baud} bps (prot={self.cat_protocol}{extra})")
            try:
                self.cat_status_var.set(f"CAT: Connected · {model} @ {baud} · {port}")
            except Exception:
                pass
            try:
                self.cat_connect_btn.configure(text="Disconnect")
            except Exception:
                pass
            self._cat_update_controls_state()
            # Start auto QSY scheduler if enabled
            self._auto_qsy_scheduler_start(self.auto_qsy_enabled_var.get())
            # TX-500MP: on CAT connect, force DIG/Data-U and schedule a tune.
            try:
                if self._tx500mp_is_active():
                    self._tx500mp_set_digital_mode()
                    self._tx500mp_tune(delay_ms=1500)
            except Exception as e:
                self.log(f"[CAT:TX-500MP] post-connect setup failed (ignored): {e}")
        except Exception as e:
            self.cat_connected = False
            self.cat_ser = None
            self.log(f"[CAT] Connect failed: {e}")
            self._cat_update_controls_state()


    def _cat_update_controls_state(self):
        connected = bool(self.cat_connected)
        # Radio/port controls are enabled when not connected (to change), or always?
        try:
            self.cat_radio_combo.configure(state="readonly" if not connected else "disabled")
        except Exception:
            pass
        try:
            self.cat_port_combo.configure(state="readonly" if not connected else "disabled")
        except Exception:
            pass
        try:
            # Auto controls only enabled if connected
            state = "readonly" if connected else "disabled"
            chk_state = "normal" if connected else "disabled"
            self.auto_qsy_check.configure(state=chk_state)
            self.auto_qsy_day_combo.configure(
                state=state if (connected and self.auto_qsy_enabled_var.get()) else ("disabled" if connected else "disabled")
            )
            self.auto_qsy_night_combo.configure(
                state=state if (connected and self.auto_qsy_enabled_var.get()) else ("disabled" if connected else "disabled")
            )
            self.cat_save_btn.configure(state="normal" if connected else "disabled")
        except Exception:
            pass

        # Keep ALE-Lite scan button in sync with CAT connection
        try:
            self._update_ale_controls_state()
        except Exception:
            pass

    def _save_cat_settings(self):
        # Save settings, (re)schedule auto-QSY if connected
        self._save_settings()
        self._cat_update_controls_state()
        self.log("[CAT] Settings saved.")
        if self.cat_connected and self.auto_qsy_enabled_var.get():
            # Apply immediately to the current period
            self._auto_qsy_scheduler_start(True)
            self._auto_qsy_tick(initial=True)

    def _apply_cat_settings_to_ui(self):
        # Called if needed to refresh UI from settings later
        self._cat_update_controls_state()

    def _auto_qsy_scheduler_start(self, enable: bool):
        # Cancel existing
        try:
            if self._auto_qsy_job is not None:
                self.master.after_cancel(self._auto_qsy_job)
        except Exception:
            pass
        self._auto_qsy_job = None
        if not enable:
            return
        # Schedule every 60 seconds
        try:
            self._auto_qsy_job = self.master.after(60 * 1000, self._auto_qsy_tick)
        except Exception:
            pass

    def _auto_qsy_tick(self, initial=False):
        # Only act if connected and enabled
        if not (self.cat_connected and self.auto_qsy_enabled_var.get()):
            return
        import time as _time
        lt = _time.localtime()
        # Day = 05:00:00 to 21:00:00; Night = otherwise
        is_day = (lt.tm_hour > 4 and (lt.tm_hour < 21 or (lt.tm_hour == 21 and lt.tm_min == 0 and lt.tm_sec == 0)))
        # The user’s requirement: Day 05:00–21:00, Night 21:01–04:59
        if lt.tm_hour < 5 or (lt.tm_hour > 21 or (lt.tm_hour == 21 and lt.tm_min >= 1)):
            is_day = False
        target_label = (self.auto_qsy_day_label_var.get() if is_day else self.auto_qsy_night_label_var.get()).strip()
        if not target_label:
            # Nothing to apply
            self.log("[CAT] Auto-QSY: No target frequency set for current period.")
        else:
            if target_label != self._auto_qsy_current_label or initial:
                ok = self._cat_qsy_label(target_label)
                if ok:
                    self._auto_qsy_current_label = target_label
        # Reschedule
        try:
            self._auto_qsy_job = self.master.after(60 * 1000, self._auto_qsy_tick)
        except Exception:
            pass

    def _cat_qsy_label(self, label: str) -> bool:
        # Map label to MHz, then call _cat_qsy_mhz
        mhz = None
        if hasattr(self, "freq_map"):
            mhz = self.freq_map.get(label)
        if mhz is None:
            # Attempt to parse a numeric from the label
            try:
                import re as _re
                m = _re.search(r'([0-9]+(?:\.[0-9]+)?)', label or "")
                if m:
                    mhz = float(m.group(1))
            except Exception:
                mhz = None
        if mhz is None:
            self.log(f"[CAT] Could not parse frequency from '{label}'")
            return False
        return self._cat_qsy_mhz(mhz)

    
    def _cat_qsy_mhz(self, mhz: float) -> bool:
        """QSY the radio to the given MHz using the selected CAT protocol."""
        if not self.cat_connected or not self.cat_ser:
            self.log("[CAT] Not connected.")
            return False
        model = (self.cat_radio_var.get() or "Generic").upper()
        protocol = getattr(self, "cat_protocol", "GENERIC").upper()
        try:
            hz = int(float(mhz) * 1_000_000)
            if protocol == "CIV":
                ok = self._civ_set_freq(hz)
                if ok:
                    self.log(f"[CAT:CIV] Set {model} to {mhz:.6f} MHz ({hz} Hz)")
                    try:
                        self._tx500mp_after_qsy(mhz)
                    except Exception:
                        pass
                return ok
            elif protocol in ("CAT", "YAESU", "YAESUBINARY"):
                ok = self._yaesu_set_freq(hz, "A")
                if ok:
                    self.log(f"[CAT:YAESU] Set {model} to {mhz:.6f} MHz ({hz} Hz)")
                    try:
                        self._tx500mp_after_qsy(mhz)
                    except Exception:
                        pass
                return ok
            elif protocol == "KENWOOD":
                ok = self._kenwood_set_freq(hz)
                if ok:
                    self.log(f"[CAT:KENWOOD] Set {model} to {mhz:.6f} MHz ({hz} Hz)")
                    try:
                        self._tx500mp_after_qsy(mhz)
                    except Exception:
                        pass
                return ok
            else:
                # Fallback: no protocol-specific implementation, just log.
                self.log(f"[CAT] QSY to {mhz:.6f} MHz ({hz} Hz) on {model} (no protocol handler)")
                try:
                    self._tx500mp_after_qsy(mhz)
                except Exception:
                    pass
                return True
        except Exception as e:
            self.log(f"[CAT] QSY failed: {e}")
            return False

        model = (self.cat_radio_var.get() or "Generic").upper()
        protocol = getattr(self, "cat_protocol", "GENERIC").upper()
        try:
            hz = int(float(mhz) * 1_000_000)
            if protocol == "CIV":
                ok = self._civ_set_freq(hz)
                if ok:
                    self.log(f"[CAT:CIV] Set {model} to {mhz:.6f} MHz ({hz} Hz)")
                return ok
            elif protocol == "CAT":
                ok = self._yaesu_set_freq(hz, "A")
                if ok:
                    self.log(f"[CAT:YAESU] Set {model} to {mhz:.6f} MHz ({hz} Hz)")
                return ok
            else:
                self.log(f"[CAT] QSY to {mhz:.6f} MHz ({hz} Hz) on {model} (no protocol)")
                return True
        except Exception as e:
            self.log(f"[CAT] QSY failed: {e}")
            return False

    # ----- ALE-Lite scan helpers -----

    def _update_ale_controls_state(self):
        """Enable/disable the Scan button based on CAT + scan state."""
        if not hasattr(self, "ale_scan_btn"):
            return
        connected = bool(getattr(self, "cat_connected", False))
        if self.ale_scan_active:
            text = "Stop Scan"
            state = "normal"
        else:
            text = "Scan"
            state = "normal" if connected else "disabled"
        try:
            self.ale_scan_btn.configure(text=text, state=state)
        except Exception:
            pass

    
    def _ale_scan_toggle(self):
        """Start/stop the ALE-Lite scan."""
        # Debug: confirm button press
        self.log("[ALE] Scan button pressed.")
        # If already running, stop
        if getattr(self, "ale_scan_active", False):
            self.log("[ALE] Scan is active, stopping (manual).")
            self._ale_scan_stop(reason="manual")
            return

        # Must have CAT connected
        if not (getattr(self, "cat_connected", False) and getattr(self, "cat_ser", None)):
            self.log("[ALE] Cannot start scan: CAT not connected (either cat_connected or cat_ser is false).")
            try:
                messagebox.showwarning("ALE-Lite Scan", "Connect CAT first on the CAT page, then start scan.")
            except Exception:
                pass
            return

        # Build scan list from enabled slots
        freqs = []
        freq_map = getattr(self, "freq_map", {}) or {}
        try:
            rows = int(getattr(self, "ale_scan_rows", 0))
        except Exception:
            rows = 0
        self.log(f"[ALE] Building scan list from {rows} slots.")
        for i in range(rows):
            try:
                enabled = bool(self.ale_scan_enabled_vars[i].get())
            except Exception:
                enabled = False
            label = (self.ale_scan_label_vars[i].get() or "").strip() if hasattr(self, "ale_scan_label_vars") else ""
            self.log(f"[ALE] Slot {i+1}: enabled={enabled}, label='{label}'")
            if not enabled or not label:
                continue

            # Try map first
            mhz = None
            if label in freq_map:
                try:
                    mhz = float(freq_map[label])
                    self.log(f"[ALE] Slot {i+1}: using mapped MHz {mhz:.6f}")
                except Exception:
                    mhz = None

            # Fallback: parse number
            if mhz is None:
                try:
                    import re as _re
                    cleaned = _re.sub(r"[^0-9.]", "", label).replace(",", ".")
                    if cleaned:
                        mhz = float(cleaned)
                        self.log(f"[ALE] Slot {i+1}: parsed MHz {mhz:.6f} from label")
                except Exception as e:
                    self.log(f"[ALE] Slot {i+1}: parse failed for '{label}': {e}")
                    mhz = None

            if mhz is None:
                self.log(f"[ALE] Skipping slot '{label}' (no numeric frequency)")
                continue

            freqs.append((label, mhz))

        if not freqs:
            self.log("[ALE] No valid enabled scan frequencies after parsing.")
            try:
                messagebox.showinfo("ALE-Lite Scan", "Tick at least one valid scan frequency first.")
            except Exception:
                pass
            return

        self.ale_scan_list = freqs
        self.ale_scan_index = 0
        self.ale_scan_active = True

        # Auto-QSY must not fight the scanner
        self.log("[ALE] Disabling Auto-QSY scheduler while scan is active.")
        try:
            self._auto_qsy_scheduler_start(False)
        except Exception as e:
            self.log(f"[ALE] Auto-QSY scheduler stop error (ignored): {e}")

        self.log(f"[ALE] Scan started on {len(freqs)} channels, dwell {self.ale_scan_dwell_sec:.0f}s.")
        self._update_ale_controls_state()
        self._ale_scan_step()

    def _ale_scan_step(self):
        """Hop to the next enabled frequency; rescheduled every dwell seconds."""
        if not self.ale_scan_active:
            return
        if not (getattr(self, "cat_connected", False) and getattr(self, "cat_ser", None)):
            self.log("[ALE] CAT disconnected, stopping scan.")
            self._ale_scan_stop(reason="CAT lost")
            return
        if not self.ale_scan_list:
            self.log("[ALE] Empty scan list, stopping.")
            self._ale_scan_stop(reason="no channels")
            return

        # Round-robin
        if self.ale_scan_index >= len(self.ale_scan_list):
            self.ale_scan_index = 0

        label, mhz = self.ale_scan_list[self.ale_scan_index]
        self.ale_scan_index += 1

        self.log(f"[ALE] QSY to {label} ({mhz:.6f} MHz)")
        self._cat_qsy_mhz(mhz)

        # Schedule next hop
        try:
            ms = max(1, int(self.ale_scan_dwell_sec * 1000))
            self.ale_scan_job = self.master.after(ms, self._ale_scan_step)
        except Exception:
            self.ale_scan_job = None

    def _ale_scan_stop(self, reason: str = ""):
        """Full stop of scan & tidy up."""
        if self.ale_scan_job:
            try:
                self.master.after_cancel(self.ale_scan_job)
            except Exception:
                pass
            self.ale_scan_job = None

        if self.ale_scan_active:
            self.ale_scan_active = False
            msg = "[ALE] Scan stopped."
            if reason:
                msg = f"[ALE] Scan stopped ({reason})."
            self.log(msg)

        # If auto-QSY is enabled and CAT still up, resume scheduler
        if getattr(self, "cat_connected", False) and self.auto_qsy_enabled_var.get():
            self._auto_qsy_scheduler_start(True)

        self._update_ale_controls_state()

    def _ale_scan_stop_on_beacon(self, txt: str = ""):
        """Stop scan when a beacon is heard on any scanned frequency."""
        if not self.ale_scan_active:
            return
        if txt:
            self.log(f"[ALE] Beacon detected while scanning: {txt}")
        self._ale_scan_stop(reason="beacon heard")

    def _load_freqs(self):
        """
        Load frequency options from freqs.json and build:
          - self.freq_display_values: list[str] for the combobox
          - self.freq_map: {label -> float MHz} for future CAT/QSY
        Accepts flexible JSON:
          - ["(30m) 10.1483 MHz", "14.109", 7.090]
          - [{"band":"30m","mhz":10.1483,"label":"(30m) 10.1483 MHz"}, ...]
          - {"30m":[10.1483, 10.147], "20m":[14.109], "40m":[7.090]}
        """
        self.freq_display_values = []
        self.freq_map = {}

        path = app_path("freqs.json")
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                data = json.load(f)
        except Exception:
            data = None

        def _add(label, mhz):
            if label is None and mhz is None:
                return
            if not label:
                if mhz is not None:
                    label = f"{float(mhz):.6g} MHz"
                else:
                    return
            self.freq_display_values.append(label)
            if mhz is not None:
                try:
                    self.freq_map[label] = float(mhz)
                except Exception:
                    pass

        def _mk_label(band, mhz, label=None):
            if label:
                return label
            if band and mhz is not None:
                return f"({band}) {float(mhz):.6g} MHz"
            if mhz is not None:
                return f"{float(mhz):.6g} MHz"
            return None

        try:
            if isinstance(data, list):
                if all(isinstance(x, dict) for x in data):
                    for d in data:
                        band = d.get("band")
                        mhz = (d.get("mhz") or d.get("freq") or d.get("frequency"))
                        if mhz is None and "khz" in d:
                            try:
                                mhz = float(d["khz"]) / 1000.0
                            except Exception:
                                mhz = None
                        if isinstance(mhz, str):
                            try:
                                mhz = float(mhz)
                            except Exception:
                                mhz = None
                        label = _mk_label(band, mhz, d.get("label") or d.get("name") or d.get("text"))
                        _add(label, mhz)
                else:
                    for x in data:
                        if isinstance(x, (int, float)):
                            _add(f"{float(x):.6g} MHz", float(x))
                        elif isinstance(x, str):
                            import re as _re
                            m = _re.search(r"([0-9]+(?:\.[0-9]+)?)", x)
                            mhz = float(m.group(1)) if m else None
                            _add(x.strip(), mhz)
            elif isinstance(data, dict):
                for band, vals in data.items():
                    if isinstance(vals, list):
                        for v in vals:
                            mhz = None
                            if isinstance(v, (int, float, str)):
                                try:
                                    mhz = float(v)
                                except Exception:
                                    try:
                                        mhz = float(str(v))
                                    except Exception:
                                        mhz = None
                                label = _mk_label(band, mhz)
                                _add(label, mhz)
                            elif isinstance(v, dict):
                                mhz = (v.get("mhz") or v.get("freq") or v.get("frequency"))
                                if mhz is None and "khz" in v:
                                    try:
                                        mhz = float(v["khz"]) / 1000.0
                                    except Exception:
                                        mhz = None
                                if isinstance(mhz, str):
                                    try:
                                        mhz = float(mhz)
                                    except Exception:
                                        mhz = None
                                label = _mk_label(band, mhz, v.get("label") or v.get("name") or v.get("text"))
                                _add(label, mhz)

            # Deduplicate while preserving order
            seen = set()
            deduped = []
            for s in self.freq_display_values:
                if s not in seen:
                    deduped.append(s)
                    seen.add(s)
            self.freq_display_values = deduped
        except Exception:
            # On any parse error, leave empty
            self.freq_display_values = []
            self.freq_map = {}

    def __init__(self, master: tk.Tk):
        self.master = master
        self.master.title("Robust Chat v2.29")
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

        # --- CAT control state ---
        self.cat_ser = None
        self.cat_connected = False
        self.cat_port_var = tk.StringVar()
        self.cat_radio_var = tk.StringVar(value="IC-705")  # default; overridden by settings later
        self.auto_qsy_enabled_var = tk.BooleanVar(value=False)
        self.auto_qsy_day_label_var = tk.StringVar(value="")
        self.auto_qsy_night_label_var = tk.StringVar(value="")
        self._auto_qsy_job = None
        self._auto_qsy_current_label = None  # remembers last applied label

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
        self.decrypt_buttons = []
        self.decrypt_button_line = {}
        self.decrypt_handlers = {}

        # ACK / reliability state
        self.pending_acks = {}      # ack_id -> entry
        self.seen_ack_ids = {}      # (from_base, ack_id) -> {"ts": float, "ack_sent": bool}
        self.ack_lock = threading.Lock()
        self.ack_id_counter = 0

        # Remote Wi-Fi control server state
        self.remote_enabled_var = tk.BooleanVar(value=False)
        self.remote_status_var = tk.StringVar(value="Remote control disabled")
        self._remote_httpd = None
        self._remote_thread = None
        self._remote_listen = None  # (host, port) actually bound
        self._remote_sessions = {}  # token -> {'ts': float}


        
        # Auto-relay (silent third-party helper) state
        # Each ACKable third-party message may be relayed at most once.
        self.auto_relay_enabled = True
        self.auto_relay_delay = 5.0  # seconds before considering relay
        self.auto_relay_done = set()         # ack_id values we've already relayed once
        self.auto_relay_candidates = {}      # ack_id -> {"src","dst","wire","body","ts"}
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

        # Groups filter (client-side view of All)
        self.filter_enabled_var = tk.BooleanVar(value=bool(self.settings.get("filter_enabled", False)))
        self.filter_calls_vars = [tk.StringVar() for _ in range(12)]
        # Auto-connect last TNC port on startup if enabled
        self.auto_tnc_connect_var = tk.BooleanVar(value=bool(self.settings.get("auto_tnc_connect", False)))
        calls = self.settings.get("filter_calls", [])
        if isinstance(calls, list):
            for i, v in enumerate(calls[:12]):
                if v:
                    self.filter_calls_vars[i].set(str(v).strip().upper()[:10])

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
        self._load_freqs()

        # --- ALE-Lite scan state (5 slots, pre-populated from freqs.json) ---
        self.ale_scan_rows = 5
        self.ale_scan_label_vars = [tk.StringVar() for _ in range(self.ale_scan_rows)]
        self.ale_scan_enabled_vars = [tk.BooleanVar(value=False) for _ in range(self.ale_scan_rows)]
        try:
            # Use first 5 display labels from freq.json (if available)
            for i in range(self.ale_scan_rows):
                label = ""
                if hasattr(self, "freq_display_values") and i < len(self.freq_display_values):
                    label = self.freq_display_values[i]
                self.ale_scan_label_vars[i].set(label)
        except Exception:
            pass

        # Scan control state
        self.ale_scan_active = False
        self.ale_scan_job = None
        self.ale_scan_index = 0
        # Dwell time per channel (seconds)
        self.ale_scan_dwell_sec = 10.0
        # List of (label, MHz) tuples when scan is running
        self.ale_scan_list = []

        self._load_radios()


        self._build_ui()
        self._apply_settings_to_ui()
        self._apply_ai_mode()
        self._load_link_graph(prune_only=True)
        self._prune_beacons(save=True)

        self._refresh_chat_listbox()
        self._refresh_beacon_listbox()
        self._render_active_chat()
        self.show_page("Main")
        try:
            self.tx_entry.focus_set()
        except Exception:
            pass

        # If enabled in settings, try to auto-connect the last-used TNC port shortly after startup
        try:
            self.master.after(500, self._maybe_auto_connect_tnc)
        except Exception:
            pass

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

                
                "cat_radio_model": (getattr(self, "cat_radio_var", tk.StringVar()).get() or "IC-705"),
                "cat_port": (getattr(self, "cat_port_var", tk.StringVar()).get() or ""),
                "auto_qsy_enabled": bool(getattr(self, "auto_qsy_enabled_var", tk.BooleanVar(value=False)).get()),
                "auto_qsy_day_label": (getattr(self, "auto_qsy_day_label_var", tk.StringVar()).get() or ""),
                "auto_qsy_night_label": (getattr(self, "auto_qsy_night_label_var", tk.StringVar()).get() or ""),
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
                "filter_enabled": bool(getattr(self, "filter_enabled_var", tk.BooleanVar(value=False)).get()),
                # Auto TNC connect on startup
                "auto_tnc_connect": bool(getattr(self, "auto_tnc_connect_var", tk.BooleanVar(value=False)).get()),
                "filter_calls": [
                    (v.get().strip().upper() if isinstance(v.get(), str) else str(v.get()))
                    for v in getattr(self, "filter_calls_vars", [])
                ],


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

        # Auto TNC connect on startup
        try:
            if hasattr(self, "auto_tnc_connect_var"):
                self.auto_tnc_connect_var.set(bool(s.get("auto_tnc_connect", False)))
        except Exception:
            pass
        # --- Apply CAT / Auto QSY settings ---
        try:
            if hasattr(self, "cat_radio_var"):
                self.cat_radio_var.set((s.get("cat_radio_model") or self.cat_radio_var.get() or "IC-705"))
            if hasattr(self, "cat_port_var"):
                self.cat_port_var.set(s.get("cat_port", "") or self.cat_port_var.get() or "")
            if hasattr(self, "auto_qsy_enabled_var"):
                self.auto_qsy_enabled_var.set(bool(s.get("auto_qsy_enabled", False)))
            if hasattr(self, "auto_qsy_day_label_var"):
                self.auto_qsy_day_label_var.set(s.get("auto_qsy_day_label", "") or "")
            if hasattr(self, "auto_qsy_night_label_var"):
                self.auto_qsy_night_label_var.set(s.get("auto_qsy_night_label", "") or "")
        except Exception:
            pass


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
    
    # ===== Remote Wi-Fi tablet/phone control ================================

    def _remote_control_toggle(self):
        """Callback when the CAT-page remote-control checkbox is toggled."""
        enabled = bool(self.remote_enabled_var.get())
        if enabled:
            self._start_remote_server()
        else:
            self._stop_remote_server()
        self._update_remote_status()

    def _update_remote_status(self):
        """Update the CAT-page hint text for remote control."""
        try:
            if self._remote_httpd and self._remote_listen:
                host, port = self._remote_listen
                # For display, prefer a non-loopback host if we can guess one
                disp_host = host
                if disp_host in ("0.0.0.0", "127.0.0.1", "", None):
                    disp_host = self._remote_guess_listen_host() or "127.0.0.1"
                url = f"http://{disp_host}:{port}"
                self.remote_status_var.set(f"Connect tablet/phone browser to: {url}\nLogin password = MYCALL (e.g. {self.call_var.get() or 'G4ABC'})")
            else:
                self.remote_status_var.set("Remote control disabled")
        except Exception:
            # Never allow UI update errors to crash the app
            try:
                self.remote_status_var.set("Remote control disabled")
            except Exception:
                pass

    def _remote_guess_listen_host(self):
        """Best-effort guess of a LAN IP for display only."""
        try:
            # Try to derive the primary non-loopback IPv4 address
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
                # This does not need to succeed; it's just to pick an interface
                s.connect(("8.8.8.8", 80))
                host = s.getsockname()[0]
            finally:
                s.close()
            if host and not host.startswith("127."):
                return host
        except Exception:
            pass
        try:
            host = socket.gethostbyname(socket.gethostname())
            if host and not host.startswith("127."):
                return host
        except Exception:
            pass
        return "127.0.0.1"

    def _start_remote_server(self):
        """Start the background HTTP server for remote control, if not already running."""
        if self._remote_httpd:
            # Already running; just refresh status
            self._update_remote_status()
            return
        # Ensure settings exist
        try:
            mycall = (self.call_var.get() or "").strip().upper()
        except Exception:
            mycall = ""
        if not mycall:
            self.log("[Remote] MYCALL not set; remote control will still start but login will fail until MYCALL is configured.")
        try:
            # Bind to all interfaces, default port (fall back to next few ports if needed)
            port = REMOTE_DEFAULT_PORT
            httpd = None
            for attempt in range(0, 5):
                try:
                    server_address = ("0.0.0.0", port + attempt)
                    httpd = RemoteHTTPServer(server_address, RemoteRequestHandler, self)
                    bound = httpd.server_address
                    self._remote_listen = (bound[0], bound[1])
                    if attempt > 0:
                        self.log(f"[Remote] Requested port {REMOTE_DEFAULT_PORT} in use, bound to {bound[1]} instead.")
                    break
                except OSError as e:
                    httpd = None
                    if attempt == 4:
                        raise
            if not httpd:
                self.log("[Remote] Failed to create HTTP server.")
                return
            self._remote_httpd = httpd
            self._remote_sessions = {}
            # Background thread to serve requests
            t = threading.Thread(target=self._remote_serve_forever, name="RemoteHTTP", daemon=True)
            self._remote_thread = t
            t.start()
            self.log(f"[Remote] HTTP server started on {self._remote_listen[0]}:{self._remote_listen[1]}")
        except Exception as e:
            self._remote_httpd = None
            self._remote_thread = None
            self._remote_listen = None
            self.log(f"[Remote] Failed to start HTTP server: {e}")
        self._update_remote_status()

    def _remote_serve_forever(self):
        """Run the HTTP server loop."""
        try:
            while self._remote_httpd:
                self._remote_httpd.handle_request()
        except Exception as e:
            try:
                self.log(f"[Remote] HTTP server stopped with error: {e}")
            except Exception:
                pass
        finally:
            # Ensure flag is cleared
            self._remote_httpd = None
            self._remote_thread = None
            self._remote_listen = None
            try:
                self._update_remote_status()
            except Exception:
                pass

    def _stop_remote_server(self):
        """Stop the background HTTP server, if running."""
        httpd = self._remote_httpd
        self._remote_httpd = None
        self._remote_listen = None
        # A dummy request may be needed to unblock handle_request()
        if httpd:
            try:
                # Try to close the listening socket cleanly
                httpd.server_close()
            except Exception:
                pass
        self._remote_sessions = {}
        self._remote_thread = None
        self._update_remote_status()
        try:
            self.log("[Remote] HTTP server stopped.")
        except Exception:
            pass

    def _remote_check_password(self, pwd: str) -> bool:
        """Return True if the provided password matches MYCALL (case-insensitive)."""
        try:
            mycall = (self.call_var.get() or "").strip().upper()
        except Exception:
            mycall = ""
        if not mycall:
            return False
        return (pwd or "").strip().upper() == mycall

    def _remote_new_session_token(self) -> str:
        token = secrets.token_hex(16)
        self._remote_sessions[token] = {"ts": time.time()}
        return token

    def _remote_validate_session(self, token: str) -> bool:
        info = self._remote_sessions.get(token)
        if not info:
            return False
        # Simple idle timeout (12 hours)
        if time.time() - float(info.get("ts", 0)) > 12 * 3600:
            self._remote_sessions.pop(token, None)
            return False
        info["ts"] = time.time()
        return True

    def _remote_collect_state(self):
        """
        Collect a lightweight snapshot of chat + locator state for the web UI.
        Returns a dict that is safe to JSON-encode.
        """
        # Conversations: send last 100 messages from "All"
        all_msgs = []
        try:
            msgs = list(self.conversations.get("All", []))
            if len(msgs) > 100:
                msgs = msgs[-100:]
            for m in msgs:
                all_msgs.append({
                    "ts": m.get("ts"),
                    "src": m.get("src"),
                    "dst": m.get("dst"),
                    "text": m.get("text"),
                    "flags": m.get("flags", []),
                    "direction": m.get("direction"),
                    "ack_status": m.get("ack_status"),
                    "ack_id": m.get("ack_id"),
                })
        except Exception:
            all_msgs = []

        # Chat list keys
        try:
            chat_keys = sorted(k for k in self.conversations.keys())
        except Exception:
            chat_keys = ["All"]

        # Locator: own position + known stations
        locator = {
            "mycall": "",
            "mygrid": "",
            "mylat": None,
            "mylon": None,
            "stations": [],
        }
        try:
            locator["mycall"] = (self.call_var.get() or "").strip().upper()
            locator["mygrid"] = (self.mygrid_var.get() or "").strip().upper()
        except Exception:
            pass
        # Own derived lat/lon if available
        try:
            pos = self._get_own_position()
            if pos:
                locator["mylat"], locator["mylon"] = float(pos[0]), float(pos[1])
        except Exception:
            pass
        # Heard/positions list
        try:
            for call, info in (self.positions or {}).items():
                locator["stations"].append({
                    "call": call,
                    "lat": info.get("lat"),
                    "lon": info.get("lon"),
                    "grid": info.get("grid"),
                    "epoch": info.get("epoch"),
                })
        except Exception:
            pass

        return {
            "ok": True,
            "mycall": locator["mycall"],
            "chat_keys": chat_keys,
            "messages_all": all_msgs,
            "locator": locator,
        }

    def _remote_send_message(self, dst: str, text: str):
        """
        Schedule a normal send_message() originating from the web UI.
        We marshal this back to the Tk main thread to keep things safe.
        """
        def _do():
            try:
                if dst:
                    self.to_var.set(dst)
                else:
                    self.to_var.set("CQ")
            except Exception:
                pass
            try:
                self.tx_var.set(text or "")
            except Exception:
                pass
            try:
                self.send_message()
            except Exception as e:
                try:
                    self.log(f"[Remote] send_message() failed: {e}")
                except Exception:
                    pass

        try:
            self.master.after(0, _do)
        except Exception:
            # Fallback (not ideal, but avoids total failure)
            _do()
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

    # ----- Auto-relay helpers (silent third-party assist) -----

    def _auto_relay_can_reach(self, call_base: str) -> bool:
        """Return True if destination base call is directly reachable for relay.
        We treat only PARENT entries (**CALL) in self.beacons as directly heard.
        Child calls (/CALL) are *not* assumed directly reachable.
        """
        if not call_base:
            return False
        beacons = getattr(self, "beacons", {})
        return call_base in beacons

    def _auto_relay_maybe_schedule(self, src: str, dst: str, wire_text: str, body_text: str, ack_id: str):
        """Consider scheduling a one-shot auto-relay for a third-party ACKable message.

        Conditions (enforced here):
          - feature enabled
          - valid ack_id
          - not to/from MYCALL
          - not a beacon / not CQ
          - destination is a reachable PARENT (**CALL) in beacon map
          - this ack_id not already relayed or pending
        """
        if not getattr(self, "auto_relay_enabled", False):
            return
        if not ack_id:
            return

        # Basic filtering
        srcb = self._callsign_base(src)
        dstb = self._callsign_base(dst)
        my = ""
        try:
            if hasattr(self, "call_var"):
                my = (self.call_var.get() or "").strip().upper()
            if not my:
                my = (self.settings.get("mycall") or "").strip().upper()
        except Exception:
            pass
        myb = self._callsign_base(my) if my else ""

        if not srcb or not dstb:
            return
        if srcb == myb or dstb == myb:
            # Not a third-party message
            return

        stripped = (body_text or "").strip().upper()
        if not stripped:
            return
        if stripped.startswith("**"):
            # Beacon-style, ignore
            return
        if stripped.startswith("CQ "):
            # CQ / broadcast, ignore
            return

        # Destination must be directly reachable as a PARENT beacon
        if not self._auto_relay_can_reach(dstb):
            return

        # One shot per ACK ID
        if ack_id in getattr(self, "auto_relay_done", set()):
            return
        if ack_id in getattr(self, "auto_relay_candidates", {}):
            return

        if not self.kiss_mode or not self.ser:
            # Only consider when in KISS with an active TNC
            return

        now = time.time()
        cand = {
            "src": src,
            "dst": dst,
            "wire": wire_text,
            "body": body_text,
            "ts": now,
        }
        self.auto_relay_candidates[ack_id] = cand

        # Schedule evaluation after the configured delay
        delay_ms = int(getattr(self, "auto_relay_delay", 5.0) * 1000)
        try:
            self.master.after(delay_ms, lambda aid=ack_id: self._auto_relay_attempt(aid))
        except Exception:
            # If scheduling fails, drop candidate
            self.auto_relay_candidates.pop(ack_id, None)

    def _auto_relay_note_ack(self, ack_id: str):
        """Cancel any pending auto-relay when a matching ACK is observed."""
        try:
            if not hasattr(self, "auto_relay_candidates"):
                return
            if ack_id in self.auto_relay_candidates:
                self.auto_relay_candidates.pop(ack_id, None)
        except Exception:
            pass

    def _auto_relay_attempt(self, ack_id: str):
        """After the wait window, decide whether to transmit a single relay."""
        try:
            cand = getattr(self, "auto_relay_candidates", {}).pop(ack_id, None)
        except Exception:
            cand = None
        if not cand:
            return  # ACK arrived or candidate cleared

        # Global feature guard
        if not getattr(self, "auto_relay_enabled", False):
            return

        # One-shot enforcement
        if ack_id in getattr(self, "auto_relay_done", set()):
            return

        # Must still be in KISS with an open serial
        if not getattr(self, "kiss_mode", False) or not getattr(self, "ser", None):
            return

        src = cand.get("src") or ""
        dst = cand.get("dst") or ""
        wire = cand.get("wire") or ""
        srcb = self._callsign_base(src)
        dstb = self._callsign_base(dst)
        if not srcb or not dstb:
            return

        # Derive our own base for safety
        my = ""
        try:
            if hasattr(self, "call_var"):
                my = (self.call_var.get() or "").strip().upper()
            if not my:
                my = (self.settings.get("mycall") or "").strip().upper()
        except Exception:
            pass
        myb = self._callsign_base(my) if my else ""

        # Never relay if we are one of the endpoints
        if srcb == myb or dstb == myb:
            return

        # Destination must still look reachable as PARENT
        if not self._auto_relay_can_reach(dstb):
            return

        # Build and send a bit-identical UI frame (no new ACK, no retries)
        try:
            frame = self._build_kiss_ui_frame(src_call=src, dst_call=dst, text=wire)
            self._write_bytes(frame)
            # Mark as done to avoid any future relays for this ACK ID
            self.auto_relay_done.add(ack_id)
            self.log(f"[AutoRelay] Relayed {srcb}->{dstb} [ACK:{ack_id}] once")
        except Exception as e:
            self.log(f"[AutoRelay] Relay failed for {src}->{dst} [ACK:{ack_id}]: {e}")

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
        self.btn_tab_groups = make_tab("Groups")
        self.btn_tab_gps = make_tab("GPS")
        self.btn_tab_beacon = make_tab("Beacon")
        self.btn_tab_locator = make_tab("Locator")
        self.btn_tab_cat = make_tab("CAT")
        self.btn_tab_misc = make_tab("Misc")

        self.btn_tab_main.grid(row=0, column=0, padx=2)
        self.btn_tab_groups.grid(row=0, column=1, padx=2)
        self.btn_tab_gps.grid(row=0, column=2, padx=2)
        self.btn_tab_beacon.grid(row=0, column=3, padx=2)
        self.btn_tab_locator.grid(row=0, column=4, padx=2)
        self.btn_tab_cat.grid(row=0, column=5, padx=2)
        self.btn_tab_misc.grid(row=0, column=6, padx=2)

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

        # Auto TNC connect checkbox
        self.auto_tnc_connect_chk = ttk.Checkbutton(
            conn,
            text="Auto TNC Connect",
            variable=self.auto_tnc_connect_var,
            command=self._on_auto_tnc_connect_toggled,
            style="Header.TCheckbutton",
        )
        self.auto_tnc_connect_chk.grid(row=0, column=13, padx=(0, 8), sticky="w")

        # Frequency quick-select dropdown (reference frequencies)
        # Frequency quick-select dropdown (from freqs.json)
        self.freq_var = tk.StringVar()
        self.freq_combo = ttk.Combobox(
            conn,
            textvariable=self.freq_var,
            state="readonly" if getattr(self, "freq_display_values", []) else "disabled",
            values=self.freq_display_values or [],
            width=18,
        )
        self.freq_combo.set("Freq")
        self.freq_combo.grid(row=0, column=13, padx=(0, 8))
        
        
        # Forensic: report values and bind events
        try:
            vals = list(self.freq_combo["values"]) if "values" in self.freq_combo.keys() else []
            self.log(f"[FreqUI] Combobox ready with {len(vals)} options: {vals}")
        except Exception as _e:
            self.log(f"[FreqUI] Combobox init report failed: {_e}")
        # Clear old bindings by reconfiguring a fresh handler
        try:
            self.freq_combo.unbind("<<ComboboxSelected>>")
        except Exception:
            pass
        try:
            self.freq_combo.bind("<<ComboboxSelected>>", lambda e=None: self._on_freq_selected_event(e))
            self.freq_combo.bind("<Return>",             lambda e=None: self._on_freq_selected_event(e))
            self.freq_combo.bind("<KP_Enter>",           lambda e=None: self._on_freq_selected_event(e))
        except Exception as _e:
            self.log(f"[FreqUI] Bindings failed: {_e}")
        # Replace StringVar trace to observe programmatic changes
        try:
            def _freq_var_trace(*_a):
                val = (self.freq_var.get() or "").strip()
                self.log(f"[FreqUI] trace fired: '{val}'")
                if not val or val.lower() == "freq":
                    return
                # only run selection if dropdown actually owns focus to avoid startup noise
                try:
                    if str(self.master.focus_get()) == str(self.freq_combo):
                        self._on_freq_selected_event(None)
                except Exception:
                    self._on_freq_selected_event(None)
            if hasattr(self.freq_var, "_trace_id"):
                try:
                    self.freq_var.trace_remove("write", self.freq_var._trace_id)
                except Exception:
                    pass
            self.freq_var._trace_id = self.freq_var.trace_add("write", _freq_var_trace)
        except Exception as _e:
            self.log(f"[FreqUI] trace attach failed: {_e}")
        # Global troubleshooting hotkey (no UI clutter): Ctrl+Alt+Q
        try:
            self.master.bind_all("<Control-Alt-q>", lambda e=None: self._on_freq_selected_event(None))
        except Exception:
            pass
# Fire on selection or Enter, and add manual QSY button
        try:
            self.freq_combo.bind("<<ComboboxSelected>>", lambda e=None: self._on_freq_selected())
            self.freq_combo.bind("<Return>",             lambda e=None: self._on_freq_selected())
            self.freq_combo.bind("<KP_Enter>",           lambda e=None: self._on_freq_selected())
        except Exception:
            pass
        # StringVar trace (catches programmatic sets & some themes that don't emit selection events)
        try:
            def _freq_var_trace(*_a):
                # Avoid triggering on placeholder
                val = (self.freq_var.get() or "").strip()
                if not val or val.lower() == "freq":
                    return
                self._on_freq_selected()
            # remove old traces if multiple inits: safe-guard
            if hasattr(self.freq_var, "_trace_id"):
                try:
                    self.freq_var.trace_remove("write", self.freq_var._trace_id)
                except Exception:
                    pass
            self.freq_var._trace_id = self.freq_var.trace_add("write", _freq_var_trace)
        except Exception:
            pass
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
        self.page_groups = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_gps = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_beacon = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_locator = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_cat = ttk.Frame(self.page_container, style="Chat.TFrame")
        self.page_misc = ttk.Frame(self.page_container, style="Chat.TFrame")

        for p in (self.page_main, self.page_groups, self.page_gps, self.page_beacon, self.page_locator, self.page_cat, self.page_misc):
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
            cursor="arrow",
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

        self.lock_label = tk.Label(
            input_bar,
            text="🔒",
            bg="#0b141a",
            fg="#FFFFFF",
            font=("Segoe UI Emoji", 11),
        )
        self.lock_label.grid(row=0, column=3, padx=(0, 4), pady=6)
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
        self.send_btn.grid(row=0, column=4, padx=(0, 8), pady=6)

        # Groups page content
        self._build_groups_page()

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
    def _on_freq_selected(self, *_):
        label = (self.freq_var.get() or "").strip()
        if not label or label.lower() == "freq":
            self.log("[Freq] Ignored placeholder/empty selection")
            return
        self.log(f"[Freq] handler fired · raw='{label}'")
        # Map lookup
        mhz = None
        freq_map = getattr(self, "freq_map", {})
        if label in freq_map:
            try:
                mhz = float(freq_map[label])
            except Exception:
                mhz = None
        # Robust parse
        if mhz is None:
            cleaned = re.sub(r"[^0-9.,]", "", label).replace(",", ".")
            if cleaned.count(".") > 1:
                first = cleaned.find(".")
                cleaned = cleaned[:first+1] + cleaned[first+1:].replace(".", "")
            try:
                mhz = float(cleaned)
            except Exception:
                m = re.search(r'([0-9]+(?:\.[0-9]+)?)', label)
                if m:
                    try:
                        mhz = float(m.group(1))
                    except Exception:
                        mhz = None
        if mhz is None:
            self.log(f"[Freq] Could not parse a number from '{label}'")
            return
        self.log(f"[Freq] Selected {label} -> {mhz:.6f} MHz")
        # QSY if CAT connected
        if not (getattr(self, "cat_connected", False) and getattr(self, "cat_ser", None)):
            self.log("[CAT] Not connected (CAT). Open CAT tab, choose Control port, then Connect.")
            return
        proto = getattr(self, "cat_protocol", "")
        civ = getattr(self, "cat_civ_addr", "")
        port = getattr(self.cat_ser, "port", "")
        self.log(f"[CAT] QSY request: {mhz:.6f} MHz · protocol={proto} · CIV=0x{civ or '??'} · port={port}")
        self._cat_qsy_mhz(mhz)



    def _build_cat_page(self):

        f = self.page_cat
        f.rowconfigure(0, weight=1)
        f.columnconfigure(0, weight=1)

        # --- Frequency Control CAT section ---
        section = ttk.Frame(f, style="Chat.TFrame")
        section.grid(row=0, column=0, sticky="nw", padx=16, pady=(16, 8))
        section.columnconfigure(5, weight=1)

        title = ttk.Label(section, text="Frequency Control CAT", style="Header.TLabel")
        title.grid(row=0, column=0, sticky="w", pady=(0, 6), columnspan=6)

        # Radio dropdown
        ttk.Label(section, text="Radio", style="Header.TLabel").grid(row=1, column=0, sticky="w", padx=(0,6))
        self.cat_radio_combo = ttk.Combobox(section, textvariable=self.cat_radio_var, state="readonly", width=10,
                                            values=self.radio_models or [])
        self.cat_radio_combo.grid(row=1, column=1, sticky="w", padx=(0,12))
        if not (self.radio_models):
            # Disable whole section gracefully
            try:
                self.cat_radio_combo.configure(state="disabled")
                self.cat_port_combo.configure(state="disabled")
                self.cat_connect_btn.configure(state="disabled")
                self.auto_qsy_check.configure(state="disabled")
            except Exception:
                pass
            try:
                note = ttk.Label(section, text="No radios loaded — check radios.json", style="Header.TLabel")
                note.grid(row=6, column=0, sticky="w", pady=(8,0), columnspan=6)
            except Exception:
                pass

        # Control COM port
        ttk.Label(section, text="Control", style="Header.TLabel").grid(row=1, column=2, sticky="w", padx=(0,6))
        self.cat_port_combo = ttk.Combobox(section, textvariable=self.cat_port_var, state="readonly", width=9)
        self.cat_port_combo.grid(row=1, column=3, sticky="w", padx=(0,12))

        # Connect / Disconnect
        self.cat_connect_btn = ttk.Button(section, text="Connect", command=self._cat_connect_toggle, style="Conn.TButton")
        self.cat_connect_btn.grid(row=1, column=4, sticky="w", padx=(0,6))

        
        # Status label
        try:
            self.cat_status_var = tk.StringVar(value="CAT: Disconnected")
            self.cat_status_lbl = ttk.Label(section, textvariable=self.cat_status_var, style="Header.TLabel")
            self.cat_status_lbl.grid(row=0, column=5, sticky="e")
        except Exception:
            pass
# Auto Day/Night QSY row
        self.auto_qsy_check = ttk.Checkbutton(section, text="Auto Day/Night QSY Enable", variable=self.auto_qsy_enabled_var, command=self._cat_update_controls_state, style="Switch.TCheckbutton")
        self.auto_qsy_check.grid(row=2, column=0, sticky="w", pady=(10, 6), columnspan=6)

        # Day / Night selectors
        dayrow = ttk.Frame(section, style="Chat.TFrame"); dayrow.grid(row=3, column=0, sticky="w", columnspan=6)
        ttk.Label(dayrow, text="Day", style="Header.TLabel").pack(side="left", padx=(0,6))
        self.auto_qsy_day_combo = ttk.Combobox(dayrow, textvariable=self.auto_qsy_day_label_var, state="readonly", width=22,
                                               values=self.freq_display_values or [])
        self.auto_qsy_day_combo.pack(side="left", padx=(0,12))

        nightrow = ttk.Frame(section, style="Chat.TFrame"); nightrow.grid(row=4, column=0, sticky="w", columnspan=6)
        ttk.Label(nightrow, text="Night", style="Header.TLabel").pack(side="left", padx=(0,6))
        self.auto_qsy_night_combo = ttk.Combobox(nightrow, textvariable=self.auto_qsy_night_label_var, state="readonly", width=22,
                                                 values=self.freq_display_values or [])
        self.auto_qsy_night_combo.pack(side="left", padx=(0,12))

        self.cat_save_btn = tk.Button(section, text="Save", command=self._save_cat_settings, bg="#0b141a", fg="#ffffff", bd=1, padx=8, pady=2, highlightthickness=0)
        self.cat_save_btn.grid(row=5, column=0, sticky="w", pady=(8,0))

        # --- ALE-Lite Scan Feature ---
        ale_frame = ttk.LabelFrame(
            section,
            text="ALE-Lite Scan Feature",
            style="Chat.TFrame",
        )
        ale_frame.grid(row=6, column=0, columnspan=6, sticky="ew", pady=(12, 4))
        ale_frame.columnconfigure(2, weight=1)

        desc = ttk.Label(
            ale_frame,
            text="This feature will scan the frequencies (with 10s dwell time) in the fields below searching for Robust Chat beacons.\nWhen it hears one it will stop scanning.",
            style="Hint.TLabel",
            justify="left",
        )
        desc.grid(row=0, column=0, columnspan=3, sticky="w", pady=(2, 6))

        # 5 frequency rows pulled from freqs.json (read-only)
        for i in range(self.ale_scan_rows):
            ttk.Checkbutton(
                ale_frame,
                variable=self.ale_scan_enabled_vars[i],
                text="Enable",
                style="Switch.TCheckbutton",
            ).grid(row=i+1, column=0, sticky="w", padx=(0, 8), pady=2)

            ttk.Label(
                ale_frame,
                text=f"Slot {i+1}",
                style="Header.TLabel",
            ).grid(row=i+1, column=1, sticky="w", padx=(0, 4))

            ttk.Entry(
                ale_frame,
                textvariable=self.ale_scan_label_vars[i],
                state="readonly",
                width=24,
            ).grid(row=i+1, column=2, sticky="w", padx=(0, 8), pady=2)

        self.ale_scan_btn = ttk.Button(
            ale_frame,
            text="Scan",
            command=self._ale_scan_toggle,
            style="Conn.TButton",
        )
        self.ale_scan_btn.grid(row=self.ale_scan_rows+1, column=0, columnspan=3, sticky="w", pady=(8, 2))


        # Remote Wi-Fi Tablet/Phone control (embedded web UI)
        try:
            remote_frame = ttk.Frame(ale_frame, style="Chat.TFrame")
            remote_frame.grid(row=self.ale_scan_rows+2, column=0, columnspan=3, sticky="w", pady=(8, 4))

            remote_check = ttk.Checkbutton(
                remote_frame,
                text="Enable Remote Wifi Tablet or Phone control",
                variable=self.remote_enabled_var,
                command=self._remote_control_toggle,
                style="Switch.TCheckbutton",
            )
            remote_check.grid(row=0, column=0, sticky="w")

            self.remote_status_label = ttk.Label(
                remote_frame,
                textvariable=self.remote_status_var,
                style="Hint.TLabel",
            )
            self.remote_status_label.grid(row=1, column=0, sticky="w", pady=(2, 0))
        except Exception:
            # If anything goes wrong building the remote UI, log but do not crash CAT page
            try:
                self.log("[Remote] Failed to build remote Wi-Fi controls (ignored).")
            except Exception:
                pass



        # Populate ports and set initial enabled/disabled state
        self._populate_cat_ports()
        self._cat_update_controls_state()
        """Placeholder CAT Control page (for future rig CAT integration)."""
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
            "4. Turn on 'Status: Running, load model (top)'\n"
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
    def _build_misc_page(self):
        """Placeholder misc page (no UI). Left intentionally empty to avoid missing-attr crashes."""
        try:
            # No-op: some builds referenced this; keep compatibility without showing anything.
            return
        except Exception:
            return



    def _build_groups_page(self):
        f = self.page_groups
        f.columnconfigure(0, weight=0)
        f.columnconfigure(1, weight=0)

        header = ttk.Label(
            f,
            text="Groups filter (client-side only, does not transmit anything)",
            style="Header.TLabel",
        )
        header.grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8), padx=8)

        enable_chk = ttk.Checkbutton(
            f,
            text="Enable filter (limit 'All' view to callsigns below)",
            variable=self.filter_enabled_var,
            command=self._on_groups_filter_toggled,
            style="Header.TCheckbutton",
        )
        enable_chk.grid(row=1, column=0, columnspan=2, sticky="w", padx=8, pady=(0, 10))

        ttk.Label(f, text="Member callsigns (up to 12):", style="Header.TLabel").grid(
            row=2, column=0, sticky="w", padx=8, pady=(0, 4)
        )

        # 12 small entry fields in two columns
        for i, var in enumerate(self.filter_calls_vars):
            r = 3 + (i // 2)
            c = i % 2
            e = ttk.Entry(f, textvariable=var, width=10)
            e.grid(row=r, column=c, sticky="w", padx=(8 if c == 0 else 16, 4), pady=2)

    def _on_auto_tnc_connect_toggled(self):
        """Persist auto TNC connect setting immediately when toggled."""
        try:
            self._save_settings()
        except Exception:
            pass

    def _on_groups_filter_toggled(self):
        # Persist immediately and refresh labels + current view
        try:
            self._save_settings()
        except Exception:
            pass
        try:
            self._refresh_chat_listbox()
        except Exception:
            pass
        try:
            if getattr(self, "active_chat", "All") == "All":
                self._render_active_chat()
        except Exception:
            pass

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
            getattr(self, 'btn_tab_groups', None),
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
        elif self.current_page == "Groups" and hasattr(self, 'btn_tab_groups'):
            self.btn_tab_groups.configure(bg=active_bg)
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
        elif name == "Groups":
            self.page_groups.tkraise()
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

    # ----- Encryption UI helpers -----
    def _center_popup(self, top):
        """
        Center a Toplevel relative to the main window.
        """
        try:
            self.master.update_idletasks()
            top.update_idletasks()
            x = self.master.winfo_x()
            y = self.master.winfo_y()
            w = self.master.winfo_width()
            h = self.master.winfo_height()
        except Exception:
            # Fallback if coordinates not available yet
            x, y, w, h = 100, 100, 800, 480

        tw = top.winfo_width()
        th = top.winfo_height()
        if tw <= 1:
            tw = 360
        if th <= 1:
            th = 160

        nx = x + (w - tw) // 2
        ny = y + (h - th) // 2
        if nx < 0:
            nx = 0
        if ny < 0:
            ny = 0

        try:
            top.geometry(f"+{nx}+{ny}")
        except Exception:
            pass



    def _on_decrypt_click(self, event):
        """
        Handle clicks on any [Decrypt] tag; resolve which message and prompt for password.
        """
        try:
            index = self.chat_text.index(f"@{event.x},{event.y}")
            tags = self.chat_text.tag_names(index)
            for t in tags:
                if t.startswith("decrypt_"):
                    payload = self.decrypt_handlers.get(t)
                    if payload:
                        self._prompt_decrypt_for_tag(t, payload)
                    return
        except Exception:
            return

    
    def _prompt_decrypt_for_tag(self, tag: str, payload: str):
        """
        Ask user for password, attempt decryption, and replace that line with plaintext on success.
        """
        if not HAVE_AESGCM:
            messagebox.showerror(
                "Decryption unavailable",
                "AES-256 decryption requires the 'cryptography' module to be installed.\n"
                "Install with: pip install cryptography",
            )
            return

        top = tk.Toplevel(self.master)
        top.title("Decrypt message")
        top.configure(bg="#0b141a")
        top.transient(self.master)
        top.grab_set()

        lbl = tk.Label(
            top,
            text="Enter decryption password:",
            fg="#e9edef",
            bg="#0b141a",
            font=self.font_main,
        )
        lbl.grid(row=0, column=0, columnspan=2, padx=12, pady=(10, 6), sticky="w")

        pwd_var = tk.StringVar()
        pwd_entry = tk.Entry(
            top,
            textvariable=pwd_var,
            show="*",
            width=20,
            fg="#e9edef",
            bg="#202c33",
            insertbackground="#e9edef",
        )
        pwd_entry.grid(row=1, column=0, columnspan=2, padx=12, pady=6, sticky="w")

        msg_label = tk.Label(
            top,
            text="",
            fg="#ff6666",
            bg="#0b141a",
            font=self.font_meta,
            wraplength=420,
            justify="left",
        )
        msg_label.grid(row=2, column=0, columnspan=2, padx=12, pady=(0, 4), sticky="w")

        def do_close():
            try:
                top.grab_release()
            except Exception:
                pass
            top.destroy()

        def do_decrypt():
            password = pwd_var.get()
            if not password:
                msg_label.config(text="Please enter a password.")
                return
            try:
                pt = decrypt_text(password, payload)
            except Exception:
                msg_label.config(text="Decryption failed. Wrong password or corrupted message.")
                return

            # Replace encrypted line with plaintext
            try:
                ranges = self.chat_text.tag_ranges(tag)
                if ranges:
                    line_start = self.chat_text.index(f"{ranges[0]} linestart")
                    line_end = self.chat_text.index(f"{ranges[0]} lineend")
                    self.chat_text.configure(state="normal")
                    self.chat_text.delete(line_start, line_end)
                    self.chat_text.insert(line_start, f"Decrypted: {pt}\n", ("dec_msg",))
                    self.chat_text.configure(state="disabled")
            except Exception:
                # Fallback: just show plaintext if tag resolution failed
                messagebox.showinfo("Decrypted", pt)

            do_close()

        btn_frame = tk.Frame(top, bg="#0b141a")
        btn_frame.grid(row=3, column=0, columnspan=2, padx=12, pady=(4, 10), sticky="e")

        dec_btn = tk.Button(
            btn_frame,
            text="DECRYPT",
            command=do_decrypt,
            bg="#0A84FF",
            fg="#FFFFFF",
            activebackground="#3b9dff",
            activeforeground="#FFFFFF",
            bd=0,
            padx=10,
            pady=4,
            highlightthickness=0,
        )
        dec_btn.pack(side="right", padx=(4, 0))

        cancel_btn = tk.Button(
            btn_frame,
            text="CANCEL",
            command=do_close,
            bg="#202c33",
            fg="#e9edef",
            activebackground="#3b4a54",
            activeforeground="#FFFFFF",
            bd=0,
            padx=10,
            pady=4,
            highlightthickness=0,
        )
        cancel_btn.pack(side="right", padx=(0, 4))

        pwd_entry.focus_set()
        self._center_popup(top)

    
    def _prompt_decrypt_with_cb(self, payload: str, on_success):
        """Show password prompt; if correct, call on_success(plaintext)."""
        if not HAVE_AESGCM:
            messagebox.showerror("Decryption unavailable",
                                 "AES-256 decryption requires the 'cryptography' package.\n"
                                 "Install with: pip install cryptography")
            return
        top = tk.Toplevel(self.master)
        top.title("Decrypt message")
        top.configure(bg="#0b141a")
        top.transient(self.master)
        top.grab_set()

        lbl = tk.Label(top, text="Enter decryption password:", fg="#e9edef", bg="#0b141a", font=self.font_main)
        lbl.grid(row=0, column=0, columnspan=2, padx=12, pady=(10, 6), sticky="w")

        pwd_var = tk.StringVar()
        pwd_entry = tk.Entry(top, textvariable=pwd_var, show="*", width=20, fg="#e9edef", bg="#202c33", insertbackground="#e9edef")
        pwd_entry.grid(row=1, column=0, columnspan=2, padx=12, pady=6, sticky="w")

        msg_label = tk.Label(top, text="", fg="#ff6666", bg="#0b141a", font=self.font_meta, wraplength=420, justify="left")
        msg_label.grid(row=2, column=0, columnspan=2, padx=12, pady=(0, 4), sticky="w")

        def do_close():
            try: top.grab_release()
            except Exception: pass
            top.destroy()

        def do_decrypt():
            password = pwd_var.get()
            if not password:
                msg_label.config(text="Please enter a password.")
                return
            try:
                pt = decrypt_text(password, payload)
            except Exception:
                msg_label.config(text="Decryption failed. Wrong password or corrupted message.")
                return
            try:
                on_success(pt)
            except Exception:
                pass
            do_close()

        btn_frame = tk.Frame(top, bg="#0b141a")
        btn_frame.grid(row=3, column=0, columnspan=2, padx=12, pady=(4, 10), sticky="e")

        dec_btn = tk.Button(btn_frame, text="DECRYPT", command=do_decrypt,
                            bg="#0A84FF", fg="#FFFFFF", activebackground="#3b9dff",
                            activeforeground="#FFFFFF", bd=0, padx=10, pady=4, highlightthickness=0)
        dec_btn.pack(side="right", padx=(4, 0))

        cancel_btn = tk.Button(btn_frame, text="CANCEL", command=do_close,
                               bg="#202c33", fg="#e9edef", activebackground="#3b4a54",
                               activeforeground="#FFFFFF", bd=0, padx=10, pady=4, highlightthickness=0)
        cancel_btn.pack(side="right", padx=(0, 4))

        pwd_entry.focus_set()
        self._center_popup(top)


    def _on_decrypt_button(self, btn, payload):
        """Decrypt button handler: prompts and replaces that specific line with plaintext."""
        start_index = self.decrypt_button_line.get(btn)
        def on_success(pt):
            try:
                if start_index:
                    self.chat_text.configure(state="normal")
                    line_start = self.chat_text.index(f"{start_index} linestart")
                    line_end = self.chat_text.index(f"{start_index} lineend")
                    self.chat_text.delete(line_start, line_end)
                    self.chat_text.insert(line_start, f"Decrypted: {pt}\n", ("dec_msg",))
                    self.chat_text.configure(state="disabled")
            except Exception:
                messagebox.showinfo("Decrypted", pt)
        self._prompt_decrypt_with_cb(payload, on_success)

# ----- Misc UI -----



    def _lock_hover(self, hover: bool):
        self.lock_label.configure(bg="#12212c" if hover else "#0b141a")

    
    
    def on_padlock_click(self):
        """
        One-shot encrypt current send-field text into [ENC] payload.
        - Warn about licence.
        - Ask for password.
        - Encrypt ONLY the current send box text.
        - Do NOT auto-send; user presses normal Send.
        """
        if not HAVE_AESGCM:
            messagebox.showerror(
                "Encryption unavailable",
                "AES-256 encryption requires the 'cryptography' module to be installed.\n"
                "Install with: pip install cryptography",
            )
            return

        top = tk.Toplevel(self.master)
        top.title("Encrypt message")
        top.configure(bg="#0b141a")
        top.transient(self.master)
        top.grab_set()

        warning = tk.Label(
            top,
            text="WARNING: ENCRYPTION MAY BE AGAINST YOUR LICENSE CONDITIONS",
            fg="#ff6666",
            bg="#0b141a",
            font=self.font_meta,
            wraplength=420,
            justify="left",
        )
        warning.grid(row=0, column=0, columnspan=2, padx=12, pady=(10, 6), sticky="w")

        lbl = tk.Label(
            top,
            text="Password:",
            fg="#e9edef",
            bg="#0b141a",
            font=self.font_main,
        )
        lbl.grid(row=1, column=0, padx=(12, 6), pady=6, sticky="e")

        pwd_var = tk.StringVar()
        pwd_entry = tk.Entry(
            top,
            textvariable=pwd_var,
            show="*",
            width=20,
            fg="#e9edef",
            bg="#202c33",
            insertbackground="#e9edef",
        )
        pwd_entry.grid(row=1, column=1, padx=(0, 12), pady=6, sticky="w")

        btn_frame = tk.Frame(top, bg="#0b141a")
        btn_frame.grid(row=2, column=0, columnspan=2, padx=12, pady=(4, 10), sticky="e")

        def do_cancel():
            try:
                top.grab_release()
            except Exception:
                pass
            top.destroy()

        def do_encrypt():
            # Use current contents of the send box
            msg = (self.tx_var.get() or "").strip()
            if not msg:
                messagebox.showwarning("No text", "There is no text in the send box to encrypt.")
                return

            password = pwd_var.get()
            if not password:
                messagebox.showwarning("No password", "Please enter an encryption password.")
                return

            try:
                enc_payload = encrypt_text(password, msg)
            except RuntimeError as e:
                messagebox.showerror("Encryption error", str(e))
                return
            except Exception as e:
                messagebox.showerror("Encryption error", f"Failed to encrypt message: {e}")
                return

            # Put encrypted payload into send field; user sends with normal Send button / Enter.
            self.tx_var.set(enc_payload)

            try:
                top.grab_release()
            except Exception:
                pass
            top.destroy()

        encrypt_btn = tk.Button(
            btn_frame,
            text="ENCRYPT",
            command=do_encrypt,
            bg="#0A84FF",
            fg="#FFFFFF",
            activebackground="#3b9dff",
            activeforeground="#FFFFFF",
            bd=0,
            padx=10,
            pady=4,
            highlightthickness=0,
        )
        encrypt_btn.pack(side="right", padx=(4, 0))

        cancel_btn = tk.Button(
            btn_frame,
            text="CANCEL",
            command=do_cancel,
            bg="#202c33",
            fg="#e9edef",
            activebackground="#3b4a54",
            activeforeground="#FFFFFF",
            bd=0,
            padx=10,
            pady=4,
            highlightthickness=0,
        )
        cancel_btn.pack(side="right", padx=(0, 4))

        pwd_entry.focus_set()
        self._center_popup(top)
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

        # Safety: never keep a conversation actually named 'FILTER ON'
        try:
            self.conversations.pop("FILTER ON", None)
        except Exception:
            pass

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
                if name == "All" and self._is_filter_active():
                    label = "FILTER ON"
                else:
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
        # Treat the FILTER ON pseudo-row as the All conversation and
        # never stuff 'FILTER ON' into the To: field.
        if label == "FILTER ON":
            label = "All"
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

    def _is_filter_active(self) -> bool:
        """Return True if the Groups filter is logically active (box ticked + at least one callsign)."""
        try:
            if not hasattr(self, "filter_enabled_var"):
                return False
            if not self.filter_enabled_var.get():
                return False
            for var in getattr(self, "filter_calls_vars", []):
                try:
                    v = (var.get() or "").strip().upper()
                except Exception:
                    v = ""
                if v:
                    return True
            return False
        except Exception:
            return False

    def _apply_groups_filter_to_all(self, msgs):
        """Apply the Groups filter to the All view, returning a filtered list of messages."""
        if not self._is_filter_active():
            return msgs
        # Build set of base callsigns from filter fields
        filter_bases = set()
        for var in getattr(self, "filter_calls_vars", []):
            try:
                v = (var.get() or "").strip().upper()
            except Exception:
                v = ""
            if not v:
                continue
            filter_bases.add(self._callsign_base(v))
        if not filter_bases:
            return msgs

        my = (self.call_var.get() or "").strip().upper()
        my_base = self._callsign_base(my) if my else ""

        filtered = []
        for m in msgs:
            src_base = self._callsign_base(m.get("src", ""))
            dst_base = self._callsign_base(m.get("dst", ""))
            if (
                (src_base and src_base in filter_bases)
                or (dst_base and dst_base in filter_bases)
            ):
                filtered.append(m)
        return filtered


    
    
    def _render_active_chat(self):
        self.decrypt_handlers = {}
        # Clear any existing decrypt buttons before re-rendering
        try:
            for b in self.decrypt_buttons:
                try: b.destroy()
                except Exception: pass
            self.decrypt_buttons.clear()
            self.decrypt_button_line.clear()
        except Exception:
            pass
        self.chat_text.configure(state="normal")
        self.chat_text.delete("1.0", tk.END)

        msgs = self.conversations.get(self.active_chat, [])
        # Apply Groups filter to the All view if enabled
        if self.active_chat == "All":
            try:
                msgs = self._apply_groups_filter_to_all(msgs)
            except Exception:
                pass

        my = (self.call_var.get() or "").strip().upper()
        my_base = self._callsign_base(my) or "ME"

        segments = []
        last_date = None

        # Walk from newest to oldest so newest day + newest messages are at the top
        for m in reversed(msgs):
            epoch = m.get("epoch", time.time())
            try:
                dt = datetime.fromtimestamp(epoch)
            except Exception:
                dt = datetime.now()
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

            # Encrypted payloads: render 'Encrypted message [ENC] [Decrypt]'
            if is_encrypted_payload(text):
                # We'll render as a placeholder with clickable [Decrypt].
                # Store handler id for this entry.
                handler_id = f"decrypt_{len(self.decrypt_handlers) + 1}"
                self.decrypt_handlers[handler_id] = text
                # Direction meta
                if direction == "out":
                    meta = f"{ts}  {my_base} → {dst or 'CQ'}"
                    segments.append(("Encrypted message [ENC] ", ("out_msg",)))
                    segments.append(("<DECRYPT_BUTTON>\n", (handler_id, "out_msg")))
                    segments.append((meta + "\n", ("meta", "out_msg")))
                elif direction == "sys":
                    segments.append(("Encrypted system message [ENC]\n", ("system",)))
                else:
                    src_base = self._callsign_base(src)
                    dst_base = self._callsign_base(dst)
                    is_to_me = bool(my_base and dst_base == my_base)
                    if is_to_me:
                        ttag = "in_to_me"
                        mtag = ("meta", "in_to_me")
                    else:
                        ttag = "in_msg"
                        mtag = ("meta", "in_msg")
                    meta = f"{ts}  {src_base} → {dst or 'ALL'}"
                    segments.append(("Encrypted message [ENC] ", (ttag,)))
                    segments.append(("<DECRYPT_BUTTON>\n", (handler_id, ttag)))
                    segments.append((meta + "\n", mtag))
                continue

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
            if text.strip() == "<DECRYPT_BUTTON>":
                payload = None
                handler_id = None
                for t in tags:
                    if isinstance(t, str) and t.startswith("decrypt_"):
                        handler_id = t
                        payload = self.decrypt_handlers.get(t)
                        break
                btn = tk.Button(
                    self.chat_text,
                    text="DECRYPT",
                    bg="#0b141a",
                    fg="#32CD32",
                    bd=1,
                    relief="ridge",
                    padx=6, pady=1,
                    highlightthickness=1,
                    highlightbackground="#32CD32",
                    highlightcolor="#32CD32",
                    activebackground="#0b141a",
                    activeforeground="#5df35d",
                    font=self.font_small,
                )
                if payload is not None:
                    btn.configure(command=lambda b=btn, p=payload: self._on_decrypt_button(b, p))
                self.chat_text.window_create(tk.END, window=btn)
                try:
                    idx = self.chat_text.index("end-1c")
                    self.decrypt_buttons.append(btn)
                    self.decrypt_button_line[btn] = idx
                except Exception:
                    pass
            elif tags:
                self.chat_text.insert(tk.END, text, tags)
            else:
                self.chat_text.insert(tk.END, text)

        self.chat_text.configure(state="disabled")
        # Bind decrypt handlers for encrypted messages
        try:
            for tag, payload in self.decrypt_handlers.items():
                if tag.startswith("decrypt_"):
                    self.chat_text.tag_bind(tag, "<Button-1>", self._on_decrypt_click)
            self.chat_text.tag_bind("decrypt_link", "<Button-1>", self._on_decrypt_click)
        except Exception:
            pass

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
        # Determine own callsign safely; during early init call_var may not exist yet.
        my = ""
        try:
            if hasattr(self, "call_var"):
                my = (self.call_var.get() or "").strip().upper()
        except Exception:
            my = ""
        if not my:
            try:
                # Fall back to settings.json if available
                my = (self.settings.get("mycall") or "").strip().upper()
            except Exception:
                my = ""
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

        # If ALE-Lite scan is running, any valid beacon should stop it
        try:
            if getattr(self, "ale_scan_active", False):
                self._ale_scan_stop_on_beacon(txt)
        except Exception:
            pass

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
    def _maybe_auto_connect_tnc(self):
        """Attempt to auto-connect TNC on startup if enabled and last_port is valid."""
        try:
            # Option can be disabled from settings / UI
            if not hasattr(self, "auto_tnc_connect_var"):
                return
            if not self.auto_tnc_connect_var.get():
                return
            # Do not auto-connect if already connected
            if getattr(self, "ser", None):
                return
            last_port = (self.settings.get("last_port") or "").strip()
            if not last_port:
                return
            ports = []
            try:
                ports = list(self.port_combo["values"])
            except Exception:
                ports = []
            if not ports or last_port not in ports:
                # Port from last session is not currently available
                return
            # Select the last port in the UI
            try:
                self.port_var.set(last_port)
                self.port_combo.set(last_port)
            except Exception:
                pass
            self.log(f"[INFO] Auto-connect: attempting TNC connect on {last_port}")
            try:
                self.connect_port()
            except Exception as e:
                self.log(f"[WARN] Auto-connect failed on {last_port}: {e}")
        except Exception as e:
            try:
                self.log(f"[WARN] Auto-connect logic error: {e}")
            except Exception:
                pass

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
            # Normal pending-ACK handling (if this ACK is for one of our messages)
            self._handle_incoming_ack(src, ack_id)
            # Also cancel any pending auto-relay for this ACK ID
            try:
                self._auto_relay_note_ack(ack_id)
            except Exception:
                pass
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

        
        # For ACKable third-party messages (not to us), consider scheduling auto-relay
        if ack_id and not self._is_to_me(dst):
            try:
                self._auto_relay_maybe_schedule(src, dst, txt, body_text, ack_id)
            except Exception as e:
                try:
                    self.log(f"[AutoRelay] Schedule error for ACK {ack_id}: {e}")
                except Exception:
                    pass
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
        # Stop remote HTTP server if running
        try:
            self._stop_remote_server()
        except Exception:
            pass
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




# ===== Embedded HTTP server for remote tablet/phone control ================

class RemoteHTTPServer(http.server.ThreadingHTTPServer):
    """
    Thin wrapper so handlers can reach back into the RobustChatSimpleV16 app
    via self.server.app.
    """
    def __init__(self, server_address, RequestHandlerClass, app):
        super().__init__(server_address, RequestHandlerClass)
        self.app = app


class RemoteRequestHandler(http.server.BaseHTTPRequestHandler):
    server_version = "RobustChatRemote/1.0"

    def log_message(self, fmt, *args):
        # Route HTTP logs into the main app log where possible
        try:
            msg = fmt % args
        except Exception:
            msg = fmt
        try:
            self.server.app.log(f"[RemoteHTTP] {msg}")
        except Exception:
            pass

    # --- Helpers ---------------------------------------------------------

    def _send_json(self, obj, status=200):
        data = json.dumps(obj).encode("utf-8", errors="replace")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _send_html(self, html, status=200):
        data = html.encode("utf-8", errors="replace")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _get_cookies(self):
        raw = self.headers.get("Cookie") or ""
        cookies = {}
        for part in raw.split(";"):
            if "=" in part:
                k, v = part.split("=", 1)
                cookies[k.strip()] = v.strip()
        return cookies

    def _get_session_token(self):
        cookies = self._get_cookies()
        return cookies.get("rc_session")

    def _require_session(self):
        token = self._get_session_token()
        app = self.server.app
        if not token or not app._remote_validate_session(token):
            # Not authorised
            self.send_response(401)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.end_headers()
            self.wfile.write(b"Not authorised. Please log in again.\n")
            return None
        return token

    # --- HTTP verbs ------------------------------------------------------

    def do_GET(self):
        app = self.server.app
        path = self.path.split("?", 1)[0]
        if path == "/":
            # Login page
            html = """<!doctype html>
<html>
<head>
  <meta charset='utf-8'>
  <title>Robust Chat Remote Login</title>
  <meta name='viewport' content='width=device-width, initial-scale=1'>
  <style>
    body { background:#0b141a; color:#e9edef; font-family: system-ui, -apple-system, sans-serif; padding:20px; }
    .box { max-width:420px; margin:40px auto; padding:20px; background:#111b21; border-radius:12px; box-shadow:0 0 12px rgba(0,0,0,0.6); }
    h1 { font-size:1.3rem; margin-top:0; }
    label { display:block; margin-bottom:8px; }
    input[type=password] { width:100%; padding:8px; border-radius:6px; border:1px solid #202c33; background:#0b141a; color:#e9edef; }
    button { margin-top:12px; padding:8px 16px; border-radius:6px; border:none; background:#0A84FF; color:#fff; font-weight:600; cursor:pointer; }
    .hint { color:#8696a0; font-size:0.85rem; margin-top:10px; }
  </style>
</head>
<body>
  <div class="box">
    <h1>Robust Chat Remote</h1>
    <form method="POST" action="/api/login">
      <label>Password (default = MYCALL)</label>
      <input type="password" name="password" autofocus>
      <button type="submit">Login</button>
    </form>
    <div class="hint">
      Use the station callsign (MYCALL) as the password, e.g. G4ABC.<br>
      Connection is local-only over your own Wi-Fi.
    </div>
  </div>
</body>
</html>"""
            self._send_html(html)
            return


        if path == "/main":
            # Require valid session
            if not self._require_session():
                return
            html = """<!doctype html>
<html>
<head>
  <meta charset='utf-8'>
  <title>Robust Chat Remote</title>
  <meta name='viewport' content='width=device-width, initial-scale=1'>
  <style>
    body { background:#0b141a; color:#e9edef; font-family: system-ui, -apple-system, sans-serif; margin:0; padding:0; }
    header {
      padding:10px 14px;
      background:#111b21;
      border-bottom:1px solid #202c33;
      display:flex;
      justify-content:space-between;
      align-items:center;
      gap:8px;
    }
    .header-left { display:flex; flex-direction:column; }
    header h1 { font-size:1.1rem; margin:0; }
    header .sub { font-size:0.8rem; color:#8696a0; }
    .header-buttons {
      display:flex;
      gap:6px;
    }
    .header-buttons button {
      padding:4px 8px;
      border-radius:12px;
      border:1px solid #202c33;
      background:#1f2c33;
      color:#e9edef;
      font-size:0.8rem;
      cursor:pointer;
    }
    .header-buttons button.active {
      border-color:#ff7b00;
      color:#ffb366;
    }

    main { display:flex; flex-direction:column; height:calc(100vh - 52px); }
    #cols { flex:1; display:flex; min-height:0; }

    /* Desktop / default widths */
    #chatlist {
      width:160px;                 /* ~20 chars wide on desktop */
      min-width:120px;
      border-right:1px solid #202c33;
      overflow:auto;
      padding:8px;
      box-sizing:border-box;
    }
    #locator {
      width:14%;                   /* half of original 28% */
      min-width:120px;
      border-right:1px solid #202c33;
      overflow:auto;
      padding:8px;
      box-sizing:border-box;
    }
    #chat { flex:1; overflow:auto; padding:8px; box-sizing:border-box; }

    .chat-line { margin-bottom:4px; font-size:0.9rem; }
    .ts { color:#8696a0; font-size:0.75rem; margin-right:4px; }
    .srcdst { font-weight:600; margin-right:4px; }
    .msg { white-space:pre-wrap; word-break:break-word; }
    .msg-to-me { color:#ff7b00; }  /* messages TO MYCALL in orange */
    .msg-out { color:#00bcd4; }   /* outgoing messages in teal */
    .tick { margin-left:4px; font-size:0.8rem; }

    #sendbar { padding:6px 8px; border-top:1px solid #202c33; display:flex; gap:6px; }
    #sendbar input[type=text] {
      padding:6px;
      border-radius:6px;
      border:2px solid #ff7b00;    /* orange outline for TO + message */
      background:#0b141a;
      color:#e9edef;
    }
    #sendbar input[type=text]:focus {
      outline:none;
      border-color:#ffa64d;        /* lighter orange on focus */
    }
    #dst {
      width:70px;                  /* ~8 characters wide */
      text-align:center;
      font-weight:600;
      text-transform:uppercase;
      flex:0 0 auto;
    }
    #msg {
      flex:1;
    }
    #sendbar button {
      padding:6px 12px;
      border-radius:6px;
      border:none;
      background:#0A84FF;
      color:#fff;
      font-weight:600;
      cursor:pointer;
    }

    .section-title { font-size:0.8rem; text-transform:uppercase; color:#8696a0; margin-bottom:4px; }
    .call { margin-bottom:4px; font-size:0.9rem; }
    .call span { display:block; }

    /* Hide/show panels via body classes */
    body.hide-chatlist #chatlist { display:none; }
    body.hide-locator #locator { display:none; }

    /* Phone / narrow screens: panels become slide-in side drawers and start hidden */
    @media (max-width: 700px) {
      main { height:calc(100vh - 52px); }
      #cols { position:relative; }

      #chatlist, #locator {
        position:absolute;
        top:0;
        bottom:0;
        z-index:5;
        background:#111b21;
        box-shadow:0 0 18px rgba(0,0,0,0.7);
      }
      #chatlist {
        left:0;
        width:60%;                 /* side panel width on phones */
        max-width:260px;
      }
      #locator {
        right:0;
        width:60%;
        max-width:260px;
      }
    }
  </style>
</head>
<body>
  <header>
    <div class="header-left">
      <h1>Robust Chat Remote</h1>
      <div class="sub" id="status">Connecting&hellip;</div>
    </div>
    <div class="header-buttons">
      <button type="button" id="btn-chatlist">Chats</button>
      <button type="button" id="btn-locator">Locator</button>
      <button type="button" id="btn-mute">🔊</button>
    </div>
  </header>
  <main>
    <div id="cols">
      <div id="chatlist">
        <div class="section-title">Chats</div>
        <div id="chatlist-body"></div>
      </div>
      <div id="chat"></div>
      <div id="locator">
        <div class="section-title">Locator</div>
        <div id="locator-body"></div>
      </div>
    </div>
    <form id="sendbar">
      <input type="text" id="dst" maxlength="8" placeholder="TO">
      <input type="text" id="msg" placeholder="Type message&hellip;">
      <button type="submit">Send</button>
    </form>
  </main>
  <script>
    let state = null;
    let muted = false;
    let notifiedIds = new Set();
    let currentFilter = "ALL";

    function playTone2() {
      try {
        const ctx = new (window.AudioContext || window.webkitAudioContext)();

        function tone(freq, startMs, durMs) {
          const osc = ctx.createOscillator();
          const gain = ctx.createGain();
          osc.frequency.value = freq;
          gain.gain.value = 0.18; // volume
          osc.connect(gain);
          gain.connect(ctx.destination);
          const start = ctx.currentTime + startMs / 1000;
          const end   = start + durMs  / 1000;
          osc.start(start);
          osc.stop(end);
        }

        // Two short notes
        tone(880, 0,   120);   // Note 1
        tone(660, 170, 120);   // Note 2

        // Close audio context automatically
        setTimeout(() => ctx.close(), 450);
      } catch (e) {
        console.warn("Tone2 playback failed:", e);
      }
    }


    function updatePanelButtons() {
      const chatBtn = document.getElementById('btn-chatlist');
      const locBtn = document.getElementById('btn-locator');
      if (!chatBtn || !locBtn) return;
      const chatHidden = document.body.classList.contains('hide-chatlist');
      const locHidden = document.body.classList.contains('hide-locator');
      if (chatHidden) chatBtn.classList.remove('active'); else chatBtn.classList.add('active');
      if (locHidden) locBtn.classList.remove('active'); else locBtn.classList.add('active');
    }

    function applyInitialPanelState() {
      if (window.innerWidth <= 700) {
        // On phones: start with both side panels hidden to maximise message space
        document.body.classList.add('hide-chatlist', 'hide-locator');
      } else {
        // On larger screens: show both by default
        document.body.classList.remove('hide-chatlist');
        document.body.classList.remove('hide-locator');
      }
      updatePanelButtons();
    }

    function toggleChatlist() {
      document.body.classList.toggle('hide-chatlist');
      updatePanelButtons();
    }

    function toggleLocator() {
      document.body.classList.toggle('hide-locator');
      updatePanelButtons();
    }

    async function fetchState() {
      try {
        const res = await fetch('/api/state');
        if (res.status === 401) {
          window.location = '/';
          return;
        }
        const data = await res.json();
        state = data;
        renderState();
      } catch (e) {
        document.getElementById('status').textContent = 'Disconnected';
      }
    }

    function renderState() {
      if (!state || !state.ok) return;
      document.getElementById('status').textContent = 'MYCALL: ' + (state.mycall || '?');

      const chatlistBody = document.getElementById('chatlist-body');
      chatlistBody.innerHTML = '';
      const keys = state.chat_keys || [];
      keys.forEach(k => {
        const div = document.createElement('div');
        div.textContent = k;
        div.className = 'call';
        div.onclick = () => {
          const dst = document.getElementById('dst');
          if (k === 'All' || k === 'ALL') {
            dst.value = 'ALL';
            currentFilter = "ALL";
          } else {
            dst.value = k;
            currentFilter = (k || "").toUpperCase();
          }
          if (dst) dst.focus();
        };
        chatlistBody.appendChild(div);
      });

      const chatDiv = document.getElementById('chat');
      chatDiv.innerHTML = '';
      const msgs = state.messages_all || [];
      const myUpper = (state.mycall || '').toUpperCase();
      const filterUpper = (currentFilter || 'ALL').toUpperCase();

      // Build a newest-first list, de-duplicating by ack_id so retries don't duplicate lines
      const rendered = [];
      const seenAck = new Set();

      for (let i = msgs.length - 1; i >= 0; i--) {
        const m = msgs[i] || {};
        const ackId = m.ack_id || null;
        if (ackId) {
          if (seenAck.has(ackId)) continue;
          seenAck.add(ackId);
        }
        rendered.push(m);
      }

      // Now render newest -> oldest from rendered[]
      rendered.forEach(m => {
        const srcUpper = (m.src || '').toUpperCase();
        const dstUpper = (m.dst || '').toUpperCase();
        const direction = m.direction || "";
        const isOut = direction === 'out' || (srcUpper === myUpper);
        const toMe = myUpper && dstUpper === myUpper;

        // Apply filter: if currentFilter != ALL, only show where src or dst matches
        if (filterUpper !== 'ALL') {
          if (srcUpper !== filterUpper && dstUpper !== filterUpper) {
            return;
          }
        }

        // ACK tick system for outgoing messages
        let tick = "";
        if (isOut) {
          const s = m.ack_status || "";
          if (s === "pending") {
            tick = " ✓";
          } else if (s === "ok") {
            tick = " ✓✓";
          } else if (s === "failed") {
            tick = " !";
          }
        }

        // Beep for NEW messages directly to me (respect mute)
        const idKey = (m.ack_id || '') || ((m.ts || '') + '|' + (m.src || '') + '|' + (m.dst || '') + '|' + (m.text || ''));
        if (toMe && !muted && idKey && !notifiedIds.has(idKey)) {
          playTone2();
          notifiedIds.add(idKey);
        }

        const line = document.createElement('div');
        line.className = 'chat-line';

        const ts = document.createElement('span');
        ts.className = 'ts';
        ts.textContent = m.ts || '';

        const sd = document.createElement('span');
        sd.className = 'srcdst';
        sd.textContent = (m.src || '') + '>' + (m.dst || '') + ':';

        const msg = document.createElement('span');
        let msgClass = 'msg';
        if (toMe) {
          msgClass += ' msg-to-me';
        } else if (isOut) {
          msgClass += ' msg-out';
        }
        msg.className = msgClass;
        msg.textContent = ' ' + (m.text || '') + tick;  // tick at end of message

        line.appendChild(ts);
        line.appendChild(sd);
        line.appendChild(msg);
        chatDiv.appendChild(line);
      });

      // Ensure newest (top) is visible
      chatDiv.scrollTop = 0;

      const locBody = document.getElementById('locator-body');
      locBody.innerHTML = '';
      const loc = state.locator || {};
      const h = document.createElement('div');
      h.className = 'call';
      h.innerHTML = '<span><strong>' + (loc.mycall || '?') + '</strong></span>' +
                    '<span>Grid: ' + (loc.mygrid || '?') + '</span>' +
                    '<span>Lat/Lon: ' + (loc.mylat == null ? '?' : loc.mylat.toFixed(4)) +
                    ', ' + (loc.mylon == null ? '?' : loc.mylon.toFixed(4)) + '</span>';
      locBody.appendChild(h);
      const list = document.createElement('div');
      const stations = loc.stations || [];
      stations.forEach(s => {
        const d = document.createElement('div');
        d.className = 'call';
        const call = (s.call || '').toUpperCase();
        let line = '<span><strong>' + (s.call || '') + '</strong></span>';
        if (s.grid) line += '<span>Grid: ' + s.grid + '</span>';
        if (s.lat != null && s.lon != null) {
          line += '<span>Lat/Lon: ' + Number(s.lat).toFixed(4) + ', ' + Number(s.lon).toFixed(4) + '</span>';
        }
        d.innerHTML = line;
        d.onclick = () => {
          const dst = document.getElementById('dst');
          if (dst) {
            dst.value = call;
            dst.focus();
          }
          currentFilter = call;
        };
        list.appendChild(d);
      });
      locBody.appendChild(list);
    }

    async function sendMessage(dst, text) {
      try {
        const res = await fetch('/api/send', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ dst, text }),
        });
        if (res.status === 401) {
          window.location = '/';
          return;
        }
      } catch (e) {
        console.error(e);
      }
    }

    document.getElementById('sendbar').addEventListener('submit', function(ev) {
      ev.preventDefault();
      const dst = document.getElementById('dst').value;
      const msg = document.getElementById('msg').value;
      if (!msg.trim()) return;
      sendMessage(dst, msg);
      document.getElementById('msg').value = '';
    });

    document.getElementById('btn-chatlist').addEventListener('click', function() {
      toggleChatlist();
    });
    document.getElementById('btn-locator').addEventListener('click', function() {
      toggleLocator();
    });
    document.getElementById('btn-mute').addEventListener('click', function() {
      muted = !muted;
      const b = document.getElementById('btn-mute');
      if (b) b.textContent = muted ? '🔇' : '🔊';
    });

    window.addEventListener('resize', function() {
      applyInitialPanelState();
    });

    applyInitialPanelState();
    fetchState();
    setInterval(fetchState, 2000);
  </script>
</body>
</html>"""
            self._send_html(html)
            return

        if path == "/api/state":
            if not self._require_session():
                return
            try:
                state = app._remote_collect_state()
            except Exception as e:
                state = {"ok": False, "error": str(e)}
            self._send_json(state)
            return

        # Fallback for unknown paths
        self.send_response(404)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write(b"Not found\n")

    def do_POST(self):
        app = self.server.app
        path = self.path.split("?", 1)[0]
        length = int(self.headers.get("Content-Length", "0") or "0")
        raw = self.rfile.read(length) if length else b""
        if path == "/api/login":
            # Expect form-encoded body: password=...
            try:
                qs = urllib.parse.parse_qs(raw.decode("utf-8", errors="replace"))
                pwd = (qs.get("password") or [""])[0]
            except Exception:
                pwd = ""
            if app._remote_check_password(pwd):
                token = app._remote_new_session_token()
                self.send_response(302)
                self.send_header("Location", "/main")
                self.send_header("Set-Cookie", f"rc_session={token}; Path=/; HttpOnly")
                self.end_headers()
                return
            else:
                # Simple invalid reply
                html = "<!doctype html><html><body><p>Invalid password. <a href='/'>Try again</a>.</p></body></html>"
                self._send_html(html, status=401)
                return

        if path == "/api/send":
            if not self._require_session():
                return
            dst = ""
            text = ""
            try:
                payload = json.loads(raw.decode("utf-8", errors="replace") or "{}")
                dst = (payload.get("dst") or "").strip()
                text = (payload.get("text") or "").strip()
            except Exception:
                pass
            if text:
                app._remote_send_message(dst, text)
                self._send_json({"ok": True})
            else:
                self._send_json({"ok": False, "error": "Empty message"}, status=400)
            return

        # Unknown POST
        self.send_response(404)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write(b"Not found\n")
def main():
    """
    Create Tk root, initialise RobustChatSimpleV16, apply dark titlebar, and return root.
    """
    root = tk.Tk()
    app = RobustChatSimpleV16(root)
    try:
        enable_dark_titlebar(root)
    except Exception:
        pass
    return root

if __name__ == "__main__":
    from datetime import datetime
    import traceback

    def _startup_log(msg: str):
        ts = datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S UTC")
        line = f"[LOG] {msg}"
        print(line)
        try:
            path = app_path("startup_log.txt")
            with open(path, "a", encoding="utf-8") as f:
                f.write(f"{ts} {line}\n")
        except Exception:
            pass

    _startup_log("===== Robust Chat v2.25 startup =====")
    try:
        root = main()
        _startup_log("Fonts and UI initialised OK")
        _startup_log("Entering mainloop()")
        root.mainloop()
        _startup_log("===== Robust Chat v2.25 shutdown =====")
    except Exception:
        _startup_log("Unhandled exception in main():")
        tb = traceback.format_exc()
        for line in tb.rstrip().splitlines():
            print(line)
            try:
                path = app_path("startup_log.txt")
                with open(path, "a", encoding="utf-8") as f:
                    f.write(line + "\n")
            except Exception:
                pass
        try:
            input("Press Enter to close...")
        except Exception:
            pass