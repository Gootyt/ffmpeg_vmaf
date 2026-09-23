import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import subprocess
import threading
import os
import json
import shutil
import re
import time

CONFIG_FILE = "av1_vmaf_config.json"
SKIPPED_DB_FILE = "av1_skipped_db.json"
HISTORY_DB_FILE = "av1_history_db.json"

class AV1VmafApp:
    def __init__(self, root):
        self.root = root
        self.root.title("AV1 VMAF Újratömörítő (Okos Kereséssel + Sávválasztóval)")
        self.root.geometry("950x790") 
        
        self.files_to_process = []
        self.files_data = {} 
        
        self.is_processing = False
        self.cancel_requested = False
        self.current_process = None
        
        self.load_skipped_db()
        self.load_history_db()
        
        self.setup_ui()
        self.load_config()

        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

    def load_skipped_db(self):
        self.skipped_db = {}
        if os.path.exists(SKIPPED_DB_FILE):
            try:
                with open(SKIPPED_DB_FILE, 'r', encoding='utf-8') as f:
                    self.skipped_db = json.load(f)
            except Exception:
                pass

    def save_skipped_db(self):
        try:
            with open(SKIPPED_DB_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.skipped_db, f, ensure_ascii=False, indent=4)
        except Exception:
            pass

    def load_history_db(self):
        self.encode_history = []
        if os.path.exists(HISTORY_DB_FILE):
            try:
                with open(HISTORY_DB_FILE, 'r', encoding='utf-8') as f:
                    self.encode_history = json.load(f)
            except Exception:
                pass

    def save_history_db(self):
        try:
            with open(HISTORY_DB_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.encode_history[-500:], f, ensure_ascii=False, indent=4)
        except Exception:
            pass

    def add_to_history(self, vmaf, crf, preset, resolution):
        self.encode_history.append({"vmaf": vmaf, "crf": crf, "preset": preset, "resolution": resolution})
        self.save_history_db()

    def estimate_starting_crf(self, target_vmaf, preset, resolution):
        if not self.encode_history:
            return 30
            
        preset_history = [x for x in self.encode_history if x.get('preset') == preset]
        history_to_use = preset_history if preset_history else self.encode_history
        
        res_history = [x for x in history_to_use if x.get('resolution') == resolution]
        history_to_use = res_history if res_history else history_to_use
        
        sorted_history = sorted(history_to_use, key=lambda x: abs(x.get('vmaf', 93.0) - target_vmaf))
        closest = sorted_history[:5]
        
        if not closest:
            return 30
            
        avg_crf = sum(item.get('crf', 30) for item in closest) / len(closest)
        guessed_crf = int(round(avg_crf))
        
        return max(15, min(45, guessed_crf))

    def mark_as_skipped(self, filepath):
        try:
            size = os.path.getsize(filepath)
            self.skipped_db[filepath] = size
            self.save_skipped_db()
        except Exception:
            pass

    def is_av1_video(self, filepath):
        try:
            cmd = ["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=codec_name", "-of", "default=noprint_wrappers=1:nokey=1", filepath]
            startupinfo = None
            if os.name == 'nt':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, startupinfo=startupinfo)
            return result.stdout.strip().lower() == "av1"
        except Exception:
            return False

    def setup_ui(self):
        control_frame = ttk.Frame(self.root, padding=10)
        control_frame.pack(fill=tk.X)

        ttk.Label(control_frame, text="Cél VMAF (minimum):").grid(row=0, column=0, sticky=tk.W, pady=5)
        self.vmaf_entry = ttk.Entry(control_frame, width=10)
        self.vmaf_entry.grid(row=0, column=1, sticky=tk.W, pady=5, padx=5)

        ttk.Label(control_frame, text="Tűréshatár (±):").grid(row=0, column=2, sticky=tk.W, pady=5, padx=(15, 0))
        self.tol_entry = ttk.Entry(control_frame, width=10)
        self.tol_entry.grid(row=0, column=3, sticky=tk.W, pady=5, padx=5)

        ttk.Label(control_frame, text="Alsó 5% VMAF (opcionális):").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.vmaf_5_entry = ttk.Entry(control_frame, width=10)
        self.vmaf_5_entry.grid(row=1, column=1, sticky=tk.W, pady=5, padx=5)

        ttk.Label(control_frame, text="Alsó 1% VMAF (opcionális):").grid(row=1, column=2, sticky=tk.W, pady=5, padx=(15, 0))
        self.vmaf_1_entry = ttk.Entry(control_frame, width=10)
        self.vmaf_1_entry.grid(row=1, column=3, sticky=tk.W, pady=5, padx=5)

        ttk.Label(control_frame, text="AV1 Preset (0=Lassú, 13=Gyors):").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.preset_combo = ttk.Combobox(control_frame, values=[str(i) for i in range(14)], width=8, state="readonly")
        self.preset_combo.grid(row=2, column=1, sticky=tk.W, pady=5, padx=5)

        self.low_priority_var = tk.BooleanVar(value=True)
        self.low_priority_check = ttk.Checkbutton(control_frame, text="Alacsony prioritás (Háttérben futás)", variable=self.low_priority_var)
        self.low_priority_check.grid(row=2, column=2, columnspan=2, sticky=tk.W, pady=5, padx=(15, 0))

        paned_window = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        paned_window.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        list_frame = ttk.Frame(paned_window)
        paned_window.add(list_frame, weight=1)
        
        ttk.Label(list_frame, text="Feldolgozásra váró videók:").pack(anchor=tk.W)
        self.file_listbox = tk.Listbox(list_frame, selectmode=tk.EXTENDED)
        self.file_listbox.pack(fill=tk.BOTH, expand=True, pady=5)
        self.file_listbox.bind('<<ListboxSelect>>', self.on_file_select)
        
        list_btn_frame = ttk.Frame(list_frame)
        list_btn_frame.pack(fill=tk.X, pady=(0, 5))
        ttk.Button(list_btn_frame, text="Fájlok hozzáadása", command=self.add_files).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(list_btn_frame, text="Könyvtár hozzáadása", command=self.add_directory).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(list_btn_frame, text="Kijelöltek Törlése", command=self.remove_files).pack(side=tk.LEFT)
        
        sort_frame = ttk.Frame(list_frame)
        sort_frame.pack(fill=tk.X)
        ttk.Label(sort_frame, text="Rendezés:").pack(side=tk.LEFT, padx=(0, 5))
        self.sort_crit_combo = ttk.Combobox(sort_frame, values=["Méret", "Fájlnév", "Teljes elérési út", "Hossz", "Videó bitrate", "Módosítás dátuma"], state="readonly", width=18)
        self.sort_crit_combo.set("Fájlnév")
        self.sort_crit_combo.pack(side=tk.LEFT, padx=(0, 5))
        self.sort_crit_combo.bind("<<ComboboxSelected>>", self.sort_files)
        
        self.sort_order_combo = ttk.Combobox(sort_frame, values=["Növekvő", "Csökkenő"], state="readonly", width=10)
        self.sort_order_combo.set("Növekvő")
        self.sort_order_combo.pack(side=tk.LEFT)
        self.sort_order_combo.bind("<<ComboboxSelected>>", self.sort_files)
        
        self.track_frame_container = ttk.LabelFrame(paned_window, text="Megtartandó sávok (Kattints egy videóra bal oldalt)")
        paned_window.add(self.track_frame_container, weight=1)
        
        self.track_canvas = tk.Canvas(self.track_frame_container, highlightthickness=0)
        self.track_scrollbar = ttk.Scrollbar(self.track_frame_container, orient="vertical", command=self.track_canvas.yview)
        self.track_inner_frame = ttk.Frame(self.track_canvas)
        
        self.track_inner_frame.bind("<Configure>", lambda e: self.track_canvas.configure(scrollregion=self.track_canvas.bbox("all")))
        self.track_canvas.create_window((0, 0), window=self.track_inner_frame, anchor="nw")
        self.track_canvas.configure(yscrollcommand=self.track_scrollbar.set)
        
        self.track_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.track_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        global_btn_frame = ttk.Frame(self.root, padding=(10, 0, 10, 5))
        global_btn_frame.pack(fill=tk.X)
        self.cancel_btn = ttk.Button(global_btn_frame, text="Leállítás", command=self.request_cancel, state=tk.DISABLED)
        self.cancel_btn.pack(side=tk.RIGHT, padx=5)
        
        self.start_btn = ttk.Button(global_btn_frame, text="Feldolgozás Indítása", command=self.start_processing)
        self.start_btn.pack(side=tk.RIGHT, padx=5)

        log_frame = ttk.Frame(self.root, padding=(10, 5, 10, 5))
        log_frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(log_frame, text="Napló:").pack(anchor=tk.W)
        self.log_text = tk.Text(log_frame, height=8, state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)

        progress_frame = ttk.Frame(self.root, padding=(10, 5, 10, 10))
        progress_frame.pack(fill=tk.X)
        
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(progress_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(fill=tk.X, side=tk.TOP, pady=(0, 5))
        
        info_frame = ttk.Frame(progress_frame)
        info_frame.pack(fill=tk.X)
        
        self.progress_label = ttk.Label(info_frame, text="0.0%")
        self.progress_label.pack(side=tk.LEFT)
        
        self.eta_label = ttk.Label(info_frame, text="Hátralévő idő: --:--:--")
        self.eta_label.pack(side=tk.RIGHT)

    def load_config(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f:
                    config = json.load(f)
                    self.vmaf_entry.delete(0, tk.END)
                    self.vmaf_entry.insert(0, config.get("vmaf", "93.0"))
                    
                    self.vmaf_5_entry.delete(0, tk.END)
                    self.vmaf_5_entry.insert(0, config.get("vmaf_5", ""))
                    
                    self.vmaf_1_entry.delete(0, tk.END)
                    self.vmaf_1_entry.insert(0, config.get("vmaf_1", ""))
                    
                    self.tol_entry.delete(0, tk.END)
                    self.tol_entry.insert(0, config.get("tolerance", "1.0"))
                    
                    self.preset_combo.set(config.get("preset", "6"))
                    self.low_priority_var.set(config.get("low_priority", True))
                    
                    self.sort_crit_combo.set(config.get("sort_crit", "Fájlnév"))
                    self.sort_order_combo.set(config.get("sort_order", "Növekvő"))
            except Exception:
                self.set_default_config()
        else:
            self.set_default_config()

    def set_default_config(self):
        self.vmaf_entry.insert(0, "93.0")
        self.vmaf_5_entry.insert(0, "")
        self.vmaf_1_entry.insert(0, "")
        self.tol_entry.insert(0, "1.0")
        self.preset_combo.set("6")
        self.low_priority_var.set(True)
        self.sort_crit_combo.set("Fájlnév")
        self.sort_order_combo.set("Növekvő")

    def save_config(self):
        config = {
            "vmaf": self.vmaf_entry.get(),
            "vmaf_5": self.vmaf_5_entry.get(),
            "vmaf_1": self.vmaf_1_entry.get(),
            "tolerance": self.tol_entry.get(),
            "preset": self.preset_combo.get(),
            "low_priority": self.low_priority_var.get(),
            "sort_crit": self.sort_crit_combo.get(),
            "sort_order": self.sort_order_combo.get()
        }
        try:
            with open(CONFIG_FILE, 'w') as f:
                json.dump(config, f)
        except Exception:
            pass

    def on_closing(self):
        self.save_config()
        if self.is_processing:
            if messagebox.askyesno("Kilépés", "A feldolgozás még fut. Biztosan be akarod zárni (és leállítani)?"):
                self.request_cancel()
                self.root.after(1500, self.root.destroy)
            else:
                return
        else:
            self.root.destroy()

    def log(self, message):
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, message + "\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.root.update_idletasks()

    def format_time(self, seconds):
        if seconds < 0: return "--:--:--"
        h = int(seconds // 3600)
        m = int((seconds % 3600) // 60)
        s = int(seconds % 60)
        return f"{h:02d}:{m:02d}:{s:02d}"

    def format_size(self, size_in_bytes):
        for unit in ['B', 'KB', 'MB', 'GB']:
            if size_in_bytes < 1024.0:
                return f"{size_in_bytes:.2f} {unit}"
            size_in_bytes /= 1024.0
        return f"{size_in_bytes:.2f} TB"

    def update_progress(self, progress, eta_seconds=None):
        self.progress_var.set(progress)
        self.progress_label.config(text=f"{progress:.1f}%")
        if eta_seconds is not None:
            self.eta_label.config(text=f"Hátralévő idő: {self.format_time(eta_seconds)}")
        else:
            self.eta_label.config(text="Hátralévő idő: --:--:--")
        self.root.update_idletasks()

    def get_audio_bitrate(self, channels):
        return "96k" if channels <= 2 else "192k"

    def get_streams_info(self, filepath):
        cmd = ["ffprobe", "-v", "error", "-print_format", "json", "-show_format", "-show_streams", filepath]
        startupinfo = None
        if os.name == 'nt':
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        try:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, startupinfo=startupinfo)
            info = json.loads(result.stdout)
            streams = info.get('streams', [])
            fmt = info.get('format', {})
            
            audio_streams = []
            sub_streams = []
            video_bitrate = 0.0
            video_width = 0
            video_height = 0
            
            try:
                duration = float(fmt.get('duration', 0.0))
            except (ValueError, TypeError):
                duration = 0.0
            
            for s in streams:
                idx = s.get('index')
                codec_type = s.get('codec_type')
                tags = s.get('tags', {})
                lang = tags.get('language', 'und').upper()
                title = tags.get('title', '')
                codec_name = s.get('codec_name', 'unknown').upper()
                
                if codec_type == 'video':
                    video_width = s.get('width', 0)
                    video_height = s.get('height', 0)
                    try:
                        vb = float(s.get('bit_rate', 0.0))
                        if vb > 0: video_bitrate = vb
                    except (ValueError, TypeError):
                        pass
                elif codec_type == 'audio':
                    channels = s.get('channels') or 2
                    channel_layout = s.get('channel_layout', '')
                    ch_desc = channel_layout if channel_layout else f"{channels}ch"
                    bitrate = self.get_audio_bitrate(channels)
                    desc = f"{codec_name} - Nyelv: {lang} - {ch_desc} (-> OPUS {bitrate})"
                    if title: desc += f" ({title})"
                    audio_streams.append((idx, desc, channels))
                elif codec_type == 'subtitle':
                    desc = f"{codec_name} - Nyelv: {lang}"
                    if title: desc += f" ({title})"
                    sub_streams.append((idx, desc))
            
            final_bitrate = video_bitrate
            if final_bitrate == 0.0:
                try:
                    final_bitrate = float(fmt.get('bit_rate', 0.0))
                except (ValueError, TypeError):
                    final_bitrate = 0.0
            
            resolution = f"{video_width}x{video_height}"
            return audio_streams, sub_streams, duration, final_bitrate, resolution
        except Exception as e:
            self.log(f"[Figyelem] Nem sikerült beolvasni a sávokat: {os.path.basename(filepath)}")
            return [], [], 0.0, 0.0, "0x0"

    def add_files(self):
        files = filedialog.askopenfilenames(
            title="Válassz videókat",
            filetypes=[("Videó fájlok", "*.mp4 *.mkv *.avi *.mov *.webm"), ("Minden fájl", "*.*")]
        )
        
        if files:
            self._process_files_for_addition(files)

    def add_directory(self):
        directory = filedialog.askdirectory(title="Válassz mappát")
        
        if directory:
            self.root.config(cursor="wait")
            self.root.update()
            
            valid_exts = ('.mp4', '.mkv', '.avi', '.mov', '.webm')
            files_to_add = []
            
            for root_dir, _, filenames in os.walk(directory):
                for filename in filenames:
                    if filename.lower().endswith(valid_exts):
                        files_to_add.append(os.path.join(root_dir, filename))
            
            if files_to_add:
                self._process_files_for_addition(files_to_add)
            else:
                self.root.config(cursor="")
                messagebox.showinfo("Infó", "Nem található támogatott videófájl a kiválasztott mappában és alkönyvtáraiban.")

    def _process_files_for_addition(self, files):
        self.root.config(cursor="wait")
        self.root.update()
        
        skipped_av1 = 0
        skipped_larger = 0
        added_new = False
        
        for f in files:
            if f in self.skipped_db:
                try:
                    if os.path.getsize(f) == self.skipped_db[f]:
                        skipped_larger += 1
                        continue
                except Exception:
                    pass
            
            if self.is_av1_video(f):
                skipped_av1 += 1
                continue

            if f not in self.files_to_process:
                audios, subs, duration, bitrate, resolution = self.get_streams_info(f)
                
                is_hun = lambda d: any(x in d.upper() for x in ["NYELV: HUN", "NYELV: HU", "MAGYAR", "HUNGARIAN"])
                
                has_hun_audio = any(is_hun(desc) for idx, desc, channels in audios)
                
                audio_vars = {idx: tk.BooleanVar(value=is_hun(desc) if has_hun_audio else (i == 0)) for i, (idx, desc, channels) in enumerate(audios)}
                sub_vars = {idx: tk.BooleanVar(value=is_hun(desc)) for idx, desc in subs}
                
                size = os.path.getsize(f)
                mod_time = os.path.getmtime(f)
                
                if bitrate == 0.0 and duration > 0:
                    bitrate = (size * 8) / duration
                
                self.files_data[f] = {
                    'audio_streams': audios,
                    'sub_streams': subs,
                    'audio_vars': audio_vars,
                    'sub_vars': sub_vars,
                    'duration': duration,
                    'bitrate': bitrate,
                    'size': size,
                    'mod_time': mod_time,
                    'resolution': resolution
                }
                
                self.files_to_process.append(f)
                added_new = True
        
        if added_new:
            self.sort_files()
            
        self.root.config(cursor="")

        if skipped_av1 > 0 or skipped_larger > 0:
            msg = []
            if skipped_av1 > 0:
                msg.append(f"{skipped_av1} db fájl kihagyva, mert már AV1 kódolású.")
            if skipped_larger > 0:
                msg.append(f"{skipped_larger} db fájl kihagyva, mert egy korábbi próbálkozás alapján a tömörített változat nagyobb lenne az eredetinél.")
            messagebox.showinfo("Kihagyott fájlok", "\n\n".join(msg))

    def sort_files(self, event=None):
        if not self.files_to_process:
            self.file_listbox.delete(0, tk.END)
            return

        crit = self.sort_crit_combo.get()
        order = self.sort_order_combo.get()
        reverse = (order == "Csökkenő")

        def sort_key(filepath):
            data = self.files_data.get(filepath, {})
            if crit == "Fájlnév":
                return os.path.basename(filepath).lower()
            elif crit == "Teljes elérési út":
                return filepath.lower()
            elif crit == "Méret":
                return data.get('size', 0)
            elif crit == "Hossz":
                return data.get('duration', 0.0)
            elif crit == "Videó bitrate":
                return data.get('bitrate', 0.0)
            elif crit == "Módosítás dátuma":
                return data.get('mod_time', 0.0)
            return filepath.lower()

        self.files_to_process.sort(key=sort_key, reverse=reverse)

        self.file_listbox.delete(0, tk.END)
        for f in self.files_to_process:
            self.file_listbox.insert(tk.END, f)
            
        self.on_file_select(None)

    def remove_files(self):
        selected = self.file_listbox.curselection()
        for index in reversed(selected):
            filepath = self.file_listbox.get(index)
            self.file_listbox.delete(index)
            
            if filepath in self.files_to_process:
                self.files_to_process.remove(filepath)
            if filepath in self.files_data:
                del self.files_data[filepath]
                
        self.on_file_select(None)

    def remove_from_listbox_by_name(self, filepath):
        items = self.file_listbox.get(0, tk.END)
        if filepath in items:
            idx = items.index(filepath)
            self.file_listbox.delete(idx)
        self.on_file_select(None)

    def on_file_select(self, event):
        for widget in self.track_inner_frame.winfo_children():
            widget.destroy()
            
        selected = self.file_listbox.curselection()
        if not selected:
            return
            
        filepath = self.file_listbox.get(selected[0])
        data = self.files_data.get(filepath)
        if not data:
            return
            
        row = 0
        if data['audio_streams']:
            ttk.Label(self.track_inner_frame, text="Hangsávok:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, pady=(5, 2))
            row += 1
            for idx, desc, channels in data['audio_streams']:
                cb = ttk.Checkbutton(self.track_inner_frame, text=f"[ID: {idx}] {desc}", variable=data['audio_vars'][idx])
                cb.grid(row=row, column=0, sticky=tk.W, padx=10, pady=2)
                row += 1
                
        if data['sub_streams']:
            ttk.Label(self.track_inner_frame, text="Feliratok:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, pady=(15, 2))
            row += 1
            for idx, desc in data['sub_streams']:
                cb = ttk.Checkbutton(self.track_inner_frame, text=f"[ID: {idx}] {desc}", variable=data['sub_vars'][idx])
                cb.grid(row=row, column=0, sticky=tk.W, padx=10, pady=2)
                row += 1
                
        if not data['audio_streams'] and not data['sub_streams']:
            ttk.Label(self.track_inner_frame, text="Nem található választható extra sáv.").grid(row=row, column=0, sticky=tk.W, pady=5)

    def request_cancel(self):
        self.cancel_requested = True
        self.cancel_btn.config(state=tk.DISABLED)
        self.log("\n[Leállítás kérése folyamatban... FFmpeg kényszerített leállítása]")
        
        if getattr(self, 'current_process', None) is not None:
            try:
                self.current_process.kill()
            except Exception:
                pass

    def start_processing(self):
        if not self.files_to_process:
            messagebox.showwarning("Figyelmeztetés", "Nincs hozzáadva videó!")
            return
        
        self.save_config()
        
        try:
            target_vmaf = float(self.vmaf_entry.get())
            tolerance = float(self.tol_entry.get())
            
            v5_str = self.vmaf_5_entry.get().strip()
            v1_str = self.vmaf_1_entry.get().strip()
            
            target_vmaf_5 = float(v5_str) if v5_str else None
            target_vmaf_1 = float(v1_str) if v1_str else None
            
            preset = self.preset_combo.get()
        except ValueError:
            messagebox.showerror("Hiba", "A VMAF értékek és a tűréshatár csak számok lehetnek!")
            return

        self.start_btn.config(state=tk.DISABLED)
        self.cancel_btn.config(state=tk.NORMAL)
        self.is_processing = True
        self.cancel_requested = False
        is_low_prio = self.low_priority_var.get()
        
        thread = threading.Thread(target=self.process_queue, args=(target_vmaf, target_vmaf_5, target_vmaf_1, tolerance, preset, is_low_prio), daemon=True)
        thread.start()

    def get_duration(self, filepath):
        try:
            startupinfo = None
            if os.name == 'nt':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                
            cmd = ["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "default=noprint_wrappers=1:nokey=1", filepath]
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, startupinfo=startupinfo)
            return float(result.stdout.strip())
        except Exception:
            return 0.0

    def process_queue(self, target_vmaf, target_vmaf_5, target_vmaf_1, tolerance, preset, is_low_prio):
        self.log("--- FELDOLGOZÁS INDÍTVA ---")
        
        for input_file in self.files_to_process[:]:
            if self.cancel_requested: break
            
            # --- ÚJ RÉSZ: Fájl meglétének ellenőrzése ---
            if not os.path.exists(input_file):
                self.log(f"\n[Kihagyva] A fájl már nem található a lemezen: {os.path.basename(input_file)}")
                
                # Eltávolítás a belső listákból és a felületről
                if input_file in self.files_to_process:
                    self.files_to_process.remove(input_file)
                if input_file in self.files_data:
                    del self.files_data[input_file]
                self.root.after(0, lambda f=input_file: self.remove_from_listbox_by_name(f))
                
                continue # Ugrás a következő fájlra
            # --------------------------------------------
                
            self.log(f"\n-> Fájl feldolgozása: {os.path.basename(input_file)}")
            
            data = self.files_data.get(input_file)
            if data and data.get('duration', 0.0) > 0:
                total_duration = data['duration']
            else:
                total_duration = self.get_duration(input_file)
                
            resolution = data.get('resolution', '0x0') if data else "0x0"
            
            map_args = ["-map", "0:v:0"]
            audio_args = ["-c:a", "libopus"]
            audio_out_idx = 0
            
            if data:
                for idx, desc, channels in data['audio_streams']:
                    if data['audio_vars'][idx].get():
                        map_args.extend(["-map", f"0:{idx}"])
                        bitrate = self.get_audio_bitrate(channels)
                        audio_args.extend([f"-b:a:{audio_out_idx}", bitrate])
                        if channels > 2:
                            audio_args.extend([f"-mapping_family:a:{audio_out_idx}", "255"])
                        self.log(f"  > Hangsáv (ID: {idx}, {channels} csatorna) -> OPUS {bitrate}")
                        audio_out_idx += 1
                for idx, desc in data['sub_streams']:
                    if data['sub_vars'][idx].get():
                        map_args.extend(["-map", f"0:{idx}"])

            success = self.find_crf_and_encode(input_file, target_vmaf, target_vmaf_5, target_vmaf_1, tolerance, preset, is_low_prio, total_duration, map_args, audio_args, resolution)
            
            if self.cancel_requested:
                self.log(f"[MEGSZAKÍTVA] A folyamat leállítva: {os.path.basename(input_file)}")
                break
                
            if success:
                self.log(f"[KÉSZ] Fájl feldolgozva: {os.path.basename(input_file)}")
            else:
                self.log(f"[HIBA] Nem sikerült feldolgozni: {os.path.basename(input_file)}")
            
            if not self.cancel_requested:
                self.files_to_process.remove(input_file)
                if input_file in self.files_data:
                    del self.files_data[input_file]
                self.root.after(0, lambda f=input_file: self.remove_from_listbox_by_name(f))

        self.log("\n--- FELDOLGOZÁS VÉGE ---")
        self.root.after(0, self.reset_ui)
        self.is_processing = False

    def reset_ui(self):
        self.start_btn.config(state=tk.NORMAL)
        self.cancel_btn.config(state=tk.DISABLED)
        self.update_progress(0.0, None)

    def predict_metric_at(self, tried_crfs, crf, idx, value, target_crf):
        """
        Egy VMAF-mutató becsült értéke target_crf-nél, kizárólag az aktuális
        fájlon ténylegesen megmért CRF-ek alapján (lineáris becslés).
        idx: a tried_crfs tuple indexe -> 0 = átlag, 1 = 1%, 2 = 5%.
        - Ha van már mért CRF a jelenlegi fölött (tipikusan egy elbukott),
          a kettő között interpolálunk.
        - Különben a legközelebbi alatta lévő mérésből extrapolálunk.
        - Ha nincs második mérés, None-t adunk vissza: ilyenkor nincs mire
          alapozni a becslést, így a próbakódolást nem tiltjuk le.
        """
        above = [c for c, vals in tried_crfs.items() if c > crf and vals[idx] is not None]
        if above:
            ref = min(above)
        else:
            below = [c for c, vals in tried_crfs.items() if c < crf and vals[idx] is not None]
            if not below:
                return None
            ref = max(below)

        slope = (tried_crfs[ref][idx] - value) / (ref - crf)
        return value + slope * (target_crf - crf)

    def find_crf_and_encode(self, input_file, target_vmaf, target_vmaf_5, target_vmaf_1, tolerance, preset, is_low_prio, total_duration, map_args, audio_args, resolution):
        min_crf = 1
        max_crf = 46
        
        current_crf = self.estimate_starting_crf(target_vmaf, preset, resolution)
        self.log(f"  [Info] Becsült kezdő CRF a korábbi kódolások alapján: {current_crf}")
        
        temp_encode = input_file + ".temp.mkv"
        vmaf_log = "temp_vmaf_log.json" 
        
        history = []
        max_iterations = 20
        iteration = 0

        # A cél: az átlagos VMAF legyen minél közelebb a target_vmaf értékhez
        # felülről, miközben az opcionális 1% és 5% minimumok is teljesülnek.
        # Ezért az első megfelelő eredménynél NEM állunk meg.
        best_temp_encode = input_file + ".best.mkv"
        best_vmaf = None
        best_vmaf_1 = None
        best_vmaf_5 = None
        best_crf = None
        best_gap = None
        found_valid = False

        # Már kipróbált CRF értékek eredményeinek gyorsítótára: crf -> (átlag, 1%, 5%).
        # Ez akadályozza meg, hogy egy korábban már megmért CRF-et újra kódoljunk
        # (pl. amikor a finomító "+1" lépés visszaérkezik egy korábban elutasított CRF-hez).
        tried_crfs = {}

        # Nem szükséges korábbi maradék best fájl.
        if os.path.exists(best_temp_encode):
            try:
                os.remove(best_temp_encode)
            except Exception:
                pass

        while iteration < max_iterations:
            if self.cancel_requested:
                break

            iteration += 1
            from_cache = current_crf in tried_crfs

            if from_cache:
                vmaf_score, vmaf_1, vmaf_5 = tried_crfs[current_crf]
                self.log(
                    f"  [Iteráció {iteration}] CRF {current_crf} már szerepel a korábbi "
                    "próbák között -> újrafelhasznált eredmény, nincs újrakódolás."
                )
            else:
                self.log(f"  [Iteráció {iteration}] Próba kódolás CRF {current_crf} értékkel (várj türelemmel)...")

                encode_cmd = [
                    "ffmpeg", "-y", "-i", input_file
                ] + map_args + [
                    "-c:v", "libsvtav1", "-preset", preset, "-crf", str(current_crf),
                ] + audio_args + [
                    "-c:s", "copy", temp_encode
                ]

                success, err_log = self.run_command_with_progress(encode_cmd, total_duration, is_low_prio)

                if self.cancel_requested:
                    if os.path.exists(temp_encode): os.remove(temp_encode)
                    if os.path.exists(best_temp_encode): os.remove(best_temp_encode)
                    return False

                if not success or not os.path.exists(temp_encode):
                    self.log("  [Hiba] A kódolás sikertelen volt.")
                    self.log(f"  > FFmpeg hiba részletek:\n{err_log}")
                    if os.path.exists(best_temp_encode): os.remove(best_temp_encode)
                    return False

                self.log("  Kódolás kész. VMAF számolása a teljes videón...")

                # --- Felgyorsított VMAF számolás ---
                threads = max(1, (os.cpu_count() or 4) - 1)

                vmaf_cmd = [
                    "ffmpeg", "-y", "-i", temp_encode, "-i", input_file,
                    "-lavfi", f"libvmaf=log_fmt=json:log_path={vmaf_log}:n_threads={threads}:n_subsample=5",
                    "-f", "null", "-"
                ]

                success, err_log = self.run_command_with_progress(vmaf_cmd, total_duration, is_low_prio)

                if self.cancel_requested:
                    if os.path.exists(temp_encode): os.remove(temp_encode)
                    if os.path.exists(vmaf_log): os.remove(vmaf_log)
                    if os.path.exists(best_temp_encode): os.remove(best_temp_encode)
                    return False

                if not success:
                    self.log("  [Hiba] A VMAF parancs elszállt.")
                    self.log(f"  > FFmpeg hiba részletek:\n{err_log}") 
                    if os.path.exists(temp_encode): os.remove(temp_encode)
                    if os.path.exists(best_temp_encode): os.remove(best_temp_encode)
                    return False

                parsed = self.parse_vmaf(vmaf_log)
                if parsed is None:
                    self.log("  [Hiba] A JSON fájl nem olvasható vagy nem jött létre.")
                    if os.path.exists(temp_encode): os.remove(temp_encode)
                    if os.path.exists(best_temp_encode): os.remove(best_temp_encode)
                    return False

                vmaf_score, vmaf_1, vmaf_5 = parsed
                tried_crfs[current_crf] = (vmaf_score, vmaf_1, vmaf_5)
                self.add_to_history(vmaf_score, current_crf, preset, resolution)

            log_msg = f"  > Eredmény: CRF {current_crf} -> Átlag: {vmaf_score:.2f}"
            if vmaf_5 is not None:
                log_msg += f", 5%: {vmaf_5:.2f}"
            if vmaf_1 is not None:
                log_msg += f", 1%: {vmaf_1:.2f}"
            self.log(log_msg)

            history.append((current_crf, vmaf_score, vmaf_1, vmaf_5))

            mean_ok = vmaf_score >= target_vmaf
            low_1_ok = (
                target_vmaf_1 is None
                or (vmaf_1 is not None and vmaf_1 >= target_vmaf_1)
            )
            low_5_ok = (
                target_vmaf_5 is None
                or (vmaf_5 is not None and vmaf_5 >= target_vmaf_5)
            )
            all_ok = mean_ok and low_1_ok and low_5_ok

            if all_ok:
                found_valid = True
                gap = vmaf_score - target_vmaf

                # Mindig a célhoz legközelebbi, még minden minimumot teljesítő
                # eredményt tartjuk meg. Holtversenynél a magasabb CRF-et választjuk.
                is_better = (
                    best_gap is None
                    or gap < best_gap - 1e-9
                    or (abs(gap - best_gap) <= 1e-9 and current_crf > best_crf)
                )

                if is_better and not from_cache:
                    if os.path.exists(best_temp_encode):
                        try:
                            os.remove(best_temp_encode)
                        except Exception:
                            pass

                    os.replace(temp_encode, best_temp_encode)
                    best_vmaf = vmaf_score
                    best_vmaf_1 = vmaf_1
                    best_vmaf_5 = vmaf_5
                    best_crf = current_crf
                    best_gap = gap

                    self.log(
                        f"  [Új legjobb] CRF {best_crf} -> Átlag: {best_vmaf:.2f} "
                        f"(célkülönbség: +{best_gap:.2f})"
                    )
                elif is_better and from_cache:
                    # A gyakorlatban nem fordulhat elő: egy már kipróbált CRF mindig
                    # ugyanazt az eredményt adja, mint első alkalommal, és a keresés
                    # soha nem lép vissza egy már sikeresnek bizonyult CRF-hez. Biztonsági
                    # tartalékként mindenesetre nem írjuk felül a legjobbat fájl nélkül.
                    self.log(
                        f"  [Figyelem] CRF {current_crf} gyorsítótárazott eredménye jobb lenne, "
                        "de a kódolt fájl már nem érhető el újrafelhasználásra."
                    )
                else:
                    if os.path.exists(temp_encode):
                        os.remove(temp_encode)

                # Mivel most minden küszöb teljesült, még próbálunk nagyobb CRF-et.
                # A cél a lehető legmagasabb CRF, amely még éppen megfelelő.
                if current_crf >= max_crf:
                    self.log("  [Info] Elértük a maximális CRF-et.")
                    break

                next_crf = current_crf + 1

                # Mielőtt egy teljes kódolást + VMAF-ot rászánnánk: a már megmért
                # CRF-ek alapján megbecsüljük mindhárom mutatót a következő CRF-nél.
                # Nem csak az átlag tartalékát nézzük, hanem a legszűkebb küszöböt is
                # (pl. ha az 5% épp csak 0.01-gyel van felette, és egy nagyobb CRF
                # már elbukott rajta, a +1 próba szinte biztosan felesleges).
                predicted_fail = []
                for name, idx, value, threshold in (
                    ("átlag", 0, vmaf_score, target_vmaf),
                    ("5%", 2, vmaf_5, target_vmaf_5),
                    ("1%", 1, vmaf_1, target_vmaf_1),
                ):
                    if threshold is None or value is None:
                        continue
                    predicted = self.predict_metric_at(tried_crfs, current_crf, idx, value, next_crf)
                    if predicted is not None and predicted < threshold:
                        predicted_fail.append(f"{name} ~{predicted:.2f} < {threshold:.2f}")

                if predicted_fail:
                    self.log(
                        f"  [Határ] CRF {next_crf} a mért adatok alapján már nem teljesítené: "
                        f"{', '.join(predicted_fail)}. A legjobb megfelelő CRF: {best_crf}."
                    )
                    break

                self.log(
                    f"  [Info] Minden küszöb teljesült. Következő próba: CRF {next_crf}, "
                    "hátha az is megfelel (kisebb fájl)."
                )
                current_crf = next_crf

            else:
                # Ha már találtunk megfelelő jelöltet, és egy nagyobb CRF most
                # nem teljesíti valamelyik küszöböt, akkor elértük a határt.
                # A korábbi best_temp_encode marad a végleges jelölt.
                if found_valid:
                    failed = []
                    if not mean_ok:
                        failed.append("átlag")
                    if not low_5_ok:
                        failed.append("5%")
                    if not low_1_ok:
                        failed.append("1%")

                    self.log(
                        f"  [Határ] CRF {current_crf} már nem teljesíti: "
                        f"{', '.join(failed)}. A legjobb megfelelő CRF: {best_crf}."
                    )
                    if os.path.exists(temp_encode):
                        os.remove(temp_encode)
                    break

                # Még nincs megfelelő eredmény -> a meglévő keresési logika szerint
                # csökkentjük a CRF-et, amíg minden minimum nem teljesül.
                if mean_ok and not (low_1_ok and low_5_ok):
                    gap_1 = (
                        target_vmaf_1 - vmaf_1
                        if (
                            target_vmaf_1 is not None
                            and vmaf_1 is not None
                            and not low_1_ok
                        )
                        else 0
                    )
                    gap_5 = (
                        target_vmaf_5 - vmaf_5
                        if (
                            target_vmaf_5 is not None
                            and vmaf_5 is not None
                            and not low_5_ok
                        )
                        else 0
                    )
                    max_gap = max(gap_1, gap_5)

                    jump_steps = 1
                    if len(history) >= 2:
                        crf_curr, _, v1_curr, v5_curr = history[-1]
                        crf_prev, _, v1_prev, v5_prev = history[-2]

                        if (
                            gap_1 >= gap_5
                            and v1_curr is not None
                            and v1_prev is not None
                            and crf_curr != crf_prev
                        ):
                            slope = (v1_curr - v1_prev) / (crf_curr - crf_prev)
                        elif (
                            gap_5 > gap_1
                            and v5_curr is not None
                            and v5_prev is not None
                            and crf_curr != crf_prev
                        ):
                            slope = (v5_curr - v5_prev) / (crf_curr - crf_prev)
                        else:
                            slope = 0

                        if slope < -0.1:
                            jump_steps = max(
                                1, min(5, int(round(max_gap / abs(slope))))
                            )
                        else:
                            jump_steps = max(
                                1, min(5, int(round(max_gap / 0.45)))
                            )
                    else:
                        jump_steps = max(1, min(5, int(round(max_gap / 0.45))))

                    self.log(
                        f"  [Info] Átlag OK/magas, de alsó 1%/5% lemarad "
                        f"(~{max_gap:.2f}). CRF csökkentése (-{jump_steps})..."
                    )
                    next_crf = current_crf - jump_steps
                else:
                    if len(history) >= 2:
                        crf1, vmaf1 = history[-1][0], history[-1][1]
                        crf2, vmaf2 = history[-2][0], history[-2][1]

                        if crf1 != crf2:
                            slope = (vmaf1 - vmaf2) / (crf1 - crf2)
                        else:
                            slope = 0

                        if slope < -0.1:
                            jump = (target_vmaf - vmaf1) / slope
                            jump = max(-6, min(6, jump))
                            next_crf = int(round(crf1 + jump))
                        else:
                            next_crf = current_crf - 2 if vmaf_score < target_vmaf else current_crf + 2
                    else:
                        next_crf = current_crf - 4 if vmaf_score < target_vmaf else current_crf + 4

                current_crf = max(min_crf, min(max_crf, next_crf))

            if os.path.exists(vmaf_log):
                os.remove(vmaf_log)

        if os.path.exists(vmaf_log):
            os.remove(vmaf_log)

        if self.cancel_requested:
            if os.path.exists(temp_encode):
                os.remove(temp_encode)
            if os.path.exists(best_temp_encode):
                os.remove(best_temp_encode)
            return False

        # Ha találtunk megfelelő jelöltet, a legjobb (célhoz legközelebbi)
        # kódolást használjuk. Ha nem, nincs elfogadható eredmény.
        if not found_valid or not os.path.exists(best_temp_encode):
            if os.path.exists(temp_encode):
                os.remove(temp_encode)
            self.log("  [Hiba] Nem sikerült olyan CRF-et találni, amely minden VMAF minimumcélt teljesíti.")
            return False

        try:
            original_size = os.path.getsize(input_file)
            new_size = os.path.getsize(best_temp_encode)

            self.log(f"  > Végleges választás: CRF {best_crf}")
            self.log(
                f"  > Végleges VMAF: átlag {best_vmaf:.2f}, "
                f"5% {best_vmaf_5:.2f}" if best_vmaf_5 is not None
                else f"  > Végleges VMAF: átlag {best_vmaf:.2f}"
            )
            if best_vmaf_1 is not None:
                self.log(f"  > Végleges VMAF 1%: {best_vmaf_1:.2f}")
            self.log(f"  > Eredeti méret: {self.format_size(original_size)}")
            self.log(f"  > Új méret: {self.format_size(new_size)}")

            if new_size < original_size:
                saved_space = original_size - new_size
                self.log(
                    f"  > Méretcsökkenés: {self.format_size(saved_space)}. "
                    "Eredeti fájl cseréje a tömörítettre..."
                )

                os.remove(input_file)
                new_final_name = os.path.splitext(input_file)[0] + ".mkv"
                shutil.move(best_temp_encode, new_final_name)
                return True
            else:
                increased_space = new_size - original_size
                self.log(
                    f"  [Info] Az új videó {self.format_size(increased_space)}-val NAGYOBB "
                    "(vagy egyenlő), mint az eredeti!"
                )
                self.log(
                    "  [Info] A fájlcsere megszakítva. Az eredeti videó megmarad."
                )
                os.remove(best_temp_encode)
                self.mark_as_skipped(input_file)
                return True

        except Exception as e:
            self.log(f"  [Kritikus Hiba] Fájl művelet sikertelen: {e}")
            if os.path.exists(temp_encode):
                os.remove(temp_encode)
            if os.path.exists(best_temp_encode):
                os.remove(best_temp_encode)
            return False

    def run_command_with_progress(self, cmd, total_duration, is_low_prio):
        startupinfo = None
        creationflags = 0
        
        if os.name == 'nt':
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            if is_low_prio:
                creationflags = 0x00004000
        else:
            if is_low_prio:
                cmd = ["nice", "-n", "10"] + cmd

        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                universal_newlines=True,
                startupinfo=startupinfo,
                creationflags=creationflags,
                encoding='utf-8',
                errors='replace'
            )
            
            self.current_process = process 
            
            time_regex = re.compile(r"time=(\d+):(\d+):(\d+\.\d+)")
            start_time = time.time()
            output_tail = []

            for line in process.stdout:
                output_tail.append(line.strip())
                if len(output_tail) > 15:
                    output_tail.pop(0)

                if self.cancel_requested:
                    try:
                        process.kill()
                    except Exception:
                        pass
                    break

                match = time_regex.search(line)
                if match and total_duration > 0:
                    hours = float(match.group(1))
                    minutes = float(match.group(2))
                    seconds = float(match.group(3))
                    current_time = (hours * 3600) + (minutes * 60) + seconds
                    
                    progress = (current_time / total_duration) * 100
                    progress = min(progress, 100.0)
                    
                    elapsed_real_time = time.time() - start_time
                    if progress > 0.5:
                        total_estimated_time = (elapsed_real_time / progress) * 100
                        eta_seconds = total_estimated_time - elapsed_real_time
                    else:
                        eta_seconds = None
                        
                    self.root.after(0, self.update_progress, progress, eta_seconds)
            
            process.wait()
            self.current_process = None 
            self.root.after(0, self.update_progress, 0.0, None)
            
            if self.cancel_requested:
                return False, "Felhasználó által megszakítva"
            
            if process.returncode != 0:
                error_msg = "\n".join(output_tail)
                return False, error_msg
                
            return True, ""
        except Exception as e:
            self.current_process = None
            return False, str(e)

    def parse_vmaf(self, log_path):
        try:
            with open(log_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
                mean_vmaf = data['pooled_metrics']['vmaf']['mean']
                
                frame_scores = []
                for frame in data.get('frames', []):
                    if 'metrics' in frame and 'vmaf' in frame['metrics']:
                        frame_scores.append(frame['metrics']['vmaf'])
                
                low_1 = None
                low_5 = None
                
                if frame_scores:
                    frame_scores.sort()
                    idx_1 = max(0, int(len(frame_scores) * 0.01) - 1 if len(frame_scores) * 0.01 >= 1 else 0)
                    idx_5 = max(0, int(len(frame_scores) * 0.05) - 1 if len(frame_scores) * 0.05 >= 1 else 0)
                    
                    low_1 = frame_scores[idx_1]
                    low_5 = frame_scores[idx_5]
                
                return mean_vmaf, low_1, low_5
        except Exception as e:
            self.log(f"  [Hiba a VMAF JSON olvasásakor: {e}]")
            return None

if __name__ == "__main__":
    root = tk.Tk()
    app = AV1VmafApp(root)
    root.mainloop()