"""
AV1 VMAF újratömörítő
=====================

Tkinter felület, amely a kiválasztott videókat SVT-AV1 kodekkel tömöríti újra.
A CRF értékét próbakódolásokkal és VMAF-mérésekkel keresi meg: a cél az, hogy
az átlagos VMAF (és opcionálisan az alsó 1% / 5% érték) még teljesítse a
megadott minimumot, a fájl pedig a lehető legkisebb legyen. A kijelölt
hangsávok OPUS-ra konvertálódnak, a kijelölt feliratok változatlanul
átmásolódnak. Ha az eredmény kisebb az eredetinél, lecseréli azt (.mkv).

Szükséges: ffmpeg (libsvtav1 és libvmaf támogatással) és ffprobe a PATH-on.

A fájl felépítése:
    1. Konstansok
    2. Általános segédfüggvények
    3. Adatmodell
    4. Tartós tárolás (kihagyott fájlok, kódolási előzmények)
    5. ffprobe / ffmpeg segédfüggvények
    6. CRF-becslés segédfüggvényei
    7. Transcoder – a GUI-tól független feldolgozó logika
    8. AV1VmafApp – a Tkinter felület
"""

from __future__ import annotations

import collections
import contextlib
import json
import os
import queue
import re
import subprocess
import threading
import time
import tkinter as tk
from collections.abc import Callable
from dataclasses import dataclass
from tkinter import filedialog, messagebox, ttk
from typing import NamedTuple

# =============================================================================
# 1. Konstansok
# =============================================================================

CONFIG_FILE = "av1_vmaf_config.json"
SKIPPED_DB_FILE = "av1_skipped_db.json"
HISTORY_DB_FILE = "av1_history_db.json"
# Szándékosan relatív útvonal: a libvmaf szűrő paraméterlistájában a ":"
# elválasztó, így egy meghajtóbetűs Windows-útvonal elrontaná a szűrőt.
VMAF_LOG_FILE = "temp_vmaf_log.json"

IS_WINDOWS = os.name == "nt"

VIDEO_EXTENSIONS = (".mp4", ".mkv", ".avi", ".mov", ".webm")
HUNGARIAN_MARKERS = ("NYELV: HUN", "NYELV: HU", "MAGYAR", "HUNGARIAN")

HISTORY_LIMIT = 500             # ennyi korábbi mérést őrzünk meg a kezdő CRF becsléséhez
DEFAULT_START_CRF = 30
START_CRF_MIN, START_CRF_MAX = 15, 45
START_CRF_NEIGHBOURS = 5        # a célhoz legközelebbi ennyi korábbi mérés CRF-átlaga

MIN_CRF, MAX_CRF = 1, 46
MAX_ITERATIONS = 20

# CRF-lépés heurisztikák (a meredekség mértékegysége: VMAF-pont / CRF-lépés)
STEEP_SLOPE = -0.1              # ennél meredekebb esésnél a mért meredekségből számolunk ugrást
FALLBACK_LOW_SLOPE = 0.45       # feltételezett esés az alsó 1%/5%-nál, ha nincs használható mérés
MAX_LOW_JUMP = 5
MAX_MEAN_JUMP = 6
FIRST_MEAN_STEP = 4             # első elbukott mérés után (még nincs meredekség)
FALLBACK_MEAN_STEP = 2          # ha a meredekség nem használható
GAP_EPSILON = 1e-9

UI_POLL_MS = 100
OUTPUT_TAIL_LINES = 15          # hiba esetén ennyi utolsó ffmpeg-sort naplózunk

SORT_ASCENDING, SORT_DESCENDING = "Növekvő", "Csökkenő"

DEFAULT_CONFIG = {
    "vmaf": "93.0",
    "vmaf_5": "",
    "vmaf_1": "",
    "tolerance": "1.0",
    "preset": "6",
    "low_priority": True,
    "sort_crit": "Fájlnév",
    "sort_order": SORT_ASCENDING,
}

# VmafScores mezőnév -> felirat a naplóban (a sorrend a naplózás sorrendje)
METRIC_LABELS = {"mean": "átlag", "low_5": "5%", "low_1": "1%"}

FFMPEG_TIME_RE = re.compile(r"time=(\d+):(\d+):(\d+\.\d+)")


# =============================================================================
# 2. Általános segédfüggvények
# =============================================================================

def format_time(seconds: float | None) -> str:
    if seconds is None or seconds < 0:
        return "--:--:--"
    hours, rest = divmod(int(seconds), 3600)
    minutes, secs = divmod(rest, 60)
    return f"{hours:02d}:{minutes:02d}:{secs:02d}"


def format_size(size_in_bytes: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if size_in_bytes < 1024.0:
            return f"{size_in_bytes:.2f} {unit}"
        size_in_bytes /= 1024.0
    return f"{size_in_bytes:.2f} TB"


def clamp(value, low, high):
    return max(low, min(high, value))


def to_float(value, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def optional_float(text: str) -> float | None:
    """Üres szövegre None, egyébként float (hibás számnál ValueError)."""
    text = text.strip()
    return float(text) if text else None


def safe_remove(*paths: str) -> None:
    """Ideiglenes fájlok törlése; a hiányzó vagy nem törölhető fájlt figyelmen kívül hagyja."""
    for path in paths:
        with contextlib.suppress(OSError):
            os.remove(path)


def load_json(path: str, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path: str, data) -> None:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)
    except OSError:
        pass


def is_hungarian(description: str) -> bool:
    text = description.upper()
    return any(marker in text for marker in HUNGARIAN_MARKERS)


def audio_bitrate_for(channels: int) -> str:
    return "96k" if channels <= 2 else "192k"


def find_video_files(directory: str) -> list[str]:
    """A támogatott kiterjesztésű videók a könyvtárban és alkönyvtáraiban."""
    return [
        os.path.join(root_dir, filename)
        for root_dir, _, filenames in os.walk(directory)
        for filename in filenames
        if filename.lower().endswith(VIDEO_EXTENSIONS)
    ]


def replace_original(original: str, encoded: str) -> None:
    """
    Az eredeti videó helyére teszi a kódolt változatot (.mkv kiterjesztéssel).
    Előbb a kódolt fájl kerül a végleges helyére, és csak utána törlődik az
    eredeti, így egy sikertelen áthelyezés nem jár adatvesztéssel.
    """
    final_path = os.path.splitext(original)[0] + ".mkv"
    os.replace(encoded, final_path)
    if os.path.exists(original) and not os.path.samefile(original, final_path):
        os.remove(original)


# =============================================================================
# 3. Adatmodell
# =============================================================================

@dataclass(frozen=True)
class Track:
    """Egy választható hang- vagy feliratsáv."""
    index: int              # ffprobe stream index (-map 0:<index>)
    description: str
    channels: int = 0       # csak hangsávnál értelmezett


@dataclass
class MediaInfo:
    """Az ffprobe-bal kiolvasott, feldolgozáshoz szükséges adatok."""
    video_codec: str = ""
    resolution: str = "0x0"
    duration: float = 0.0
    bitrate: float = 0.0
    audio_streams: tuple[Track, ...] = ()
    sub_streams: tuple[Track, ...] = ()


@dataclass
class FileEntry:
    """Egy feldolgozásra váró fájl a listában."""
    path: str
    info: MediaInfo
    size: int
    mod_time: float
    bitrate: float
    # Sávindex -> megtartjuk-e. Sima dict (nem tk-változó), hogy a
    # feldolgozó szál is biztonságosan olvashassa.
    selected_audio: dict[int, bool]
    selected_subs: dict[int, bool]

    @classmethod
    def from_file(cls, path: str, info: MediaInfo) -> FileEntry:
        size = os.path.getsize(path)
        bitrate = info.bitrate
        if bitrate == 0.0 and info.duration > 0:
            bitrate = size * 8 / info.duration

        # Alapértelmezés: a magyar hangsáv(ok), ha van ilyen, különben az első;
        # feliratból csak a magyar(ok).
        has_hungarian_audio = any(is_hungarian(t.description) for t in info.audio_streams)
        selected_audio = {
            t.index: is_hungarian(t.description) if has_hungarian_audio else i == 0
            for i, t in enumerate(info.audio_streams)
        }
        selected_subs = {t.index: is_hungarian(t.description) for t in info.sub_streams}

        return cls(path, info, size, os.path.getmtime(path), bitrate, selected_audio, selected_subs)


SORT_KEYS: dict[str, Callable[[FileEntry], object]] = {
    "Méret": lambda e: e.size,
    "Fájlnév": lambda e: os.path.basename(e.path).lower(),
    "Teljes elérési út": lambda e: e.path.lower(),
    "Hossz": lambda e: e.info.duration,
    "Videó bitrate": lambda e: e.bitrate,
    "Módosítás dátuma": lambda e: e.mod_time,
}


class VmafScores(NamedTuple):
    mean: float
    low_1: float | None      # alsó 1% (None, ha nincs képkockánkénti adat)
    low_5: float | None      # alsó 5%


@dataclass(frozen=True)
class EncodeSettings:
    target_vmaf: float
    target_vmaf_5: float | None
    target_vmaf_1: float | None
    tolerance: float            # a felületen megadható, de a CRF-keresés jelenleg nem használja
    preset: str
    low_priority: bool

    def threshold(self, metric: str) -> float | None:
        return {"mean": self.target_vmaf, "low_1": self.target_vmaf_1, "low_5": self.target_vmaf_5}[metric]

    def failed_metrics(self, scores: VmafScores) -> list[str]:
        """Azon mutatók (VmafScores mezőnevek), amelyek nem érik el a küszöbüket."""
        failed = []
        for metric in METRIC_LABELS:
            value, threshold = getattr(scores, metric), self.threshold(metric)
            if threshold is not None and (value is None or value < threshold):
                failed.append(metric)
        return failed

    def shortfall(self, scores: VmafScores, metric: str) -> float:
        """Mennyivel marad el a mutató a küszöbtől (0, ha teljesül vagy nem mérhető)."""
        value, threshold = getattr(scores, metric), self.threshold(metric)
        if threshold is None or value is None or value >= threshold:
            return 0.0
        return threshold - value


@dataclass(frozen=True)
class Candidate:
    """Az eddigi legjobb, minden küszöböt teljesítő próbakódolás."""
    crf: int
    scores: VmafScores
    gap: float                  # átlag VMAF - cél (>= 0)


@dataclass(frozen=True)
class EncodeJob:
    """Egy fájl kódolásához szükséges összes paraméter."""
    input_file: str
    settings: EncodeSettings
    duration: float
    map_args: list[str]
    audio_args: list[str]
    resolution: str

    @property
    def temp_path(self) -> str:
        return self.input_file + ".temp.mkv"

    @property
    def best_path(self) -> str:
        return self.input_file + ".best.mkv"


class TranscodeError(Exception):
    """Egy kódolási/mérési lépés meghiúsult."""

    def __init__(self, message: str, details: str = ""):
        super().__init__(message)
        self.details = details


class _Cancelled(Exception):
    """A felhasználó leállította a feldolgozást."""


# =============================================================================
# 4. Tartós tárolás
# =============================================================================

class SkippedFiles:
    """
    Azon fájlok (útvonal -> méret), amelyeknél a tömörített változat nem lett
    kisebb az eredetinél. Amíg a fájl mérete nem változik, kihagyjuk őket.
    """

    def __init__(self, path: str = SKIPPED_DB_FILE):
        self._path = path
        data = load_json(path, {})
        self._sizes: dict[str, int] = data if isinstance(data, dict) else {}

    def is_skipped(self, filepath: str) -> bool:
        if filepath not in self._sizes:
            return False
        try:
            return os.path.getsize(filepath) == self._sizes[filepath]
        except OSError:
            return False

    def mark(self, filepath: str) -> None:
        try:
            self._sizes[filepath] = os.path.getsize(filepath)
        except OSError:
            return
        save_json(self._path, self._sizes)


class EncodeHistory:
    """Korábbi mérések (CRF -> átlag VMAF) naplója a kezdő CRF becsléséhez."""

    def __init__(self, path: str = HISTORY_DB_FILE, limit: int = HISTORY_LIMIT):
        self._path = path
        self._limit = limit
        data = load_json(path, [])
        self._records: list[dict] = [r for r in data if isinstance(r, dict)] if isinstance(data, list) else []

    def add(self, vmaf: float, crf: int, preset: str, resolution: str) -> None:
        self._records.append({"vmaf": vmaf, "crf": crf, "preset": preset, "resolution": resolution})
        self._records = self._records[-self._limit:]
        save_json(self._path, self._records)

    def estimate_starting_crf(self, target_vmaf: float, preset: str, resolution: str) -> int:
        """
        A célhoz legközelebbi korábbi mérések CRF-átlaga. Ha van ilyen, az azonos
        presetű, azon belül az azonos felbontású méréseket részesíti előnyben.
        """
        if not self._records:
            return DEFAULT_START_CRF

        candidates = [r for r in self._records if r.get("preset") == preset] or self._records
        candidates = [r for r in candidates if r.get("resolution") == resolution] or candidates

        closest = sorted(candidates, key=lambda r: abs(r.get("vmaf", 93.0) - target_vmaf))
        closest = closest[:START_CRF_NEIGHBOURS]
        avg_crf = sum(r.get("crf", DEFAULT_START_CRF) for r in closest) / len(closest)
        return clamp(round(avg_crf), START_CRF_MIN, START_CRF_MAX)


# =============================================================================
# 5. ffprobe / ffmpeg segédfüggvények
# =============================================================================

def subprocess_kwargs(low_priority: bool = False) -> dict:
    """Windows alatt elrejti a konzolablakot, és kérésre alacsony prioritással indít."""
    if not IS_WINDOWS:
        return {}
    startupinfo = subprocess.STARTUPINFO()
    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    kwargs = {"startupinfo": startupinfo}
    if low_priority:
        kwargs["creationflags"] = subprocess.BELOW_NORMAL_PRIORITY_CLASS
    return kwargs


def run_ffprobe(args: list[str]) -> str:
    result = subprocess.run(
        ["ffprobe", "-v", "error", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        **subprocess_kwargs(),
    )
    return result.stdout


def _with_title(description: str, title: str) -> str:
    return f"{description} ({title})" if title else description


def _stream_labels(stream: dict) -> tuple[str, str, str]:
    tags = stream.get("tags", {})
    codec = stream.get("codec_name", "unknown").upper()
    return codec, tags.get("language", "und").upper(), tags.get("title", "")


def _audio_track(stream: dict) -> Track:
    codec, lang, title = _stream_labels(stream)
    channels = stream.get("channels") or 2
    layout = stream.get("channel_layout") or f"{channels}ch"
    desc = f"{codec} - Nyelv: {lang} - {layout} (-> OPUS {audio_bitrate_for(channels)})"
    return Track(stream.get("index"), _with_title(desc, title), channels)


def _subtitle_track(stream: dict) -> Track:
    codec, lang, title = _stream_labels(stream)
    return Track(stream.get("index"), _with_title(f"{codec} - Nyelv: {lang}", title))


def probe_media(path: str) -> MediaInfo | None:
    """Stream- és formátuminformációk ffprobe-bal. None, ha nem olvasható."""
    try:
        raw = json.loads(run_ffprobe(["-print_format", "json", "-show_format", "-show_streams", path]))
    except (OSError, ValueError):
        return None

    fmt = raw.get("format", {})
    video = None
    audio_streams, sub_streams = [], []
    for stream in raw.get("streams", []):
        codec_type = stream.get("codec_type")
        if codec_type == "video":
            if video is None:           # csak az első videósáv számít (-map 0:v:0)
                video = stream
        elif codec_type == "audio":
            audio_streams.append(_audio_track(stream))
        elif codec_type == "subtitle":
            sub_streams.append(_subtitle_track(stream))

    info = MediaInfo(
        duration=to_float(fmt.get("duration")),
        audio_streams=tuple(audio_streams),
        sub_streams=tuple(sub_streams),
    )
    video_bitrate = 0.0
    if video is not None:
        info.video_codec = str(video.get("codec_name", "")).lower()
        info.resolution = f"{video.get('width', 0)}x{video.get('height', 0)}"
        video_bitrate = to_float(video.get("bit_rate"))
    info.bitrate = video_bitrate if video_bitrate > 0 else to_float(fmt.get("bit_rate"))
    return info


def probe_duration(path: str) -> float:
    try:
        output = run_ffprobe(["-show_entries", "format=duration", "-of", "default=noprint_wrappers=1:nokey=1", path])
        return float(output.strip())
    except (OSError, ValueError):
        return 0.0


def parse_ffmpeg_time(line: str) -> float | None:
    """Az ffmpeg állapotsorának "time=HH:MM:SS.xx" értéke másodpercben."""
    match = FFMPEG_TIME_RE.search(line)
    if not match:
        return None
    hours, minutes, seconds = match.groups()
    return int(hours) * 3600 + int(minutes) * 60 + float(seconds)


def _low_percentile(sorted_scores: list[float], fraction: float) -> float:
    return sorted_scores[max(0, int(len(sorted_scores) * fraction) - 1)]


def parse_vmaf_log(path: str) -> VmafScores:
    """A libvmaf JSON naplójából az átlag, valamint az alsó 1% és 5% képkocka-érték."""
    with open(path, encoding="utf-8") as f:
        data = json.load(f)

    mean = data["pooled_metrics"]["vmaf"]["mean"]
    frame_scores = sorted(
        frame["metrics"]["vmaf"]
        for frame in data.get("frames", [])
        if "vmaf" in frame.get("metrics", {})
    )
    if not frame_scores:
        return VmafScores(mean, None, None)
    return VmafScores(mean, _low_percentile(frame_scores, 0.01), _low_percentile(frame_scores, 0.05))


# =============================================================================
# 6. CRF-becslés segédfüggvényei
# =============================================================================

def predict_metric(measurements: dict[int, VmafScores], crf: int, metric: str, target_crf: int) -> float | None:
    """
    Egy VMAF-mutató becsült értéke target_crf-nél, kizárólag az aktuális fájlon
    ténylegesen megmért CRF-ek alapján (lineáris becslés):
    - Ha van már mért CRF a jelenlegi fölött (tipikusan egy elbukott), a kettő
      között interpolálunk.
    - Különben a legközelebbi alatta lévő mérésből extrapolálunk.
    - Ha nincs második mérés, None: ilyenkor nincs mire alapozni a becslést,
      így a próbakódolást nem tiltjuk le.
    """
    value = getattr(measurements[crf], metric)
    known = {c: getattr(s, metric) for c, s in measurements.items() if getattr(s, metric) is not None}
    above = [c for c in known if c > crf]
    below = [c for c in known if c < crf]
    if above:
        ref = min(above)
    elif below:
        ref = max(below)
    else:
        return None

    slope = (known[ref] - value) / (ref - crf)
    return value + slope * (target_crf - crf)


def metric_slope(history: list[tuple[int, VmafScores]], metric: str) -> float:
    """Az utolsó két mérés közti meredekség (VMAF-pont / CRF-lépés), 0 ha nem számolható."""
    if len(history) < 2:
        return 0.0
    (crf_prev, prev), (crf_curr, curr) = history[-2], history[-1]
    v_prev, v_curr = getattr(prev, metric), getattr(curr, metric)
    if v_prev is None or v_curr is None or crf_prev == crf_curr:
        return 0.0
    return (v_curr - v_prev) / (crf_curr - crf_prev)


def format_scores(crf: int, scores: VmafScores) -> str:
    text = f"  > Eredmény: CRF {crf} -> Átlag: {scores.mean:.2f}"
    if scores.low_5 is not None:
        text += f", 5%: {scores.low_5:.2f}"
    if scores.low_1 is not None:
        text += f", 1%: {scores.low_1:.2f}"
    return text


# =============================================================================
# 7. Transcoder – a GUI-tól független feldolgozó logika
# =============================================================================

class Transcoder:
    """
    Egy fájl feldolgozása: CRF-keresés próbakódolásokkal és VMAF-méréssel,
    majd az eredeti cseréje, ha a legjobb eredmény kisebb nála.

    Háttérszálon fut; a naplózás és a folyamatjelzés a konstruktorban kapott
    callbackeken keresztül történik, a leállítás a cancel() metódussal.
    """

    def __init__(
        self,
        history: EncodeHistory,
        skipped: SkippedFiles,
        log: Callable[[str], None],
        on_progress: Callable[[float, float | None], None],
    ):
        self._history = history
        self._skipped = skipped
        self._log = log
        self._on_progress = on_progress
        self._cancel_event = threading.Event()
        self._process: subprocess.Popen | None = None

    # --- Leállítás --------------------------------------------------------

    @property
    def cancelled(self) -> bool:
        return self._cancel_event.is_set()

    def reset(self) -> None:
        self._cancel_event.clear()

    def cancel(self) -> None:
        """Leállítást kér, és azonnal kilövi a futó ffmpeg folyamatot."""
        self._cancel_event.set()
        process = self._process
        if process is not None:
            _kill_quietly(process)

    def _check_cancel(self) -> None:
        if self.cancelled:
            raise _Cancelled()

    # --- Egy fájl feldolgozása ---------------------------------------------

    def process_file(self, entry: FileEntry, settings: EncodeSettings) -> bool:
        """
        True, ha a fájl rendben lefutott (akkor is, ha az eredményt eldobtuk,
        mert nem lett kisebb az eredetinél). Megszakításkor és hibánál False.
        """
        duration = entry.info.duration if entry.info.duration > 0 else probe_duration(entry.path)
        map_args, audio_args = self._build_stream_args(entry)
        job = EncodeJob(entry.path, settings, duration, map_args, audio_args, entry.info.resolution)

        safe_remove(job.best_path)      # egy korábbi, megszakított futás maradéka
        try:
            best = self._search_best_crf(job)
            if best is None:
                self._log("  [Hiba] Nem sikerült olyan CRF-et találni, amely minden VMAF minimumcélt teljesíti.")
                return False
            return self._finalize(job, best)
        except _Cancelled:
            return False
        except TranscodeError as e:
            self._log(f"  [Hiba] {e}")
            if e.details:
                self._log(f"  > FFmpeg hiba részletek:\n{e.details}")
            return False
        except OSError as e:
            self._log(f"  [Kritikus Hiba] Fájl művelet sikertelen: {e}")
            return False
        finally:
            safe_remove(job.temp_path, job.best_path, VMAF_LOG_FILE)

    def _build_stream_args(self, entry: FileEntry) -> tuple[list[str], list[str]]:
        """A -map és a hangkódolási paraméterek a kijelölt sávok alapján."""
        map_args = ["-map", "0:v:0"]
        audio_args = ["-c:a", "libopus"]

        selected_audio = [t for t in entry.info.audio_streams if entry.selected_audio.get(t.index)]
        for out_idx, track in enumerate(selected_audio):
            bitrate = audio_bitrate_for(track.channels)
            map_args += ["-map", f"0:{track.index}"]
            audio_args += [f"-b:a:{out_idx}", bitrate]
            if track.channels > 2:
                audio_args += [f"-mapping_family:a:{out_idx}", "255"]
            self._log(f"  > Hangsáv (ID: {track.index}, {track.channels} csatorna) -> OPUS {bitrate}")

        for track in entry.info.sub_streams:
            if entry.selected_subs.get(track.index):
                map_args += ["-map", f"0:{track.index}"]

        return map_args, audio_args

    # --- CRF-keresés -------------------------------------------------------

    def _search_best_crf(self, job: EncodeJob) -> Candidate | None:
        """
        A cél: az átlagos VMAF legyen minél közelebb a célértékhez felülről,
        miközben az opcionális 1% és 5% minimumok is teljesülnek. Ezért az első
        megfelelő eredménynél nem állunk meg, hanem a CRF-et addig emeljük,
        amíg valamelyik küszöb el nem bukik (vagy a becslés szerint elbukna).

        Visszatérés: a legjobb jelölt (a kódolt fájl a job.best_path-on), vagy
        None, ha egyik próba sem teljesített minden küszöböt.
        """
        settings = job.settings
        crf = self._history.estimate_starting_crf(settings.target_vmaf, settings.preset, job.resolution)
        self._log(f"  [Info] Becsült kezdő CRF a korábbi kódolások alapján: {crf}")

        # crf -> mért eredmény. Egy már megmért CRF-et nem kódolunk újra
        # (pl. amikor a keresés visszaérkezik egy korábban elutasított CRF-hez).
        tried: dict[int, VmafScores] = {}
        # Időrendi mérési sor (a gyorsítótárból újrafelhasználtakkal együtt) a lépésközökhöz.
        history: list[tuple[int, VmafScores]] = []
        best: Candidate | None = None

        for iteration in range(1, MAX_ITERATIONS + 1):
            self._check_cancel()

            from_cache = crf in tried
            if from_cache:
                scores = tried[crf]
                self._log(
                    f"  [Iteráció {iteration}] CRF {crf} már szerepel a korábbi "
                    "próbák között -> újrafelhasznált eredmény, nincs újrakódolás."
                )
            else:
                self._log(f"  [Iteráció {iteration}] Próba kódolás CRF {crf} értékkel (várj türelemmel)...")
                scores = self._measure(job, crf)
                tried[crf] = scores
                self._history.add(scores.mean, crf, settings.preset, job.resolution)

            self._log(format_scores(crf, scores))
            history.append((crf, scores))
            failed = settings.failed_metrics(scores)

            if not failed:
                best = self._keep_if_better(job, best, crf, scores, from_cache)
                next_crf = self._next_crf_after_pass(tried, crf, settings, best) if best is not None else None
            elif best is not None:
                # Egy nagyobb CRF már nem teljesít valamit: elértük a határt,
                # a korábbi legjobb marad a végleges jelölt.
                labels = ", ".join(METRIC_LABELS[m] for m in failed)
                self._log(f"  [Határ] CRF {crf} már nem teljesíti: {labels}. A legjobb megfelelő CRF: {best.crf}.")
                next_crf = None
            else:
                next_crf = self._next_crf_after_fail(history, crf, scores, settings, failed)

            if next_crf is None:
                break
            crf = next_crf

        self._check_cancel()
        return best

    def _keep_if_better(
        self, job: EncodeJob, best: Candidate | None, crf: int, scores: VmafScores, from_cache: bool
    ) -> Candidate | None:
        """
        Mindig a célhoz legközelebbi, minden minimumot teljesítő eredményt
        tartjuk meg; holtversenynél a magasabb CRF-et (kisebb fájl).
        """
        gap = scores.mean - job.settings.target_vmaf
        is_better = (
            best is None
            or gap < best.gap - GAP_EPSILON
            or (abs(gap - best.gap) <= GAP_EPSILON and crf > best.crf)
        )

        if not is_better:
            safe_remove(job.temp_path)
            return best

        if from_cache:
            # A gyakorlatban nem fordulhat elő: a keresés soha nem lép vissza egy
            # már sikeresnek bizonyult CRF-hez. Fájl nélkül nem írjuk felül a legjobbat.
            self._log(
                f"  [Figyelem] CRF {crf} gyorsítótárazott eredménye jobb lenne, "
                "de a kódolt fájl már nem érhető el újrafelhasználásra."
            )
            return best

        os.replace(job.temp_path, job.best_path)
        self._log(f"  [Új legjobb] CRF {crf} -> Átlag: {scores.mean:.2f} (célkülönbség: +{gap:.2f})")
        return Candidate(crf, scores, gap)

    def _next_crf_after_pass(
        self, tried: dict[int, VmafScores], crf: int, settings: EncodeSettings, best: Candidate
    ) -> int | None:
        """Minden küszöb teljesült: próbáljuk a következő CRF-et, ha van esély rá."""
        if crf >= MAX_CRF:
            self._log("  [Info] Elértük a maximális CRF-et.")
            return None

        next_crf = crf + 1

        # Mielőtt egy teljes kódolást + VMAF-ot rászánnánk: a már megmért CRF-ek
        # alapján megbecsüljük mindhárom mutatót a következő CRF-nél. Nem csak az
        # átlag tartalékát nézzük, hanem a legszűkebb küszöböt is (pl. ha az 5% épp
        # csak 0.01-gyel van felette, és egy nagyobb CRF már elbukott rajta, a +1
        # próba szinte biztosan felesleges).
        predicted_fail = []
        for metric, label in METRIC_LABELS.items():
            threshold = settings.threshold(metric)
            if threshold is None or getattr(tried[crf], metric) is None:
                continue
            predicted = predict_metric(tried, crf, metric, next_crf)
            if predicted is not None and predicted < threshold:
                predicted_fail.append(f"{label} ~{predicted:.2f} < {threshold:.2f}")

        if predicted_fail:
            self._log(
                f"  [Határ] CRF {next_crf} a mért adatok alapján már nem teljesítené: "
                f"{', '.join(predicted_fail)}. A legjobb megfelelő CRF: {best.crf}."
            )
            return None

        self._log(
            f"  [Info] Minden küszöb teljesült. Következő próba: CRF {next_crf}, "
            "hátha az is megfelel (kisebb fájl)."
        )
        return next_crf

    def _next_crf_after_fail(
        self,
        history: list[tuple[int, VmafScores]],
        crf: int,
        scores: VmafScores,
        settings: EncodeSettings,
        failed: list[str],
    ) -> int:
        """Még nincs megfelelő eredmény: a CRF csökkentése, amíg minden minimum nem teljesül."""
        if "mean" not in failed:
            # Az átlag rendben van, csak az alsó 1% / 5% marad le: a nagyobb
            # lemaradás mutatójának meredekségéből becsüljük a lépést.
            gap_1 = settings.shortfall(scores, "low_1")
            gap_5 = settings.shortfall(scores, "low_5")
            max_gap = max(gap_1, gap_5)
            slope = metric_slope(history, "low_1" if gap_1 >= gap_5 else "low_5")
            drop_per_step = abs(slope) if slope < STEEP_SLOPE else FALLBACK_LOW_SLOPE
            jump = clamp(round(max_gap / drop_per_step), 1, MAX_LOW_JUMP)
            self._log(
                f"  [Info] Átlag OK/magas, de alsó 1%/5% lemarad "
                f"(~{max_gap:.2f}). CRF csökkentése (-{jump})..."
            )
            next_crf = crf - jump
        elif len(history) < 2:
            next_crf = crf - FIRST_MEAN_STEP
        else:
            # Az átlag a cél alatt: az utolsó két mérés meredekségéből ugrunk.
            slope = metric_slope(history, "mean")
            if slope < STEEP_SLOPE:
                jump = clamp((settings.target_vmaf - scores.mean) / slope, -MAX_MEAN_JUMP, MAX_MEAN_JUMP)
                next_crf = round(crf + jump)
            else:
                next_crf = crf - FALLBACK_MEAN_STEP

        return clamp(next_crf, MIN_CRF, MAX_CRF)

    # --- Mérés és véglegesítés ---------------------------------------------

    def _measure(self, job: EncodeJob, crf: int) -> VmafScores:
        """Próbakódolás a megadott CRF-fel, majd VMAF-mérés az eredetihez képest."""
        settings = job.settings
        encode_cmd = [
            "ffmpeg", "-y", "-i", job.input_file,
            *job.map_args,
            "-c:v", "libsvtav1", "-preset", settings.preset, "-crf", str(crf),
            *job.audio_args,
            "-c:s", "copy", job.temp_path,
        ]
        ok, err_log = self._run_ffmpeg(encode_cmd, job.duration, settings.low_priority)
        self._check_cancel()
        if not ok or not os.path.exists(job.temp_path):
            raise TranscodeError("A kódolás sikertelen volt.", err_log)

        self._log("  Kódolás kész. VMAF számolása a teljes videón...")
        threads = max(1, (os.cpu_count() or 4) - 1)
        vmaf_cmd = [
            "ffmpeg", "-y", "-i", job.temp_path, "-i", job.input_file,
            "-lavfi", f"libvmaf=log_fmt=json:log_path={VMAF_LOG_FILE}:n_threads={threads}:n_subsample=5",
            "-f", "null", "-",
        ]
        ok, err_log = self._run_ffmpeg(vmaf_cmd, job.duration, settings.low_priority)
        self._check_cancel()
        if not ok:
            raise TranscodeError("A VMAF parancs elszállt.", err_log)

        try:
            return parse_vmaf_log(VMAF_LOG_FILE)
        except Exception as e:  # sérült / hiányos JSON bármilyen formában
            self._log(f"  [Hiba a VMAF JSON olvasásakor: {e}]")
            raise TranscodeError("A JSON fájl nem olvasható vagy nem jött létre.") from e
        finally:
            safe_remove(VMAF_LOG_FILE)

    def _finalize(self, job: EncodeJob, best: Candidate) -> bool:
        """Ha a legjobb jelölt kisebb az eredetinél, lecseréli vele; különben eldobja."""
        original_size = os.path.getsize(job.input_file)
        new_size = os.path.getsize(job.best_path)
        scores = best.scores

        self._log(f"  > Végleges választás: CRF {best.crf}")
        summary = f"  > Végleges VMAF: átlag {scores.mean:.2f}"
        if scores.low_5 is not None:
            summary += f", 5% {scores.low_5:.2f}"
        self._log(summary)
        if scores.low_1 is not None:
            self._log(f"  > Végleges VMAF 1%: {scores.low_1:.2f}")
        self._log(f"  > Eredeti méret: {format_size(original_size)}")
        self._log(f"  > Új méret: {format_size(new_size)}")

        if new_size >= original_size:
            self._log(
                f"  [Info] Az új videó {format_size(new_size - original_size)}-val NAGYOBB "
                "(vagy egyenlő), mint az eredeti!"
            )
            self._log("  [Info] A fájlcsere megszakítva. Az eredeti videó megmarad.")
            safe_remove(job.best_path)
            self._skipped.mark(job.input_file)
            return True

        self._log(
            f"  > Méretcsökkenés: {format_size(original_size - new_size)}. "
            "Eredeti fájl cseréje a tömörítettre..."
        )
        replace_original(job.input_file, job.best_path)
        return True

    # --- ffmpeg futtatása --------------------------------------------------

    def _run_ffmpeg(self, cmd: list[str], total_duration: float, low_priority: bool) -> tuple[bool, str]:
        """
        Lefuttat egy ffmpeg parancsot; a "time=" sorokból folyamatjelzést és
        hátralévő időt számol. Visszatérés: (siker, hibánál a kimenet vége).
        """
        if low_priority and not IS_WINDOWS:
            cmd = ["nice", "-n", "10", *cmd]

        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                **subprocess_kwargs(low_priority),
            )
        except OSError as e:
            return False, str(e)

        self._process = process
        output_tail: collections.deque[str] = collections.deque(maxlen=OUTPUT_TAIL_LINES)
        start_time = time.monotonic()
        try:
            for line in process.stdout:
                output_tail.append(line.strip())
                if self.cancelled:
                    _kill_quietly(process)
                    break

                position = parse_ffmpeg_time(line)
                if position is not None and total_duration > 0:
                    progress = min(position / total_duration * 100, 100.0)
                    elapsed = time.monotonic() - start_time
                    eta = elapsed / progress * 100 - elapsed if progress > 0.5 else None
                    self._on_progress(progress, eta)
            process.wait()
        except (OSError, ValueError) as e:
            _kill_quietly(process)
            return False, str(e)
        finally:
            self._process = None
            self._on_progress(0.0, None)

        if self.cancelled:
            return False, "Felhasználó által megszakítva"
        if process.returncode != 0:
            return False, "\n".join(output_tail)
        return True, ""


def _kill_quietly(process: subprocess.Popen) -> None:
    with contextlib.suppress(OSError):
        process.kill()


# =============================================================================
# 8. AV1VmafApp – a Tkinter felület
# =============================================================================

class AV1VmafApp:
    """
    A felület. A Tk-widgeteket kizárólag a fő szál kezeli: a feldolgozó szál
    a _run_on_ui() sorba teszi a felületet érintő hívásait, amelyeket a fő
    szál UI_POLL_MS időközönként végrehajt.
    """

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("AV1 VMAF Újratömörítő (Okos Kereséssel + Sávválasztóval)")
        self.root.geometry("950x790")

        # Útvonal -> adat, a lista aktuális sorrendjében.
        self.entries: dict[str, FileEntry] = {}
        self.is_processing = False
        self._track_vars: list[tk.BooleanVar] = []    # a sávlista pipáinak élő referenciái
        self._ui_queue: queue.Queue = queue.Queue()

        self.skipped = SkippedFiles()
        self.transcoder = Transcoder(EncodeHistory(), self.skipped, log=self.log, on_progress=self._report_progress)

        self._build_ui()
        self.load_config()

        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self._poll_ui_queue()

    # --- Szálak közti kommunikáció ------------------------------------------

    def _run_on_ui(self, func: Callable, *args) -> None:
        self._ui_queue.put((func, args))

    def _poll_ui_queue(self) -> None:
        try:
            while True:
                try:
                    func, args = self._ui_queue.get_nowait()
                except queue.Empty:
                    break
                func(*args)
        finally:
            self.root.after(UI_POLL_MS, self._poll_ui_queue)

    def log(self, message: str) -> None:
        """Bármelyik szálból hívható."""
        if threading.current_thread() is threading.main_thread():
            self._append_log(message)
        else:
            self._run_on_ui(self._append_log, message)

    def _report_progress(self, progress: float, eta_seconds: float | None) -> None:
        self._run_on_ui(self.update_progress, progress, eta_seconds)

    # --- Felület felépítése -------------------------------------------------

    def _build_ui(self) -> None:
        self._build_settings_panel()
        self._build_file_and_track_panels()
        self._build_action_buttons()
        self._build_log_panel()
        self._build_progress_panel()

    def _build_settings_panel(self) -> None:
        frame = ttk.Frame(self.root, padding=10)
        frame.pack(fill=tk.X)

        self.vmaf_entry = self._labeled_entry(frame, "Cél VMAF (minimum):", row=0, column=0)
        self.tol_entry = self._labeled_entry(frame, "Tűréshatár (±):", row=0, column=2)
        self.vmaf_5_entry = self._labeled_entry(frame, "Alsó 5% VMAF (opcionális):", row=1, column=0)
        self.vmaf_1_entry = self._labeled_entry(frame, "Alsó 1% VMAF (opcionális):", row=1, column=2)

        ttk.Label(frame, text="AV1 Preset (0=Lassú, 13=Gyors):").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.preset_combo = ttk.Combobox(frame, values=[str(i) for i in range(14)], width=8, state="readonly")
        self.preset_combo.grid(row=2, column=1, sticky=tk.W, pady=5, padx=5)

        self.low_priority_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            frame, text="Alacsony prioritás (Háttérben futás)", variable=self.low_priority_var
        ).grid(row=2, column=2, columnspan=2, sticky=tk.W, pady=5, padx=(15, 0))

    @staticmethod
    def _labeled_entry(parent: ttk.Frame, text: str, row: int, column: int) -> ttk.Entry:
        ttk.Label(parent, text=text).grid(
            row=row, column=column, sticky=tk.W, pady=5, padx=(15, 0) if column else 0
        )
        entry = ttk.Entry(parent, width=10)
        entry.grid(row=row, column=column + 1, sticky=tk.W, pady=5, padx=5)
        return entry

    def _build_file_and_track_panels(self) -> None:
        paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        paned.add(self._build_file_panel(paned), weight=1)
        paned.add(self._build_track_panel(paned), weight=1)

    def _build_file_panel(self, parent: ttk.PanedWindow) -> ttk.Frame:
        frame = ttk.Frame(parent)

        ttk.Label(frame, text="Feldolgozásra váró videók:").pack(anchor=tk.W)
        self.file_listbox = tk.Listbox(frame, selectmode=tk.EXTENDED)
        self.file_listbox.pack(fill=tk.BOTH, expand=True, pady=5)
        self.file_listbox.bind("<<ListboxSelect>>", self._show_selected_tracks)

        buttons = ttk.Frame(frame)
        buttons.pack(fill=tk.X, pady=(0, 5))
        ttk.Button(buttons, text="Fájlok hozzáadása", command=self.add_files).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(buttons, text="Könyvtár hozzáadása", command=self.add_directory).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(buttons, text="Kijelöltek Törlése", command=self.remove_selected_files).pack(side=tk.LEFT)

        sort_frame = ttk.Frame(frame)
        sort_frame.pack(fill=tk.X)
        ttk.Label(sort_frame, text="Rendezés:").pack(side=tk.LEFT, padx=(0, 5))
        self.sort_crit_combo = ttk.Combobox(sort_frame, values=list(SORT_KEYS), state="readonly", width=18)
        self.sort_crit_combo.pack(side=tk.LEFT, padx=(0, 5))
        self.sort_order_combo = ttk.Combobox(
            sort_frame, values=[SORT_ASCENDING, SORT_DESCENDING], state="readonly", width=10
        )
        self.sort_order_combo.pack(side=tk.LEFT)
        for combo in (self.sort_crit_combo, self.sort_order_combo):
            combo.bind("<<ComboboxSelected>>", self.sort_files)

        return frame

    def _build_track_panel(self, parent: ttk.PanedWindow) -> ttk.LabelFrame:
        container = ttk.LabelFrame(parent, text="Megtartandó sávok (Kattints egy videóra bal oldalt)")

        canvas = tk.Canvas(container, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        self.track_frame = ttk.Frame(canvas)
        self.track_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.track_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        return container

    def _build_action_buttons(self) -> None:
        frame = ttk.Frame(self.root, padding=(10, 0, 10, 5))
        frame.pack(fill=tk.X)
        self.cancel_btn = ttk.Button(frame, text="Leállítás", command=self.request_cancel, state=tk.DISABLED)
        self.cancel_btn.pack(side=tk.RIGHT, padx=5)
        self.start_btn = ttk.Button(frame, text="Feldolgozás Indítása", command=self.start_processing)
        self.start_btn.pack(side=tk.RIGHT, padx=5)

    def _build_log_panel(self) -> None:
        frame = ttk.Frame(self.root, padding=(10, 5, 10, 5))
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text="Napló:").pack(anchor=tk.W)
        self.log_text = tk.Text(frame, height=8, state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)

    def _build_progress_panel(self) -> None:
        frame = ttk.Frame(self.root, padding=(10, 5, 10, 10))
        frame.pack(fill=tk.X)

        self.progress_var = tk.DoubleVar()
        ttk.Progressbar(frame, variable=self.progress_var, maximum=100).pack(fill=tk.X, side=tk.TOP, pady=(0, 5))

        info = ttk.Frame(frame)
        info.pack(fill=tk.X)
        self.progress_label = ttk.Label(info, text="0.0%")
        self.progress_label.pack(side=tk.LEFT)
        self.eta_label = ttk.Label(info, text=f"Hátralévő idő: {format_time(None)}")
        self.eta_label.pack(side=tk.RIGHT)

    # --- Beállítások ----------------------------------------------------------

    def _config_entries(self) -> tuple[tuple[ttk.Entry, str], ...]:
        return (
            (self.vmaf_entry, "vmaf"),
            (self.vmaf_5_entry, "vmaf_5"),
            (self.vmaf_1_entry, "vmaf_1"),
            (self.tol_entry, "tolerance"),
        )

    def load_config(self) -> None:
        stored = load_json(CONFIG_FILE, {})
        config = {**DEFAULT_CONFIG, **(stored if isinstance(stored, dict) else {})}

        for widget, key in self._config_entries():
            widget.delete(0, tk.END)
            widget.insert(0, config[key])
        self.preset_combo.set(config["preset"])
        self.low_priority_var.set(config["low_priority"])
        self.sort_crit_combo.set(config["sort_crit"])
        self.sort_order_combo.set(config["sort_order"])

    def save_config(self) -> None:
        config = {key: widget.get() for widget, key in self._config_entries()}
        config.update(
            preset=self.preset_combo.get(),
            low_priority=self.low_priority_var.get(),
            sort_crit=self.sort_crit_combo.get(),
            sort_order=self.sort_order_combo.get(),
        )
        save_json(CONFIG_FILE, config)

    def _read_settings(self) -> EncodeSettings:
        """A beviteli mezők értelmezése; hibás számnál ValueError."""
        return EncodeSettings(
            target_vmaf=float(self.vmaf_entry.get()),
            target_vmaf_5=optional_float(self.vmaf_5_entry.get()),
            target_vmaf_1=optional_float(self.vmaf_1_entry.get()),
            tolerance=float(self.tol_entry.get()),
            preset=self.preset_combo.get(),
            low_priority=self.low_priority_var.get(),
        )

    # --- Napló és folyamatjelző -------------------------------------------------

    def _append_log(self, message: str) -> None:
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, message + "\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.root.update_idletasks()

    def update_progress(self, progress: float, eta_seconds: float | None = None) -> None:
        self.progress_var.set(progress)
        self.progress_label.config(text=f"{progress:.1f}%")
        self.eta_label.config(text=f"Hátralévő idő: {format_time(eta_seconds)}")

    # --- Fájllista ----------------------------------------------------------

    @contextlib.contextmanager
    def _busy_cursor(self):
        self.root.config(cursor="watch")   # hordozható "homokóra" (Windows alatt is natív)
        self.root.update()
        try:
            yield
        finally:
            self.root.config(cursor="")

    def add_files(self) -> None:
        patterns = " ".join(f"*{ext}" for ext in VIDEO_EXTENSIONS)
        paths = filedialog.askopenfilenames(
            title="Válassz videókat",
            filetypes=[("Videó fájlok", patterns), ("Minden fájl", "*.*")],
        )
        if paths:
            self._add_files(paths)

    def add_directory(self) -> None:
        directory = filedialog.askdirectory(title="Válassz mappát")
        if not directory:
            return
        with self._busy_cursor():
            paths = find_video_files(directory)
        if paths:
            self._add_files(paths)
        else:
            messagebox.showinfo(
                "Infó", "Nem található támogatott videófájl a kiválasztott mappában és alkönyvtáraiban."
            )

    def _add_files(self, paths) -> None:
        skipped_av1 = skipped_larger = 0
        added_new = False

        with self._busy_cursor():
            for path in paths:
                if self.skipped.is_skipped(path):
                    skipped_larger += 1
                    continue
                if path in self.entries:
                    continue

                info = probe_media(path)
                if info is None:
                    self.log(f"[Figyelem] Nem sikerült beolvasni a sávokat: {os.path.basename(path)}")
                    info = MediaInfo()
                elif info.video_codec == "av1":
                    skipped_av1 += 1
                    continue

                try:
                    self.entries[path] = FileEntry.from_file(path, info)
                except OSError:
                    self.log(f"[Figyelem] A fájl nem olvasható: {os.path.basename(path)}")
                    continue
                added_new = True

            if added_new:
                self.sort_files()

        messages = []
        if skipped_av1:
            messages.append(f"{skipped_av1} db fájl kihagyva, mert már AV1 kódolású.")
        if skipped_larger:
            messages.append(
                f"{skipped_larger} db fájl kihagyva, mert egy korábbi próbálkozás alapján "
                "a tömörített változat nagyobb lenne az eredetinél."
            )
        if messages:
            messagebox.showinfo("Kihagyott fájlok", "\n\n".join(messages))

    def sort_files(self, _event=None) -> None:
        key = SORT_KEYS.get(self.sort_crit_combo.get(), SORT_KEYS["Teljes elérési út"])
        reverse = self.sort_order_combo.get() == SORT_DESCENDING
        self.entries = {e.path: e for e in sorted(self.entries.values(), key=key, reverse=reverse)}

        self.file_listbox.delete(0, tk.END)
        for path in self.entries:
            self.file_listbox.insert(tk.END, path)
        self._show_selected_tracks()

    def remove_selected_files(self) -> None:
        for index in reversed(self.file_listbox.curselection()):
            self.entries.pop(self.file_listbox.get(index), None)
            self.file_listbox.delete(index)
        self._show_selected_tracks()

    def _remove_entry(self, path: str) -> None:
        self.entries.pop(path, None)
        items = self.file_listbox.get(0, tk.END)
        if path in items:
            self.file_listbox.delete(items.index(path))
        self._show_selected_tracks()

    # --- Sávválasztó --------------------------------------------------------

    def _show_selected_tracks(self, _event=None) -> None:
        for widget in self.track_frame.winfo_children():
            widget.destroy()
        self._track_vars.clear()

        selection = self.file_listbox.curselection()
        if not selection:
            return
        entry = self.entries.get(self.file_listbox.get(selection[0]))
        if entry is None:
            return

        row = 0
        if entry.info.audio_streams:
            row = self._add_track_section("Hangsávok:", entry.info.audio_streams, entry.selected_audio, row, 5)
        if entry.info.sub_streams:
            row = self._add_track_section("Feliratok:", entry.info.sub_streams, entry.selected_subs, row, 15)
        if row == 0:
            ttk.Label(self.track_frame, text="Nem található választható extra sáv.").grid(
                row=row, column=0, sticky=tk.W, pady=5
            )

    def _add_track_section(
        self, title: str, tracks: tuple[Track, ...], selected: dict[int, bool], row: int, top_pad: int
    ) -> int:
        ttk.Label(self.track_frame, text=title, font=("", 10, "bold")).grid(
            row=row, column=0, sticky=tk.W, pady=(top_pad, 2)
        )
        row += 1
        for track in tracks:
            var = tk.BooleanVar(value=selected.get(track.index, False))
            self._track_vars.append(var)

            def on_toggle(index=track.index, var=var):
                selected[index] = var.get()

            ttk.Checkbutton(
                self.track_frame, text=f"[ID: {track.index}] {track.description}", variable=var, command=on_toggle
            ).grid(row=row, column=0, sticky=tk.W, padx=10, pady=2)
            row += 1
        return row

    # --- Feldolgozás --------------------------------------------------------

    def start_processing(self) -> None:
        if not self.entries:
            messagebox.showwarning("Figyelmeztetés", "Nincs hozzáadva videó!")
            return

        self.save_config()
        try:
            settings = self._read_settings()
        except ValueError:
            messagebox.showerror("Hiba", "A VMAF értékek és a tűréshatár csak számok lehetnek!")
            return

        self.start_btn.config(state=tk.DISABLED)
        self.cancel_btn.config(state=tk.NORMAL)
        self.is_processing = True
        self.transcoder.reset()

        paths = list(self.entries)
        threading.Thread(target=self._process_queue, args=(paths, settings), daemon=True).start()

    def request_cancel(self) -> None:
        self.transcoder.cancel()
        self.cancel_btn.config(state=tk.DISABLED)
        self.log("\n[Leállítás kérése folyamatban... FFmpeg kényszerített leállítása]")

    def _process_queue(self, paths: list[str], settings: EncodeSettings) -> None:
        """A feldolgozó szál: sorban végigmegy a lista indításkori tartalmán."""
        self.log("--- FELDOLGOZÁS INDÍTVA ---")
        try:
            for path in paths:
                if self.transcoder.cancelled:
                    break
                entry = self.entries.get(path)
                if entry is None:       # időközben törölték a listából
                    continue

                name = os.path.basename(path)
                if not os.path.exists(path):
                    self.log(f"\n[Kihagyva] A fájl már nem található a lemezen: {name}")
                    self._run_on_ui(self._remove_entry, path)
                    continue

                self.log(f"\n-> Fájl feldolgozása: {name}")
                success = self.transcoder.process_file(entry, settings)

                if self.transcoder.cancelled:
                    self.log(f"[MEGSZAKÍTVA] A folyamat leállítva: {name}")
                    break
                if success:
                    self.log(f"[KÉSZ] Fájl feldolgozva: {name}")
                else:
                    self.log(f"[HIBA] Nem sikerült feldolgozni: {name}")
                self._run_on_ui(self._remove_entry, path)
        except Exception as e:  # a szál váratlan hibája se hagyja "futó" állapotban a felületet
            self.log(f"\n[Kritikus Hiba] Váratlan hiba a feldolgozás közben: {e}")
        finally:
            self.log("\n--- FELDOLGOZÁS VÉGE ---")
            self._run_on_ui(self._on_processing_finished)

    def _on_processing_finished(self) -> None:
        self.is_processing = False
        self.start_btn.config(state=tk.NORMAL)
        self.cancel_btn.config(state=tk.DISABLED)
        self.update_progress(0.0, None)

    def on_closing(self) -> None:
        self.save_config()
        if not self.is_processing:
            self.root.destroy()
            return
        if messagebox.askyesno("Kilépés", "A feldolgozás még fut. Biztosan be akarod zárni (és leállítani)?"):
            self.request_cancel()
            self.root.after(1500, self.root.destroy)


def main() -> None:
    root = tk.Tk()
    AV1VmafApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
