#!/usr/bin/env python3
"""
Hanamidi - turn a song into MIDI, one instrument at a time.

Splits a song into instruments (Demucs), transcribes each one to MIDI, and snaps
the notes to the beat. A flower grows while it works and is in full bloom when
your MIDI is ready.

First time: double-click setup.bat (same folder) to install everything.
Then open this file. Keep it anywhere - all output (MIDI, stems, downloaded
models, settings) goes into a 'SongOutput' folder created next to it.
"""

import base64
import importlib
import importlib.util
import json
import math
import os
import queue
import random
import re
import shutil
import struct
import subprocess
import sys
import threading
import time
import tkinter as tk
import zlib
from pathlib import Path
from tkinter import filedialog

APP_NAME = "Hanamidi"

STEM_PROGRAMS = {
    "vocals": 54, "bass": 33, "guitar": 25,
    "piano": 0, "other": 80, "drums": 0,
}
# Everything lives next to this script, wherever it is stored.
BASE_DIR = Path(sys.argv[0]).resolve().parent if getattr(sys, "frozen", False) \
    else Path(__file__).resolve().parent
DEFAULT_OUT = BASE_DIR / "SongOutput"
MODELS_DIR = DEFAULT_OUT / "_models"      # model cache stays here too
SETTINGS_FILE = DEFAULT_OUT / "_settings.json"
FLOWERS_DIR = DEFAULT_OUT / "_flowers"       # imported flower timelapses (JPG frames)
REQUIRED = {"demucs": "demucs", "basic_pitch": "basic-pitch", "pretty_midi": "pretty_midi",
            "pkg_resources": "setuptools<81", "librosa": "librosa"}  # newer setuptools dropped pkg_resources

ALL_STEMS = ["vocals", "drums", "bass", "guitar", "piano", "other"]

MONO = "Consolas"
SANS = "Segoe UI"
SANS_B = "Segoe UI Semibold"
LIGHT = "Segoe UI Light"

SCALE = 1.0


def px(n):
    return int(round(n * SCALE))


# ---------------------------------------------------------------- colour + themes
def _rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def mix(a, b, t):
    ra, rb = _rgb(a), _rgb(b)
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * t)) for x, y in zip(ra, rb))


THEMES = {
    "Mono": dict(bg="#000000", panel="#0a0a0a", field="#101010", line="#2b2b2b", text="#f0f0f0",
                 muted="#8a8a8a", accent="#f0f0f0", on_accent="#000000", warn="#ff6b6b", flower="line"),
    "Paper": dict(bg="#ecebe6", panel="#f6f5f1", field="#ffffff", line="#c4c2ba", text="#111111",
                  muted="#6b6963", accent="#111111", on_accent="#f6f5f1", warn="#b3261e", flower="line"),
    "Sakura": dict(bg="#0f0c14", panel="#17121f", field="#211a2b", line="#33293f", text="#f4eff8",
                   muted="#8f859d", accent="#f4a6a6", on_accent="#2b1519", warn="#ff9b9b", flower="color"),
    "Terminal": dict(bg="#020a04", panel="#06130a", field="#0a1c0f", line="#17442a", text="#8dffa8",
                     muted="#3f9b5b", accent="#8dffa8", on_accent="#020a04", warn="#ffb86b", flower="line"),
    "Amber": dict(bg="#0b0805", panel="#120d07", field="#1a130a", line="#4a3510", text="#ffb43a",
                  muted="#9a6f20", accent="#ffb43a", on_accent="#0b0805", warn="#ff7a59", flower="line"),
    "Blueprint": dict(bg="#0a1a33", panel="#0d2140", field="#10284d", line="#2b4a7d", text="#d6e6ff",
                      muted="#7f9cc8", accent="#d6e6ff", on_accent="#0a1a33", warn="#ffb3a1", flower="line"),
}
THEME_ORDER = list(THEMES)

CURRENT_THEME = "Mono"
CURRENT_FLOWERS = "line"
BG = PANEL = FIELD = LINE = TEXT = MUTED = ACCENT = ACCENT_HI = ON_ACCENT = WARN = INK = "#000000"


def apply_theme(name, flowers=None):
    """Set the module-level palette. Widgets read these names every time they draw."""
    global CURRENT_THEME, CURRENT_FLOWERS
    global BG, PANEL, FIELD, LINE, TEXT, MUTED, ACCENT, ACCENT_HI, ON_ACCENT, WARN, INK
    t = THEMES.get(name) or THEMES["Mono"]
    CURRENT_THEME = name if name in THEMES else "Mono"
    CURRENT_FLOWERS = flowers if flowers in ("line", "color") else t["flower"]
    BG, PANEL, FIELD, LINE = t["bg"], t["panel"], t["field"], t["line"]
    TEXT, MUTED, ACCENT, ON_ACCENT, WARN = t["text"], t["muted"], t["accent"], t["on_accent"], t["warn"]
    ACCENT_HI = mix(t["accent"], t["bg"], 0.16)
    INK = t["text"]


DEFAULT_SETTINGS = {"theme": "Mono", "flowers": None, "source": "drawn", "gray": False}


def load_settings():
    d = dict(DEFAULT_SETTINGS)
    try:
        d.update(json.loads(SETTINGS_FILE.read_text(encoding="utf-8")))
    except Exception:  # noqa: BLE001
        pass
    return d


def save_settings(d):
    try:
        DEFAULT_OUT.mkdir(parents=True, exist_ok=True)
        SETTINGS_FILE.write_text(json.dumps(d), encoding="utf-8")
    except Exception:  # noqa: BLE001
        pass


apply_theme("Mono")


# ---------------------------------------------------------------- icon
ICON_PNGS = {
    256: (
        "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"
        "1dpNDz3z9Ntf+L73lePTvrQuz+Y3PxsXi5mKwQ1pL5UvVyuaGWKtRo03tkdluVr7t76R7a9r/bvyjTduMVK+nICLCOIVTHiJ"
        "K2Vf0vPAUYR6FEFpzQA0xTfNHvFzszFhtr8/US7NjmWHh0fXGyH3BgE0z/9/6Uv9lXrwjXQm8+LZ2VlNREzNwxpHcXgC/QDE"
        "3xaGvgcy306PjDx+6OtPFgrO0K/8CuHCC9VMsXima3C7EJSNlKLVNmbDbBwphZ9IoBqEf5venv/DVgdb18+lZTuyctNNf+Mn"
        "kn9YDUMorY0gEqtNmq7jsDFcigQu7M/nH8DttztTX/kKbxsbOywlKX3hCydSoH+RoS4lIV/BzEcnhIZNMTP19ffLSqn0k7TR"
        "l2FkZLqRErAlgDaQABFxtVg8jRmf9tzENnIcgA0gBKJ6HUEUlQD6oRC4DRrfP5rDc6HgYHCQkcsZxPkdtyqN2d03vSvrp64r"
        "VauremuOMUb7qZTUxlTDKPzdvpGRfyoUCmJ0dJQ7xciYmTA6SjQ2Zsrjxd+UjviYI4RXrddXVUExs876vpyp1N47sGP7J1sj"
        "MwMEZmBiQmDvXqJjEYIwlxDolcaY81Oum3VTKcDENsVRhFoQTob16m9suPbanzVtsFN9qOOn6BQKBTHWjDjF4lvIYEgZvVEK"
        "elQb8z3hON/O5PNPHu7wkw4G9x3m8Ec05okJgVzOlMZv+r9Z33vt7CqkAo3802QzGRkGwT31unpb/1Xbv8PFokQ+bzrw4hPi"
        "YlFQPq/379p1cSaR+HQimTq7VC5rYOVTgqb0L1Vr/9Y3fOXrm8/saM65GEIoF4snG6UulkK8TBk+1RXyGSFpMpXL/Z/WANTJ"
        "/tMVY7RaSeDo0nRxDn+s3Ha6WDzLNbhdSJGNomjFUgFm1lII6adSqNWDz2uj3pcdGXmqk3PLQ2s1T3z2sydmE4l/SCdTV1aD"
        "ANqYFVNSc9KfTTkiumAgn79/qenSYgjhaKmOJYD1YGgAoViMc8y9exlDQwL7lufwxzLk6V3j7+5P+59cqVTAGKMznidDrWtG"
        "mz9Jb8//fev7dcWzafkulWLxfRL0NwnH9Uu16oooqWNJ/+OypyYhbN5MmJoyU4AYGhxkyucXvetkCaBbCKYlFZgdH7+lz0+/"
        "7nhSgeaU3azviyAI/itQ0Xv6R0a+G9910BjM2W3rF99RaqZ3774w6bifSKVSLytXKqYxX29ZBcI56V+p/nvfyPbXLST9LSwB"
        "HI8RCyIytS9+8UwTqjuWmwoYZp10XekIgVDpT5b2PfVHJ73vfeVuivoLqYHHrr/e39C/4X87jnw/MyNQStESj6evhPTvddhW"
        "4KWwZbzHLb0rrnggYv3HKdcVWMK8/EbTie5LpyXAjwVaXeFfmXtvrzg/MN809Jx3vrPqb8//bi3U/w3gR7J+PHB0id15JpVI"
        "iEjxHw/k8/dzsSit81sFsC5TgblCn+ehWqt+NWT+7Q3Dwz9rDPHgXpOszXWkfF4/c+ONz005iY+lvdSvVoM6tF64QGil/8rA"
        "TgRaugpgjvd/uPbFL763Wg/uSLhuNtLaHC2PjY/wejJQqlarB/8rvX37h4C42YiIVK+uIwA9WSg4m6666ucA3lIpFt8vhfjL"
        "lJtIl2u1o5IqAybhulQLgtmEK9/T+kyshVoFsKa57Ozu3e/KZrLXlSuVyDA7oqUeYJiNIEImnRZBvX5HuR69d9PV3VvoW/Za"
        "tqxHo0D4j6lk8oJytWpM3EcsWtaUBZHKpNNuqVJ+T9/w8HW9kj5ZAlhPRtvYdmyQwM7swIa31ctlRFrPdYj4ySQMMyIVfay0"
        "b9+f9FKufzyk+tj11/v9ff1/lUwkfkcQoRoEcaMUEblSIpVOozQ985m+HcNv6+BGKUsAXZHHNlC5aeKDUuB9DDpFxrfHaofo"
        "RzUVFfqHh7/aauB25RYmAQCYGR9/U9JxxwzzSwSRNMwg5sc14+PpK3N/fUg6YWEJoD1KoBl9DuzcOeAk0y9lqBNSyeTDX9qz"
        "57/yExOaCwWBDurlXxfE2jhLkMvl5Kd/bftLtY5OI+k8+0yt9IPnXXvt9KFrb2HR9si1lD+3sGtqFUA3Rq6JibhglcsxiNhG"
        "qBWotRSYMDhBjXW1W30WFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFkfA/w+Jlb0gSmzNSAAAAABJRU5ErkJggg=="
    ),
    96: (
        "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"
        "5fNQL+32/wBzs81puSm/MAAAAABJRU5ErkJggg=="
    ),
}


def write_icon(path=None):
    """Write hanamidi.ico (PNG-compressed icon) so shortcuts can use it."""
    path = Path(path or BASE_DIR / "hanamidi.ico")
    png = base64.b64decode(ICON_PNGS[256])
    header = struct.pack("<HHH", 0, 1, 1)
    entry = struct.pack("<BBBBHHII", 0, 0, 0, 0, 1, 32, len(png), 22)   # 0 = 256 px
    path.write_bytes(header + entry + png)
    return path


# ----------------------------------------------------------------------
# Transcription helpers
# ----------------------------------------------------------------------
MONO_RANGES = {"vocals": (65.0, 1100.0), "bass": (30.0, 400.0)}   # Hz (fmin, fmax)


def _same(a, b):
    return a == b or (a != a and b != b)          # NaN-aware equality


def _runs(vals):
    """Run-length encode: [[value, start, end_exclusive], ...] (NaN allowed)."""
    out, start = [], 0
    for i in range(1, len(vals) + 1):
        if i == len(vals) or not _same(vals[i], vals[start]):
            out.append([vals[start], start, i])
            start = i
    return out


def _clean_runs(pitch, min_frames, gap_frames):
    """Remove glitch notes and bridge tiny gaps in a frame-wise pitch track."""
    import numpy as np
    pitch = pitch.copy()
    for _ in range(3):
        runs, changed = _runs(pitch), False
        for k, (v, st, en) in enumerate(runs):
            if v == v and (en - st) < min_frames:
                prev = runs[k - 1][0] if k > 0 else np.nan
                nxt = runs[k + 1][0] if k + 1 < len(runs) else np.nan
                pitch[st:en] = prev if (prev == prev and prev == nxt) else np.nan
                changed = True
        if not changed:
            break
    runs = _runs(pitch)
    for k in range(1, len(runs) - 1):
        v, st, en = runs[k]
        if v != v and (en - st) <= gap_frames:
            a, b = runs[k - 1][0], runs[k + 1][0]
            if a == a and a == b:
                pitch[st:en] = a
    return pitch


def transcribe_mono(wav_path, name, minlen_ms):
    """Single-note-at-a-time transcription (vocals/bass) using pYIN pitch tracking."""
    import warnings
    import numpy as np
    import librosa
    import pretty_midi

    fmin, fmax = MONO_RANGES[name]
    sr, hop = 22050, 256
    y, _ = librosa.load(str(wav_path), sr=sr, mono=True)
    f0, _, _ = librosa.pyin(y, fmin=fmin, fmax=fmax, sr=sr, frame_length=2048,
                            hop_length=hop, fill_na=np.nan)
    rms = librosa.feature.rms(y=y, frame_length=2048, hop_length=hop)[0]
    n = min(len(f0), len(rms))
    f0, rms = f0[:n], rms[:n]
    ref = np.percentile(rms, 95) + 1e-9

    ok = ~np.isnan(f0) & (rms > 0.08 * ref)
    midi = np.full(n, np.nan)
    midi[ok] = 69 + 12 * np.log2(f0[ok] / 440.0)

    # median-smooth the pitch so vibrato/scoops don't split notes
    sm = np.full(n, np.nan)
    w = 4
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        for i in np.flatnonzero(ok):
            sm[i] = np.nanmedian(midi[max(0, i - w): i + w + 1])
    pitch = np.round(sm)

    frame_s = hop / sr
    min_frames = max(2, int(round(minlen_ms / 1000.0 / frame_s)))
    gap_frames = max(2, int(round(0.08 / frame_s)))
    pitch = _clean_runs(pitch, min_frames, gap_frames)

    inst = pretty_midi.Instrument(program=STEM_PROGRAMS.get(name, 0), name=name)
    for v, st, en in _runs(pitch):
        if v != v:
            continue
        vel = int(np.clip(40 + 70 * (rms[st:en].mean() / ref), 30, 120))
        inst.notes.append(pretty_midi.Note(
            velocity=vel, pitch=int(np.clip(v, 0, 127)),
            start=st * frame_s, end=en * frame_s))
    return inst


def transcribe_drums(wav_path):
    """Rough drum transcription: onsets in kick / snare / hi-hat frequency bands."""
    import numpy as np
    import librosa
    import pretty_midi

    sr, hop, n_fft = 44100, 512, 2048
    y, _ = librosa.load(str(wav_path), sr=sr, mono=True)
    S = np.abs(librosa.stft(y, n_fft=n_fft, hop_length=hop))
    freqs = librosa.fft_frequencies(sr=sr, n_fft=n_fft)
    # (GM drum note, (low Hz, high Hz), min gap in frames, peak delta)
    bands = [(36, (40, 130), 7, 0.20), (38, (180, 1800), 6, 0.20), (42, (7000, 16000), 3, 0.25)]

    inst = pretty_midi.Instrument(program=0, is_drum=True, name="drums")
    for note, (lo, hi), wait, delta in bands:
        env = S[(freqs >= lo) & (freqs < hi)].sum(axis=0)
        env = np.maximum(0, np.diff(env, prepend=env[0]))
        env = env / (env.max() + 1e-9)
        frames = librosa.onset.onset_detect(
            onset_envelope=env, sr=sr, hop_length=hop, units="frames", backtrack=False,
            delta=delta, wait=wait, pre_max=3, post_max=3, pre_avg=10, post_avg=10)
        for f in frames:
            t = float(librosa.frames_to_time(f, sr=sr, hop_length=hop))
            vel = int(np.clip(50 + 70 * env[f], 40, 120))
            inst.notes.append(pretty_midi.Note(velocity=vel, pitch=note, start=t, end=t + 0.08))
    inst.notes.sort(key=lambda n: n.start)
    return inst


def detect_grid(wav_path, subdiv, bpm_override=None):
    """Find the beat and build a grid of 'subdiv' steps per beat covering the whole song."""
    import numpy as np
    import librosa

    y, sr = librosa.load(str(wav_path), sr=22050, mono=True)
    dur = len(y) / sr
    _, beats = librosa.beat.beat_track(y=y, sr=sr, units="time")
    beats = np.asarray(beats, dtype=float)
    if len(beats) < 4:
        raise RuntimeError("no steady beat found")

    k = np.arange(len(beats))
    period, t0 = np.polyfit(k, beats, 1)
    steady = bool(np.abs(beats - (t0 + k * period)).max() < 0.12 * period)

    if bpm_override:
        period = 60.0 / bpm_override
        t0 = beats[0] % period
        steady = True

    if steady:
        # perfectly regular grid (what a DAW expects)
        step = period / subdiv
        i0 = -int(np.floor(t0 / step)) - subdiv
        i1 = int(np.ceil((dur - t0) / step)) + subdiv
        grid = t0 + step * np.arange(i0, i1 + 1)
        bpm = 60.0 / period
        delay = float((-t0) % period)
    else:
        # tempo drifts: follow the detected beats and subdivide between them
        ext = list(beats)
        first, last = beats[1] - beats[0], beats[-1] - beats[-2]
        while ext[0] > 0:
            ext.insert(0, ext[0] - first)
        while ext[-1] < dur:
            ext.append(ext[-1] + last)
        ext = np.array(ext)
        idx = np.arange((len(ext) - 1) * subdiv + 1) / subdiv
        grid = np.interp(idx, np.arange(len(ext)), ext)
        bpm = 60.0 / float(np.median(np.diff(beats)))
        delay = 0.0
    return {"grid": grid, "bpm": float(bpm), "steady": steady, "delay": delay}


def _snap_index(times, grid):
    import numpy as np
    j = np.clip(np.searchsorted(grid, times), 1, len(grid) - 1)
    return np.where(np.abs(grid[j] - times) < np.abs(times - grid[j - 1]), j, j - 1)


def quantize_instrument(inst, grid, mono=False, drum=False):
    """Snap note starts/ends to the beat grid and resolve overlaps the snapping creates."""
    import numpy as np
    from collections import defaultdict
    notes = inst.notes
    if not notes:
        return
    starts = _snap_index(np.array([n.start for n in notes]), grid)
    durs = [n.end - n.start for n in notes]

    if drum:
        seen, out = set(), []
        order = sorted(range(len(notes)), key=lambda k: (starts[k], -notes[k].velocity))
        for k in order:
            key = (notes[k].pitch, int(starts[k]))
            if key in seen:
                continue
            seen.add(key)
            notes[k].start = float(grid[starts[k]])
            notes[k].end = notes[k].start + durs[k]
            out.append(notes[k])
        inst.notes = sorted(out, key=lambda n: n.start)
        return

    ends = _snap_index(np.array([n.end for n in notes]), grid)
    for n, a, b in zip(notes, starts, ends):
        b = min(max(int(b), int(a) + 1), len(grid) - 1)
        n.start, n.end = float(grid[a]), float(grid[b])

    groups = defaultdict(list)
    for n, d in zip(notes, durs):
        groups[0 if mono else n.pitch].append((n, d))
    out = []
    for g in groups.values():
        g.sort(key=lambda x: (x[0].start, -x[1]))
        kept = []
        for n, _ in g:
            if kept and kept[-1].start == n.start:
                continue                      # two notes landed on the same slot
            if kept and kept[-1].end > n.start:
                kept[-1].end = n.start        # no overlaps
            kept.append(n)
        out.extend(kept)
    inst.notes = sorted(out, key=lambda n: n.start)
    inst.pitch_bends = []                     # bend times no longer match the snapped notes


def cleanup_notes(inst, min_len_s, gap_s=0.05):
    """Merge fragmented repeats of the same pitch and drop very short notes."""
    from collections import defaultdict
    if not inst.notes:
        return
    by = defaultdict(list)
    for n in sorted(inst.notes, key=lambda n: (n.pitch, n.start)):
        by[n.pitch].append(n)
    out = []
    for ns in by.values():
        cur = ns[0]
        for n in ns[1:]:
            if n.start - cur.end <= gap_s:
                cur.end = max(cur.end, n.end)
                cur.velocity = max(cur.velocity, n.velocity)
            else:
                out.append(cur)
                cur = n
        out.append(cur)
    inst.notes = sorted((n for n in out if n.end - n.start >= min_len_s), key=lambda n: n.start)


QUANT_CHOICES = {"Off": 0, "1/8": 2, "1/16": 4, "1/32": 8}
MODELS = {"6 stems": "htdemucs_6s", "4 stems": "htdemucs"}


def short_name(stem, limit=48):
    """Short, filesystem-safe name for work folders and MIDI files.

    Windows fails on paths near 260 characters, and a long song title used to appear
    several times in one path. Names that fit are kept; long ones are cut and tagged.
    """
    clean = re.sub(r"[^A-Za-z0-9 _.\-]+", " ", stem)
    clean = re.sub(r"\s+", " ", clean).strip(" ._-")
    if not clean:
        clean = "song"
    if len(clean) <= limit:
        return clean
    tag = "%04x" % (zlib.crc32(stem.encode("utf-8")) & 0xFFFF)     # keeps different long titles apart
    return clean[:max(4, limit - 5)].rstrip(" ._-") + "-" + tag


class Cancelled(Exception):
    pass


# ======================================================================
# Recorded flower timelapses (imported as JPG frames, scrubbed by progress)
# ======================================================================
IMG_EXT = (".png", ".jpg", ".jpeg", ".webp", ".bmp")
VIDEO_EXT = (".mp4", ".mov", ".m4v", ".webm", ".mkv", ".avi")
MAX_FRAMES = 150          # frames kept per timelapse
MAX_SIDE = 900            # longest side in pixels


def have_pil():
    try:
        import PIL.Image  # noqa: F401
        import PIL.ImageTk  # noqa: F401
        return True
    except Exception:  # noqa: BLE001
        return False


def list_clips():
    """{name: [frame paths]} for every imported timelapse."""
    out = {}
    try:
        for d in sorted(FLOWERS_DIR.iterdir()):
            if d.is_dir():
                frames = sorted(d.glob("*.jpg"))
                if len(frames) >= 2:
                    out[d.name] = frames
    except Exception:  # noqa: BLE001
        pass
    return out


def _pick_evenly(items, n):
    if len(items) <= n:
        return list(items)
    return [items[int(round(i * (len(items) - 1) / (n - 1)))] for i in range(n)]


def _save_frame(im, dest, k):
    from PIL import Image
    im = im.convert("RGB")
    w, h = im.size
    s = min(1.0, float(MAX_SIDE) / max(w, h))
    if s < 1.0:
        im = im.resize((max(1, int(w * s)), max(1, int(h * s))), Image.LANCZOS)
    im.save(dest / ("%04d.jpg" % k), "JPEG", quality=88)


def _extract_video(src, dest, say):
    ff = shutil.which("ffmpeg")
    if not ff:
        raise RuntimeError("importing a video needs ffmpeg. Run setup.bat (it installs it), then reopen "
                           + APP_NAME + ". GIFs and folders of images work without it.")
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    probe = subprocess.run([ff, "-hide_banner", "-i", str(src)], capture_output=True, text=True,
                           encoding="utf-8", errors="replace", creationflags=flags)
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", probe.stderr)
    dur = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3)) if m else 0.0
    fps = max(0.2, min(24.0, MAX_FRAMES / dur)) if dur > 0 else 8.0
    side = "min(1,%d/max(iw,ih))" % MAX_SIDE
    scale = "scale='trunc(iw*%s/2)*2':'trunc(ih*%s/2)*2'" % (side, side)
    say("Extracting frames...")
    cmd = [ff, "-hide_banner", "-loglevel", "error", "-y", "-i", str(src),
           "-vf", "fps=%.4f,%s" % (fps, scale), "-q:v", "3", str(dest / "raw_%05d.jpg")]
    r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
                       creationflags=flags)
    raws = sorted(dest.glob("raw_*.jpg"))
    if r.returncode != 0 or len(raws) < 2:
        raise RuntimeError("ffmpeg could not read that video. " + (r.stderr or "").strip()[-160:])
    for k, p in enumerate(_pick_evenly(raws, MAX_FRAMES), 1):
        p.rename(dest / ("%04d.jpg" % k))
    for p in raws:
        if p.exists():
            p.unlink()


def import_clip(src, say=lambda text: None):
    """Turn a video, animated GIF/WebP or folder of images into a timelapse. Returns its name."""
    try:
        from PIL import Image
    except Exception:  # noqa: BLE001
        raise RuntimeError("Pillow is not installed. Run setup.bat again.")
    src = Path(src)
    base = re.sub(r"[^A-Za-z0-9 _-]+", "", src.name if src.is_dir() else src.stem).strip()[:40] or "flower"
    FLOWERS_DIR.mkdir(parents=True, exist_ok=True)
    dest, k = FLOWERS_DIR / base, 2
    while dest.exists():
        dest = FLOWERS_DIR / ("%s %d" % (base, k))
        k += 1
    dest.mkdir()
    try:
        if src.is_dir():
            files = sorted(p for p in src.iterdir() if p.suffix.lower() in IMG_EXT)
            if len(files) < 2:
                raise RuntimeError("that folder needs at least 2 images.")
            say("Reading images...")
            for n, p in enumerate(_pick_evenly(files, MAX_FRAMES), 1):
                with Image.open(p) as im:
                    _save_frame(im, dest, n)
        elif src.suffix.lower() in VIDEO_EXT:
            _extract_video(src, dest, say)
        else:
            say("Reading frames...")
            with Image.open(src) as im:
                total = getattr(im, "n_frames", 1)
                if total < 2:
                    raise RuntimeError("that image is not animated.")
                for n, i in enumerate(_pick_evenly(list(range(total)), MAX_FRAMES), 1):
                    im.seek(i)
                    _save_frame(im.copy(), dest, n)
        if len(list(dest.glob("*.jpg"))) < 2:
            raise RuntimeError("no frames could be read.")
        return dest.name
    except Exception:
        shutil.rmtree(dest, ignore_errors=True)
        raise


# ======================================================================
# Bloom animation
# ======================================================================
def clamp01(x):
    return 0.0 if x < 0 else 1.0 if x > 1 else x


def ease(x):
    x = clamp01(x)
    return x * x * (3 - 2 * x)


def ease_out(x):
    x = clamp01(x)
    return 1 - (1 - x) ** 3


def bez(p0, p1, p2, t):
    u = 1 - t
    return (u * u * p0[0] + 2 * u * t * p1[0] + t * t * p2[0],
            u * u * p0[1] + 2 * u * t * p1[1] + t * t * p2[1])


# petal outlines: x = side (-1..1), y = along the petal (0 base .. 1 tip)
PETAL_SHAPES = {
    "round": [(0, 0), (-.6, .15), (-1, .55), (-.7, .95), (0, 1), (.7, .95), (1, .55), (.6, .15)],
    "notch": [(0, 0), (-.55, .2), (-1, .6), (-.75, .98), (-.28, .98), (0, .82),
              (.28, .98), (.75, .98), (1, .6), (.55, .2)],
    "thin": [(0, 0), (-.7, .2), (-1, .55), (-.6, .92), (0, 1), (.6, .92), (1, .55), (.7, .2)],
    "point": [(0, 0), (-.8, .3), (-1, .55), (-.5, .86), (0, 1.04), (.5, .86), (1, .55), (.8, .3)],
}

FLOWERS = [
    dict(name="Cherry blossom", scale=1.0,
         layers=[dict(n=5, L=1.0, w=0.50, shape="notch", color="#F4A6A6")],
         center=dict(kind="stamens", color="#F1F1F1", dot="#E8788C", r=0.40)),
    dict(name="Daisy", scale=0.95,
         layers=[dict(n=16, L=1.0, w=0.12, shape="thin", color="#FFFFFF"),
                 dict(n=16, L=0.80, w=0.115, shape="thin", color="#E9E4F2",
                      off=math.pi / 16, lag=0.1)],
         center=dict(kind="seeds", color="#F5C518", dot="#C98F00", r=0.30)),
    dict(name="Sunflower", scale=1.1,
         layers=[dict(n=20, L=1.0, w=0.15, shape="thin", color="#FFC933"),
                 dict(n=20, L=0.86, w=0.14, shape="thin", color="#F5A300",
                      off=math.pi / 20, lag=0.1)],
         center=dict(kind="seeds", color="#5A3A1E", dot="#9A6A38", r=0.46)),
    dict(name="Lotus", scale=1.0,
         layers=[dict(n=8, L=1.0, w=0.30, shape="point", color="#F6B8D3"),
                 dict(n=8, L=0.82, w=0.28, shape="point", color="#EE8FBA",
                      off=math.pi / 8, lag=0.1),
                 dict(n=6, L=0.55, w=0.24, shape="point", color="#FFE0EC", lag=0.22)],
         center=dict(kind="disc", color="#F7D154", dot="#FFE9A0", r=0.13)),
    dict(name="Poppy", scale=1.0,
         layers=[dict(n=4, L=0.98, w=0.62, shape="round", color="#E5383B"),
                 dict(n=4, L=0.80, w=0.55, shape="round", color="#BA181B",
                      off=math.pi / 4, lag=0.08)],
         center=dict(kind="seeds", color="#2B1B22", dot="#7A5A6A", r=0.17)),
    dict(name="Cosmos", scale=1.0,
         layers=[dict(n=8, L=1.0, w=0.36, shape="notch", color="#D58BF5"),
                 dict(n=8, L=0.80, w=0.32, shape="notch", color="#BE6BEA",
                      off=math.pi / 8, lag=0.1)],
         center=dict(kind="seeds", color="#FFD43B", dot="#E0A800", r=0.20)),
]

GREEN = "#5FAE6B"
GREEN_DK = "#468553"
LEAF = [(0, 0), (-.38, .28), (-.34, .7), (0, 1), (.34, .7), (.38, .28)]


def petal_points(shape, cx, cy, ang, length, half_w):
    dx, dy = math.sin(ang), -math.cos(ang)       # direction (0 = straight up)
    qx, qy = math.cos(ang), math.sin(ang)        # sideways
    pts = []
    for x, y in PETAL_SHAPES[shape]:
        pts += [cx + dx * y * length + qx * x * half_w, cy + dy * y * length + qy * x * half_w]
    return pts


def _lw():
    return max(1, px(1))


class Stage:
    """Draws the growing flower. Progress 0..1 = stem grows, then the bloom opens."""

    def __init__(self, cv):
        self.cv = cv
        self.idx = random.randrange(len(FLOWERS))
        self.disp = 0.0          # what is drawn
        self.target = 0.0        # real progress from the converter
        self.mode = "idle"       # idle | running | done | stopped
        self.t = 0.0
        self.last = time.perf_counter()
        self.parts = []
        self.burst = None
        self.dirty = True
        self.source = "drawn"     # drawn | recorded
        self.gray = False
        self.clip, self.frames, self.last_clip = None, [], None
        self._cache = {}

    @property
    def spec(self):
        return FLOWERS[self.idx]

    @property
    def active(self):
        return self.mode in ("running", "done") or bool(self.parts)

    def adopt(self, other):
        for k in ("idx", "disp", "target", "mode", "t", "last", "parts", "burst", "clip", "frames", "last_clip"):
            setattr(self, k, getattr(other, k))
        self.dirty = True

    def new_flower(self):
        self.idx = random.choice([i for i in range(len(FLOWERS)) if i != self.idx])

    def start(self):
        self.new_flower()
        self.clip, self.frames = None, []
        if self.source == "recorded" and have_pil():
            self._pick_clip()
        self.disp = self.target = 0.0
        self.mode = "running"
        self.parts, self.burst = [], None
        self.last = time.perf_counter()
        self.dirty = True

    def _pick_clip(self):
        clips = list_clips()
        if not clips:
            return
        names = [n for n in clips if n != self.last_clip] or list(clips)
        self.clip = random.choice(names)
        self.frames = clips[self.clip]
        self.last_clip = self.clip

    def finish(self):
        self.target = 1.0
        self.mode = "done"

    def stop(self):
        self.mode = "stopped"
        self.dirty = True

    def reset(self):
        self.mode = "idle"
        self.disp = self.target = 0.0
        self.parts, self.burst = [], None
        self.dirty = True

    # ------------------------------------------------------------ update
    def tick(self):
        now = time.perf_counter()
        dt = min(now - self.last, 0.1)
        self.last = now
        self.t += dt
        if self.mode == "running":
            goal = min(self.target + 0.03, 0.985)
        elif self.mode == "done":
            goal = 1.0
        else:
            goal = self.disp
        if self.disp < goal:
            self.disp = min(goal, self.disp + (goal - self.disp) * (1 - math.exp(-dt * 2.2)) + 0.0004 * dt)
        if self.mode == "done" and self.disp > 0.994:
            self.disp = 1.0
            if self.burst is None:
                self.burst = self.t
                if not self.clip:
                    self._spawn(30, burst=True)
            elif not self.clip and self.t - self.burst < 7 and random.random() < dt * 3:
                self._spawn(1, burst=False)
        for p in self.parts:
            p["x"] += p["vx"] * dt
            p["y"] += p["vy"] * dt
            p["vy"] += px(110) * dt
            p["vx"] *= 0.992
            p["a"] += p["va"] * dt
            p["life"] -= dt
        self.parts = [p for p in self.parts if p["life"] > 0]

    def _geometry(self):
        w, h = max(self.cv.winfo_width(), 50), max(self.cv.winfo_height(), 50)
        gy = h - px(104)
        hs = gy * 0.52
        R = min(w * 0.27, gy * 0.20) * self.spec["scale"]
        return w, h, w / 2.0, gy, hs, R

    def _spawn(self, n, burst):
        w, h, cx, gy, hs, R = self._geometry()
        hx, hy = cx, gy - hs
        cols = [l["color"] for l in self.spec["layers"]] + ["#FFFFFF"]
        for _ in range(n):
            a = random.uniform(0, 2 * math.pi)
            sp = random.uniform(px(60), px(170)) if burst else random.uniform(0, px(25))
            self.parts.append(dict(
                x=hx + (math.cos(a) * R * 0.3 if burst else random.uniform(-R, R)),
                y=hy + (math.sin(a) * R * 0.3 if burst else -R * 0.9),
                vx=math.cos(a) * sp, vy=math.sin(a) * sp - (px(70) if burst else 0),
                a=random.uniform(0, 6.28), va=random.uniform(-3, 3),
                size=random.uniform(0.10, 0.17) * R, color=random.choice(cols),
                life=random.uniform(3.0, 5.0) if burst else random.uniform(3.5, 5.5)))

    # -------------------------------------------------------------- draw
    def draw(self):
        cv = self.cv
        w, h, cx, gy, Hs, R = self._geometry()
        d = self.disp
        s = ease(d / 0.34)                       # stem growth
        b = clamp01((d - 0.22) / 0.78)           # bloom
        live = self.mode in ("running", "done")
        sway = (math.sin(self.t * 1.3) * 0.6 + math.sin(self.t * 0.7 + 1.0) * 0.4) if live else 0.0
        hx, hy = cx + sway * px(7) * s, gy - Hs * s
        c = dict(w=w, h=h, cx=cx, gy=gy, R=R, d=d, s=s, b=b, head_s=ease((d - 0.08) / 0.2),
                 hx=hx, hy=hy, p0=(cx, gy), p1=(cx - sway * px(10) * s, (gy + hy) / 2), p2=(hx, hy))

        cv.delete("all")
        cv.create_rectangle(0, 0, w - 1, h - 1, fill=PANEL, outline=LINE, width=1)
        if self.clip and self.frames and self.mode != "idle":
            try:
                self._draw_clip(w, h, d)
                self._marks(w, h)
                self._text(w, h, d, backdrop=True)
                self.dirty = False
                return
            except Exception:  # noqa: BLE001
                self.clip, self.frames = None, []       # fall back to the drawn flower
        self._marks(w, h)
        line = CURRENT_FLOWERS == "line"
        if line:
            self._ground_line(c)
        else:
            self._ground_color(c)
        self._stem(c, line)
        if c["head_s"] > 0.01:
            self._head(c, line)
        if line and self.mode == "done" and d >= 1:
            rr = R * (1.22 + 0.03 * math.sin(self.t * 2.0))
            cv.create_oval(hx - rr, hy - rr, hx + rr, hy + rr, outline=MUTED, dash=(2, 6), width=1)
        for p in self.parts:
            fade = clamp01(p["life"] / 1.2)
            pts = petal_points("round", p["x"], p["y"], p["a"], p["size"] * 2.0, p["size"])
            if line:
                cv.create_polygon(pts, smooth=True, fill=PANEL, outline=mix(PANEL, INK, fade), width=1)
            else:
                cv.create_polygon(pts, smooth=True, fill=mix(PANEL, p["color"], fade), outline="")
        self._text(w, h, d)
        self.dirty = False

    def _draw_clip(self, w, h, d):
        """Show the recorded frame that matches the progress (0 = first frame, 1 = last)."""
        from PIL import Image, ImageOps, ImageTk
        n = len(self.frames)
        i = max(0, min(n - 1, int(clamp01(d) * (n - 1) + 0.5)))
        aw, ah = max(10, w - 2), max(10, h - px(96))
        key = (self.clip, i, aw, ah, self.gray)
        photo = self._cache.get(key)
        if photo is None:
            im = Image.open(self.frames[i]).convert("RGB")
            if self.gray:
                im = ImageOps.grayscale(im).convert("RGB")
            sc = max(aw / float(im.width), ah / float(im.height))          # cover the area
            nw, nh = max(aw, int(im.width * sc + 0.5)), max(ah, int(im.height * sc + 0.5))
            im = im.resize((nw, nh), Image.LANCZOS)
            left, top = (nw - aw) // 2, (nh - ah) // 2
            photo = ImageTk.PhotoImage(im.crop((left, top, left + aw, top + ah)))
            if len(self._cache) >= 40:
                self._cache.pop(next(iter(self._cache)))
            self._cache[key] = photo
        self.cv.create_image(1, 1, image=photo, anchor="nw")

    def _marks(self, w, h):
        col = mix(PANEL, TEXT, 0.35)
        m, L = px(10), px(10)
        for x, sx in ((m, 1), (w - 1 - m, -1)):
            for y, sy in ((m, 1), (h - 1 - m, -1)):
                self.cv.create_line(x, y + sy * L, x, y, x + sx * L, y, fill=col, width=1)

    def _text(self, w, h, d, backdrop=False):
        cv, spec = self.cv, self.spec
        mode = self.mode
        if mode == "idle":
            top, pct, word, sub = "--  STANDBY", "---", "IDLE", "Choose a song."
        else:
            top = (self.clip or "").upper()[:26] if self.clip else "%02d  %s" % (self.idx + 1, spec["name"].upper())
            pct = "%03d%%" % (100 if mode == "done" else int(round(min(d, 0.99) * 100)))
            word = {"running": "GROWING", "done": "IN BLOOM", "stopped": "STOPPED"}[mode]
            sub = {"running": "Working on your song.", "done": "Complete. MIDI is ready.",
                   "stopped": "Stopped before finishing."}[mode]
        if backdrop:
            cv.create_rectangle(px(14), px(11), px(26) + len(top) * px(7), px(33), fill=PANEL, outline="")
            cv.create_rectangle(w - px(26) - len(APP_NAME) * px(7), px(11), w - px(14), px(33), fill=PANEL, outline="")
        cv.create_text(px(20), px(22), text=top, anchor="w", fill=MUTED, font=(MONO, 9))
        cv.create_text(w - px(20), px(22), text=APP_NAME.upper(), anchor="e", fill=MUTED, font=(MONO, 9))
        cv.create_line(px(20), h - px(88), w - px(20), h - px(88), fill=LINE, width=1)
        cv.create_text(px(20), h - px(56), text=pct, anchor="w", fill=TEXT, font=(MONO, 30, "bold"))
        cv.create_text(w - px(20), h - px(62), text=word, anchor="e", fill=TEXT, font=(MONO, 10, "bold"))
        cv.create_text(px(20), h - px(22), text=sub, anchor="w", fill=MUTED, font=(MONO, 9))

    # ---------------------------------------------------------- scenery
    def _ground_line(self, c):
        cv, cx, gy = self.cv, c["cx"], c["gy"]
        hatch = mix(PANEL, INK, 0.45)
        cv.create_line(cx - px(120), gy, cx + px(120), gy, fill=INK, width=_lw())
        for k in range(-5, 6):
            x = cx + k * px(20)
            cv.create_line(x, gy + px(2), x - px(6), gy + px(9), fill=hatch, width=1)
        if c["d"] < 0.05:
            r = px(4) * (1.0 + 0.12 * math.sin(self.t * 3.0))
            cv.create_oval(cx - r, gy - 2 * r, cx + r, gy, outline=INK, fill=PANEL, width=_lw())

    def _ground_color(self, c):
        cv, cx, gy, hx, hy, R = self.cv, c["cx"], c["gy"], c["hx"], c["hy"], c["R"]
        base = self.spec["layers"][0]["color"]
        pulse = 1.0 + (0.25 * math.sin(self.t * 2.0) if self.mode == "done" and c["d"] >= 1 else 0.0)
        g = ease(c["b"])
        for i in range(12):                       # many faint rings = a smooth glow
            f = i / 11.0
            rr = min(R * (2.2 - 1.2 * f) * (0.5 + 0.5 * g), c["w"] / 2.0 - px(6))
            cv.create_oval(hx - rr, hy - rr, hx + rr, hy + rr,
                           fill=mix(PANEL, base, (0.02 + 0.15 * f * f) * g * pulse), outline="")
        cv.create_oval(cx - px(86), gy - px(12), cx + px(86), gy + px(18), fill=mix(PANEL, TEXT, .08), outline="")
        cv.create_oval(cx - px(60), gy - px(14), cx + px(60), gy + px(6), fill=mix(PANEL, TEXT, .14), outline="")
        if c["d"] < 0.05:
            r = px(5) * (1.0 + 0.12 * math.sin(self.t * 3.0))
            cv.create_oval(cx - r, gy - r * 0.8, cx + r, gy + r * 0.8, fill=mix(base, "#8a6a50", .5), outline="")

    def _stem(self, c, line):
        cv, s = self.cv, c["s"]
        if s <= 0.01:
            return
        p0, p1, p2 = c["p0"], c["p1"], c["p2"]
        cv.create_line(p0[0], p0[1], p1[0], p1[1], p2[0], p2[1], smooth=True,
                       fill=INK if line else GREEN, width=px(2) if line else px(5), capstyle="round")
        leaf_p = ease((s - 0.30) / 0.6)
        if leaf_p <= 0.02:
            return
        for t_pos, side in ((0.34, -1), (0.58, 1)):
            lx, ly = bez(p0, p1, p2, t_pos)
            ang = side * math.radians(62)
            size = px(54) * leaf_p * (1.0 if t_pos < 0.5 else 0.85)
            pts = []
            for x, y in LEAF:
                pts += [lx + math.sin(ang) * y * size + math.cos(ang) * x * size * 0.55,
                        ly - math.cos(ang) * y * size + math.sin(ang) * x * size * 0.55]
            if line:
                cv.create_polygon(pts, smooth=True, fill=PANEL, outline=INK, width=_lw())
                rib = mix(PANEL, INK, .5)
            else:
                cv.create_polygon(pts, smooth=True, fill=GREEN, outline="")
                rib = mix(GREEN, "#ffffff", .25)
            cv.create_line(lx, ly, lx + math.sin(ang) * size * .85, ly - math.cos(ang) * size * .85,
                           fill=rib, width=1)

    def _head(self, c, line):
        cv, spec = self.cv, self.spec
        hx, hy, b = c["hx"], c["hy"], c["b"]
        Re = c["R"] * c["head_s"]
        cal = 0.5 + 0.5 * b
        cv.create_oval(hx - Re * 0.26 * cal, hy - Re * 0.02, hx + Re * 0.26 * cal, hy + Re * 0.30 * cal,
                       fill=PANEL if line else GREEN_DK, outline=INK if line else "", width=_lw())
        for li, layer in enumerate(spec["layers"]):
            lag = layer.get("lag", 0.0)
            lb = clamp01((b - lag) / (1 - lag))
            le, lo = ease_out(lb), ease(lb)
            length = Re * layer["L"] * (0.30 + 0.70 * le)
            hw = Re * layer["w"] * (0.55 + 0.45 * le)
            n, off = layer["n"], layer.get("off", 0.0)
            for i in range(n):
                ang = (off + (i - (n - 1) / 2.0) * 2 * math.pi / n) * lo
                pts = petal_points(layer["shape"], hx, hy, ang, length, hw)
                if line:
                    cv.create_polygon(pts, smooth=True, fill=mix(PANEL, INK, 0.05 + 0.09 * li),
                                      outline=INK, width=_lw())
                    cv.create_line(hx, hy, hx + math.sin(ang) * length * .62, hy - math.cos(ang) * length * .62,
                                   fill=mix(PANEL, INK, .5), width=1)
                else:
                    cv.create_polygon(pts, smooth=True, fill=layer["color"], outline="")
                    cv.create_polygon(petal_points(layer["shape"], hx, hy, ang, length * 0.72, hw * 0.40),
                                      smooth=True, fill=mix(layer["color"], "#ffffff", 0.22), outline="")
        self._center(c, Re, line)

    def _center(self, c, Re, line):
        cv, spec = self.cv, self.spec["center"]
        hx, hy, b = c["hx"], c["hy"], c["b"]
        grow = 0.4 + 0.6 * ease_out(clamp01((b - 0.15) / 0.85))
        cr = Re * spec["r"] * grow
        kind = spec["kind"]
        main = INK if line else spec["color"]
        dot = PANEL if line else spec["dot"]
        if kind == "stamens":
            for j in range(5):
                a = j * 2 * math.pi / 5
                x1, y1 = hx + math.sin(a) * cr * 1.15, hy - math.cos(a) * cr * 1.15
                cv.create_line(hx + math.sin(a) * Re * 0.05, hy - math.cos(a) * Re * 0.05, x1, y1,
                               fill=main, width=max(2, px(3) if line else px(4)), capstyle="round")
                cv.create_oval(x1 - Re * .045, y1 - Re * .045, x1 + Re * .045, y1 + Re * .045,
                               fill=INK if line else spec["dot"], outline="")
            return
        if kind == "disc" and line:
            cv.create_oval(hx - cr, hy - cr, hx + cr, hy + cr, fill=PANEL, outline=INK, width=_lw())
            hr = cr * 0.45
            cv.create_oval(hx - hr, hy - hr, hx + hr, hy + hr, fill=INK, outline="")
            return
        cv.create_oval(hx - cr, hy - cr, hx + cr, hy + cr, fill=main, outline="")
        if kind == "seeds" and cr > px(6):
            dr = max(1.0, cr * 0.06)
            for k in range(1, 46):
                r = cr * 0.9 * math.sqrt(k / 46.0)
                th = k * 2.399963
                x, y = hx + math.cos(th) * r, hy + math.sin(th) * r
                cv.create_oval(x - dr, y - dr, x + dr, y + dr, fill=dot, outline="")
        elif kind == "disc":
            hr = cr * 0.45
            cv.create_oval(hx - hr, hy - hr, hx + hr, hy + hr, fill=spec["dot"], outline="")


# ======================================================================
# Widgets: flat, square, 1px lines. Colours are read at draw time so a
# theme change only needs the window to be rebuilt.
# ======================================================================
def _bind_var(widget, var):
    """Redraw when a variable changes; detach when the widget goes away."""
    tid = var.trace_add("write", lambda *a: widget.redraw() if widget.winfo_exists() else None)
    widget.bind("<Destroy>", lambda e: var.trace_remove("write", tid), add="+")


class Btn(tk.Canvas):
    def __init__(self, parent, text, command, kind="primary", height=46, width=100):
        super().__init__(parent, height=px(height), width=px(width), bg=BG,
                         highlightthickness=0, bd=0, cursor="hand2")
        self.text, self.command, self.kind = text, command, kind
        self.enabled, self.hover, self.down = True, False, False
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Enter>", lambda e: self._set(hover=True))
        self.bind("<Leave>", lambda e: self._set(hover=False, down=False))
        self.bind("<ButtonPress-1>", lambda e: self._set(down=True))
        self.bind("<ButtonRelease-1>", self._release)

    def _set(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)
        self.redraw()

    def _release(self, e):
        was = self.down
        self._set(down=False)
        if was and self.enabled and 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height():
            self.command()

    def set_enabled(self, on):
        self.enabled = on
        self.config(cursor="hand2" if on else "arrow")
        self.redraw()

    def set_text(self, text):
        self.text = text
        self.redraw()

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        if self.kind == "primary":
            if not self.enabled:
                fill, fg, outline = FIELD, MUTED, LINE
            else:
                fill = mix(ACCENT, BG, 0.35) if self.down else ACCENT_HI if self.hover else ACCENT
                fg, outline = ON_ACCENT, ACCENT
        else:
            fill = FIELD if (self.hover and self.enabled) else BG
            fg = TEXT if self.enabled else MUTED
            outline = TEXT if (self.hover and self.enabled) else LINE
        self.create_rectangle(0, 0, w - 1, h - 1, fill=fill, outline=outline, width=1)
        self.create_text(w / 2, h / 2, text=self.text.upper(), fill=fg,
                         font=(MONO, 11 if self.kind == "primary" else 9, "bold"))


class Chip(tk.Canvas):
    """Square toggle. With value=None it flips a BooleanVar, otherwise it selects `value`."""

    def __init__(self, parent, text, var, value=None, height=36):
        super().__init__(parent, height=px(height), width=px(40), bg=BG,
                         highlightthickness=0, bd=0, cursor="hand2")
        self.text, self.var, self.value, self.hover = text, var, value, False
        _bind_var(self, var)
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Enter>", lambda e: self._hov(True))
        self.bind("<Leave>", lambda e: self._hov(False))
        self.bind("<ButtonRelease-1>", self._click)

    def _hov(self, v):
        self.hover = v
        self.redraw()

    def _click(self, e):
        if self.value is None:
            self.var.set(not self.var.get())
        else:
            self.var.set(self.value)

    def selected(self):
        return bool(self.var.get()) if self.value is None else self.var.get() == self.value

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        on = self.selected()
        fill = ACCENT if on else BG
        fg = ON_ACCENT if on else TEXT
        outline = ACCENT if on else (TEXT if self.hover else LINE)
        self.create_rectangle(0, 0, w - 1, h - 1, fill=fill, outline=outline, width=1)
        self.create_text(w / 2, h / 2, text=self.text.upper(), fill=fg, font=(MONO, 9, "bold"))


class Switch(tk.Canvas):
    def __init__(self, parent, text, var):
        super().__init__(parent, height=px(28), width=px(200), bg=BG,
                         highlightthickness=0, bd=0, cursor="hand2")
        self.text, self.var = text, var
        _bind_var(self, var)
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonRelease-1>", lambda e: var.set(not var.get()))

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        s = px(14)
        y0 = (h - s) / 2
        self.create_rectangle(1, y0, 1 + s, y0 + s, fill=BG, outline=TEXT, width=1)
        if self.var.get():
            i = px(3)
            self.create_rectangle(1 + i, y0 + i, 1 + s - i, y0 + s - i, fill=ACCENT, outline="")
        self.create_text(s + px(14), h / 2, text=self.text, fill=TEXT, font=(SANS, 10), anchor="w")


class Slider(tk.Canvas):
    def __init__(self, parent, var, lo, hi, step, fmt=str):
        super().__init__(parent, height=px(26), width=px(200), bg=BG,
                         highlightthickness=0, bd=0, cursor="hand2")
        self.var, self.lo, self.hi, self.step, self.fmt = var, lo, hi, step, fmt
        _bind_var(self, var)
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._drag)
        self.bind("<B1-Motion>", self._drag)

    def _track(self):
        return px(6), self.winfo_width() - px(62)

    def _drag(self, e):
        x0, x1 = self._track()
        pos = clamp01((e.x - x0) / max(1, x1 - x0))
        val = self.lo + pos * (self.hi - self.lo)
        val = round(round(val / self.step) * self.step, 4)
        self.var.set(min(self.hi, max(self.lo, val)))

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        x0, x1 = self._track()
        pos = clamp01((float(self.var.get()) - self.lo) / (self.hi - self.lo))
        xk = x0 + pos * (x1 - x0)
        self.create_line(x0, h / 2, x1, h / 2, fill=LINE, width=1)
        self.create_line(x0, h / 2, xk, h / 2, fill=ACCENT, width=px(2))
        kw, kh = px(5), px(8)
        self.create_rectangle(xk - kw, h / 2 - kh, xk + kw, h / 2 + kh, fill=ACCENT, outline=BG, width=1)
        self.create_text(w - 1, h / 2, text=self.fmt(self.var.get()), fill=MUTED, font=(MONO, 9), anchor="e")


class Prog(tk.Canvas):
    def __init__(self, parent):
        super().__init__(parent, height=px(3), width=px(100), bg=BG, highlightthickness=0, bd=0)
        self.v = 0.0
        self.bind("<Configure>", lambda e: self.redraw())

    def set(self, v):
        if abs(v - self.v) > 0.001:
            self.v = v
            self.redraw()

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        self.create_rectangle(0, 0, w, h, fill=LINE, outline="")
        if self.v > 0.002:
            self.create_rectangle(0, 0, w * min(1.0, self.v), h, fill=ACCENT, outline="")


class Picker(tk.Canvas):
    """Click target showing the chosen song."""

    def __init__(self, parent, command):
        super().__init__(parent, height=px(76), width=px(200), bg=BG,
                         highlightthickness=0, bd=0, cursor="hand2")
        self.command, self.hover = command, False
        self.title, self.sub = "Choose a song", ""
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Enter>", lambda e: self._hov(True))
        self.bind("<Leave>", lambda e: self._hov(False))
        self.bind("<ButtonRelease-1>", lambda e: self.command())

    def _hov(self, v):
        self.hover = v
        self.redraw()

    def set(self, title, sub):
        self.title, self.sub = title, sub
        self.redraw()

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4:
            return
        self.create_rectangle(0, 0, w - 1, h - 1, fill=FIELD, outline=TEXT if self.hover else LINE, width=1)
        self.create_text(px(14), px(15), text="SONG", fill=MUTED, font=(MONO, 8), anchor="w")
        if self.sub:
            self.create_text(w - px(14), px(15), text=self.sub, fill=MUTED, font=(MONO, 8), anchor="e")
        name = self.title
        limit = max(8, int((w - px(28)) / px(9)))
        if len(name) > limit:
            name = name[:limit - 1] + "\u2026"
        self.create_text(px(14), h - px(26), text=name, fill=TEXT, font=(SANS, 13), anchor="w")


class Link(tk.Label):
    def __init__(self, parent, text, command, fg=None):
        self._fg = fg or MUTED
        super().__init__(parent, text=text, bg=BG, fg=self._fg, font=(MONO, 9), cursor="hand2")
        self.bind("<Enter>", lambda e: self.config(fg=TEXT, font=(MONO, 9, "underline")))
        self.bind("<Leave>", lambda e: self.config(fg=self._fg, font=(MONO, 9)))
        self.bind("<ButtonRelease-1>", lambda e: command())

    def set_active(self, on):
        self._fg = TEXT if on else MUTED
        self.config(fg=self._fg)


class Logo(tk.Canvas):
    """The sakura mark, drawn in the current theme."""

    def __init__(self, parent, size=46):
        super().__init__(parent, width=px(size), height=px(size), bg=BG, highlightthickness=0, bd=0)
        self.size = px(size)
        self.bind("<Configure>", lambda e: self.redraw())
        self.after(10, self.redraw)

    def redraw(self):
        self.delete("all")
        s = self.size
        cx = cy = s / 2.0
        R = s * 0.43
        color = CURRENT_FLOWERS == "color"
        for i in range(5):
            ang = (i - 2) * 2 * math.pi / 5
            pts = petal_points("notch", cx, cy + R * 0.06, ang, R, R * 0.5)
            if color:
                self.create_polygon(pts, smooth=True, fill=ACCENT, outline="")
            else:
                self.create_polygon(pts, smooth=True, fill=BG, outline=TEXT, width=max(1, px(1)))
        for i in range(5):
            ang = (i - 2) * 2 * math.pi / 5
            self.create_line(cx + math.sin(ang) * R * 0.06, cy + R * 0.06 - math.cos(ang) * R * 0.06,
                             cx + math.sin(ang) * R * 0.42, cy + R * 0.06 - math.cos(ang) * R * 0.42,
                             fill=TEXT, width=max(2, px(2)), capstyle="round")


# ======================================================================
# The app
# ======================================================================
class App(tk.Tk):
    def __init__(self, settings=None):
        global SCALE
        super().__init__()
        SCALE = max(1.0, self.winfo_fpixels("1i") / 96.0)
        self.title(APP_NAME)
        self.configure(bg=BG)

        self.q = queue.Queue()
        self.proc = None
        self.cancel_flag = threading.Event()
        self.worker = None
        self.last_midi_dir = None
        self.running = False
        self.body = None
        self.stage = None
        self.root_frame = None
        self._pop = self._pop_key = None
        self.dock_items = {}
        self.importing = False
        settings = settings or load_settings()
        self._warned = False
        self._done_ok = False

        self.audio_var = tk.StringVar()
        self.out_var = tk.StringVar(value=str(DEFAULT_OUT))
        self.model_var = tk.StringVar(value="6 stems")
        self.quant_var = tk.StringVar(value="1/16")
        self.onset_var = tk.DoubleVar(value=0.5)
        self.frame_var = tk.DoubleVar(value=0.3)
        self.minlen_var = tk.DoubleVar(value=100)
        self.bpm_var = tk.StringVar(value="")
        self.mono_var = tk.BooleanVar(value=True)
        self.clean_var = tk.BooleanVar(value=True)
        self.align_var = tk.BooleanVar(value=True)
        self.stem_vars = {s: tk.BooleanVar(value=(s != "drums")) for s in ALL_STEMS}
        self.status = tk.StringVar(value="Choose a song, then press Convert.")
        self.theme_var = tk.StringVar(value=CURRENT_THEME)
        self.flower_var = tk.StringVar(value="Colour" if CURRENT_FLOWERS == "color" else "Line")
        self.source_var = tk.StringVar(value="Recorded" if settings.get("source") == "recorded" else "Drawn")
        self.gray_var = tk.BooleanVar(value=bool(settings.get("gray")))
        self.source_var.trace_add("write", lambda *a: self.after(10, self._source_changed))
        self.gray_var.trace_add("write", lambda *a: self.after(10, self._source_changed))
        self.out_var.trace_add("write", lambda *a: self._refresh_dock())
        self.theme_var.trace_add("write", lambda *a: self.after(10, self._theme_changed))
        self.flower_var.trace_add("write", lambda *a: self.after(10, self._theme_changed))
        self.audio_var.trace_add("write", lambda *a: self._song_changed())
        self.adv_open = self.log_open = False

        self._set_icon()
        self._build()
        self.update_idletasks()
        self.minsize(self.winfo_reqwidth(), self.winfo_reqheight())
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.bind_all("<ButtonPress-1>", self._outside_click, add="+")
        self.bind("<Escape>", lambda e: self._close_pop())
        self.after(60, self._style_titlebar)
        self.after(100, self._poll)
        self.after(33, self._frame)
        self.after(400, self._check_deps)
        try:
            write_icon()
        except Exception:  # noqa: BLE001
            pass

    # ------------------------------------------------------------ chrome
    def _set_icon(self):
        try:
            self._icon = tk.PhotoImage(data=ICON_PNGS[96])
            self.iconphoto(True, self._icon)
        except Exception:  # noqa: BLE001
            pass

    def _style_titlebar(self):
        """Title bar that matches the theme (Windows 10/11)."""
        try:
            import ctypes
            self.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.winfo_id())

            def colorref(h):
                r, g, b = _rgb(h)
                return r | (g << 8) | (b << 16)

            def attr(code, value):
                v = ctypes.c_int(value)
                ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, code, ctypes.byref(v), ctypes.sizeof(v))

            dark = sum(_rgb(BG)) < 384
            attr(20, 1 if dark else 0)        # dark / light title bar
            attr(35, colorref(BG))            # caption colour (Windows 11)
            attr(36, colorref(TEXT))          # caption text colour
        except Exception:  # noqa: BLE001
            pass

    # ------------------------------------------------------------ themes
    def _theme_changed(self):
        theme = self.theme_var.get()
        flowers = "color" if self.flower_var.get() == "Colour" else "line"
        if theme != CURRENT_THEME:                 # picking a theme resets to its own flower style
            flowers = THEMES[theme]["flower"]
            self.flower_var.set("Colour" if flowers == "color" else "Line")
        if theme == CURRENT_THEME and flowers == CURRENT_FLOWERS:
            return
        apply_theme(theme, flowers)
        self._save_settings()
        self._rebuild()

    def _rebuild(self):
        old = self.stage
        log_text = self.log.get("1.0", "end-1c")
        adv, log, open_shown = self.adv_open, self.log_open, self._done_ok and self.open_link.winfo_ismapped()
        pop = self._pop_key
        self.root_frame.destroy()
        self._pop = self._pop_key = None
        self.configure(bg=BG)
        self.adv_open = self.log_open = False
        self._build()
        if old is not None:
            self.stage.adopt(old)
        self.log.config(state="normal")
        self.log.insert("end", log_text)
        self.log.config(state="disabled")
        if adv:
            self._toggle_adv()
        if log:
            self._toggle_log(show=True)
        if open_shown:
            self.open_link.pack(anchor="w", pady=(px(8), 0), after=self.prog)
        self.start_btn.set_enabled(not self.running)
        self.start_btn.set_text("Converting..." if self.running else "Convert")
        self.cancel_btn.set_enabled(self.running)
        self._song_changed()
        self.prog.set(self.stage.disp if self.stage.mode in ("running", "done") else 0.0)
        self._style_titlebar()
        self.stage.dirty = True
        if pop:
            self.after(40, lambda: self._open_pop(pop))

    # ------------------------------------------------------------ layout
    def _section(self, parent, num, title, first=False):
        row = tk.Frame(parent, bg=BG)
        row.pack(fill="x", pady=(0 if first else px(20), px(8)))
        tk.Label(row, text=num, font=(MONO, 9, "bold"), fg=TEXT, bg=BG).pack(side="left")
        tk.Label(row, text="  " + title, font=(MONO, 9), fg=MUTED, bg=BG).pack(side="left")
        tk.Frame(row, height=1, bg=LINE).pack(side="left", fill="x", expand=True, padx=(px(10), 0))

    def _build(self):
        root = tk.Frame(self, bg=BG)
        root.pack(fill="both", expand=True)
        self.root_frame = root
        self._build_dock(root)
        body = tk.Frame(root, bg=BG)
        body.pack(fill="both", expand=True, padx=px(26), pady=px(24))
        self.body = body
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)

        left = tk.Frame(body, bg=BG)
        left.grid(row=0, column=0, sticky="ns")
        tk.Frame(left, width=px(420), height=1, bg=BG).pack()

        # header
        hdr = tk.Frame(left, bg=BG)
        hdr.pack(fill="x")
        Logo(hdr).pack(side="left")
        txt = tk.Frame(hdr, bg=BG)
        txt.pack(side="left", padx=px(14))
        tk.Label(txt, text=APP_NAME, font=(LIGHT, 24), fg=TEXT, bg=BG).pack(anchor="w")
        tk.Label(txt, text="AUDIO TO MIDI", font=(MONO, 8), fg=MUTED, bg=BG).pack(anchor="w")

        # 01 song
        self._section(left, "01", "SONG")
        self.picker = Picker(left, self._pick_audio)
        self.picker.pack(fill="x")

        # 02 instruments
        self._section(left, "02", "INSTRUMENTS")
        grid = tk.Frame(left, bg=BG)
        grid.pack(fill="x")
        for c in range(3):
            grid.columnconfigure(c, weight=1, uniform="stem")
        for i, name in enumerate(ALL_STEMS):
            Chip(grid, name, self.stem_vars[name]).grid(
                row=i // 3, column=i % 3, sticky="ew",
                padx=(0 if i % 3 == 0 else px(6), 0), pady=(0 if i < 3 else px(6), 0))
        tk.Label(left, text="Violin, synths and everything else are in Other.",
                 font=(SANS, 9), fg=MUTED, bg=BG).pack(anchor="w", pady=(px(8), 0))

        # 03 timing
        self._section(left, "03", "SNAP TO BEAT")
        seg = tk.Frame(left, bg=BG)
        seg.pack(fill="x")
        for c, key in enumerate(QUANT_CHOICES):
            seg.columnconfigure(c, weight=1, uniform="q")
            Chip(seg, key, self.quant_var, value=key).grid(
                row=0, column=c, sticky="ew", padx=(0 if c == 0 else px(6), 0))

        # run
        row = tk.Frame(left, bg=BG)
        row.pack(fill="x", pady=(px(24), 0))
        self.start_btn = Btn(row, "Convert", self._start, kind="primary", height=50)
        self.start_btn.pack(side="left", fill="x", expand=True)
        self.cancel_btn = Btn(row, "Cancel", self._cancel, kind="ghost", height=50, width=96)
        self.cancel_btn.pack(side="left", padx=(px(8), 0))
        self.cancel_btn.set_enabled(False)

        self.status_lbl = tk.Label(left, textvariable=self.status, fg=WARN if self._warned else MUTED, bg=BG,
                                   font=(SANS, 10), anchor="w", justify="left", wraplength=px(420))
        self.status_lbl.pack(fill="x", pady=(px(14), px(8)))
        self.prog = Prog(left)
        self.prog.pack(fill="x")
        self.open_link = Link(left, "OPEN MIDI FOLDER  >", self._open_folder, fg=TEXT)

        # settings + log
        links = tk.Frame(left, bg=BG)
        links.pack(fill="x", pady=(px(20), 0))
        self.adv_link = Link(links, "+ MIDI SETTINGS", self._toggle_adv)
        self.adv_link.pack(side="left")
        self.log_link = Link(links, "+ LOG", self._toggle_log)
        self.log_link.pack(side="left", padx=(px(20), 0))
        self.adv = tk.Frame(left, bg=BG)
        self._build_settings(self.adv)
        self.log_frame = tk.Frame(left, bg=BG)
        self.log = tk.Text(self.log_frame, height=9, wrap="word", state="disabled", bg=FIELD, fg=TEXT,
                           relief="flat", bd=0, highlightthickness=1, highlightbackground=LINE,
                           font=(MONO, 9), padx=px(8), pady=px(6), insertbackground=TEXT)
        self.log.pack(fill="both", expand=True)

        # flower stage
        cv = tk.Canvas(body, width=px(380), height=px(600), bg=BG, highlightthickness=0, bd=0)
        cv.grid(row=0, column=1, sticky="nsew", padx=(px(26), 0))
        self.stage = Stage(cv)
        cv.bind("<Configure>", lambda e: setattr(self.stage, "dirty", True))
        self.stage.source = "recorded" if self.source_var.get() == "Recorded" else "drawn"
        self.stage.gray = bool(self.gray_var.get())

    # ------------------------------------------------------------ top dock
    def _build_dock(self, parent):
        dock = tk.Frame(parent, bg=BG)
        dock.pack(fill="x", padx=px(26), pady=px(11))
        self.dock = dock
        self.dock_items = {}
        for key in ("theme", "flowers", "output"):
            it = Link(dock, key, lambda k=key: self._toggle_pop(k))
            it.pack(side="left", padx=(0, px(26)))
            self.dock_items[key] = it
        self._dock_line = tk.Frame(parent, height=1, bg=LINE)
        self._dock_line.pack(fill="x")
        self._refresh_dock()

    def _refresh_dock(self):
        if not self.dock_items:
            return
        out = self.out_var.get().strip() or "."
        out = Path(out).name or out
        if self.source_var.get() == "Recorded":
            src = "RECORDED (%d)" % len(list_clips())
        else:
            src = "DRAWN " + ("COLOUR" if CURRENT_FLOWERS == "color" else "LINE")
        texts = {"theme": "THEME: " + CURRENT_THEME.upper(), "flowers": "FLOWERS: " + src,
                 "output": "OUTPUT: " + out[:22].upper()}
        for k, it in self.dock_items.items():
            try:
                it.config(text=texts[k] + "  \u25BE")
            except Exception:  # noqa: BLE001
                pass

    def _plabel(self, parent, text, first=False):
        r = tk.Frame(parent, bg=BG)
        r.pack(fill="x", pady=(0 if first else px(16), px(6)))
        tk.Label(r, text=text, font=(MONO, 8, "bold"), fg=TEXT, bg=BG).pack(side="left")
        tk.Frame(r, height=1, bg=LINE).pack(side="left", fill="x", expand=True, padx=(px(10), 0))

    def _toggle_pop(self, key):
        again = self._pop_key == key
        self._close_pop()
        if not again:
            self._open_pop(key)

    def _close_pop(self):
        if self._pop is not None:
            try:
                self._pop.destroy()
            except Exception:  # noqa: BLE001
                pass
        for it in self.dock_items.values():
            try:
                it.set_active(False)
            except Exception:  # noqa: BLE001
                pass
        self._pop = self._pop_key = None

    def _refresh_pop(self):
        key = self._pop_key
        if key:
            self._close_pop()
            self._open_pop(key)

    def _open_pop(self, key):
        """Settings dock: a panel that floats over the window instead of pushing it taller."""
        f = tk.Frame(self.root_frame, bg=BG, highlightthickness=1, highlightbackground=TEXT)
        inner = tk.Frame(f, bg=BG)
        inner.pack(padx=px(16), pady=px(14))
        tk.Frame(inner, width=px(344), height=1, bg=BG).pack()
        {"theme": self._pop_theme, "flowers": self._pop_flowers, "output": self._pop_output}[key](inner)
        self._pop, self._pop_key = f, key
        self.update_idletasks()
        x = self.dock_items[key].winfo_rootx() - self.root_frame.winfo_rootx()
        x = max(px(8), min(x, self.root_frame.winfo_width() - f.winfo_reqwidth() - px(8)))
        y = self._dock_line.winfo_rooty() - self.root_frame.winfo_rooty() + 1
        f.place(x=x, y=y)
        f.lift()
        for k, it in self.dock_items.items():
            it.set_active(k == key)

    def _outside_click(self, e):
        if self._pop is None:
            return
        w = str(e.widget)
        if w.startswith(str(self._pop)) or any(w == str(it) for it in self.dock_items.values()):
            return
        self._close_pop()

    def _pop_theme(self, f):
        self._plabel(f, "THEME", first=True)
        tg = tk.Frame(f, bg=BG)
        tg.pack(fill="x")
        for i, name in enumerate(THEME_ORDER):
            tg.columnconfigure(i % 3, weight=1, uniform="th")
            Chip(tg, name, self.theme_var, value=name, height=32).grid(
                row=i // 3, column=i % 3, sticky="ew",
                padx=(0 if i % 3 == 0 else px(6), 0), pady=(0 if i < 3 else px(6), 0))

    def _pop_flowers(self, f):
        self._plabel(f, "SOURCE", first=True)
        seg = tk.Frame(f, bg=BG)
        seg.pack(fill="x")
        for c, name in enumerate(("Drawn", "Recorded")):
            seg.columnconfigure(c, weight=1, uniform="src")
            Chip(seg, name, self.source_var, value=name, height=32).grid(
                row=0, column=c, sticky="ew", padx=(0 if c == 0 else px(6), 0))

        self._plabel(f, "DRAWN FLOWERS")
        seg = tk.Frame(f, bg=BG)
        seg.pack(fill="x")
        for c, name in enumerate(("Line", "Colour")):
            seg.columnconfigure(c, weight=1, uniform="sty")
            Chip(seg, name, self.flower_var, value=name, height=32).grid(
                row=0, column=c, sticky="ew", padx=(0 if c == 0 else px(6), 0))

        self._plabel(f, "RECORDED TIMELAPSES")
        clips = list_clips()
        if not have_pil():
            tk.Label(f, text="Needs Pillow. Run setup.bat again to add it.", font=(SANS, 9), fg=WARN,
                     bg=BG, anchor="w").pack(fill="x")
        if not clips:
            tk.Label(f, text="None imported yet.", font=(SANS, 10), fg=MUTED, bg=BG, anchor="w").pack(fill="x")
        for name, frames in list(clips.items())[:8]:
            r = tk.Frame(f, bg=BG)
            r.pack(fill="x", pady=1)
            tk.Label(r, text=name, font=(SANS, 10), fg=TEXT, bg=BG).pack(side="left")
            Link(r, "REMOVE", lambda n=name: self._remove_clip(n)).pack(side="right")
            tk.Label(r, text="%d frames" % len(frames), font=(MONO, 8), fg=MUTED, bg=BG).pack(
                side="right", padx=(0, px(12)))
        if len(clips) > 8:
            tk.Label(f, text="+ %d more" % (len(clips) - 8), font=(MONO, 8), fg=MUTED, bg=BG).pack(anchor="w")
        row = tk.Frame(f, bg=BG)
        row.pack(fill="x", pady=(px(10), 0))
        row.columnconfigure(0, weight=1, uniform="imp")
        row.columnconfigure(1, weight=1, uniform="imp")
        Btn(row, "Import video / GIF", self._import_file, kind="ghost", height=34).grid(row=0, column=0, sticky="ew")
        Btn(row, "Import folder", self._import_folder, kind="ghost", height=34).grid(
            row=0, column=1, sticky="ew", padx=(px(6), 0))
        Switch(f, "Black and white", self.gray_var).pack(fill="x", pady=(px(8), 0))
        tk.Label(f, text="A timelapse plays in step with progress: first frame at 0%, last frame at 100%. "
                         "Use one that ends in full bloom. Each conversion picks one at random.",
                 font=(SANS, 9), fg=MUTED, bg=BG, justify="left", wraplength=px(344), anchor="w").pack(
            fill="x", pady=(px(8), 0))

    def _pop_output(self, f):
        self._plabel(f, "OUTPUT FOLDER", first=True)
        of = tk.Frame(f, bg=BG)
        of.pack(fill="x")
        self._entry(of, self.out_var).pack(side="left", fill="x", expand=True, ipady=px(6))
        Btn(of, "Browse", self._pick_out, kind="ghost", height=34, width=84).pack(side="left", padx=(px(6), 0))
        tk.Label(f, text="Each song gets its own subfolder with its MIDI files and stems.",
                 font=(SANS, 9), fg=MUTED, bg=BG, anchor="w").pack(fill="x", pady=(px(8), 0))

    # ------------------------------------------------------------ flower source
    def _save_settings(self):
        save_settings({"theme": CURRENT_THEME, "flowers": CURRENT_FLOWERS,
                       "source": "recorded" if self.source_var.get() == "Recorded" else "drawn",
                       "gray": bool(self.gray_var.get())})

    def _source_changed(self):
        self.stage.source = "recorded" if self.source_var.get() == "Recorded" else "drawn"
        self.stage.gray = bool(self.gray_var.get())
        self.stage._cache.clear()
        self.stage.dirty = True
        self._save_settings()
        self._refresh_dock()

    def _import_file(self):
        p = filedialog.askopenfilename(
            title="Import a flower timelapse",
            filetypes=[("Video or animated image", "*.mp4 *.mov *.m4v *.webm *.mkv *.avi *.gif *.webp *.apng"),
                       ("All files", "*.*")])
        if p:
            self._start_import(p)

    def _import_folder(self):
        p = filedialog.askdirectory(title="Choose a folder of image frames")
        if p:
            self._start_import(p)

    def _start_import(self, path):
        if self.importing:
            return
        if self.running:
            self._warn("Wait for the conversion to finish before importing.")
            return
        self.importing = True
        self._say("Importing timelapse...")
        threading.Thread(target=self._import_worker, args=(path,), daemon=True).start()

    def _import_worker(self, path):
        try:
            name = import_clip(path, lambda t: self.q.put(("status", t)))
            self.q.put(("clip_done", True, 'Imported "%s". Set Source to Recorded to use it.' % name))
        except Exception as e:  # noqa: BLE001
            self.q.put(("clip_done", False, "Import failed: %s" % e))

    def _remove_clip(self, name):
        shutil.rmtree(FLOWERS_DIR / name, ignore_errors=True)
        if self.stage.clip == name and self.stage.mode != "running":
            self.stage.clip, self.stage.frames = None, []
        self.stage._cache.clear()
        self._refresh_dock()
        self._refresh_pop()

    def _entry(self, parent, var, width=None):
        e = tk.Entry(parent, textvariable=var, bg=FIELD, fg=TEXT, insertbackground=TEXT, relief="flat",
                     bd=0, highlightthickness=1, highlightbackground=LINE, highlightcolor=TEXT,
                     font=(MONO, 10), selectbackground=ACCENT, selectforeground=ON_ACCENT)
        if width:
            e.config(width=width)
        return e

    def _build_settings(self, a):
        def head(text, first=False):
            r = tk.Frame(a, bg=BG)
            r.pack(fill="x", pady=(px(14) if first else px(18), px(6)))
            tk.Label(r, text=text, font=(MONO, 8, "bold"), fg=TEXT, bg=BG).pack(side="left")
            tk.Frame(r, height=1, bg=LINE).pack(side="left", fill="x", expand=True, padx=(px(10), 0))

        def small(text):
            tk.Label(a, text=text, font=(SANS, 9), fg=MUTED, bg=BG).pack(anchor="w", pady=(px(10), px(3)))

        head("PROCESSING", first=True)
        small("Separation model")
        seg = tk.Frame(a, bg=BG)
        seg.pack(fill="x")
        for c, key in enumerate(MODELS):
            seg.columnconfigure(c, weight=1, uniform="m")
            Chip(seg, key, self.model_var, value=key, height=32).grid(
                row=0, column=c, sticky="ew", padx=(0 if c == 0 else px(6), 0))
        tk.Label(a, text="6 stems adds guitar and piano. 4 stems is lighter and faster.",
                 font=(SANS, 9), fg=MUTED, bg=BG).pack(anchor="w", pady=(px(4), 0))
        small("Note sensitivity (higher = fewer notes)")
        Slider(a, self.onset_var, 0.1, 0.9, 0.05, fmt=lambda v: "%.2f" % v).pack(fill="x")
        small("Note length cutoff (higher = shorter notes)")
        Slider(a, self.frame_var, 0.1, 0.9, 0.05, fmt=lambda v: "%.2f" % v).pack(fill="x")
        small("Shortest note")
        Slider(a, self.minlen_var, 20, 400, 10, fmt=lambda v: "%d ms" % v).pack(fill="x")
        small("Tempo in BPM (blank = detect automatically)")
        self._entry(a, self.bpm_var, width=10).pack(anchor="w", ipady=px(5))

        head("OPTIONS")
        Switch(a, "Single-note tracking for vocals and bass", self.mono_var).pack(fill="x")
        Switch(a, "Clean up notes (merge fragments, remove glitches)", self.clean_var).pack(fill="x")
        Switch(a, "Line up with the DAW grid (may delay MIDI by under a beat)", self.align_var).pack(fill="x")

    def _toggle_adv(self):
        self.adv_open = not self.adv_open
        if self.adv_open:
            self.adv.pack(fill="x", after=self.adv_link.master)
        else:
            self.adv.pack_forget()
        self.adv_link.config(text=("- " if self.adv_open else "+ ") + "MIDI SETTINGS")
        self.geometry("")

    def _toggle_log(self, show=None):
        self.log_open = (not self.log_open) if show is None else show
        if self.log_open:
            self.log_frame.pack(fill="both", expand=True, pady=(px(10), 0))
        else:
            self.log_frame.pack_forget()
        self.log_link.config(text=("- " if self.log_open else "+ ") + "LOG")
        self.geometry("")

    # ------------------------------------------------------------ helpers
    def _say(self, text, warn=False):
        self._warned = warn
        self.status.set(text)
        self.status_lbl.config(fg=WARN if warn else MUTED)

    def _warn(self, text):
        self._say(text, warn=True)

    def _song_changed(self):
        if self.body is None:
            return
        p = self.audio_var.get().strip().strip('"')
        if p:
            path = Path(p)
            self.picker.set(path.name, path.parent.name or str(path.parent))
        else:
            self.picker.set("Choose a song", "")

    def _missing_libs(self):
        importlib.invalidate_caches()
        return [pip for mod, pip in REQUIRED.items() if importlib.util.find_spec(mod) is None]

    def _check_deps(self):
        missing = self._missing_libs()
        if missing:
            self.start_btn.set_enabled(False)
            self._warn("Setup needed (" + ", ".join(missing) + "). Close this window, run setup.bat, "
                       "then open " + APP_NAME + " again.")

    # ------------------------------------------------------------ actions
    def _pick_audio(self):
        if self.running:
            return
        p = filedialog.askopenfilename(
            title="Choose a song",
            filetypes=[("Audio", "*.wav *.mp3 *.flac *.m4a *.ogg *.aac"), ("All files", "*.*")])
        if p:
            self.audio_var.set(p)
            if self.stage.mode != "idle":
                self.stage.reset()
                self.prog.set(0)
                self.open_link.pack_forget()
                self._done_ok = False
            self._say("Ready. Press Convert.")

    def _pick_out(self):
        p = filedialog.askdirectory(title="Choose output folder")
        if p:
            self.out_var.set(p)

    def _open_folder(self):
        if self.last_midi_dir and Path(self.last_midi_dir).exists():
            os.startfile(self.last_midi_dir)  # Windows

    def _cancel(self):
        self.cancel_flag.set()
        self._say("Cancelling...")
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()

    def _on_close(self):
        self.cancel_flag.set()
        try:
            if self.proc and self.proc.poll() is None:
                self.proc.terminate()
        except Exception:  # noqa: BLE001
            pass
        self.destroy()

    def _start(self):
        if self.running:
            return
        audio = Path(self.audio_var.get().strip().strip('"'))
        if not audio.is_file():
            self._warn("Choose a song first.")
            return
        keep = [s for s in ALL_STEMS if self.stem_vars[s].get()]
        if not keep:
            self._warn("Pick at least one instrument.")
            return
        bpm_override = None
        txt = self.bpm_var.get().strip()
        if txt:
            try:
                bpm_override = float(txt)
                if not 30 <= bpm_override <= 300:
                    raise ValueError
            except ValueError:
                self._warn("Tempo must be a number between 30 and 300, or blank.")
                if not self.adv_open:
                    self._toggle_adv()
                return

        base = Path(self.out_var.get())
        name = short_name(audio.stem, max(16, min(48, 150 - len(str(base)))))
        cfg = dict(
            audio=audio,
            out=Path(self.out_var.get()) / name,
            name=name,
            model=MODELS[self.model_var.get()],
            keep=keep,
            onset=float(self.onset_var.get()),
            frame=float(self.frame_var.get()),
            minlen=float(self.minlen_var.get()),
            mono=bool(self.mono_var.get()),
            cleanup=bool(self.clean_var.get()),
            subdiv=QUANT_CHOICES[self.quant_var.get()],
            bpm=bpm_override,
            align=bool(self.align_var.get()),
        )
        self.cancel_flag.clear()
        self.running = True
        self._done_ok = False
        self.start_btn.set_text("Converting...")
        self.start_btn.set_enabled(False)
        self.cancel_btn.set_enabled(True)
        self.open_link.pack_forget()
        self._clear_log()
        self._say("Starting...")
        self.stage.start()
        self.prog.set(0)
        self.worker = threading.Thread(target=self._run, args=(cfg,), daemon=True)
        self.worker.start()

    # ------------------------------------------------------------ frame loop
    def _frame(self):
        st = self.stage
        if st.active or st.dirty:
            if st.active:
                st.tick()
            st.draw()
            if st.mode in ("running", "done"):
                self.prog.set(st.disp)
        self.after(33 if st.active else 150, self._frame)

    def _clear_log(self):
        self.log.config(state="normal")
        self.log.delete("1.0", "end")
        self.log.config(state="disabled")

    def _append_log(self, text):
        self.log.config(state="normal")
        self.log.insert("end", text + "\n")
        self.log.see("end")
        self.log.config(state="disabled")

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "log":
                    self._append_log(msg[1])
                elif kind == "status":
                    self._say(msg[1])
                elif kind == "progress":
                    self.stage.target = max(self.stage.target, msg[1] / 100.0)
                elif kind == "midi_dir":
                    self.last_midi_dir = msg[1]
                elif kind == "clip_done":
                    self.importing = False
                    self._say(msg[2], warn=not msg[1])
                    self._refresh_dock()
                    self._refresh_pop()
                elif kind == "done":
                    ok, text = msg[1], msg[2]
                    self.running = False
                    self.start_btn.set_text("Convert")
                    self.start_btn.set_enabled(True)
                    self.cancel_btn.set_enabled(False)
                    if ok:
                        self._say(text)
                        self.stage.finish()
                        self._done_ok = True
                        self.open_link.pack(anchor="w", pady=(px(8), 0), after=self.prog)
                    else:
                        self._say(text, warn="Cancel" not in text)
                        self.stage.stop()
                        if "Cancel" not in text:
                            self._toggle_log(show=True)
        except queue.Empty:
            pass
        self.after(100, self._poll)

    # ------------------------------------------------------- thread side
    def _run(self, cfg):
        try:
            self._pipeline(cfg)
        except Cancelled:
            self.q.put(("done", False, "Cancelled."))
        except Exception as e:  # noqa: BLE001
            self.q.put(("log", f"ERROR: {e}"))
            self.q.put(("done", False, "Failed - see log."))

    def _python_exe(self):
        exe = sys.executable
        if exe.lower().endswith("pythonw.exe"):
            exe = exe[: -len("pythonw.exe")] + "python.exe"
        return exe

    def _pipeline(self, cfg):
        audio, out, model = cfg["audio"], cfg["out"], cfg["model"]
        out.mkdir(parents=True, exist_ok=True)
        stems_root = out / "stems"

        song = cfg["name"]
        need = 6 if model == "htdemucs_6s" else 4
        stem_dir = stems_root / model             # stems go straight in here, no second copy of the title
        legacy = stems_root / model / audio.stem  # older runs used a folder named after the song
        if legacy.exists() and len(list(legacy.glob("*.wav"))) >= need:
            stem_dir = legacy
        already = stem_dir.exists() and len(list(stem_dir.glob("*.wav"))) >= need

        if already:
            self.q.put(("log", "Stems already exist for this song - skipping separation."))
        else:
            # Step 1: Demucs
            self.q.put(("status", "Step 1/2: separating stems (this is the slow part)..."))
            self.q.put(("progress", 0))
            cmd = [self._python_exe(), "-m", "demucs", "-n", model, "-o", str(stems_root),
                   "--filename", "{stem}.{ext}", str(audio)]
            MODELS_DIR.mkdir(parents=True, exist_ok=True)
            env = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8",
                       TORCH_HOME=str(MODELS_DIR), HF_HOME=str(MODELS_DIR / "hf"),
                       HF_HUB_DISABLE_SYMLINKS_WARNING="1")
            flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            self.proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                encoding="utf-8", errors="replace", universal_newlines=True,
                env=env, creationflags=flags)
            pct_re = re.compile(r"(\d{1,3})%")
            tail = []
            for line in self.proc.stdout:
                if self.cancel_flag.is_set():
                    raise Cancelled
                line = line.strip()
                if not line:
                    continue
                m = pct_re.search(line)
                if m and "|" in line:
                    self.q.put(("progress", min(int(m.group(1)), 100) * 0.5))
                else:
                    self.q.put(("log", line))
                    tail.append(line)
                    tail = tail[-5:]
            code = self.proc.wait()
            if self.cancel_flag.is_set():
                raise Cancelled
            if code != 0:
                raise RuntimeError("Demucs failed:\n" + "\n".join(tail))

        if not stem_dir.exists():
            raise FileNotFoundError(f"Demucs output not found at {stem_dir}")

        # Step 2: transcription
        self.q.put(("status", "Step 2/2: loading transcription model..."))
        self.q.put(("progress", 50))
        import pretty_midi
        from basic_pitch import ICASSP_2022_MODEL_PATH
        from basic_pitch.inference import predict

        midi_dir = out / "midi"
        midi_dir.mkdir(exist_ok=True)
        wavs = [stem_dir / f"{s}.wav" for s in cfg["keep"] if (stem_dir / f"{s}.wav").exists()]
        if not wavs:
            raise RuntimeError("None of the selected stems were produced by this model.")

        # Find the beat so notes can be snapped to it
        grid_info = None
        if cfg["subdiv"] > 0:
            self.q.put(("status", "Step 2/2: finding the beat..."))
            ref = stem_dir / "drums.wav"
            if not ref.exists():
                ref = wavs[0]
            try:
                grid_info = detect_grid(ref, cfg["subdiv"], cfg["bpm"])
                kind = "steady" if grid_info["steady"] else "drifting - following the song's beat"
                self.q.put(("log", f"Tempo: {grid_info['bpm']:.1f} BPM ({kind})"))
                if cfg["align"] and grid_info["delay"] > 0.0005:
                    self.q.put(("log", f"MIDI is delayed {grid_info['delay']:.3f}s so notes sit on the "
                                       f"DAW grid. To line it up with the original audio, start the "
                                       f"MIDI clip {grid_info['delay']:.3f}s earlier."))
            except Exception as e:  # noqa: BLE001
                self.q.put(("log", f"Couldn't detect the beat ({e}); leaving timing unquantized."))

        def new_midi():
            if grid_info:
                return pretty_midi.PrettyMIDI(resolution=480, initial_tempo=grid_info["bpm"])
            return pretty_midi.PrettyMIDI()

        combined = new_midi()

        for i, wav in enumerate(wavs):
            if self.cancel_flag.is_set():
                raise Cancelled
            name = wav.stem
            self.q.put(("status", f"Step 2/2: transcribing {name} ({i + 1}/{len(wavs)})..."))
            self.q.put(("log", f"Transcribing {name}"))
            inst = None
            if name == "drums":
                try:
                    inst = transcribe_drums(wav)
                except Exception as e:  # noqa: BLE001
                    self.q.put(("log", f"  drum detection failed ({e}); skipping drums"))
                    continue
            elif cfg["mono"] and name in MONO_RANGES:
                try:
                    inst = transcribe_mono(wav, name, cfg["minlen"])
                except Exception as e:  # noqa: BLE001
                    self.q.put(("log", f"  pitch tracking failed ({e}); using Basic Pitch instead"))

            if inst is None:
                _, midi_data, _ = predict(
                    str(wav), ICASSP_2022_MODEL_PATH,
                    onset_threshold=cfg["onset"], frame_threshold=cfg["frame"],
                    minimum_note_length=cfg["minlen"], multiple_pitch_bends=False,
                    melodia_trick=True)
                inst = pretty_midi.Instrument(program=STEM_PROGRAMS.get(name, 0), name=name)
                for src in midi_data.instruments:
                    inst.notes.extend(src.notes)
                    inst.pitch_bends.extend(src.pitch_bends)
                inst.notes.sort(key=lambda n: n.start)
                if cfg["cleanup"]:
                    cleanup_notes(inst, cfg["minlen"] / 1000.0)

            if grid_info:
                quantize_instrument(inst, grid_info["grid"],
                                    mono=name in MONO_RANGES, drum=(name == "drums"))
                if cfg["align"] and grid_info["delay"]:
                    for n in inst.notes:
                        n.start += grid_info["delay"]
                        n.end += grid_info["delay"]

            single = new_midi()
            single.instruments.append(inst)
            single.write(str(midi_dir / f"{song}_{name}.mid"))
            combined.instruments.append(inst)
            self.q.put(("log", f"  {len(inst.notes)} notes"))
            self.q.put(("progress", 50 + 50 * (i + 1) / len(wavs)))

        combined.write(str(midi_dir / f"{song}_all_stems.mid"))
        self.q.put(("midi_dir", str(midi_dir)))
        self.q.put(("done", True, f"Done. MIDI files saved in {midi_dir}"))



def main():
    if "--make-icon" in sys.argv:        # used by setup.bat for the desktop shortcut
        write_icon()
        return
    settings = load_settings()
    apply_theme(settings["theme"], settings["flowers"])
    try:                                  # crisp rendering + own taskbar identity (Windows)
        import ctypes
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:  # noqa: BLE001
            ctypes.windll.user32.SetProcessDPIAware()
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("hanamidi.midi.app")
    except Exception:  # noqa: BLE001
        pass
    App(settings).mainloop()


if __name__ == "__main__":
    main()
