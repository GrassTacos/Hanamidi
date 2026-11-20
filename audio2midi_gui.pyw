#!/usr/bin/env python3
"""
audio2midi_gui.py - desktop interface for splitting a song into stems
(Demucs) and transcribing each stem to MIDI (Basic Pitch).

Self-contained: keep this file anywhere. On first launch it offers to install
its libraries, and all output (MIDI, stems, downloaded models) goes into a
'SongOutput' folder created next to this file. ffmpeg is still needed for
mp3/m4a input (wav works without it).

Run:
    py -3.11 audio2midi_gui.py
Tip: rename this file to audio2midi_gui.pyw to open it by double-click
with no console window.
"""

import importlib
import importlib.util
import os
import queue
import re
import subprocess
import sys
import threading
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

STEM_PROGRAMS = {
    "vocals": 54, "bass": 33, "guitar": 25,
    "piano": 0, "other": 80, "drums": 0,
}
# Everything lives next to this script, wherever it is stored.
BASE_DIR = Path(sys.argv[0]).resolve().parent if getattr(sys, "frozen", False) \
    else Path(__file__).resolve().parent
DEFAULT_OUT = BASE_DIR / "SongOutput"
MODELS_DIR = DEFAULT_OUT / "_models"      # Demucs model cache stays here too
REQUIRED = {"demucs": "demucs", "basic_pitch": "basic-pitch", "pretty_midi": "pretty_midi",
            "pkg_resources": "setuptools<81", "librosa": "librosa"}  # newer setuptools dropped pkg_resources

ALL_STEMS = ["vocals", "drums", "bass", "guitar", "piano", "other"]
MODELS = {
    "6 stems: vocals, drums, bass, guitar, piano, other": "htdemucs_6s",
    "4 stems: vocals, drums, bass, other (lighter)": "htdemucs",
}


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


QUANT_CHOICES = {"Off (keep original timing)": 0, "1/8 notes": 2,
                 "1/16 notes (recommended)": 4, "1/32 notes": 8}


class Cancelled(Exception):
    pass


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Audio to MIDI")
        self.geometry("680x760")
        self.minsize(620, 680)

        self.q = queue.Queue()
        self.proc = None
        self.cancel_flag = threading.Event()
        self.worker = None
        self.last_midi_dir = None

        self.audio_var = tk.StringVar()
        self.out_var = tk.StringVar(value=str(DEFAULT_OUT))
        self.model_var = tk.StringVar(value=list(MODELS)[0])
        self.onset_var = tk.DoubleVar(value=0.5)
        self.frame_var = tk.DoubleVar(value=0.3)
        self.minlen_var = tk.IntVar(value=100)
        self.mono_var = tk.BooleanVar(value=True)
        self.clean_var = tk.BooleanVar(value=True)
        self.quant_var = tk.StringVar(value=list(QUANT_CHOICES)[2])
        self.bpm_var = tk.StringVar(value="")
        self.align_var = tk.BooleanVar(value=True)
        self.stem_vars = {s: tk.BooleanVar(value=(s != "drums")) for s in ALL_STEMS}

        self._build()
        self.after(100, self._poll)
        self.after(400, self._check_deps)

    # ---------------------------------------------------------------- UI
    def _build(self):
        pad = {"padx": 10, "pady": 4}

        f = ttk.LabelFrame(self, text="Files")
        f.pack(fill="x", **pad)
        f.columnconfigure(1, weight=1)
        ttk.Label(f, text="Audio file").grid(row=0, column=0, sticky="w", padx=6, pady=4)
        ttk.Entry(f, textvariable=self.audio_var).grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Button(f, text="Browse...", command=self._pick_audio).grid(row=0, column=2, padx=6)
        ttk.Label(f, text="Output folder").grid(row=1, column=0, sticky="w", padx=6, pady=4)
        ttk.Entry(f, textvariable=self.out_var).grid(row=1, column=1, sticky="ew", padx=6)
        ttk.Button(f, text="Browse...", command=self._pick_out).grid(row=1, column=2, padx=6)

        m = ttk.LabelFrame(self, text="Separation model")
        m.pack(fill="x", **pad)
        ttk.Combobox(m, textvariable=self.model_var, values=list(MODELS),
                     state="readonly").pack(fill="x", padx=6, pady=6)

        s = ttk.LabelFrame(self, text="Transcribe these stems")
        s.pack(fill="x", **pad)
        for i, name in enumerate(ALL_STEMS):
            ttk.Checkbutton(s, text=name, variable=self.stem_vars[name]).grid(
                row=0, column=i, padx=8, pady=6)
        ttk.Label(s, text="Drums aren't pitched, so they're off by default. "
                          "Violin/synth end up in 'other'.",
                  foreground="#666").grid(row=1, column=0, columnspan=6,
                                          sticky="w", padx=8, pady=(0, 6))

        t = ttk.LabelFrame(self, text="Note detection")
        t.pack(fill="x", **pad)
        t.columnconfigure(1, weight=1)
        self._slider(t, 0, "Onset threshold (higher = fewer notes)",
                     self.onset_var, 0.1, 0.9, 0.05)
        self._slider(t, 1, "Frame threshold (higher = shorter notes)",
                     self.frame_var, 0.1, 0.9, 0.05)
        self._slider(t, 2, "Minimum note length (ms)",
                     self.minlen_var, 20, 400, 10, integer=True)
        ttk.Checkbutton(t, text="Single-note mode for vocals & bass (pitch tracking, usually much cleaner)",
                        variable=self.mono_var).grid(row=3, column=0, columnspan=3, sticky="w", padx=6)
        ttk.Checkbutton(t, text="Clean up notes (merge fragments, remove glitches)",
                        variable=self.clean_var).grid(row=4, column=0, columnspan=3, sticky="w", padx=6, pady=(0, 4))

        q = ttk.LabelFrame(self, text="Timing (snap notes to the beat)")
        q.pack(fill="x", **pad)
        q.columnconfigure(1, weight=1)
        ttk.Label(q, text="Snap notes to").grid(row=0, column=0, sticky="w", padx=6, pady=4)
        ttk.Combobox(q, textvariable=self.quant_var, values=list(QUANT_CHOICES),
                     state="readonly").grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Label(q, text="Tempo override (BPM)").grid(row=1, column=0, sticky="w", padx=6, pady=4)
        ttk.Entry(q, textvariable=self.bpm_var, width=8).grid(row=1, column=1, sticky="w", padx=6)
        ttk.Label(q, text="leave blank to auto-detect", foreground="#666").grid(
            row=1, column=1, sticky="e", padx=6)
        ttk.Checkbutton(q, text="Line up with the DAW grid (delays MIDI by under one beat; "
                                "the log says by how much)",
                        variable=self.align_var).grid(row=2, column=0, columnspan=2,
                                                      sticky="w", padx=6, pady=(0, 4))

        b = ttk.Frame(self)
        b.pack(fill="x", **pad)
        self.start_btn = ttk.Button(b, text="Convert", command=self._start)
        self.start_btn.pack(side="left")
        self.cancel_btn = ttk.Button(b, text="Cancel", command=self._cancel, state="disabled")
        self.cancel_btn.pack(side="left", padx=6)
        self.open_btn = ttk.Button(b, text="Open MIDI folder", command=self._open_folder,
                                   state="disabled")
        self.open_btn.pack(side="right")

        self.status = tk.StringVar(value="Pick an audio file and press Convert.")
        ttk.Label(self, textvariable=self.status).pack(fill="x", padx=10)
        self.bar = ttk.Progressbar(self, maximum=100)
        self.bar.pack(fill="x", padx=10, pady=4)

        lf = ttk.LabelFrame(self, text="Log")
        lf.pack(fill="both", expand=True, **pad)
        self.log = tk.Text(lf, height=8, wrap="word", state="disabled")
        sb = ttk.Scrollbar(lf, command=self.log.yview)
        self.log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.log.pack(fill="both", expand=True)

    def _slider(self, parent, row, label, var, lo, hi, step, integer=False):
        ttk.Label(parent, text=label).grid(row=row, column=0, sticky="w", padx=6, pady=2)
        val = ttk.Label(parent, width=5, text=str(var.get()))
        val.grid(row=row, column=2, padx=6)

        def on_change(v):
            x = float(v)
            if integer:
                x = int(round(x / step) * step)
            else:
                x = round(round(x / step) * step, 2)
            var.set(x)
            val.config(text=str(x))

        ttk.Scale(parent, from_=lo, to=hi, variable=var, command=on_change).grid(
            row=row, column=1, sticky="ew", padx=6)

    # ------------------------------------------------- first-run installer
    def _missing_libs(self):
        importlib.invalidate_caches()
        return [pip for mod, pip in REQUIRED.items() if importlib.util.find_spec(mod) is None]

    def _check_deps(self):
        missing = self._missing_libs()
        if not missing:
            return
        if not messagebox.askyesno(
                "First-time setup",
                "These libraries are needed and not installed yet:\n\n  "
                + ", ".join(missing)
                + "\n\nInstall them now? (several GB, can take 10+ minutes)"):
            self.status.set("Libraries missing - conversion won't work until installed.")
            return
        self.start_btn.config(state="disabled")
        self.cancel_btn.config(state="disabled")
        self.bar.config(mode="indeterminate")
        self.bar.start(15)
        self.status.set("Installing libraries... leave this window open.")
        threading.Thread(target=self._install, args=(missing,), daemon=True).start()

    def _install(self, missing):
        try:
            cmd = [self._python_exe(), "-m", "pip", "install", *missing]
            self.q.put(("log", "Running: " + " ".join(cmd)))
            proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                encoding="utf-8", errors="replace",
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            for line in proc.stdout:
                line = line.strip()
                if line:
                    self.q.put(("log", line))
            if proc.wait() != 0:
                raise RuntimeError("pip install failed - see log above.")
            if self._missing_libs():
                raise RuntimeError("Install finished but libraries still missing.")
            self.q.put(("setup_done", True, "Setup complete. Pick a song and press Convert."))
        except Exception as e:  # noqa: BLE001
            self.q.put(("log", f"ERROR: {e}"))
            self.q.put(("setup_done", False, "Setup failed - see log."))

    # ----------------------------------------------------------- actions
    def _pick_audio(self):
        p = filedialog.askopenfilename(
            title="Choose audio",
            filetypes=[("Audio", "*.wav *.mp3 *.flac *.m4a *.ogg *.aac"), ("All files", "*.*")])
        if p:
            self.audio_var.set(p)

    def _pick_out(self):
        p = filedialog.askdirectory(title="Choose output folder")
        if p:
            self.out_var.set(p)

    def _open_folder(self):
        if self.last_midi_dir and Path(self.last_midi_dir).exists():
            os.startfile(self.last_midi_dir)  # Windows

    def _cancel(self):
        self.cancel_flag.set()
        self.status.set("Cancelling...")
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()

    def _start(self):
        audio = Path(self.audio_var.get().strip().strip('"'))
        if not audio.is_file():
            messagebox.showerror("No file", "Choose an audio file first.")
            return
        keep = [s for s in ALL_STEMS if self.stem_vars[s].get()]
        if not keep:
            messagebox.showerror("No stems", "Tick at least one stem to transcribe.")
            return

        bpm_override = None
        txt = self.bpm_var.get().strip()
        if txt:
            try:
                bpm_override = float(txt)
                if not 30 <= bpm_override <= 300:
                    raise ValueError
            except ValueError:
                messagebox.showerror("Tempo", "Tempo override must be a number between 30 and 300, or blank.")
                return

        cfg = dict(
            audio=audio,
            out=Path(self.out_var.get()) / audio.stem,
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
        self.start_btn.config(state="disabled")
        self.cancel_btn.config(state="normal")
        self.open_btn.config(state="disabled")
        self.bar.config(mode="determinate", value=0)
        self._clear_log()
        self.worker = threading.Thread(target=self._run, args=(cfg,), daemon=True)
        self.worker.start()

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

        stem_dir = stems_root / model / audio.stem
        need = 6 if model == "htdemucs_6s" else 4
        already = stem_dir.exists() and len(list(stem_dir.glob("*.wav"))) >= need

        if already:
            self.q.put(("log", "Stems already exist for this song - skipping separation."))
        else:
            # Step 1: Demucs
            self.q.put(("status", "Step 1/2: separating stems (this is the slow part)..."))
            self.q.put(("progress", 0))
            cmd = [self._python_exe(), "-m", "demucs", "-n", model, "-o", str(stems_root), str(audio)]
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

        stem_dir = stems_root / model / audio.stem
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
            single.write(str(midi_dir / f"{audio.stem}_{name}.mid"))
            combined.instruments.append(inst)
            self.q.put(("log", f"  {len(inst.notes)} notes"))
            self.q.put(("progress", 50 + 50 * (i + 1) / len(wavs)))

        combined.write(str(midi_dir / f"{audio.stem}_all_stems.mid"))
        self.q.put(("midi_dir", str(midi_dir)))
        self.q.put(("done", True, f"Done. MIDI files saved in {midi_dir}"))

    # ---------------------------------------------------------- UI loop
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
                    self.status.set(msg[1])
                elif kind == "progress":
                    self.bar.config(value=msg[1])
                elif kind == "setup_done":
                    self.bar.stop()
                    self.bar.config(mode="determinate", value=0)
                    self.status.set(msg[2])
                    self.start_btn.config(state="normal")
                elif kind == "midi_dir":
                    self.last_midi_dir = msg[1]
                elif kind == "done":
                    ok, text = msg[1], msg[2]
                    self.status.set(text)
                    self.start_btn.config(state="normal")
                    self.cancel_btn.config(state="disabled")
                    if ok:
                        self.bar.config(value=100)
                        self.open_btn.config(state="normal")
        except queue.Empty:
            pass
        self.after(100, self._poll)


if __name__ == "__main__":
    App().mainloop()
