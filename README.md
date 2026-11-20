
Hanamidi

Hanamidi is a desktop utility that splits audio tracks into isolated instrument stems and transcribes them into clean, 
DAW-ready MIDI files. It pairs source separation with customizable note detection and beat-snapping controls to streamline 
converting mixed audio into editable musical data.

Features

• Multi-Stem Separation: Splits audio tracks into up to 6 distinct stems (vocals, drums, bass, guitar, piano, and other).
• Selective MIDI Transcription: Choose exactly which stems to convert to MIDI. Unpitched stems like drums are disabled by default to avoid messy transcriptions, while instruments like violins and synths are grouped under other.
• Customizable Note Detection:
	• Onset Threshold: Adjust sensitivity to detect fewer or more note attacks.
	• Frame Threshold: Control note sustain and length sensitivity.
	• Minimum Note Length (ms): Filter out unwanted micro-notes and noise artifacts.
	• Single-Note Mode: Enforces monophonic pitch tracking on vocals and bass for cleaner, more accurate lines.
	• Note Cleanup: Automatically merges fragmented notes and strips out transcription glitches.
• DAW-Ready Timing & Quantization:
	• Beat Snapping: Quantizes transcribed notes to the beat (e.g., 1/16 notes), with support for auto-detected tempo or manual BPM overrides.
	• DAW Grid Alignment: Automatically shifts MIDI timing by under a beat so tracks drop straight onto your DAW's grid without manual nudging, reporting the exact offset in the process log.
• Built-in Progress & Logging: Includes real-time conversion status tracking, cancellation controls, a detailed execution log, and one-click access to your output folder.

Basic Usage

1. Select an input Audio file and choose an Output folder.
2. Pick a Separation model (e.g., 6-stem mode) and check the stems you want to transcribe.
3. Fine-tune the Note detection sliders and Timing settings if needed, or stick with the defaults.
4. Click Convert to process the track, then click Open MIDI folder to grab your files.
