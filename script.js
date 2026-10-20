/*
 * ASCII MOTION
 *
 * Part 1  AsciiCore      Pure logic (no DOM): grid maths, brightness -> character mapping,
 *                        frame scheduler, Python player generator. Also runs under Node for tests.
 * Part 2  Conversion     Video decoding + canvas sampling (needs a browser).
 * Part 3  UI             Rendering, playback, controls.
 *
 * The browser preview and the generated Python script are two renderers of the SAME
 * precomputed frame list. Nothing is converted a second time in Python.
 */
"use strict";

/* ========================================================================== *
 * Part 1: AsciiCore
 * ========================================================================== */
const AsciiCore = (() => {
  /** Height of one character cell divided by its width is 1 / CHAR_ASPECT. */
  const CHAR_ASPECT = 0.5;

  /** Rendering spec shared with the Python player. */
  const RENDER = {
    charAspect: CHAR_ASPECT,
    foreground: "#D7DEEA",
    background: "#07090D",
    fontFamily:
      'ui-monospace, "SF Mono", SFMono-Regular, Menlo, "Cascadia Mono", Consolas, "Liberation Mono", "DejaVu Sans Mono", monospace',
  };

  const LIMITS = {
    maxDurationSec: 180,
    maxFrames: 900,
    maxFileBytes: 350 * 1024 * 1024,
    minCols: 32,
    maxCols: 140,
    minRows: 10,
    maxRows: 72,
  };

  const COLUMN_OPTIONS = [48, 72, 96, 120];
  const FPS_OPTIONS = [8, 12, 16, 20];

  /**
   * Character ramps. Index 0 is used for black pixels, the last index for white.
   * Add an entry here and it appears in the UI and works in the Python player.
   */
  const RAMPS = [
    {
      id: "luma",
      label: "Luma",
      hint: "Bright pixels use dense characters, so the picture reads as light text on black.",
      chars: " .:-=+*#%@",
    },
    {
      id: "bold",
      label: "Bold",
      hint: "Same light-on-dark reading with a heavier character set.",
      chars: " .,:;+*?%S#@",
    },
    {
      id: "inverted",
      label: "Inverted",
      hint: "Dark pixels use dense characters (@%#*+=-:. ). A stencil look rather than a natural picture.",
      chars: "@%#*+=-:. ",
    },
  ];

  function clamp(value, min, max) {
    return Math.min(max, Math.max(min, value));
  }

  function rampById(id) {
    return RAMPS.find((ramp) => ramp.id === id) || RAMPS[0];
  }

  /** Output grid for a video. Rows follow the video aspect and the character cell aspect. */
  function computeGrid(videoWidth, videoHeight, targetCols) {
    const cols = clamp(Math.round(targetCols), LIMITS.minCols, LIMITS.maxCols);
    const videoAspect = videoWidth / Math.max(1, videoHeight);
    const rows = clamp(Math.round((cols * CHAR_ASPECT) / videoAspect), LIMITS.minRows, LIMITS.maxRows);
    return { cols, rows };
  }

  /** Where the picture sits inside the grid. Extreme aspect ratios are letterboxed, never stretched. */
  function fitDrawRect(cols, rows, videoWidth, videoHeight) {
    const frameAspect = videoWidth / Math.max(1, videoHeight);
    let w = cols;
    let h = Math.max(1, Math.round((cols * CHAR_ASPECT) / frameAspect));
    if (h > rows) {
      h = rows;
      w = Math.max(1, Math.round((rows * frameAspect) / CHAR_ASPECT));
    }
    w = Math.min(cols, w);
    h = Math.min(rows, h);
    return { x: Math.floor((cols - w) / 2), y: Math.floor((rows - h) / 2), w, h };
  }

  /** True when the ramp's blank glyph stands for black (letterbox bars should be black). */
  function letterboxIsBlack(ramp) {
    const spaceAt = ramp.indexOf(" ");
    if (spaceAt < 0) return true;
    return spaceAt < ramp.length / 2;
  }

  function luminance(r, g, b) {
    return 0.299 * r + 0.587 * g + 0.114 * b;
  }

  /** RGBA pixels (cols x rows) -> one frame string: `rows` lines of exactly `cols` characters. */
  function pixelsToFrame(data, cols, rows, ramp) {
    const rampMax = ramp.length - 1;
    const lines = new Array(rows);
    for (let y = 0; y < rows; y++) {
      let line = "";
      const row = y * cols * 4;
      for (let x = 0; x < cols; x++) {
        const i = row + x * 4;
        const bright = luminance(data[i], data[i + 1], data[i + 2]);
        let idx = Math.round((bright / 255) * rampMax);
        if (idx < 0) idx = 0;
        else if (idx > rampMax) idx = rampMax;
        line += ramp[idx];
      }
      lines[y] = line;
    }
    return lines.join("\n");
  }

  /** Uniform output clock. frameDurationMs * frameCount === durationMs (not rounded). */
  function planSampling(durationMs, requestedFps) {
    const duration = Math.max(1, durationMs);
    const wanted = clamp(requestedFps, 1, 24);
    let frameCount = Math.max(1, Math.round((duration / 1000) * wanted));
    if (frameCount > LIMITS.maxFrames) frameCount = LIMITS.maxFrames;
    const frameDurationMs = duration / frameCount;
    return { fps: 1000 / frameDurationMs, frameCount, frameDurationMs };
  }

  /** Sample each output frame at the middle of its time slot. */
  function sampleTimestamps(durationMs, frameCount) {
    const seconds = durationMs / 1000;
    const last = Math.max(0, seconds - 0.001);
    const times = [];
    for (let i = 0; i < frameCount; i++) {
      times.push(Math.min(((i + 0.5) / frameCount) * seconds, last));
    }
    return times;
  }

  /**
   * Elapsed-time frame scheduler. The Python player has the identical function
   * (frame_index_state). The clock is absolute, so a slow paint skips ahead
   * instead of letting playback drift.
   */
  function frameIndexAt(elapsedMs, originIndex, frameCount, frameDurationMs, loop) {
    if (frameCount <= 0 || frameDurationMs <= 0) return { index: 0, done: true };
    const elapsed = Math.max(0, elapsedMs);
    const advanced = Math.floor(elapsed / frameDurationMs);
    if (loop) return { index: ((originIndex % frameCount) + advanced) % frameCount, done: false };
    if (originIndex + advanced >= frameCount) return { index: frameCount - 1, done: true };
    return { index: originIndex + advanced, done: false };
  }

  /** `<name>.mp4` -> `<name>_ascii.py`. Only the final extension is removed. */
  function asciiScriptFilename(original) {
    const leaf = String(original).replace(/\\/g, "/").split("/").pop() || "video";
    const dot = leaf.lastIndexOf(".");
    const base = dot > 0 ? leaf.slice(0, dot) : leaf;
    return base + "_ascii.py";
  }

  /** A decorative still shown before any video is loaded (never presented as a conversion result). */
  function decorativeAperture(cols, rows) {
    const ramp = " .:-=+*#%@";
    const lines = [];
    for (let y = 0; y < rows; y++) {
      let line = "";
      const ny = ((y + 0.5) / rows) * 2 - 1;
      const dy = (ny * rows) / (cols * CHAR_ASPECT);
      for (let x = 0; x < cols; x++) {
        const nx = ((x + 0.5) / cols) * 2 - 1;
        const radius = Math.hypot(nx, dy);
        const ring = Math.max(0, 1 - Math.abs(radius - 0.72) * 7);
        const core = radius < 0.16 ? 0.35 : 0;
        const shade = Math.min(1, ring * 0.85 + core);
        line += ramp[Math.round(shade * (ramp.length - 1))];
      }
      lines.push(line);
    }
    return lines.join("\n");
  }

  /**
   * One cell's color as 12 bits (4 bits per channel).
   * The color is first brought to full brightness (largest channel = 255): the CHARACTER already
   * carries the brightness, so using the raw pixel color would darken dark areas twice.
   * Browser and Python both expand a 4-bit value v to 8 bits as v * 17, so they show identical colors.
   */
  function quantizeColor(r, g, b) {
    const max = Math.max(r, g, b);
    const gain = max > 0 ? 255 / max : 0;
    const q = (v) => clamp(Math.round((v * gain) / 17), 0, 15);
    return (q(r) << 8) | (q(g) << 4) | q(b);
  }

  /** RGBA pixels -> one 12-bit color per cell (row-major, same order as the characters). */
  function pixelsToColors(data, cols, rows) {
    const out = new Uint16Array(cols * rows);
    for (let i = 0; i < out.length; i++) out[i] = quantizeColor(data[i * 4], data[i * 4 + 1], data[i * 4 + 2]);
    return out;
  }

  function colorCodeToRgb(code) {
    return [((code >> 8) & 15) * 17, ((code >> 4) & 15) * 17, (code & 15) * 17];
  }

  /** All frames' colors as little-endian uint16 bytes (frame after frame). */
  function colorsToBytes(colorFrames) {
    const cells = colorFrames.length ? colorFrames[0].length : 0;
    const bytes = new Uint8Array(colorFrames.length * cells * 2);
    colorFrames.forEach((frame, f) => {
      for (let i = 0; i < cells; i++) {
        bytes[(f * cells + i) * 2] = frame[i] & 255;
        bytes[(f * cells + i) * 2 + 1] = frame[i] >> 8;
      }
    });
    return bytes;
  }

  /** Throws if any frame breaks the grid or uses a character outside the ramp. */
  function assertFrameGeometry(frames, cols, rows, ramp) {
    const allowed = new Set(ramp.split(""));
    frames.forEach((frame, index) => {
      const lines = frame.split("\n");
      if (lines.length !== rows) throw new Error("Frame " + index + " has " + lines.length + " rows, expected " + rows + ".");
      lines.forEach((line, y) => {
        if (line.length !== cols) {
          throw new Error("Frame " + index + " row " + y + " has " + line.length + " columns, expected " + cols + ".");
        }
        for (const ch of line) {
          if (!allowed.has(ch)) throw new Error("Frame " + index + " contains a character outside the ramp.");
        }
      });
    });
  }

  function hexToRgb(hex) {
    const n = hex.replace("#", "");
    return [parseInt(n.slice(0, 2), 16), parseInt(n.slice(2, 4), 16), parseInt(n.slice(4, 6), 16)];
  }

  /** Rough size of the generated script before compression. */
  function estimateRawBytes(cols, rows, frameCount) {
    return (cols + 1) * rows * frameCount;
  }

  function bytesToBase64Lines(bytes) {
    let binary = "";
    const step = 0x8000;
    for (let i = 0; i < bytes.length; i += step) {
      binary += String.fromCharCode.apply(null, bytes.subarray(i, i + step));
    }
    const b64 = btoa(binary);
    const lines = [];
    for (let i = 0; i < b64.length; i += 100) lines.push(b64.slice(i, i + 100));
    return lines.join("\n");
  }

  /** zlib-format deflate, or null when the browser can't (Python reads it with the standard zlib). */
  async function deflate(bytes) {
    if (typeof CompressionStream !== "function") return null;
    try {
      const stream = new Blob([bytes]).stream().pipeThrough(new CompressionStream("deflate"));
      return new Uint8Array(await new Response(stream).arrayBuffer());
    } catch (_error) {
      return null;
    }
  }

  /**
   * Pack every frame (joined by the ASCII record separator 0x1E) and, in color mode, every cell's
   * color, for embedding in Python. Everything is compressed, or nothing is (one flag in the script).
   */
  async function encodeFrames(frames, colorFrames) {
    const frameBytes = new TextEncoder().encode(frames.join("\u001e"));
    const colorBytes = colorFrames ? colorsToBytes(colorFrames) : null;
    const framePacked = await deflate(frameBytes);
    const colorPacked = colorBytes ? await deflate(colorBytes) : null;
    const compressed = !!framePacked && (!colorBytes || !!colorPacked);
    return {
      b64: bytesToBase64Lines(compressed ? framePacked : frameBytes),
      colorB64: colorBytes ? bytesToBase64Lines(compressed ? colorPacked : colorBytes) : null,
      compressed,
    };
  }

  /**
   * Build the standalone Python 3 player (standard library only).
   * `project.payload` comes from encodeFrames(); frames are never converted again.
   */
  function buildPythonScript(project, loop) {
    const spec = project.spec;
    if (!project.payload || project.frames.length !== spec.frameCount) {
      throw new Error("Couldn\u2019t generate the Python script because the frame data is incomplete.");
    }
    const fg = hexToRgb(spec.foreground);
    const bg = hexToRgb(spec.background);
    const safeName = String(project.sourceName).replace(/[^\w.\- ]+/g, "_").slice(0, 80) || "video";
    const py = (value) => (value ? "True" : "False");
    const hasColor = !!project.payload.colorB64;

    return String.raw`#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ASCII MOTION standalone player
# Source name (not needed at runtime): ${safeName}
"""Standalone ASCII animation player generated by ASCII MOTION.

Needs only Python 3 (standard library). It does not need the original video,
an internet connection, or the web app.

The browser preview and this player play the SAME frame list: the frames below
were converted once, in the browser, and are embedded here unchanged. Both use
the same grid, the same characters, the same colors and the same
elapsed-time scheduler. A terminal font cannot match a browser pixel for pixel,
but the characters, rows, columns and timing are identical.

Run in PowerShell or Windows Terminal:
    python your_script_name.py

Color: when the preview was in color mode, the same per-cell colors are embedded and shown
with 24-bit ANSI color (Windows Terminal, PowerShell on Windows 10/11, most modern terminals).

Options:
    --mono     ignore the embedded colors and play in the plain light-on-dark text
    --256      use the 256-color palette (older terminals) instead of 24-bit color
    --loop     repeat until Ctrl+C
    --once     play once, then wait for Enter
    --force    play even if the terminal looks too small
    --no-resize    don't try to enlarge the window automatically
    --no-relaunch  (Windows) don't reopen in a classic console window when the window can't be enlarged
    --check    validate the embedded frames and exit
    --dump N   print frame N (0-based) and exit
    --timing   run the timing self-test and exit

Recommended terminal size: ${spec.cols + 1} columns x ${spec.rows} rows or larger.
The player tries to enlarge the window by itself and puts the old size back when it exits.
Some terminals (for example Windows Terminal) don't let programs resize them; on Windows the player
then reopens itself in a classic console window. If that isn't possible either, zoom out with Ctrl + mouse wheel.
Recommended font: Consolas, Cascadia Mono or another fixed-width font.
Ctrl+C stops playback and restores the terminal.
"""

from __future__ import annotations

import base64
import os
import shutil
import sys
import time
import zlib

# ---- Shared rendering specification (same values the browser preview used) ----
COLS = ${spec.cols}
ROWS = ${spec.rows}
FRAME_COUNT = ${spec.frameCount}
DURATION_MS = ${spec.durationMs}
FRAME_DT = (DURATION_MS / FRAME_COUNT) / 1000.0  # seconds per frame, same split as the browser
FPS = ${Number(spec.fps.toFixed(4))}
LOOP = ${py(loop)}
CHAR_ASPECT = ${spec.charAspect}
RAMP = ${JSON.stringify(spec.ramp)}
FG = (${fg.join(", ")})
BG = (${bg.join(", ")})
SOURCE_WIDTH = ${spec.sourceWidth}
SOURCE_HEIGHT = ${spec.sourceHeight}
RECOMMENDED_COLUMNS = COLS + 1
RECOMMENDED_ROWS = ROWS
COMPRESSED = ${py(project.payload.compressed)}
COLOR = ${py(hasColor)}  # per-cell colors embedded (4 bits per channel)

# ---- Frame data (frames separated by the 0x1E record separator, then packed) ----
_PAYLOAD = """
${project.payload.b64}
"""

_COLORS = """
${hasColor ? project.payload.colorB64 : ""}
"""


def load_frames():
    raw = base64.b64decode(_PAYLOAD)
    if COMPRESSED:
        raw = zlib.decompress(raw)
    return raw.decode("utf-8").split("\x1e")


def load_colors():
    """Per-frame bytes: two bytes (little-endian) per cell, 4 bits each for R, G, B."""
    if not COLOR:
        return None
    raw = base64.b64decode(_COLORS)
    if COMPRESSED:
        raw = zlib.decompress(raw)
    per = COLS * ROWS * 2
    if len(raw) != per * FRAME_COUNT:
        raise SystemExit("Color data has the wrong size.")
    return [raw[i * per:(i + 1) * per] for i in range(FRAME_COUNT)]


def cell_rgb(code):
    """Expand 4-bit channels to 8-bit the same way the browser does (v * 17)."""
    return ((code >> 8) & 15) * 17, ((code >> 4) & 15) * 17, (code & 15) * 17


_SGR_CACHE = {}


def sgr(code, mode):
    key = (code, mode)
    text = _SGR_CACHE.get(key)
    if text is None:
        r, g, b = cell_rgb(code)
        if mode == 256:
            text = "\x1b[38;5;%dm" % (16 + 36 * int(round(r / 51.0)) + 6 * int(round(g / 51.0)) + int(round(b / 51.0)))
        else:
            text = "\x1b[38;2;%d;%d;%dm" % (r, g, b)
        _SGR_CACHE[key] = text
    return text


def colorize(frame, cell_bytes, mode):
    """Frame text -> text with a color escape before each change of color (blanks keep the current one)."""
    out = []
    current = -1
    k = 0
    for line in frame.split("\n"):
        for ch in line:
            if ch != " ":
                code = (cell_bytes[k * 2 + 1] << 8) | cell_bytes[k * 2]
                if code != current:
                    out.append(sgr(code, mode))
                    current = code
            out.append(ch)
            k += 1
        out.append("\n")
    out.pop()
    return "".join(out)


def color_mode(argv, ansi):
    """None = plain text, 24 = truecolor, 256 = 256-color palette."""
    if not COLOR or not ansi or "--mono" in argv:
        return None
    if "--256" in argv:
        return 256
    if os.name == "nt":
        return 24
    return 24 if os.environ.get("COLORTERM", "").lower() in ("truecolor", "24bit") else 256


def frame_index_state(elapsed, origin, count, frame_dt, loop):
    """Same scheduler as the browser (frameIndexAt). Absolute clock, no drift."""
    if count <= 0 or frame_dt <= 0:
        return 0, True
    if elapsed < 0:
        elapsed = 0.0
    advanced = int(elapsed / frame_dt)
    if loop:
        return (origin + advanced) % count, False
    if origin + advanced >= count:
        return count - 1, True
    return origin + advanced, False


def validate(frames):
    if len(frames) != FRAME_COUNT:
        raise SystemExit("Expected %d frames, found %d." % (FRAME_COUNT, len(frames)))
    allowed = set(RAMP)
    for i, frame in enumerate(frames):
        lines = frame.split("\n")
        if len(lines) != ROWS:
            raise SystemExit("Frame %d has %d rows, expected %d." % (i, len(lines), ROWS))
        for y, line in enumerate(lines):
            if len(line) != COLS:
                raise SystemExit("Frame %d row %d has %d columns, expected %d." % (i, y, len(line), COLS))
            for ch in line:
                if ch not in allowed:
                    raise SystemExit("Frame %d contains a character outside the ramp." % i)


def timing_self_test():
    cases = [
        (0.0, 0, 10, 0.1, False, 0, False),
        (0.1, 0, 10, 0.1, False, 1, False),
        (0.99, 0, 10, 0.1, False, 9, False),
        (1.0, 0, 10, 0.1, False, 9, True),
        (0.35, 2, 10, 0.1, False, 5, False),
        (0.2, 8, 10, 0.1, True, 0, False),
    ]
    for elapsed, origin, count, dt, loop, exp_i, exp_done in cases:
        idx, done = frame_index_state(elapsed, origin, count, dt, loop)
        if idx != exp_i or done != exp_done:
            raise SystemExit("Timing mismatch at elapsed=%s" % elapsed)
    print("TIMING OK")


def enable_windows_vt():
    """Turn on ANSI escape sequence handling in the Windows console."""
    if os.name != "nt":
        return True
    try:
        import ctypes

        kernel32 = ctypes.windll.kernel32
        handle = kernel32.GetStdHandle(-11)
        mode = ctypes.c_uint()
        if not kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            return False
        return bool(kernel32.SetConsoleMode(handle, mode.value | 0x0004))  # ENABLE_VIRTUAL_TERMINAL_PROCESSING
    except Exception:
        return False


def use_ansi():
    if not sys.stdout.isatty():
        return False
    if os.name != "nt":
        return os.environ.get("TERM", "") != "dumb"
    return enable_windows_vt()


def current_size():
    size = shutil.get_terminal_size(fallback=(80, 24))
    return size.columns, size.lines


def big_enough():
    cols, rows = current_size()
    return cols >= RECOMMENDED_COLUMNS and rows >= RECOMMENDED_ROWS


def wait_until_big_enough(timeout=0.8):
    end = time.time() + timeout
    while time.time() < end:
        if big_enough():
            return True
        time.sleep(0.05)
    return big_enough()


def set_window_size(cols, rows, vt):
    """Ask the terminal for a window of cols x rows. Best effort: many terminals ignore it."""
    if vt and sys.stdout.isatty():
        sys.stdout.write("\x1b[8;%d;%dt" % (rows, cols))  # xterm window-resize request
        sys.stdout.flush()
    elif os.name == "nt":
        os.system("mode con: cols=%d lines=%d >nul 2>&1" % (cols, rows))


def try_enlarge():
    """Grow (never shrink) the window to the recommended size. Returns True once it is big enough."""
    cols, rows = current_size()
    want_cols = max(cols, RECOMMENDED_COLUMNS)
    want_rows = max(rows, RECOMMENDED_ROWS + 2)  # two spare rows for the "finished" prompt
    vt = enable_windows_vt() if os.name == "nt" else True
    set_window_size(want_cols, want_rows, vt)
    if wait_until_big_enough():
        return True
    if os.name == "nt":
        set_window_size(want_cols, want_rows, False)  # classic console: mode con
        return wait_until_big_enough()
    return False


def restore_size(original):
    if not original:
        return
    cols, rows = original
    vt = enable_windows_vt() if os.name == "nt" else True
    set_window_size(cols, rows, vt)
    if os.name == "nt":
        set_window_size(cols, rows, False)


_RELAUNCH_ENV = "ASCII_MOTION_RELAUNCHED"
_waited_for_enter = False


def relaunch_in_classic_console():
    """Windows Terminal can't be resized by programs. A classic console window (conhost) can."""
    if os.name != "nt" or os.environ.get(_RELAUNCH_ENV):
        return False
    try:
        import subprocess

        env = dict(os.environ)
        env[_RELAUNCH_ENV] = "1"
        subprocess.Popen(["conhost.exe", sys.executable, os.path.abspath(__file__)] + sys.argv[1:], env=env)
        return True
    except Exception:
        return False


def pause_if_relaunched():
    """A relaunched window closes with the program, so hold it open to let you read any message."""
    if os.environ.get(_RELAUNCH_ENV) and not _waited_for_enter and sys.stdin.isatty():
        try:
            input("\n[Press Enter to close this window]")
        except (EOFError, KeyboardInterrupt):
            pass


def paint(frame, ansi):
    if ansi:
        sys.stdout.write("\x1b[H" + frame)  # home the cursor, overwrite in place: no flicker, no scrolling
    elif os.name == "nt":
        os.system("cls")
        sys.stdout.write(frame)
    else:
        sys.stdout.write("\x1b[H\x1b[2J" + frame)
    sys.stdout.flush()


def play(frames, colors, loop):
    if not sys.stdout.isatty():
        sys.stderr.write("This player needs a terminal. Run it in PowerShell, Windows Terminal or another console.\n")
        raise SystemExit(1)
    original = current_size()
    resized_from = None
    if not big_enough() and "--no-resize" not in sys.argv:
        enlarged = try_enlarge()
        if current_size() != original:
            resized_from = original
        if not enlarged and "--no-relaunch" not in sys.argv and "--force" not in sys.argv:
            restore_size(resized_from)
            if relaunch_in_classic_console():
                print("This window can't be resized, so the animation opens in a classic console window.")
                return
    size = shutil.get_terminal_size(fallback=(80, 24))
    too_small = size.columns < RECOMMENDED_COLUMNS or size.lines < RECOMMENDED_ROWS
    if too_small and "--force" not in sys.argv:
        restore_size(resized_from)
        sys.stderr.write(
            "Terminal is %d columns x %d rows.\n"
            "This animation needs at least %d columns x %d rows, or lines will wrap and the picture breaks.\n"
            "The window couldn't be enlarged automatically. Enlarge it by hand or zoom out (Ctrl + mouse wheel),\n"
            "then run it again. Or pass --force to play anyway.\n"
            % (size.columns, size.lines, RECOMMENDED_COLUMNS, RECOMMENDED_ROWS)
        )
        raise SystemExit(2)
    if too_small:
        sys.stderr.write("Warning: terminal is smaller than %d x %d. Frames may wrap.\n" % (RECOMMENDED_COLUMNS, RECOMMENDED_ROWS))

    ansi = use_ansi()
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass
    if not ansi:
        sys.stderr.write("Color and cursor control are unavailable here. Playing as plain text.\n")

    mode = color_mode(sys.argv, ansi)
    color = "\x1b[38;2;%d;%d;%dm\x1b[48;2;%d;%d;%dm" % (FG + BG)
    finished_once = False
    try:
        if ansi:
            # alternate screen, hide cursor, no auto-wrap, set colors, clear
            sys.stdout.write("\x1b[?1049h\x1b[?25l\x1b[?7l" + color + "\x1b[2J\x1b[H")
            sys.stdout.flush()
        last = -1
        start = time.perf_counter()
        while True:
            elapsed = time.perf_counter() - start
            index, done = frame_index_state(elapsed, 0, len(frames), FRAME_DT, loop)
            if index != last:
                paint(frames[index] if mode is None else colorize(frames[index], colors[index], mode), ansi)
                last = index
            if done:
                finished_once = True
                break
            advanced = int(elapsed / FRAME_DT) if elapsed > 0 else 0
            delay = ((advanced + 1) * FRAME_DT) - (time.perf_counter() - start)
            if delay > 0:
                time.sleep(delay)
        if finished_once:
            # Like the browser preview, hold the last frame until the viewer is done with it.
            if not ansi:
                sys.stdout.write("\n[Playback finished. Press Enter to exit.]")
                sys.stdout.flush()
            elif size.lines > ROWS:
                sys.stdout.write("\r\n\x1b[0m[Playback finished. Press Enter to exit.]")
                sys.stdout.flush()
            global _waited_for_enter
            _waited_for_enter = True
            try:
                input()
            except EOFError:
                pass
    except KeyboardInterrupt:
        pass
    finally:
        if ansi:
            sys.stdout.write("\x1b[0m\x1b[?7h\x1b[?25h\x1b[?1049l")
        else:
            sys.stdout.write("\n")
        sys.stdout.flush()
        restore_size(resized_from)  # put the window back the way it was


def main(argv):
    if "--timing" in argv:
        timing_self_test()
        return
    frames = load_frames()
    validate(frames)
    colors = load_colors()
    if "--check" in argv:
        print("OK %d %d %d %d" % (COLS, ROWS, len(frames), DURATION_MS))
        return
    if "--dump" in argv:
        at = argv.index("--dump")
        if at + 1 >= len(argv):
            raise SystemExit("Usage: --dump N")
        n = int(argv[at + 1])
        if n < 0 or n >= len(frames):
            raise SystemExit("Frame %d is out of range." % n)
        sys.stdout.write(frames[n] + "\n")
        return
    loop = LOOP
    if "--loop" in argv:
        loop = True
    if "--once" in argv:
        loop = False
    play(frames, colors, loop)


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    finally:
        pause_if_relaunched()
`;
  }

  return {
    CHAR_ASPECT, RENDER, LIMITS, COLUMN_OPTIONS, FPS_OPTIONS, RAMPS,
    clamp, rampById, computeGrid, fitDrawRect, letterboxIsBlack, luminance, pixelsToFrame,
    planSampling, sampleTimestamps, frameIndexAt, asciiScriptFilename, decorativeAperture,
    assertFrameGeometry, hexToRgb, estimateRawBytes, encodeFrames, buildPythonScript,
    quantizeColor, pixelsToColors, colorCodeToRgb,
  };
})();

if (typeof module !== "undefined" && module.exports) {
  module.exports = AsciiCore;
}

/* ========================================================================== *
 * Part 2: Conversion engine (browser only)
 * ========================================================================== */
const AsciiConverter = (() => {
  if (typeof document === "undefined") return null;
  const C = AsciiCore;

  class ConvertAborted extends Error {
    constructor() {
      super("Conversion cancelled");
      this.name = "ConvertAborted";
    }
  }

  function throwIfAborted(signal) {
    if (signal.aborted) throw new ConvertAborted();
  }

  /** Resolve on `eventName`, reject on decode error, timeout, or abort. */
  function waitFor(video, eventName, timeoutMs, signal) {
    throwIfAborted(signal);
    return new Promise((resolve, reject) => {
      const timer = window.setTimeout(() => {
        cleanup();
        reject(new Error("Timed out while reading the video. It may be corrupted or use an unsupported codec."));
      }, timeoutMs);
      const onAbort = () => { cleanup(); reject(new ConvertAborted()); };
      const onEvent = () => { cleanup(); resolve(); };
      const onError = () => { cleanup(); reject(new Error("This browser couldn\u2019t decode that video. Try an MP4 (H.264) or WebM file.")); };
      function cleanup() {
        window.clearTimeout(timer);
        signal.removeEventListener("abort", onAbort);
        video.removeEventListener(eventName, onEvent);
        video.removeEventListener("error", onError);
      }
      signal.addEventListener("abort", onAbort);
      video.addEventListener(eventName, onEvent);
      video.addEventListener("error", onError);
    });
  }

  async function seekTo(video, time, signal) {
    throwIfAborted(signal);
    const limit = Number.isFinite(video.duration) ? Math.max(0, video.duration - 0.001) : time;
    const target = Math.min(Math.max(0, time), limit);
    if (Math.abs(video.currentTime - target) < 0.0005 && video.readyState >= 2) return;
    const pending = waitFor(video, "seeked", 8000, signal);
    video.currentTime = target;
    await pending;
    if (video.readyState < 2) await waitFor(video, "loadeddata", 4000, signal);
  }

  function sampleHash(data) {
    let hash = 0;
    for (let i = 0; i < data.length; i += 67) hash = (hash * 33 + data[i]) | 0;
    return hash;
  }

  function nextPaint() {
    return new Promise((resolve) => window.requestAnimationFrame(() => resolve()));
  }

  function validateFile(file) {
    if (!file) throw new Error("No file selected. Choose a video to convert.");
    if (file.size <= 0) throw new Error("That file is empty. Choose a video to convert.");
    if (file.size > C.LIMITS.maxFileBytes) throw new Error("That video is over 350 MB. Export a smaller file and try again.");
    const extOk = /\.(mp4|webm|mov|m4v|ogv|ogg)$/i.test(file.name);
    const typeOk = file.type === "" || file.type.startsWith("video/") || file.type === "application/octet-stream";
    if (!typeOk && !extOk) throw new Error("Unsupported file. Choose an MP4, WebM, or MOV video.");
  }

  /** Some containers report Infinity until the end is reached once. */
  async function readDuration(video, signal) {
    if (Number.isFinite(video.duration) && video.duration > 0) return video.duration;
    try {
      const jump = waitFor(video, "seeked", 8000, signal);
      video.currentTime = 1e101;
      await jump;
    } catch (error) {
      if (error instanceof ConvertAborted) throw error;
    }
    const duration = video.duration;
    try {
      const back = waitFor(video, "seeked", 8000, signal);
      video.currentTime = 0;
      await back;
    } catch (error) {
      if (error instanceof ConvertAborted) throw error;
    }
    if (!Number.isFinite(duration) || duration <= 0) {
      throw new Error("This video has no readable duration. Export it as MP4 and try again.");
    }
    return duration;
  }

  /**
   * Convert a video file into an ASCII project.
   *
   * Timing model: the output clock is uniform. We pick frameCount frames spaced
   * frameDurationMs apart across the whole clip and seek to the middle of each slot.
   * Seeking (instead of playing and racing the decoder) makes the result independent
   * of device speed, and awaiting each seek keeps the page responsive.
   * Memory model: only one 64 x 36-ish canvas exists; each frame becomes a short string.
   */
  async function convertVideoFile(file, settings, hooks) {
    validateFile(file);
    throwIfAborted(hooks.signal);
    const large = file.size > 80 * 1024 * 1024;
    hooks.onProgress({
      progress: 2,
      message: large ? "Preparing video\u2026 Large file, still processed on this device." : "Preparing video\u2026",
    });

    const url = URL.createObjectURL(file);
    const video = document.createElement("video");
    video.muted = true;
    video.defaultMuted = true;
    video.playsInline = true;
    video.preload = "auto";
    video.setAttribute("playsinline", "");
    video.setAttribute("webkit-playsinline", "");
    // Kept in the DOM (tiny, invisible) because iOS Safari decodes more reliably that way.
    video.style.cssText = "position:fixed;left:0;top:0;width:4px;height:4px;opacity:0;pointer-events:none";
    document.body.appendChild(video);

    const canvas = document.createElement("canvas");
    const ctx = canvas.getContext("2d", { willReadFrequently: true, alpha: false });
    if (!ctx) throw new Error("Couldn\u2019t start frame processing in this browser.");

    try {
      const metadata = waitFor(video, "loadedmetadata", 15000, hooks.signal);
      video.src = url;
      video.load();
      await metadata;
      throwIfAborted(hooks.signal);

      if (!video.videoWidth || !video.videoHeight) {
        throw new Error("Couldn\u2019t read this video\u2019s picture size. It may be corrupted or audio-only.");
      }
      const durationSec = await readDuration(video, hooks.signal);
      const durationMs = Math.round(durationSec * 1000);
      if (durationMs < 1) throw new Error("That video is too short to convert.");
      if (durationMs > C.LIMITS.maxDurationSec * 1000) {
        throw new Error("This video is longer than 3 minutes. Trim it and try again.");
      }

      const grid = C.computeGrid(video.videoWidth, video.videoHeight, settings.cols);
      const sampling = C.planSampling(durationMs, settings.fps);
      const ramp = C.rampById(settings.rampId);
      const rect = C.fitDrawRect(grid.cols, grid.rows, video.videoWidth, video.videoHeight);
      const times = C.sampleTimestamps(durationMs, sampling.frameCount);
      const detail = {
        durationMs,
        width: video.videoWidth,
        height: video.videoHeight,
        plan: {
          cols: grid.cols,
          rows: grid.rows,
          frameCount: sampling.frameCount,
          fps: sampling.fps,
          rawBytes: C.estimateRawBytes(grid.cols, grid.rows, sampling.frameCount),
        },
      };
      hooks.onProgress({ progress: 6, message: "Extracting frames\u2026", detail });

      try {
        await video.play(); // wakes the decoder on browsers that need a user-gesture play
      } catch (_error) {
        /* seeking still works without playback */
      }
      video.pause();

      canvas.width = grid.cols;
      canvas.height = grid.rows;
      ctx.imageSmoothingEnabled = true;
      ctx.imageSmoothingQuality = "high";
      const fill = C.letterboxIsBlack(ramp.chars) ? "#000000" : "#ffffff";

      const capture = () => {
        ctx.fillStyle = fill;
        ctx.fillRect(0, 0, grid.cols, grid.rows);
        ctx.drawImage(video, rect.x, rect.y, rect.w, rect.h);
        try {
          return ctx.getImageData(0, 0, grid.cols, grid.rows);
        } catch (_error) {
          throw new Error("The browser blocked frame access for this video. Try an MP4 or WebM from this device.");
        }
      };

      const frames = [];
      const colors = [];
      let previousHash = 0;
      for (let i = 0; i < times.length; i++) {
        throwIfAborted(hooks.signal);
        hooks.onProgress({ progress: 8 + (i / times.length) * 84, message: "Converting frames to ASCII\u2026", detail });
        try {
          await seekTo(video, times[i], hooks.signal);
        } catch (error) {
          if (error instanceof ConvertAborted) throw error;
          await seekTo(video, times[i], hooks.signal); // one retry for a flaky seek
        }
        let image = capture();
        const hash = sampleHash(image.data);
        // Some browsers paint the previous frame on the first `seeked` event.
        if (i > 0 && hash === previousHash) {
          await nextPaint();
          throwIfAborted(hooks.signal);
          image = capture();
        }
        previousHash = sampleHash(image.data);
        frames.push(C.pixelsToFrame(image.data, grid.cols, grid.rows, ramp.chars));
        if (settings.color) colors.push(C.pixelsToColors(image.data, grid.cols, grid.rows));
      }

      hooks.onProgress({ progress: 94, message: "Generating Python script\u2026" });
      await new Promise((resolve) => window.setTimeout(resolve, 16));
      throwIfAborted(hooks.signal);

      C.assertFrameGeometry(frames, grid.cols, grid.rows, ramp.chars);
      const project = {
        spec: {
          cols: grid.cols,
          rows: grid.rows,
          frameCount: frames.length,
          durationMs,
          frameDurationMs: sampling.frameDurationMs,
          fps: sampling.fps,
          requestedFps: settings.fps,
          requestedCols: settings.cols,
          charAspect: C.RENDER.charAspect,
          rampId: ramp.id,
          ramp: ramp.chars,
          foreground: C.RENDER.foreground,
          background: C.RENDER.background,
          sourceWidth: video.videoWidth,
          sourceHeight: video.videoHeight,
          sourceAspect: video.videoWidth / video.videoHeight,
          color: !!settings.color,
          requestedColor: !!settings.color,
        },
        frames,
        colors: settings.color ? colors : null,
        sourceName: file.name || "video",
        payload: await C.encodeFrames(frames, settings.color ? colors : null),
      };
      throwIfAborted(hooks.signal);
      C.buildPythonScript(project, false); // fail now, not at download time, if generation is broken
      hooks.onProgress({ progress: 100, message: "Conversion complete" });
      return project;
    } catch (error) {
      if (error instanceof ConvertAborted) throw error;
      if (error instanceof Error && /memory|allocation/i.test(error.message)) {
        throw new Error("This video is too heavy for the browser\u2019s memory. Try a shorter clip or fewer columns.");
      }
      throw error;
    } finally {
      // Release the decoder, the object URL and the canvas whatever happened.
      video.pause();
      video.removeAttribute("src");
      video.load();
      video.remove();
      URL.revokeObjectURL(url);
      canvas.width = 0;
      canvas.height = 0;
    }
  }

  return { ConvertAborted, convertVideoFile, validateFile };
})();

/* ========================================================================== *
 * Part 3: UI (browser only)
 * ========================================================================== */
(() => {
  if (typeof document === "undefined") return;
  const C = AsciiCore;
  const { ConvertAborted, convertVideoFile, validateFile } = AsciiConverter;

  const $ = (id) => document.getElementById(id);
  const els = {
    app: $("app"),
    upload: $("upload-button"),
    input: $("video-input"),
    fileInfo: $("file-info"),
    notice: $("notice"),
    cols: $("cols-options"),
    fps: $("fps-options"),
    ramp: $("ramp-options"),
    color: $("color-options"),
    canvas: $("ascii-canvas"),
    rampHint: $("ramp-hint"),
    settingsSummary: $("settings-summary"),
    reconvert: $("reconvert-button"),
    stage: $("stage"),
    frame: $("ascii-frame"),
    progress: $("progress-overlay"),
    progressValue: $("progress-value"),
    progressMessage: $("progress-message"),
    progressFill: $("progress-fill"),
    errorOverlay: $("error-overlay"),
    errorText: $("error-text"),
    retry: $("retry-button"),
    stageHint: $("stage-hint"),
    play: $("play-button"),
    playLabel: $("play-label"),
    restart: $("restart-button"),
    loop: $("loop-button"),
    time: $("time-readout"),
    seek: $("seek-slider"),
    download: $("download-button"),
    scriptInfo: $("script-info"),
    scriptNotes: $("script-notes"),
  };

  const PLACEHOLDER = C.decorativeAperture(48, 16);
  const MIN_STAGE_HEIGHT = 240;

  const state = {
    settings: { cols: 72, fps: 12, rampId: "luma", color: true },
    touchedSettings: false,
    phase: "idle", // idle | busy | ready | error
    file: null,
    project: null,
    loop: false,
    job: 0,
    controller: null,
    inflight: null,
    fileMeta: null,
  };

  /* ---------- small helpers ---------- */

  function formatBytes(bytes) {
    if (bytes < 1024) return bytes + " B";
    if (bytes < 1024 * 1024) return Math.max(1, Math.round(bytes / 1024)) + " KB";
    return (bytes / (1024 * 1024)).toFixed(1) + " MB";
  }

  function formatClock(ms) {
    const total = Math.max(0, Math.round(ms / 1000));
    return Math.floor(total / 60) + ":" + String(total % 60).padStart(2, "0");
  }

  function formatFps(fps) {
    const rounded = Math.round(fps * 10) / 10;
    return Number.isInteger(rounded) ? String(rounded) : rounded.toFixed(1);
  }

  function showNotice(message) {
    els.notice.textContent = message || "";
    els.notice.hidden = !message;
  }

  /* ---------- option buttons ---------- */

  function buildSegments(container, items, isPressed, onPick) {
    container.textContent = "";
    items.forEach((item) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "segment";
      button.textContent = item.label;
      button.dataset.value = String(item.value);
      button.addEventListener("click", () => onPick(item.value));
      container.appendChild(button);
    });
    refreshSegments(container, isPressed);
  }

  function refreshSegments(container, isPressed) {
    container.querySelectorAll(".segment").forEach((button) => {
      const pressed = isPressed(button.dataset.value);
      button.setAttribute("aria-pressed", pressed ? "true" : "false");
      button.disabled = state.phase === "busy";
    });
  }

  function renderSettings() {
    const s = state.settings;
    refreshSegments(els.cols, (v) => Number(v) === s.cols);
    refreshSegments(els.fps, (v) => Number(v) === s.fps);
    refreshSegments(els.ramp, (v) => v === s.rampId);
    refreshSegments(els.color, (v) => (v === "on") === s.color);
    els.rampHint.textContent = C.rampById(s.rampId).hint;
    els.settingsSummary.textContent = s.cols + " columns \u00b7 " + s.fps + " fps \u00b7 " + C.rampById(s.rampId).label + " \u00b7 " + (s.color ? "Color" : "Mono");
    const p = state.project;
    const dirty = !!p && (s.cols !== p.spec.requestedCols || s.fps !== p.spec.requestedFps || s.rampId !== p.spec.rampId || s.color !== p.spec.requestedColor);
    els.reconvert.hidden = !(dirty && state.phase !== "busy" && state.file);
  }

  function pickSetting(key, value) {
    state.touchedSettings = true;
    state.settings[key] = value;
    renderSettings();
  }

  buildSegments(els.cols, C.COLUMN_OPTIONS.map((v) => ({ value: v, label: String(v) })), (v) => Number(v) === state.settings.cols, (v) => pickSetting("cols", v));
  buildSegments(els.fps, C.FPS_OPTIONS.map((v) => ({ value: v, label: v + " fps" })), (v) => Number(v) === state.settings.fps, (v) => pickSetting("fps", v));
  buildSegments(els.color, [{ value: "on", label: "Color" }, { value: "off", label: "Mono" }], (v) => (v === "on") === state.settings.color, (v) => pickSetting("color", v === "on"));
  buildSegments(els.ramp, C.RAMPS.map((r) => ({ value: r.id, label: r.label })), (v) => v === state.settings.rampId, (v) => pickSetting("rampId", v));

  /* ---------- preview layout: one grid, scaled proportionally ---------- */

  let emWidth = 0; // character advance as a fraction of font-size, measured, not assumed

  function measureEmWidth() {
    const probe = document.createElement("span");
    probe.textContent = "0000000000";
    probe.style.cssText =
      "position:absolute;visibility:hidden;white-space:pre;font-size:100px;letter-spacing:0;font-weight:400;font-variant-ligatures:none;font-family:" +
      C.RENDER.fontFamily;
    document.body.appendChild(probe);
    const width = probe.getBoundingClientRect().width / 10 / 100;
    probe.remove();
    return width > 0 ? width : 0.6;
  }

  /**
   * Font size is derived from the actual grid, so characters keep the same
   * proportions as the terminal: cell height = cell width / CHAR_ASPECT,
   * and the grid scales uniformly (never stretched in one direction).
   */
  function layoutStage() {
    if (!emWidth) emWidth = measureEmWidth();
    const spec = state.project ? state.project.spec : null;
    const cols = spec ? spec.cols : 48;
    const rows = spec ? spec.rows : 16;
    const style = window.getComputedStyle(els.stage);
    const padX = parseFloat(style.paddingLeft) + parseFloat(style.paddingRight);
    const padY = parseFloat(style.paddingTop) + parseFloat(style.paddingBottom);
    const cellHeightEm = emWidth / C.CHAR_ASPECT; // used as the unitless line-height
    const availW = Math.max(8, els.stage.clientWidth - padX - 1);
    const availH = Math.max(8, Math.min(window.innerHeight * 0.72, 760) - padY);
    let fontSize = Math.min(availW / (cols * emWidth), availH / (rows * cellHeightEm));
    fontSize = C.clamp(Math.floor(fontSize * 100) / 100, 3, 40);
    els.frame.style.fontSize = fontSize + "px";
    els.frame.style.lineHeight = String(cellHeightEm);
    els.stage.style.height = Math.max(MIN_STAGE_HEIGHT, Math.ceil(rows * cellHeightEm * fontSize + padY)) + "px";

    view.fontSize = fontSize;
    view.cellW = emWidth * fontSize;
    view.cellH = cellHeightEm * fontSize;
    if (colorActive()) {
      sizeCanvas(cols, rows);
      drawColorFrame(player.index);
    }
  }

  /* ---------- color renderer (canvas): same grid, same characters, per-cell colors ---------- */

  const view = { fontSize: 8, cellW: 5, cellH: 10, ctx: null, cssW: 0, cssH: 0 };
  const colorCss = [];

  function colorActive() {
    return !!(state.project && state.project.spec.color && state.project.colors);
  }

  function cssForColor(code) {
    return colorCss[code] || (colorCss[code] = "rgb(" + C.colorCodeToRgb(code).join(",") + ")");
  }

  function sizeCanvas(cols, rows) {
    const dpr = window.devicePixelRatio || 1;
    view.cssW = cols * view.cellW;
    view.cssH = rows * view.cellH;
    const pxW = Math.max(1, Math.round(view.cssW * dpr));
    const pxH = Math.max(1, Math.round(view.cssH * dpr));
    els.canvas.style.width = view.cssW + "px";
    els.canvas.style.height = view.cssH + "px";
    if (els.canvas.width !== pxW || els.canvas.height !== pxH) {
      els.canvas.width = pxW;
      els.canvas.height = pxH;
    }
    view.ctx = els.canvas.getContext("2d", { alpha: true });
    view.ctx.setTransform(pxW / view.cssW, 0, 0, pxH / view.cssH, 0, 0);
  }

  /** Draw one frame: runs of equal color are drawn as one string, blanks are skipped. */
  function drawColorFrame(index) {
    const p = state.project;
    const ctx = view.ctx;
    if (!p || !ctx || !p.colors) return;
    const { cols, rows } = p.spec;
    const cells = p.colors[index];
    const lines = p.frames[index].split("\n");
    ctx.clearRect(0, 0, view.cssW, view.cssH);
    ctx.font = view.fontSize + "px " + C.RENDER.fontFamily;
    ctx.textBaseline = "middle";
    ctx.textAlign = "left";
    for (let y = 0; y < rows; y++) {
      const line = lines[y];
      const rowBase = y * cols;
      const yPos = y * view.cellH + view.cellH / 2;
      let x = 0;
      while (x < cols) {
        if (line[x] === " ") { x++; continue; }
        const code = cells[rowBase + x];
        const start = x;
        while (x < cols && line[x] !== " " && cells[rowBase + x] === code) x++;
        ctx.fillStyle = cssForColor(code);
        ctx.fillText(line.slice(start, x), start * view.cellW, yPos);
      }
    }
  }

  let layoutQueued = false;
  function queueLayout() {
    if (layoutQueued) return;
    layoutQueued = true;
    window.requestAnimationFrame(() => {
      layoutQueued = false;
      layoutStage();
    });
  }
  window.addEventListener("resize", queueLayout);
  window.addEventListener("orientationchange", queueLayout);
  if (document.fonts && document.fonts.ready) {
    document.fonts.ready.then(() => { emWidth = 0; queueLayout(); }).catch(() => {});
  }

  /* ---------- playback (elapsed-time scheduled, <pre> text node updated in place) ---------- */

  const textNode = document.createTextNode(PLACEHOLDER);
  els.frame.textContent = "";
  els.frame.appendChild(textNode);

  const player = {
    raf: 0,
    playing: false,
    index: 0,
    origin: 0,
    startedAt: 0,
    resumeWhenVisible: false,
  };

  function showFrame(index) {
    const p = state.project;
    if (!p) return;
    player.index = index;
    textNode.nodeValue = p.frames[index]; // the <pre> always holds the exact text (screen readers, mono mode)
    if (colorActive()) drawColorFrame(index);
    els.seek.value = String(index);
    els.time.textContent =
      formatClock(Math.min(p.spec.durationMs, index * p.spec.frameDurationMs)) +
      " / " + formatClock(p.spec.durationMs) + " \u00b7 " + (index + 1) + "/" + p.spec.frameCount;
  }

  function setPlaying(value) {
    player.playing = value;
    els.playLabel.textContent = value ? "Pause" : "Play";
    els.play.setAttribute("aria-label", value ? "Pause" : "Play");
    els.play.dataset.state = value ? "playing" : "paused";
  }

  function tick(now) {
    const p = state.project;
    if (!p || !player.playing) return;
    const next = C.frameIndexAt(now - player.startedAt, player.origin, p.frames.length, p.spec.frameDurationMs, state.loop);
    if (next.index !== player.index) showFrame(next.index);
    if (next.done) {
      setPlaying(false);
      return;
    }
    player.raf = window.requestAnimationFrame(tick);
  }

  function playFrom(index) {
    window.cancelAnimationFrame(player.raf);
    player.origin = index;
    showFrame(index);
    player.startedAt = performance.now();
    setPlaying(true);
    player.raf = window.requestAnimationFrame(tick);
  }

  function pausePlayback() {
    window.cancelAnimationFrame(player.raf);
    setPlaying(false);
  }

  function togglePlayback() {
    const p = state.project;
    if (!p) return;
    if (player.playing) {
      pausePlayback();
      return;
    }
    const atEnd = !state.loop && player.index >= p.frames.length - 1;
    playFrom(atEnd ? 0 : player.index);
  }

  function seekTo(index) {
    const p = state.project;
    if (!p) return;
    const clamped = C.clamp(index, 0, p.frames.length - 1);
    if (player.playing) playFrom(clamped);
    else {
      player.origin = clamped;
      showFrame(clamped);
    }
  }

  function resetPlayer() {
    window.cancelAnimationFrame(player.raf);
    player.playing = false;
    player.index = 0;
    player.origin = 0;
    setPlaying(false);
  }

  // A hidden tab stops requestAnimationFrame; resume from the current frame instead of jumping ahead.
  document.addEventListener("visibilitychange", () => {
    if (document.hidden && player.playing) {
      player.resumeWhenVisible = true;
      pausePlayback();
    } else if (!document.hidden && player.resumeWhenVisible) {
      player.resumeWhenVisible = false;
      if (state.project) playFrom(player.index);
    }
  });

  els.play.addEventListener("click", togglePlayback);
  els.restart.addEventListener("click", () => state.project && playFrom(0));
  els.seek.addEventListener("input", () => seekTo(Number(els.seek.value)));
  els.loop.addEventListener("click", () => {
    state.loop = !state.loop;
    els.loop.setAttribute("aria-pressed", state.loop ? "true" : "false");
    renderDownloadInfo();
  });
  document.addEventListener("keydown", (event) => {
    if (event.code !== "Space" || !state.project) return;
    if (event.target.closest && event.target.closest("input, textarea, button, select, a")) return;
    event.preventDefault();
    togglePlayback();
  });

  /* ---------- rendering of overall state ---------- */

  function renderFileInfo() {
    const m = state.fileMeta;
    if (!m) {
      els.fileInfo.textContent = "No file selected. MP4, WebM, or MOV. Nothing leaves this device.";
      return;
    }
    const parts = [m.name];
    if (m.width && m.height) parts.push(m.width + "\u00d7" + m.height);
    if (m.durationMs) parts.push(formatClock(m.durationMs));
    parts.push(formatBytes(m.size));
    els.fileInfo.textContent = parts.join(" \u00b7 ");
  }

  function renderDownloadInfo() {
    const p = state.project;
    if (!p) {
      els.download.disabled = true;
      els.scriptInfo.textContent = "Available after conversion.";
      els.scriptNotes.textContent =
        "The script is built from the frames shown above. It runs offline with Python 3 and needs no extra packages.";
      return;
    }
    let sizeText = "";
    try {
      const source = C.buildPythonScript(p, state.loop);
      sizeText = " \u00b7 " + formatBytes(new TextEncoder().encode(source).length);
      els.download.disabled = false;
    } catch (_error) {
      els.download.disabled = true;
      els.scriptInfo.textContent = "Couldn\u2019t generate the Python script.";
      return;
    }
    const s = p.spec;
    els.scriptInfo.textContent = C.asciiScriptFilename(p.sourceName) + sizeText;
    const parts = [
      s.cols + "\u00d7" + s.rows + " characters \u00b7 " + formatFps(s.fps) + " fps \u00b7 " + s.frameCount + " frames.",
      "Run it in PowerShell or Windows Terminal. It needs a window of at least " + (s.cols + 1) + " columns by " + s.rows +
        " rows and tries to enlarge the window itself; if your terminal doesn\u2019t allow that, enlarge it or zoom out by hand. Use a fixed-width font (Consolas or Cascadia Mono).",
    ];
    if (s.fps + 0.05 < s.requestedFps) {
      parts.push("Sampled at " + formatFps(s.fps) + " fps instead of " + s.requestedFps + " to stay within " + C.LIMITS.maxFrames + " frames.");
    }
    parts.push(
      state.loop
        ? "Loop is on: the script repeats until Ctrl+C."
        : "Loop is off: the script plays once, then waits for Enter. The preview holds its last frame.",
    );
    if (s.color) {
      parts.push("Color is embedded too (24-bit in Windows Terminal). Add --256 for older consoles or --mono for plain text.");
    }
    parts.push("The frames are embedded, so the original video isn\u2019t needed. Terminal fonts can\u2019t match the browser pixel for pixel; characters, grid and timing are the same.");
    els.scriptNotes.textContent = parts.join(" ");
  }

  function renderStage() {
    const busy = state.phase === "busy";
    const failed = state.phase === "error";
    els.progress.hidden = !busy;
    els.errorOverlay.hidden = !failed;
    const useColor = colorActive();
    els.frame.hidden = useColor;
    els.canvas.hidden = !useColor;
    els.frame.classList.toggle("is-dimmed", busy || failed);
    els.canvas.classList.toggle("is-dimmed", busy || failed);
    els.upload.disabled = false; // choosing another video while converting cancels the old job
    els.play.disabled = !state.project;
    els.restart.disabled = !state.project;
    els.loop.disabled = !state.project;
    els.seek.disabled = !state.project;
    els.stage.setAttribute("aria-busy", busy ? "true" : "false");
    els.stageHint.hidden = state.phase !== "idle";
    els.retry.hidden = !state.file;
    els.app.dataset.phase = state.phase;
    renderSettings();
  }

  function setProgress(percent, message) {
    const value = C.clamp(percent, 0, 100);
    els.progressValue.textContent = Math.round(value) + "%";
    els.progressMessage.textContent = message;
    els.progressFill.style.width = value + "%";
    els.progress.setAttribute("aria-valuenow", String(Math.round(value)));
    els.progress.setAttribute("aria-valuetext", Math.round(value) + " percent. " + message);
  }

  /* ---------- starting a conversion ---------- */

  async function startConversion(file) {
    try {
      validateFile(file);
    } catch (error) {
      // An invalid pick must not destroy a result the user already has.
      showNotice(error.message);
      return;
    }
    const s = state.settings;
    const signature = [file.name, file.size, file.lastModified, s.cols, s.fps, s.rampId].join(":");
    if (state.inflight === signature) return; // same job already running: ignore the duplicate
    state.inflight = signature;

    if (state.controller) state.controller.abort(); // abandon the previous job
    const controller = new AbortController();
    state.controller = controller;
    const job = ++state.job;

    showNotice("");
    state.file = file;
    state.fileMeta = { name: file.name, size: file.size };
    state.project = null; // old generated data is dropped here
    state.phase = "busy";
    resetPlayer();
    textNode.nodeValue = PLACEHOLDER;
    els.seek.max = "0";
    els.seek.value = "0";
    els.time.textContent = "0:00 / 0:00";
    renderFileInfo();
    setProgress(2, "Preparing video\u2026");
    renderStage();
    renderDownloadInfo();
    layoutStage();

    try {
      const project = await convertVideoFile(file, { ...s }, {
        signal: controller.signal,
        onProgress: (update) => {
          if (job !== state.job) return; // a newer upload owns the UI
          let message = update.message;
          if (update.detail) {
            state.fileMeta = {
              name: file.name,
              size: file.size,
              width: update.detail.width,
              height: update.detail.height,
              durationMs: update.detail.durationMs,
            };
            renderFileInfo();
            const plan = update.detail.plan;
            if (plan && update.message.startsWith("Extracting")) {
              message += " " + plan.frameCount + " frames at " + formatFps(plan.fps) + " fps, " + plan.cols + "\u00d7" + plan.rows + " characters.";
            }
          }
          setProgress(update.progress, message);
        },
      });
      if (job !== state.job) return; // stale result must never overwrite a newer upload
      state.project = project;
      state.phase = "ready";
      els.seek.max = String(project.frames.length - 1);
      renderStage();
      renderDownloadInfo();
      layoutStage();
      playFrom(0); // plays automatically when conversion completes
    } catch (error) {
      if (job !== state.job || error instanceof ConvertAborted) return;
      state.project = null;
      state.phase = "error";
      els.errorText.textContent = error instanceof Error ? error.message : "Conversion failed.";
      renderStage();
      renderDownloadInfo();
    } finally {
      if (job === state.job) state.inflight = null;
    }
  }

  /* ---------- wiring ---------- */

  els.upload.addEventListener("click", () => els.input.click());
  els.input.addEventListener("change", () => {
    const file = els.input.files && els.input.files[0];
    els.input.value = ""; // lets the same file be chosen again
    if (file) startConversion(file);
    else showNotice("No file selected.");
  });
  els.retry.addEventListener("click", () => state.file && startConversion(state.file));
  els.reconvert.addEventListener("click", () => state.file && startConversion(state.file));

  // Drag and drop anywhere on the page.
  let dragDepth = 0;
  const hasFiles = (event) => event.dataTransfer && Array.from(event.dataTransfer.types || []).includes("Files");
  document.addEventListener("dragenter", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    dragDepth += 1;
    els.app.dataset.dragging = "true";
  });
  document.addEventListener("dragover", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
  });
  document.addEventListener("dragleave", (event) => {
    if (!hasFiles(event)) return;
    dragDepth = Math.max(0, dragDepth - 1);
    if (dragDepth === 0) els.app.dataset.dragging = "false";
  });
  document.addEventListener("drop", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    dragDepth = 0;
    els.app.dataset.dragging = "false";
    const file = event.dataTransfer.files && event.dataTransfer.files[0];
    if (file) startConversion(file);
  });

  els.download.addEventListener("click", () => {
    const p = state.project;
    if (!p) return;
    try {
      const source = C.buildPythonScript(p, state.loop);
      const blob = new Blob([source], { type: "text/x-python;charset=utf-8" });
      const url = URL.createObjectURL(blob);
      const link = document.createElement("a");
      link.href = url;
      link.download = C.asciiScriptFilename(p.sourceName);
      document.body.appendChild(link);
      link.click();
      link.remove();
      window.setTimeout(() => URL.revokeObjectURL(url), 15000); // Safari needs the URL to outlive the click
    } catch (_error) {
      showNotice("Couldn\u2019t generate the Python script. Convert the video again.");
    }
  });

  // Default grid width follows the screen until the user picks one.
  const width = window.innerWidth;
  state.settings.cols = width < 720 ? 48 : width < 1100 ? 72 : 96;

  renderFileInfo();
  renderStage();
  renderDownloadInfo();
  layoutStage();

  // Small, read-only hook used by the automated test (tests/verify.mjs).
  window.AsciiMotion = {
    core: AsciiCore,
    getState: () => ({ phase: state.phase, project: state.project, playing: player.playing, index: player.index, loop: state.loop }),
  };
})();
