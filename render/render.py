#!/usr/bin/env python3
"""Agrotics reel renderer.

Renders the two vertical (1080x1920) reel formats without Creatomate:

  kind=htmlreel  animated 3-scene text/illustration reel (vector, crisp)
  kind=reel      Pexels stock video + voiceover + logo/headline/CTA overlay

Every frame of the overlay is drawn by headless Chromium (HTML/CSS/SVG, so text
and illustrations are vector sharp), then ffmpeg encodes at high quality.

Inputs come from environment variables (set by the GitHub Actions workflow):
  KIND, JOB, AUDIO_URL, FIELDS, SCRIPT, VIDEO_URL, HEADLINE, CTA
Output: out/<JOB>.mp4
"""
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

W, H, FPS = 1080, 1920, 30
ASSETS = "https://cdn.jsdelivr.net/gh/g6zde/agrotics-assets@main/svg"
FFMPEG = os.environ.get("FFMPEG", "ffmpeg")
WORKERS = int(os.environ.get("WORKERS", "4"))

ILLUSTRATIONS = (
    "drop leaf sprout sun almond frost bars disease pest bee tree soil cloud drone "
    "flask shield calendar satellite tractor sensor phone map coin bulb wind"
).split()

PALETTES = {
    "dark": ["#2C333A", "#FFFFFF", "#1DD1A1", "#E27228", "#E7E8EB"],
    "light": ["#FFFFFF", "#2C333A", "#16A27C", "#D1651D", "#576574"],
    "warm": ["#FFF8F0", "#2C333A", "#D1651D", "#16A27C", "#576574"],
}

PAGE = """<!doctype html><html><head><meta charset="utf-8">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Montserrat:wght@500;600;700;800&display=swap" rel="stylesheet">
<style>
*{box-sizing:border-box;margin:0;padding:0}
html,body{width:@@W@@px;height:@@H@@px;overflow:hidden;background:@@BG@@}
#stage{position:relative;width:@@W@@px;height:@@H@@px;overflow:hidden;font-family:'Montserrat',Arial,sans-serif}
.el{position:absolute;left:0;top:0;transform-origin:0 0;will-change:transform,opacity}
.txt{white-space:normal;line-height:1.12}
.fill{background-repeat:no-repeat;background-position:center;background-size:contain}
</style></head><body><div id="stage"></div>
<script>
const SPEC = @@SPEC@@;
const stage = document.getElementById('stage');
const items = [];

function ease(name, p){ return name === 'out' ? 1 - (1-p)*(1-p) : p; }
function clamp01(x){ return Math.max(0, Math.min(1, x)); }

// value of a sequence of segments {time,dur,from,to,ease} at local time t
function seqVal(segs, t, dflt){
  if(!segs.length) return dflt;
  const s = segs.slice().sort((a,b)=>a.time-b.time);
  if(t < s[0].time) return s[0].from;
  let last = s[0].from;
  for(const a of s){
    if(t < a.time) return last;
    if(t < a.time + a.dur) return a.from + (a.to - a.from) * ease(a.ease, (t-a.time)/a.dur);
    last = a.to;
  }
  return last;
}

function build(){
  document.body.style.background = SPEC.bg || 'transparent';
  stage.style.background = SPEC.bg || 'transparent';
  for(const e of SPEC.elements){
    const d = document.createElement('div');
    d.className = 'el' + (e.kind === 'text' ? ' txt' : '');
    d.style.width = e.w + 'px';
    if(e.h) d.style.height = e.h + 'px';
    if(e.kind === 'img'){
      d.classList.add('fill');
      d.style.backgroundImage = 'url(' + e.src + ')';
      if(e.bgcolor) d.style.backgroundColor = e.bgcolor;
    } else if(e.kind === 'circle'){
      d.style.borderRadius = '50%';
      d.style.background = e.color;
    } else if(e.kind === 'rect'){
      d.style.background = e.color;
      if(e.radius) d.style.borderRadius = e.radius + 'px';
    } else if(e.kind === 'text'){
      d.textContent = e.text;
      const s = d.style;
      s.fontWeight = e.weight; s.fontSize = e.size + 'px'; s.color = e.color;
      s.textAlign = e.align || 'left';
      if(e.upper) s.textTransform = 'uppercase';
      if(e.letter) s.letterSpacing = e.letter + 'px';
      if(e.lh) s.lineHeight = e.lh;
      if(e.pill){
        s.background = e.pill; s.padding = e.padding || '14px 30px';
        s.borderRadius = '999px'; s.width = 'auto'; s.maxWidth = e.w + 'px';
        s.whiteSpace = 'nowrap'; s.display = 'inline-block';
      }
      if(e.nowrap) s.whiteSpace = 'nowrap';
    } else if(e.kind === 'html'){
      d.innerHTML = e.html;
    }
    stage.appendChild(d);
    items.push({e, d, idx: items.length});
  }
}

// shrink text until it fits its box (no overflow, limited number of lines)
function fitAll(){
  for(const {e, d} of items){
    if(e.kind !== 'text' || !e.fit) continue;
    const maxLines = e.fit.lines || 1;
    const minSize = e.size * (e.fit.min || 0.55);
    const boxW = e.w;
    let size = e.size;
    for(let i = 0; i < 80; i++){
      d.style.fontSize = size + 'px';
      const lh = parseFloat(getComputedStyle(d).lineHeight) || size * 1.12;
      const padX = e.pill ? 60 : 0, padY = e.pill ? 28 : 0;
      const lines = Math.round((d.scrollHeight - padY) / lh);
      const tooWide = d.scrollWidth > boxW + 1 || (e.pill && d.offsetWidth > boxW + 1);
      if(lines <= maxLines && !tooWide) break;
      if(size <= minSize) break;
      size -= 2;
    }
    e.finalSize = size;
  }
}

// stack elements that follow another element so lines can never overlap, even if a headline wraps
function layoutStack(){
  for(const it of items){
    const e = it.e;
    if(e.after == null) continue;
    const prev = items.find(x => x.idx === e.after);
    if(!prev) continue;
    e.y = prev.e.y + prev.d.offsetHeight + (e.gap || 0);
  }
}

function setTime(t){
  for(const {e, d} of items){
    const local = t - e.time;
    const vis = local >= 0 && local < e.dur;
    d.style.display = vis ? '' : 'none';
    if(!vis) continue;
    const A = e.anims || [];
    const fades = A.filter(a=>a.type==='fade').map(a=>({time:a.time,dur:a.dur,from:0,to:1,ease:a.ease}));
    const scales = A.filter(a=>a.type==='scale').map(a=>({time:a.time,dur:a.dur,from:a.from,to:a.to,ease:a.ease}));
    const slides = A.filter(a=>a.type==='slide');
    let op = seqVal(fades, local, 1);
    let sc = seqVal(scales, local, 1);
    let tx = 0, ty = 0;
    for(const a of slides){
      const p = ease(a.ease, clamp01((local - a.time) / a.dur));
      const off = (1 - p) * a.dist;
      if(a.dir === 'up') ty += off; else if(a.dir === 'down') ty -= off;
      else if(a.dir === 'left') tx += off; else if(a.dir === 'right') tx -= off;
    }
    d.style.opacity = op * (e.opacity == null ? 1 : e.opacity);
    const ax = (e.ax || 0) * 100, ay = (e.ay || 0) * 100;
    d.style.transform = 'translate(' + (e.x + tx) + 'px,' + (e.y + ty) + 'px) scale(' + sc + ') translate(-' + ax + '%,-' + ay + '%)';
  }
}

async function ready(){
  await document.fonts.load('500 40px Montserrat');
  await document.fonts.load('600 40px Montserrat');
  await document.fonts.load('700 40px Montserrat');
  await document.fonts.load('800 40px Montserrat');
  await document.fonts.ready;
  const urls = SPEC.elements.filter(e=>e.kind==='img').map(e=>e.src);
  await Promise.all([...new Set(urls)].map(u => new Promise(res => {
    const im = new Image(); im.onload = im.onerror = () => res(); im.src = u;
  })));
  build();
  fitAll();
  layoutStack();
  setTime(0);
  window.__ready = true;
}
window.__go = ready();
</script></body></html>
"""


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------
def log(*a):
    print(*a, flush=True)


def run(cmd):
    log("+", " ".join(str(c) for c in cmd))
    subprocess.run([str(c) for c in cmd], check=True)


def download(url, dest, min_bytes=2000, tries=3):
    last = None
    for attempt in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 agrotics-render"})
            with urllib.request.urlopen(req, timeout=180) as r, open(dest, "wb") as f:
                shutil.copyfileobj(r, f)
            size = Path(dest).stat().st_size
            head = Path(dest).read_bytes()[:64].lstrip().lower()
            if head.startswith(b"<!doctype") or head.startswith(b"<html"):
                raise RuntimeError("got an HTML page instead of a media file (is the link public?): " + url)
            if size < min_bytes:
                raise RuntimeError("download too small (%d bytes): %s" % (size, url))
            return dest
        except Exception as e:  # retry transient network problems
            last = e
            log("download failed (%d/%d): %s" % (attempt + 1, tries, e))
            time.sleep(3)
    raise last


def media_duration(path):
    p = subprocess.run([FFMPEG, "-i", str(path)], capture_output=True, text=True)
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+\.\d+)", p.stderr)
    if not m:
        raise RuntimeError("cannot read duration of " + str(path))
    return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))


def px(frac, total):
    return frac * total


def clean(s):
    return re.sub(r"\s+", " ", (s or "").replace("—", ",").replace("–", ",")).strip()


# ----------------------------------------------------------------------------
# HTML reel (3 animated scenes)
# ----------------------------------------------------------------------------
def anim(type_, time, dur, ease="lin", **kw):
    a = {"type": type_, "time": time, "dur": dur, "ease": ease}
    a.update(kw)
    return a


def scale(time, dur, a, b, ease="lin"):
    return anim("scale", time, dur, ease, **{"from": a, "to": b})


def fade(time, dur):
    return anim("fade", time, dur)


def slide(time, dur, direction, dist):
    return anim("slide", time, dur, "out", dir=direction, dist=dist)


def split_sentences(text):
    t = text.replace("? ", ". ").replace("! ", ". ")
    return [s for s in t.split(". ") if s.strip()]


def scene_times(script, audio_dur):
    """Same timing rules the Make scenario used: scene 1 = sentence 1, etc."""
    sents = split_sentences(script)
    total = len(" ".join(sents)) or 1
    l1 = len(sents[0]) if sents else total // 3
    l2 = len(sents[1]) if len(sents) > 1 else total // 3
    t1 = max(3.0, audio_dur * l1 / total)
    t2 = max(6.8, audio_dur * (l1 + l2) / total)
    t3 = max(9.8, audio_dur + 0.5)
    t1 = math.floor(t1 * 100) / 100
    t2 = max(t1 + 3.0, math.floor(t2 * 100) / 100)
    t3 = max(t2 + 3.0, math.floor(t3 * 100) / 100)
    return t1, t2, t3


KEYS = ["theme", "ill1", "tag", "s1a", "s1b", "s1sub", "s2a", "s2b", "step1", "step2", "step3",
        "s3a", "s3b", "s3sub", "ill3"]


def parse_fields(raw):
    """Return a 1-based list of the 15 art-director fields.

    Preferred input is a JSON object with the keys in KEYS; the old pipe separated line is still
    understood (and repaired when the model dropped a field but kept the trailing illustration).
    """
    raw = (raw or "").strip()
    a, b = raw.find("{"), raw.rfind("}")
    if a != -1 and b > a:
        try:
            d = json.loads(raw[a:b + 1])
            return [""] + [clean(str(d.get(k, ""))) for k in KEYS]
        except ValueError:
            pass
    parts = [clean(x) for x in raw.replace("\n", " ").split("|")]
    if len(parts) < 15 and parts and parts[-1].lower() in ILLUSTRATIONS:
        last = parts.pop()
        parts += [""] * (14 - len(parts))
        parts.append(last)
    parts += [""] * (15 - len(parts))
    return [""] + parts[:15]


def htmlreel_spec(fields_raw, script, audio_dur):
    f = parse_fields(fields_raw)

    theme = f[1].lower() if f[1].lower() in PALETTES else "dark"
    pal = PALETTES[theme]
    bg, fg, accent, accent2, muted = pal

    def ill(name, fallback):
        name = name.strip().lower()
        return name if name in ILLUSTRATIONS else fallback

    ill1 = ill(f[2], "leaf")
    ill3 = ill(f[15], ill1)
    logo = "logo-white.svg" if theme == "dark" else "logo-dark.svg"
    t1, t2, t3 = scene_times(script, audio_dur)

    els = []

    def zoomed_ill(name, cx, cy, w, t_start, t_dur, a0):
        els.append({
            "kind": "img", "src": "%s/ill-%s.svg" % (ASSETS, name),
            "x": cx * W, "y": cy * H, "ax": .5, "ay": .5, "w": w * W, "h": w * W,
            "time": t_start, "dur": t_dur,
            "anims": [scale(a0, .55, 0, 1.12, "out"), scale(a0 + .55, .25, 1.12, 1.0),
                      scale(a0 + .8, t_dur, 1.0, 1.06)],
        })

    # background circles (drawn first so everything sits on top)
    els.append({"kind": "circle", "color": accent, "x": .90 * W, "y": .10 * H, "ax": .5, "ay": .5,
                "w": .90 * W, "h": .50 * H, "opacity": .09, "time": 0, "dur": t3,
                "anims": [scale(0, t3, .85, 1.15)]})
    els.append({"kind": "circle", "color": accent2, "x": .06 * W, "y": .92 * H, "ax": .5, "ay": .5,
                "w": .70 * W, "h": .38 * H, "opacity": .06, "time": 0, "dur": t3,
                "anims": [scale(0, t3, 1.0, .8)]})

    # scene 1 illustration (centre-top) and scene 3 illustration
    zoomed_ill(ill1, .5, .37, .62, 0, t1, .2)
    zoomed_ill(ill3, .5, .30, .46, t2, t3 - t2, .15)

    # brand logo top-left (whole video)
    els.append({"kind": "img", "src": "%s/%s" % (ASSETS, logo), "x": .07 * W, "y": .08 * H, "ax": 0, "ay": .5,
                "w": .38 * W, "h": .38 * W * 130 / 900, "time": 0, "dur": t3,
                "anims": [fade(0, .7), slide(0, .7, "right", .06 * W)]})
    # big logo in the closing scene
    els.append({"kind": "img", "src": "%s/%s" % (ASSETS, logo), "x": .5 * W, "y": .80 * H, "ax": .5, "ay": .5,
                "w": .62 * W, "h": .62 * W * 130 / 900, "time": t2, "dur": t3 - t2,
                "anims": [scale(1.2, .6, .6, 1.0, "out"), fade(1.2, .5)]})

    def text(txt, x, y, size, weight, color, time, dur, anims, w=.86, ax=0, ay=0, align="left", fit=None,
             after=None, gap=0, **kw):
        if not txt or txt.strip().lower() in ILLUSTRATIONS:
            return None
        e = {"kind": "text", "text": txt, "x": x * W, "y": y * H, "ax": ax, "ay": ay, "w": w * W,
             "size": size, "weight": weight, "color": color, "align": align, "time": time, "dur": dur,
             "anims": anims}
        if fit:
            e["fit"] = fit
        if after is not None:
            e["after"] = after
            e["gap"] = gap
        e.update(kw)
        els.append(e)
        return len(els) - 1

    # tag pill top-right
    text(f[3], .93, .08, 28, 700, bg, 0, t3, [scale(.1, .6, .7, 1.0, "out"), fade(.1, .5)],
         w=.40, ax=1, ay=.5, align="center", upper=True, pill=accent, padding="14px 30px",
         fit={"lines": 1, "min": .6}, letter=1)

    # scene 1
    HEAD = dict(fit={"lines": 1, "min": .5}, lh=1.1)
    a = text(f[4], .07, .60, 100, 800, fg, 0, t1, [slide(.9, .7, "up", .08 * H), fade(.9, .5)], **HEAD)
    b = text(f[5], .07, .67, 100, 800, accent, 0, t1, [slide(1.3, .7, "up", .08 * H), fade(1.3, .5)],
             after=a, gap=4, **HEAD)
    text(f[6], .07, .755, 44, 500, muted, 0, t1, [fade(2.0, .7)], fit={"lines": 2, "min": .7},
         after=b if b is not None else a, gap=28)

    # scene 2
    a = text(f[7], .07, .15, 100, 800, fg, t1, t2 - t1, [slide(.2, .7, "up", .08 * H), fade(.2, .5)], **HEAD)
    text(f[8], .07, .22, 100, 800, accent, t1, t2 - t1, [slide(.5, .7, "up", .08 * H), fade(.5, .5)],
         after=a, gap=4, **HEAD)
    steps = [(.41, f[9], accent, 1.0), (.54, f[10], accent2, 1.7), (.67, f[11], accent, 2.4)]
    for i, (y, label, col, t0) in enumerate(steps, 1):
        els.append({"kind": "circle", "color": col, "x": .07 * W, "y": y * H, "ax": 0, "ay": 0,
                    "w": .12 * W, "h": .12 * W, "time": t1, "dur": t2 - t1,
                    "anims": [scale(t0, .5, 0, 1.1, "out"), scale(t0 + .5, .2, 1.1, 1.0)]})
        text(str(i), .13, y + .0, 52, 800, bg, t1, t2 - t1, [fade(t0 + .2, .4)], w=.10, ax=.5, ay=0,
             align="center", lh=2.2 * .12 * W / 52 / 2.2)
        text(label, .23, y + .018, 54, 700, fg, t1, t2 - t1,
             [slide(t0, .6, "left", .08 * W), fade(t0, .5)], w=.70,
             fit={"lines": 2, "min": .6}, lh=1.1)

    # scene 3
    a = text(f[12], .07, .48, 100, 800, fg, t2, t3 - t2, [slide(.7, .7, "up", .08 * H), fade(.7, .5)], **HEAD)
    b = text(f[13], .07, .55, 100, 800, accent, t2, t3 - t2, [slide(1.1, .7, "up", .08 * H), fade(1.1, .5)],
             after=a, gap=4, **HEAD)
    text(f[14], .07, .64, 44, 500, muted, t2, t3 - t2, [fade(1.7, .7)], fit={"lines": 2, "min": .7},
         after=b if b is not None else a, gap=28)

    return {"bg": bg, "elements": els, "duration": t3}


# ----------------------------------------------------------------------------
# Reel: stock video + overlay
# ----------------------------------------------------------------------------
def reel_spec(headline, cta, duration):
    headline = clean(headline)[:40]
    cta = clean(cta)[:60]
    els = []
    # legibility gradients
    els.append({"kind": "html", "w": W, "h": H, "x": 0, "y": 0, "time": 0, "dur": duration, "anims": [fade(0, .6)],
                "html": ('<div style="position:absolute;inset:0;background:linear-gradient(180deg,'
                         'rgba(28,34,40,.55) 0%,rgba(28,34,40,0) 22%,rgba(28,34,40,0) 52%,'
                         'rgba(28,34,40,.88) 100%)"></div>')})
    els.append({"kind": "img", "src": ASSETS + "/logo-white.svg", "x": 72, "y": 230, "ax": 0, "ay": .5,
                "w": 330, "h": 48, "time": 0, "dur": duration,
                "anims": [fade(0, .6), slide(0, .6, "right", 40)]})
    left, right_pad = 72, 170          # keep clear of Instagram's right-hand buttons
    box_w = W - left - right_pad
    bottom = H - 400                    # keep clear of the caption area

    cta_h = 96 if cta else 0
    head_lines_h = (1 if len(headline) <= 16 else 2) * 84 * 1.1
    top = bottom - (cta_h + (40 if cta else 0)) - head_lines_h - 24 - 8 - 32

    els.append({"kind": "rect", "color": "#1DD1A1", "radius": 4, "x": left, "y": top, "ax": 0, "ay": 0,
                "w": 96, "h": 8, "time": 0, "dur": duration, "anims": [scale(.3, .5, 0, 1, "out")]})
    head_y = top + 8 + 32
    els.append({"kind": "text", "text": headline, "x": left, "y": head_y, "ax": 0, "ay": 0, "w": box_w,
                "size": 84, "weight": 800, "color": "#FFFFFF", "align": "left", "lh": 1.1, "letter": -1,
                "fit": {"lines": 2, "min": .6}, "time": 0, "dur": duration,
                "anims": [slide(.5, .7, "up", 60), fade(.5, .6)]})
    if cta:
        els.append({"kind": "text", "text": cta, "x": left, "y": head_y + head_lines_h + 40, "ax": 0, "ay": 0,
                    "w": box_w, "size": 34, "weight": 700, "color": "#2C333A", "align": "left",
                    "pill": "#1DD1A1", "padding": "20px 36px", "fit": {"lines": 1, "min": .6},
                    "time": 0, "dur": duration, "anims": [slide(1.3, .6, "up", 40), fade(1.3, .5)]})
    return {"bg": None, "elements": els, "duration": duration}


# ----------------------------------------------------------------------------
# frame rendering (multi-process)
# ----------------------------------------------------------------------------
def render_chunk(args):
    spec, frames, outdir, transparent = args
    from playwright.sync_api import sync_playwright
    html = (PAGE.replace("@@W@@", str(W)).replace("@@H@@", str(H))
            .replace("@@BG@@", "transparent" if transparent else (spec.get("bg") or "#000"))
            .replace("@@SPEC@@", json.dumps(spec).replace("</", "<\\/")))
    with sync_playwright() as p:
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": W, "height": H}, device_scale_factor=1)
        page.set_content(html, wait_until="load")
        page.wait_for_function("window.__ready === true", timeout=90000)
        for i in frames:
            page.evaluate("t => setTime(t)", i / FPS)
            page.screenshot(path=os.path.join(outdir, "f%05d.png" % i), omit_background=transparent,
                            type="png")
        browser.close()
    return len(frames)


def render_frames(spec, nframes, outdir, transparent):
    os.makedirs(outdir, exist_ok=True)
    n = max(1, min(WORKERS, nframes))
    chunks = [list(range(k, nframes, n)) for k in range(n)]
    with ProcessPoolExecutor(max_workers=n) as ex:
        done = sum(ex.map(render_chunk, [(spec, c, outdir, transparent) for c in chunks]))
    if done != nframes:
        raise RuntimeError("rendered %d of %d frames" % (done, nframes))


# ----------------------------------------------------------------------------
def main():
    kind = os.environ.get("KIND", "htmlreel")
    job = re.sub(r"[^A-Za-z0-9_.-]", "_", os.environ["JOB"])
    out_dir = Path(os.environ.get("OUT_DIR", "out"))
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / (job + ".mp4")
    work = Path(tempfile.mkdtemp(prefix="reel_"))

    voice = download(os.environ["AUDIO_URL"], work / "voice.mp3")
    adur = media_duration(voice)
    log("voice duration", adur)

    x264 = ["-c:v", "libx264", "-preset", "slow", "-crf", "14", "-maxrate", "20M", "-bufsize", "40M",
            "-pix_fmt", "yuv420p", "-profile:v", "high", "-movflags", "+faststart"]
    aac = ["-c:a", "aac", "-b:a", "192k", "-ar", "44100"]

    if kind == "htmlreel":
        spec = htmlreel_spec(os.environ["FIELDS"], clean(os.environ.get("SCRIPT", "")), adur)
        dur = spec["duration"]
        n = int(math.ceil(dur * FPS))
        render_frames(spec, n, str(work / "frames"), transparent=False)
        run([FFMPEG, "-y", "-framerate", FPS, "-i", work / "frames" / "f%05d.png", "-i", voice,
             *x264, *aac, "-r", FPS, "-t", "%.2f" % dur, out])
    elif kind == "reel":
        x264 = ["-c:v", "libx264", "-preset", "slow", "-crf", "17", "-maxrate", "12M", "-bufsize", "24M",
                "-pix_fmt", "yuv420p", "-profile:v", "high", "-movflags", "+faststart"]
        bg = download(os.environ["VIDEO_URL"], work / "bg.mp4", min_bytes=20000)
        dur = max(8.0, adur + 0.6)
        spec = reel_spec(os.environ.get("HEADLINE", ""), os.environ.get("CTA", ""), dur)
        anim_end = 2.2                                   # all overlay motion is finished by then
        n = int(math.ceil(anim_end * FPS))
        render_frames(spec, n, str(work / "ov"), transparent=True)
        vf = ("[0:v]scale=%d:%d:force_original_aspect_ratio=increase:flags=lanczos,crop=%d:%d,fps=%d,setsar=1[bg];"
              "[1:v]format=rgba,tpad=stop_mode=clone:stop_duration=%d[ov];"
              "[bg][ov]overlay=0:0:format=auto,format=yuv420p[v]") % (W, H, W, H, FPS, int(dur) + 5)
        run([FFMPEG, "-y", "-stream_loop", "-1", "-i", bg, "-framerate", FPS, "-i", work / "ov" / "f%05d.png",
             "-i", voice, "-filter_complex", vf, "-map", "[v]", "-map", "2:a", *x264, *aac,
             "-r", FPS, "-t", "%.2f" % dur, out])
    else:
        raise SystemExit("unknown KIND " + kind)

    log("done", out, out.stat().st_size, "bytes")
    shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
