#!/usr/bin/env python3
"""
FC 27 Scout Room - price engine (runs on GitHub every 15 minutes)

Each run: load the saved price history, read the latest PS5 prices from FUT.GG's public
price file, let the scouts flag cards, let the chief director approve or turn them down,
move the paper trades along, and write state.json for the website.
"""

import bisect
import gzip
import json
import math
import os
import pickle
import ssl
import statistics
import sys
import threading
import time
import traceback
import urllib.error
import urllib.request
import uuid
from datetime import datetime, timedelta, timezone
from array import array

# ----------------------------------------------------------------- settings --
GAME = "27"
PLATFORM = "ps5"                 # "ps5" (PlayStation) or "pc"
DATA_DIR = os.environ.get("SCOUT_DATA", "data")
TAX = 0.05                       # EA keeps 5% of every sale

# Director rules (you can change most of these in the page too)
DEFAULTS = {
    "budget": 100000,            # coins you are willing to invest
    "daily_limit": 50000,        # spend at most this many coins on new buys per day
    "min_roi": 0.06,             # minimum profit after tax, as a share of the buy price
    "min_profit": 2000,          # minimum profit after tax for the whole pick (all copies), in coins
    "max_copies": 10,            # most copies of one card per pick; buying more pushes its price up
    "stop_loss": 0.06,           # sell if the price falls this far below what you paid
    "max_hold_hours": 24,        # daily trades: a 1-day listing, then sell at market
    "checkin_hours": 2,          # you check the app about every 2 hours, so drops are only acted on then
    "watchlist": [],             # card ids you always want checked
    "v": 2,
}

# A strategy goes live only after its paper trades prove it
TRIAL_DAYS = 3
TRIAL_MIN_TRADES = 10
TRIAL_MIN_WINRATE = 0.60
# Fast track: lots of trades with a strong win rate can prove a strategy in 2 days instead of 3
FAST_DAYS, FAST_MIN_TRADES, FAST_MIN_WINRATE = 2, 40, 0.65

# Each strategy is also tested with a more cautious and a more ambitious sell target
VARIANTS = (("", 1.0, "Standard"), ("safe", 0.7, "Safe target"), ("bold", 1.3, "Bold target"))
SITE_URL = "https://jovansaran48-sudo.github.io/fc27-scout/"

R2 = "https://r2.fut.gg/" + GAME + "/"
SITE = "https://www.fut.gg"
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) fc27-scout/1.0"

# price history kept: (name, bucket seconds, points kept)
SERIES = (("fine", 0, 12),           # every run (~15 min apart), last few hours
          ("mid", 900, 4 * 24 * 4),  # every 15 minutes, 4 days  -> day and 3-day charts
          ("hourly", 3600, 24 * 31)) # every hour, 31 days       -> week and month charts
UNIVERSE = (200, 300000)             # only cards priced in this range are tracked (your daily limit is far lower)
SIM = os.environ.get("FC27_SIM") == "1"

POSITIONS = {0: "GK", 2: "RWB", 3: "RB", 5: "CB", 7: "LB", 8: "LWB", 10: "CDM", 12: "RM",
             14: "CM", 16: "LM", 18: "CAM", 21: "CF", 23: "RW", 25: "ST", 27: "LW"}

lock = threading.RLock()


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


# ------------------------------------------------------------- price steps --
def step(p):
    return 50 if p < 1000 else 100 if p < 10000 else 250 if p < 50000 else 500 if p < 100000 else 1000


def round_down(p):
    s = step(p)
    return int(p // s * s)


def round_up(p):
    s = step(p)
    return int(math.ceil(p / s) * s)


def after_tax(p):
    return int(p * (1 - TAX))


def break_even(buy):
    return round_up(buy / (1 - TAX))


def base_id(card_id):
    return card_id % 16777216


def card_url(card_id):
    return f"{SITE}/players/{base_id(card_id)}/{GAME}-{card_id}/"


# ------------------------------------------------------------- networking --
_ctx = None


def ssl_ctx():
    global _ctx
    if _ctx is None:
        _ctx = ssl.create_default_context()
        try:
            import certifi  # optional, fixes python.org installs without certificates
            _ctx = ssl.create_default_context(cafile=certifi.where())
        except Exception:
            pass
    return _ctx


def get_json(url, timeout=30):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout, context=ssl_ctx()) as r:
        return json.loads(r.read().decode("utf-8"))


# ------------------------------------------------------------ market store --
class Market:
    """Price history for every card at three resolutions (see SERIES)."""

    def __init__(self):
        self.ts = {name: [] for name, _, _ in SERIES}
        self.data = {name: {} for name, _, _ in SERIES}   # name -> card_id -> array('I')
        self.status = {}

    @property
    def fine_ts(self):
        return self.ts["fine"]

    @property
    def fine(self):
        return self.data["fine"]

    def ingest(self, ts, ids, prices, statuses):
        incoming = {}
        for cid, p, s in zip(ids, prices, statuses):
            incoming[cid] = max(0, int(p))
            self.status[cid] = s
        for name, bucket, keep in SERIES:
            tl, series = self.ts[name], self.data[name]
            if bucket and tl and int(ts // bucket) == int(tl[-1] // bucket):
                continue                                   # still inside the same bucket
            tl.append(ts)
            n = len(tl)
            for cid, p in incoming.items():
                a = series.get(cid)
                if a is None:
                    a = series[cid] = array("I", [0] * (n - 1))
                a.append(p)
            for cid, a in series.items():                  # cards missing from this file
                if len(a) < n:
                    a.append(a[-1] if a else 0)
            if n > keep:
                cut = n - keep
                self.ts[name] = tl[cut:]
                for k in series:
                    series[k] = series[k][cut:]

    def window(self, name, cid, start, end):
        """(timestamps, prices) of one series between two moments, zero prices dropped."""
        tl = self.ts[name]
        a = self.data[name].get(cid)
        if not a or not tl:
            return [], []
        i, j = bisect.bisect_left(tl, start), bisect.bisect_right(tl, end)
        pts = [(tl[k], a[k]) for k in range(i, j) if a[k]]
        return [t for t, _ in pts], [p for _, p in pts]

    # price at (or just before) a moment in the past; 0 if unknown
    def price_ago(self, cid, seconds):
        if not self.fine_ts:
            return 0
        t = self.fine_ts[-1] - seconds
        for name in ("fine", "mid", "hourly"):
            tl = self.ts[name]
            if tl and tl[0] <= t:
                a = self.data[name].get(cid)
                i = bisect.bisect_right(tl, t) - 1
                return a[i] if a and i >= 0 else 0
        return 0

    def history_hours(self):
        firsts = [tl[0] for tl in self.ts.values() if tl]
        if not firsts:
            return 0.0
        return (self.fine_ts[-1] - min(firsts)) / 3600

    def save(self, path):
        tmp = path + ".tmp"
        with gzip.open(tmp, "wb", compresslevel=3) as f:
            pickle.dump({"v": 2, "ts": self.ts, "data": self.data, "status": self.status}, f)
        os.replace(tmp, path)

    def load(self, path):
        with gzip.open(path, "rb") as f:
            d = pickle.load(f)
        if d.get("v") == 2:
            for name, _, _ in SERIES:
                self.ts[name] = d["ts"].get(name, [])
                self.data[name] = d["data"].get(name, {})
        else:                                              # file from the first version
            self.ts["fine"], self.data["fine"] = d["fine_ts"], d["fine"]
            self.ts["hourly"], self.data["hourly"] = d["hourly_ts"], d["hourly"]
        self.status = d["status"]


# ------------------------------------------------------------ card features --
def day_profile(m, cid, now_ts):
    """Look at the last 4 days, one 24-hour window at a time (newest first)."""
    days = []
    for d in range(4):
        end = now_ts - d * 86400
        tl, ps = m.window("mid", cid, end - 86400, end)
        if d == 0:                                         # include the very latest checks
            ft, fp = m.window("fine", cid, end - 86400, end)
            merged = sorted(zip(tl + ft, ps + fp))
            tl, ps = [t for t, _ in merged], [p for _, p in merged]
        if len(ps) < 30:                                   # needs ~8 hours of 15-minute points to count as a day
            break
        lo, hi = min(ps), max(ps)
        ilo = ps.index(lo)
        hi_after = max(ps[ilo:])                           # best price reached after the day's low
        days.append({"lo": lo, "hi": hi, "hi_after": hi_after})
    return days


def features(m, cid):
    f = m.fine.get(cid)
    if not f or not f[-1]:
        return None
    now = f[-1]
    now_ts = m.fine_ts[-1]
    h = m.data["hourly"].get(cid, array("I"))
    week = [x for x in h[-168:] if x]
    ret = []
    pts = [x for x in h[-72:] if x]
    for a, b in zip(pts, pts[1:]):
        ret.append(math.log(b / a))

    def ch(seconds):
        p = m.price_ago(cid, seconds)
        return (now / p - 1) if p else None
    recent = [p for p in f[-4:-1] if p]
    ref = statistics.median(recent) if recent else now
    glitch = bool(recent) and (now < ref * 0.5 or now > ref * 2)     # one-off bad reading from FUT.GG
    _, day = m.window("mid", cid, now_ts - 86400, now_ts)
    moves = sum(1 for a, b in zip(day, day[1:]) if a != b)
    return {
        "moves24": moves, "pts24": len(day), "glitch": glitch,
        "now": now, "ts": now_ts,
        "ch30m": ch(1800), "ch1h": ch(3600), "ch2h": ch(7200), "ch6h": ch(6 * 3600), "ch24h": ch(86400),
        "p24h": m.price_ago(cid, 86400),
        "med7": statistics.median(week) if len(week) >= 12 else None,
        "hi7": max(week) if week else None,
        "lo7": min(week) if week else None,
        "hours": len(week),
        "fine_pts": len([x for x in f if x]),
        "vol": statistics.pstdev(ret) if len(ret) >= 6 else None,
        "status": m.status.get(cid, 0),
        "_m": m, "_cid": cid,                              # for scouts that need the full chart
    }


def market_mood(m, feats):
    ch24 = [x["ch24h"] for x in feats.values() if x["ch24h"] is not None and 5000 <= x["now"] <= 500000]
    ch6 = [x["ch6h"] for x in feats.values() if x["ch6h"] is not None and 5000 <= x["now"] <= 500000]
    return {
        "ch24h": statistics.median(ch24) if len(ch24) > 200 else None,
        "ch6h": statistics.median(ch6) if len(ch6) > 200 else None,
    }


# ------------------------------------------------------------------ scouts --
CTX = {"now": 0, "meta": {}, "sbc_new": False, "demand": {}, "cheap": {}, "twins": {}}


def _ovr(cid):
    return (CTX["meta"].get(str(cid)) or {}).get("ovr") or 0


def _window(spans):
    """True when UK time falls inside any (weekday, start hour, end hour) span; end may pass midnight."""
    t = london(CTX["now"])
    wd, h = t.weekday(), t.hour + t.minute / 60
    for d, a, b in spans:
        if b > 24:
            if (wd == d and h >= a) or (wd == (d + 1) % 7 and h < b - 24):
                return True
        elif wd == d and a <= h < b:
            return True
    return False


def _rname(cid):
    return ((CTX["meta"].get(str(cid)) or {}).get("rname") or "").lower()


def _ago(x, hours):
    p = x["_m"].price_ago(x["_cid"], hours * 3600)
    return p or None

# Each scout watches its own slice of the market and hands candidates to the director.
def scout_daily(cid, x, mood):
    """Daily Swing: buy near the day's low on cards that have bounced back day after day."""
    if not (5000 <= x["now"] <= 30000) or (x["ch30m"] is not None and x["ch30m"] < -0.02):
        return None
    days = day_profile(x["_m"], cid, x["ts"])
    if len(days) < 3:                                      # today plus at least 2 earlier days
        return None
    today, past = days[0], days[1:4]
    rng = today["hi"] / today["lo"] - 1
    if rng < 0.11:
        return None
    pos = (x["now"] - today["lo"]) / (today["hi"] - today["lo"])
    if pos > 0.25:
        return None
    if today["lo"] < past[0]["lo"] * 0.95:                 # lows keep falling: a crash, not a swing
        return None
    proven = [d for d in past if d["hi_after"] >= d["lo"] * 1.11 and abs(d["lo"] / today["lo"] - 1) <= 0.06]
    if len(proven) < 2:
        return None
    usual_high = statistics.median([d["hi_after"] for d in proven] + [today["hi"]])
    return {"target": usual_high * 0.98, "hold": "same day or next",
            "why": (f"near today's low with a {rng:.0%} daily range, and it bounced back to its high "
                    f"on {len(proven)} of the last {len(past)} days")}


def scout_dip(cid, x, mood):
    if not (5000 <= x["now"] <= 3000000) or not x["med7"] or x["hours"] < 24:
        return None
    gap = 1 - x["now"] / x["med7"]
    if gap >= 0.12 and (x["ch30m"] or 0) >= -0.02:
        return {"target": x["med7"] * 0.98, "hold": "1-3 days",
                "why": f"{gap:.0%} below its usual price this week and has stopped falling"}


def scout_crash(cid, x, mood):
    mk = mood["ch24h"]
    if mk is None or mk > -0.04 or not (10000 <= x["now"] <= 2000000) or x["ch24h"] is None:
        return None
    if x["ch24h"] <= mk * 1.5 and (x["ch1h"] or 0) >= -0.01 and x["p24h"]:
        return {"target": x["p24h"] * 0.97, "hold": "1-4 days",
                "why": f"market is down {abs(mk):.0%} today and this card fell {abs(x['ch24h']):.0%}, more than most"}


def scout_momentum(cid, x, mood):
    c24, c6, c1 = x["ch24h"], x["ch6h"], x["ch1h"]
    if not (3000 <= x["now"] <= 1500000) or c6 is None or c1 is None:
        return None
    if c24 is not None and 0.04 <= c24 <= 0.25 and c6 > 0.01 and c1 >= 0:
        lift = min(0.6 * c24, 0.15)
        return {"target": x["now"] * (1 + lift), "hold": "a few hours to a day",
                "why": f"up {c24:.0%} in 24h and still climbing"}
    if c24 is None and 0.05 <= c6 <= 0.25 and c1 > 0:     # warm-up: only a few hours recorded
        return {"target": x["now"] * (1 + min(0.6 * c6, 0.13)), "hold": "a few hours",
                "why": f"up {c6:.0%} in the last 6 hours and still climbing"}


def scout_fodder(cid, x, mood):
    if not (1000 <= x["now"] <= 30000) or x["ch6h"] is None or x["ch1h"] is None:
        return None
    if 0.06 <= x["ch6h"] <= 0.40 and x["ch1h"] >= 0:
        return {"target": x["now"] * 1.15, "hold": "same day",
                "why": f"cheap card up {x['ch6h']:.0%} in 6 hours, often an early sign of SBC demand"}


def scout_rebound(cid, x, mood):
    if not (5000 <= x["now"] <= 2000000) or x["ch24h"] is None or x["ch2h"] is None or not x["p24h"]:
        return None
    if x["ch24h"] <= -0.20 and x["ch2h"] >= 0.02:
        return {"target": x["now"] + 0.5 * (x["p24h"] - x["now"]), "hold": "1-2 days",
                "why": f"dropped {abs(x['ch24h']):.0%} in 24h and is now bouncing back"}


def scout_sbc(cid, x, mood):
    """SBC Sniper: a new SBC is pushing one rating's fodder up; buy the cheap cards of that rating that haven't moved yet."""
    if not CTX["sbc_new"] or not (500 <= x["now"] <= 30000):
        return None
    o = _ovr(cid)
    d = CTX["demand"].get(o)
    if d is None or d < 0.04 or cid not in CTX["cheap"].get(o, ()):
        return None
    c6 = x["ch6h"]
    if c6 is None or c6 > d * 0.5 or (x["ch1h"] or 0) < -0.01:
        return None
    return {"target": x["now"] * (1 + min(d, 0.15)), "hold": "same day", "hold_h": 24,
            "why": f"{o}-rated fodder is up {d:.0%} in 6 hours since a new SBC, and this card hasn't caught up yet"}


def scout_prebuy(cid, x, mood):
    """Promo Pre-buy: the afternoon before TOTW (Wed) or promo (Fri) packs, buy high-rated cards already being bid up."""
    if not _window([(1, 12, 39), (3, 12, 39)]):        # Tue 12:00 to Wed 15:00, Thu 12:00 to Fri 15:00 (UK)
        return None
    o = _ovr(cid)
    if o < 84 or not (5000 <= x["now"] <= 60000) or x["ch24h"] is None:
        return None
    if 0.03 <= x["ch24h"] <= 0.15 and (x["ch2h"] or 0) >= 0:
        return {"target": x["now"] * 1.10, "hold": "until just after the pack drop", "hold_h": 36,
                "why": f"{o}-rated card up {x['ch24h']:.0%} the day before a pack drop, often a sign people expect an upgrade or demand"}


def scout_promodip(cid, x, mood):
    """Promo Dip: buy quality cards that fell hard when TOTW or promo packs dropped; they usually recover in a day or two."""
    if not _window([(2, 18, 32), (4, 18, 32)]):        # Wed 18:00 to Thu 08:00, Fri 18:00 to Sat 08:00 (UK)
        return None
    o = _ovr(cid)
    if o < 82 or not (5000 <= x["now"] <= 80000) or x["ch6h"] is None:
        return None
    p6 = _ago(x, 6)
    if p6 and x["ch6h"] <= -0.06 and (x["ch1h"] or 0) >= -0.01:
        return {"target": p6 * 0.97, "hold": "1-2 days", "hold_h": 48,
                "why": f"dropped {abs(x['ch6h']):.0%} since the pack drop and has stopped falling; prices usually recover within a day or two"}


def scout_wl(cid, x, mood):
    """Weekend League Meta: buy strong cards in Thursday's rewards dip, sell into Friday's Weekend League demand."""
    if not _window([(3, 6, 14)]):                       # Thursday 06:00-14:00 UK
        return None
    o = _ovr(cid)
    if o < 85 or not (8000 <= x["now"] <= 50000):
        return None
    p12 = _ago(x, 12)
    if p12 and x["now"] / p12 - 1 <= -0.04 and (x["ch1h"] or 0) >= -0.01:
        return {"target": p12 * 0.99, "hold": "until Friday evening", "hold_h": 36,
                "why": f"{o}-rated card down {1 - x['now'] / p12:.0%} in Thursday's rewards dip; Weekend League demand usually lifts it by Friday"}


def scout_sunday(cid, x, mood):
    """Sunday Night Dip: buy strong cards after Weekend League ends, when prices are at their weekly low."""
    if not _window([(6, 20, 38)]):                      # Sunday 20:00 to Monday 14:00 UK
        return None
    o = _ovr(cid)
    if o < 84 or not (5000 <= x["now"] <= 60000) or x["ch24h"] is None:
        return None
    if x["ch24h"] <= -0.05 and (x["ch2h"] or 0) >= -0.01:
        base = _ago(x, 48) or x["p24h"]
        return {"target": base * 0.97, "hold": "2-3 days", "hold_h": 60,
                "why": f"down {abs(x['ch24h']):.0%} as Weekend League ends; prices usually climb back through the week"}


def scout_overnight(cid, x, mood):
    """Gold Overnight (from the videos): meta golds dip 1-4am UK while players are asleep and recover by the evening."""
    if not _window([(d, 0, 5) for d in range(7)]):
        return None
    o = _ovr(cid)
    if o < 82 or not (2000 <= x["now"] <= 60000) or x.get("moves24", 0) < 6:
        return None
    _, day = x["_m"].window("mid", cid, CTX["now"] - 86400, CTX["now"])
    if len(day) < 30:
        return None
    hi, med = max(day), statistics.median(day)
    if x["now"] <= med * 0.93 and (x["ch1h"] or 0) >= -0.01:
        return {"target": min(hi, med * 1.12) * 0.98, "hold": "until this evening's peak", "hold_h": 20,
                "why": f"{o}-rated card {1 - x['now'] / med:.0%} below its usual daily price in the overnight lull; it normally recovers when players log back on"}


def scout_iconflip(cid, x, mood):
    """Icon & Hero Fluctuation (from the videos): buy icons and heroes after a 6-12 hour slide, evenings and overnight."""
    if not _window([(d, 17, 30) for d in range(7)]):     # 5pm to 6am UK
        return None
    r = _rname(cid)
    if "icon" not in r and "hero" not in r or not (10000 <= x["now"] <= 50000):
        return None
    p12 = _ago(x, 12)
    if p12 and x["now"] / p12 - 1 <= -0.08 and (x["ch1h"] or 0) >= -0.005:
        return {"target": p12 * 0.98, "hold": "1-2 days", "hold_h": 48,
                "why": f"{_ovr(cid)}-rated {'icon' if 'icon' in r else 'hero'} down {1 - x['now'] / p12:.0%} in 12 hours and has stopped sliding"}


def scout_flood(cid, x, mood):
    """Reward Flood (closest testable version of mass bidding): cheap meta cards that crash when rewards or promo packs hit the market."""
    if not _window([(3, 9.5, 13), (4, 18.5, 22)]):       # Thu 9:30am-1pm, Fri 6:30-10pm UK
        return None
    o = _ovr(cid)
    if not (75 <= o <= 84) or not (1000 <= x["now"] <= 15000) or x["ch2h"] is None:
        return None
    p3 = _ago(x, 3)
    if p3 and x["now"] / p3 - 1 <= -0.12 and (x["ch30m"] or 0) >= -0.01:
        return {"target": p3 * 0.97, "hold": "1-2 days", "hold_h": 36,
                "why": f"down {1 - x['now'] / p3:.0%} since the latest reward or pack flood hit the market; flooded cards usually bounce back"}


def scout_fod(cid, x, mood):
    """FOD Investor (from the videos): 84-88 special cards at their weekly low, held while supply dries up."""
    r = _rname(cid)
    if not r or r in ("rare", "common") or "icon" in r or "hero" in r:
        return None
    o = _ovr(cid)
    if not (84 <= o <= 88) or not (800 <= x["now"] <= 9000) or not x["med7"] or not x["lo7"] or x["hours"] < 48:
        return None
    if x["now"] <= x["lo7"] * 1.03 and x["now"] <= x["med7"] * 0.92 and (x["ch2h"] or 0) >= 0:
        return {"target": x["med7"] * 0.99, "hold": "up to 3 days", "hold_h": 72,
                "why": f"{o}-rated special card at its weekly low, {1 - x['now'] / x['med7']:.0%} under its usual price"}


def scout_silver(cid, x, mood):
    """Silver Thursday Rebuy (from the videos): silvers crash on midweek content; buy them back Thursday evening."""
    if not _window([(3, 17, 24)]):                       # Thursday 5pm to midnight UK
        return None
    o = _ovr(cid)
    if not (65 <= o <= 74) or not (500 <= x["now"] <= 8000):
        return None
    p30 = _ago(x, 30)
    if p30 and x["now"] <= p30 * 0.88 and (x["ch1h"] or 0) >= -0.01:
        return {"target": p30 * 0.97, "hold": "sell before next Wednesday's content", "hold_h": 120,
                "why": f"silver down {1 - x['now'] / p30:.0%} since midweek content; sell back before next Wednesday's drop"}


SCOUTS = [
    {"key": "daily", "name": "Daily Swing", "focus": "5k-30k cards near today's low that bounced back on 2 of the last 3 days", "fn": scout_daily},
    {"key": "dip", "name": "Dip Hunter", "focus": "Cards trading well below their usual weekly price", "fn": scout_dip},
    {"key": "crash", "name": "Crash Buyer", "focus": "Quality cards hit hardest on market-wide crash days", "fn": scout_crash},
    {"key": "momentum", "name": "Momentum Rider", "focus": "Cards on a steady climb that hasn't stalled", "fn": scout_momentum},
    {"key": "fodder", "name": "Fodder Scout", "focus": "Cheap cards (1k-30k) where SBC demand starts", "fn": scout_fodder},
    {"key": "rebound", "name": "Rebound Spotter", "focus": "Big fallers that have started bouncing", "fn": scout_rebound},
    {"key": "sbc", "name": "SBC Sniper", "focus": "Fodder a new SBC needs, bought before its price catches up", "fn": scout_sbc},
    {"key": "prebuy", "name": "Promo Pre-buy", "focus": "84+ cards being bid up the day before TOTW or promo packs", "fn": scout_prebuy},
    {"key": "promodip", "name": "Promo Dip", "focus": "82+ cards that fell when packs dropped (Wed and Fri evenings)", "fn": scout_promodip},
    {"key": "wl", "name": "Weekend League Meta", "focus": "85+ cards in Thursday's rewards dip, sold into Friday demand", "fn": scout_wl},
    {"key": "sunday", "name": "Sunday Night Dip", "focus": "84+ cards at their weekly low after Weekend League ends", "fn": scout_sunday},
    {"key": "overnight", "name": "Gold Overnight", "focus": "82+ golds in the 1-4am UK lull, sold at the evening peak (from your videos)", "fn": scout_overnight},
    {"key": "iconflip", "name": "Icon & Hero Flip", "focus": "Icons and heroes up to 50k after a 6-12 hour slide (from your videos)", "fn": scout_iconflip},
    {"key": "flood", "name": "Reward Flood", "focus": "75-84 cards crashed by rewards or promo packs; the testable side of mass bidding (from your videos)", "fn": scout_flood},
    {"key": "fod", "name": "FOD Investor", "focus": "84-88 special cards at their weekly low (from your videos)", "fn": scout_fod},
    {"key": "silver", "name": "Silver Thursday Rebuy", "focus": "Silvers that crashed on midweek content, bought back Thursday evening (from your videos)", "fn": scout_silver},
]
SCOUT_NAMES = {s["key"]: s["name"] for s in SCOUTS}


# ---------------------------------------------------------------- director --
def ea_event(ts):
    """EA's weekly rhythm (UK time). Returns a reason to wait, or None."""
    t = london(ts)
    wd, h = t.weekday(), t.hour + t.minute / 60
    if wd == 4 and 15 <= h < 18.5:
        return "New promo packs usually drop Friday at 6pm UK time (9pm UAE) and prices often dip then, so it's waiting until after"
    if wd == 2 and 15 <= h < 18.5:
        return "Team of the Week packs usually drop Wednesday at 6pm UK time (9pm UAE) and prices often dip then, so it's waiting until after"
    if wd == 3 and 7.5 <= h < 10:
        return "Weekly rewards usually land Thursday morning UK time and flood the market, so it's waiting until prices settle"
    return None


def london(ts):
    try:
        from zoneinfo import ZoneInfo
        return datetime.fromtimestamp(ts, ZoneInfo("Europe/London"))
    except Exception:
        return datetime.fromtimestamp(ts, timezone.utc)


def next_events(ts):
    """The next few market events, as (name, unix time, note)."""
    base = london(ts)
    plan = [(2, 18, "Team of the Week", "new TOTW in packs; fodder often dips"),
            (3, 9, "Weekly rewards", "Rivals rewards flood the market; prices dip"),
            (4, 18, "Promo drop", "new promo packs; the biggest dip of the week, then demand")]
    out = []
    for wd, hr, name, note in plan:
        d = base.replace(hour=hr, minute=0, second=0, microsecond=0) + timedelta(days=(wd - base.weekday()) % 7)
        if d.timestamp() <= ts:
            d += timedelta(days=7)
        out.append({"name": name, "at": int(d.timestamp()), "note": note})
    return sorted(out, key=lambda e: e["at"])


def director(cid, x, flags, cfg, held_ids, allowance, mood=None, event=None):
    """Decide BUY / WATCH / REJECT for one card the scouts flagged."""
    buy = round_down(x["now"])
    target = round_down(sum(f["target"] for f in flags) / len(flags))
    net = after_tax(target) - buy
    roi = net / buy if buy else 0
    reasons, risks = [], []
    qty = min(cfg["max_copies"], int(allowance // buy)) if buy else 0
    total = net * qty

    def no(why):
        return "REJECT", [why], buy, target, net, roi, 0, max(qty, 1)
    if x["status"]:
        return no("FUT.GG marks this price as unreliable")
    if x.get("glitch"):
        return no("This price looks like a one-off bad reading, so it's ignored until the next check")
    if cid in CTX["twins"]:
        lo = CTX["twins"][cid]
        return no(f"This version's price looks wrong: an identical card trades for about {lo:,}, so it's ignored")
    if cid in held_ids:
        return no("You already hold this card")
    if qty < 1:
        return no(f"Costs more than the {int(allowance):,} coins you have left to spend today")
    if roi < cfg["min_roi"]:
        return no(f"Only {roi:.1%} profit after EA tax, below your {cfg['min_roi']:.0%} minimum")
    if total < cfg["min_profit"]:
        return no(f"Only {total:,} coins profit after tax on {qty} cop{'y' if qty == 1 else 'ies'}, "
                  f"below your {cfg['min_profit']:,} minimum")
    if x["ch30m"] is not None and x["ch30m"] < -0.04:
        return no("Price is still dropping fast; buying now risks catching a falling card")
    if x["fine_pts"] < 20 and x["hours"] < 3:
        return "WATCH", ["Not enough price history recorded yet"], buy, target, net, roi, 0, qty
    if x.get("pts24", 0) >= 40 and x.get("moves24", 99) < 3:
        return no("Its price has barely moved today, so hardly anyone is trading it and it could be slow to sell")
    keys = {f.get("key") for f in flags}
    contrarian = keys <= {"crash", "rebound", "promodip", "wl", "sunday", "overnight", "iconflip", "flood", "fod", "silver"}   # built for dips
    mk = (mood or {}).get("ch24h")
    if mk is not None and not contrarian:
        if mk <= -0.08:
            return "WATCH", [f"The whole market is down {abs(mk):.0%} today, so it's waiting for things to settle"], buy, target, net, roi, 0, qty
        if mk <= -0.03 and roi < cfg["min_roi"] + 0.03:
            return "WATCH", [f"The market is down {abs(mk):.0%} today, so it wants at least {cfg['min_roi'] + 0.03:.0%} profit"], buy, target, net, roi, 0, qty
    if event and not contrarian:
        return "WATCH", [event], buy, target, net, roi, 0, qty

    score = roi * 100
    if len(flags) > 1:
        score *= 1 + 0.25 * (len(flags) - 1)
        reasons.append(f"{len(flags)} scouts agree")
    if x["hours"] < 24:
        score *= 0.75
        risks.append("less than a day of history")
    if x["vol"] is not None and x["vol"] > 0.06:
        score *= 0.7
        risks.append("price swings a lot hour to hour")
    # Momentum picks aim above recent highs on purpose, so only judge other picks by the week's high,
    # and only once there are 3 days of hourly prices to make that high meaningful.
    climbers = all(f.get("key") in ("momentum", "fodder", "sbc", "prebuy") for f in flags)
    if x["hi7"] and target > x["hi7"] and x["hours"] >= 72 and not climbers:
        score *= 0.6
        risks.append("target is above this week's high")
    if x["ch24h"] is not None and x["ch24h"] > 0.25:
        score *= 0.7
        risks.append("already up a lot today")

    decision = "BUY" if score >= 8 else "WATCH"
    if decision == "WATCH":
        reasons.append("profit is possible but the case isn't strong enough yet")
    return decision, reasons + [f"Risk: {r}" for r in risks], buy, target, net, roi, round(score, 1), qty


def exit_check(buy, target, opened, now_price, now_ts, cfg):
    """Daily-trade exit rules shared by paper trades and your real cards.
    Returns (action, price, reason); action is SELL, CUT or HOLD."""
    hours = (now_ts - opened) / 3600
    if target and now_price >= target:
        return "SELL", target, "Target price reached"
    if now_price <= buy * (1 - cfg["stop_loss"]) and buy - now_price >= 2 * step(buy):   # one price step is just noise
        return "CUT", now_price, f"Down {cfg['stop_loss']:.0%}: stop-loss"
    if hours >= cfg["max_hold_hours"]:
        if now_price >= break_even(buy):
            return "SELL", now_price, f"Held {hours:.0f} hours: sell at break-even or better"
        return "CUT", now_price, f"Held {hours:.0f} hours without recovering: sell and move on"
    return "HOLD", None, f"Needs {break_even(buy):,} to break even" if now_price < break_even(buy) else "In profit; waiting for the target"



# ------------------------------------------------------------------ engine --
def load_json(name, default):
    try:
        with open(os.path.join(DATA_DIR, name)) as f:
            return json.load(f)
    except Exception:
        return default


def save_json(name, data, pretty=False):
    path = os.path.join(DATA_DIR, name)
    with open(path + ".tmp", "w") as f:
        json.dump(data, f, separators=(",", ":"))
    os.replace(path + ".tmp", path)


def load_config():
    try:
        with open("config.json") as f:
            return json.load(f)
    except Exception:
        return {}


def vkey(key, tag):
    return f"{key}:{tag}" if tag else key


def scaled(flags, now, k):
    return [{**f, "target": now + (f["target"] - now) * k} for f in flags]


def ntfy_post(topic, body, title=None, tags=None, click=None, priority=None):
    if not topic or SIM:
        return False
    headers = {"User-Agent": UA}
    if title:
        headers["Title"] = title.encode("utf-8").decode("latin-1", "replace")
    if tags:
        headers["Tags"] = tags
    if click:
        headers["Click"] = click
    if priority:
        headers["Priority"] = str(priority)
    try:
        req = urllib.request.Request(f"https://ntfy.sh/{topic}", data=body.encode("utf-8"), headers=headers, method="POST")
        urllib.request.urlopen(req, timeout=15, context=ssl_ctx()).read()
        return True
    except Exception as e:
        log("Phone alert failed:", e)
        return False


class Engine:
    def __init__(self):
        os.makedirs(DATA_DIR, exist_ok=True)
        self.cfg = dict(DEFAULTS)
        self.cfg.update(load_json("settings.json", {}))
        self.conf = load_config()
        self.market = Market()
        self.meta = load_json("cards.json", {})
        self.paper = load_json("paper.json", {"open": [], "closed": [], "first": {}})
        self.crawl = load_json("catalog_state.json", {"page": 1})
        self.alerts = load_json("alerts.json", {"sent": {}, "brief": "", "status": {}})
        self.mood_hist = load_json("mood.json", [])
        self.sbcs = []
        self.holdings = []
        self.sync_seen = None
        self.ids = []
        self.rarities = load_json("rarities.json", {})
        self.status = {"state": "live", "message": "Live"}
        try:
            self.market.load(os.path.join(DATA_DIR, "history.pkl.gz"))
        except FileNotFoundError:
            pass
        except Exception as e:
            log("Could not read price history, starting fresh:", e)

    # ---------------------------------------------------------- reading data
    def fetch(self):
        man = get_json(R2 + "manifest.json")
        ph, ih = man[f"player-prices-{PLATFORM}-dyn"], man["player-prices-index"]
        ts = man.get("_published_at", {}).get(f"player-prices-{PLATFORM}-dyn") or time.time()
        if self.market.fine_ts and ts <= self.market.fine_ts[-1]:
            log("No new prices since the last run")
            return False
        idx = get_json(f"{R2}player-prices-index.v1.{ih}.json")
        ids = [idx["id0"]]
        for d in idx["d"]:
            ids.append(ids[-1] + d)
        pr = get_json(f"{R2}player-prices-{PLATFORM}-dyn.v1.{ph}.json")
        if len(pr["p"]) != len(ids):
            raise ValueError("FUT.GG's price file and card list don't match yet")
        st = pr.get("s") or [0] * len(ids)
        lo, hi = UNIVERSE
        tracked = self.market.data["fine"]
        keep = [(c, p, s) for c, p, s in zip(ids, pr["p"], st) if c in tracked or lo <= p <= hi]
        self.market.ingest(ts, [k[0] for k in keep], [k[1] for k in keep], [k[2] for k in keep])
        if not self.rarities or self.rarities.get("_v") != man.get("fc-core-data"):
            try:
                core = get_json(f"{R2}fc-core-data.v1.{man['fc-core-data']}.json")
                self.rarities = {str(r["eaId"]): r["name"] for r in core.get("rarities", [])}
                self.rarities["_v"] = man.get("fc-core-data")
                save_json("rarities.json", self.rarities)
            except Exception as e:
                log("Could not load card types:", e)
        log(f"Read {len(keep):,} card prices")
        return True

    def crawl_catalog(self, pages=12):
        """Read FUT.GG's player list a few pages per run, so every card gets a name and rating."""
        st = self.crawl
        if st.get("done_at") and time.time() - st["done_at"] < 86400:
            return
        page = st.get("page", 1)
        for _ in range(pages):
            try:
                d = get_json(f"{SITE}/api/fut/players/v2/{GAME}/?page={page}", timeout=20)
            except Exception as e:
                log("Player list page", page, "failed:", e)
                break
            for v in d.get("data", []):
                key = str(v.get("eaId"))
                m = self.meta.get(key) or {}
                m["name"] = v.get("commonName") or v.get("cardName") or m.get("name")
                m["ovr"] = v.get("overall") or m.get("ovr")
                m["rname"] = v.get("rarityName") or m.get("rname")
                m.pop("failed", None)
                self.meta[key] = m
            nxt = d.get("next")
            if not nxt or not d.get("data"):
                st.update(page=1, done_at=time.time())
                log("Player list complete:", len(self.meta), "cards named")
                break
            page = nxt
            st["page"] = page
            time.sleep(0.6)
        save_json("catalog_state.json", st)

    def lookup_names(self, cids, limit=30):
        done = 0
        for cid in cids:
            known = self.meta.get(str(cid))
            if done >= limit or (known and (known.get("name") or time.time() - known.get("failed", 0) < 12 * 3600)):
                continue
            try:
                data = get_json(f"{SITE}/api/fut/players/v2/all-versions/{base_id(cid)}/", timeout=15)
                for v in data.get("data", []):
                    if str(v.get("game")) != GAME:
                        continue
                    m = self.meta.get(str(v["eaId"])) or {}
                    m.update(name=v.get("nickname") or v.get("commonName") or
                             f"{v.get('firstName', '')} {v.get('lastName', '')}".strip(),
                             ovr=v.get("overall"), rarity=v.get("rarityEaId"),
                             pos=POSITIONS.get(v.get("position"), ""))
                    self.meta[str(v["eaId"])] = m
                self.meta.setdefault(str(cid), {"name": None, "failed": time.time()})
            except Exception as e:
                log("Name lookup failed for", cid, "-", e)
                self.meta.setdefault(str(cid), {"name": None, "failed": time.time()})
                if done == 0 and isinstance(e, urllib.error.HTTPError) and e.code in (401, 403, 429):
                    break
            done += 1
            time.sleep(0.8)

    def fetch_sbcs(self):
        try:
            d = get_json(f"{SITE}/api/fut/sbc/{GAME}/", timeout=20)
        except Exception as e:
            log("SBC list failed:", e)
            return
        out = []
        for v in d.get("data", []):
            out.append({"name": v.get("name"), "desc": v.get("description"), "cost": v.get("cost"),
                        "ends": v.get("endTime"), "created": v.get("createdAt"), "new": bool(v.get("isNew")),
                        "repeat": bool(v.get("isRepeatable")), "url": SITE + (v.get("url") or "/sbc/")})
        out.sort(key=lambda v: v.get("created") or "", reverse=True)
        self.sbcs = out[:30]

    def read_holdings(self):
        """Your cards, as the website last shared them (so alerts can tell you when to sell)."""
        topic = self.conf.get("sync_topic")
        if not topic or SIM:
            return
        try:
            req = urllib.request.Request(f"https://ntfy.sh/{topic}/json?poll=1&since=12h", headers={"User-Agent": UA})
            lines = urllib.request.urlopen(req, timeout=15, context=ssl_ctx()).read().decode().splitlines()
            msgs = [json.loads(l) for l in lines if l.strip()]
            msgs = [m for m in msgs if m.get("event") == "message"]
            if not msgs:
                return
            last = msgs[-1]
            body = json.loads(last["message"])
            self.holdings = [{"id": h[0], "card_id": int(h[1]), "qty": int(h[2]), "buy": int(h[3]),
                              "target": int(h[4]) if h[4] else None, "bought_at": float(h[5]),
                              "hold_h": int(h[6]) if len(h) > 6 and h[6] else None}
                             for h in body.get("h", [])]
            # ntfy keeps messages 12 hours; re-share them before they expire
            if time.time() - last.get("time", 0) > 8 * 3600:
                ntfy_post(topic, last["message"])
        except Exception as e:
            log("Could not read your cards from the website:", e)

    def card_info(self, cid):
        m = self.meta.get(str(cid)) or {}
        r = m.get("rname") or (self.rarities.get(str(m.get("rarity")), "") if m.get("rarity") is not None else "")
        return {"id": cid, "url": card_url(cid), "name": m.get("name") or f"Card {cid}",
                "ovr": m.get("ovr"), "pos": m.get("pos") or "", "rarity": r}

    # --------------------------------------------------------------- grading
    def strategy_stats(self, now_ts):
        out = {}
        for s in SCOUTS:
            for tag, k, label in VARIANTS:
                key = vkey(s["key"], tag)
                closed = [t for t in self.paper["closed"] if t["scout"] == key and t["closed"] >= now_ts - 7 * 86400]
                n = len(closed)
                wins = sum(1 for t in closed if t["net"] > 0)
                net = sum(t["net"] for t in closed)
                invested = sum(t["buy"] for t in closed)
                first = self.paper["first"].get(key)
                days = (now_ts - first) / 86400 if first else 0
                wr = wins / n if n else None
                if n >= TRIAL_MIN_TRADES and days >= TRIAL_DAYS:
                    status = "LIVE" if wr >= TRIAL_MIN_WINRATE and net > 0 else "OFF"
                elif n >= FAST_MIN_TRADES and days >= FAST_DAYS and wr >= FAST_MIN_WINRATE and net > 0:
                    status = "LIVE"
                else:
                    status = "TRIAL"
                out[key] = {"key": key, "base": s["key"], "variant": label, "k": k, "name": s["name"],
                            "focus": s["focus"], "status": status, "trades": n, "wins": wins, "winrate": wr,
                            "net": net, "roi": net / invested if invested else None, "days": round(days, 1),
                            "open": sum(1 for t in self.paper["open"] if t["scout"] == key)}
        return out

    def paper_step(self, feats, picks, now_ts):
        p, still = self.paper, []
        for t in p["open"]:
            x = feats.get(t["card"])
            if not x:
                still.append(t)
                continue
            now = x["now"]
            if x.get("glitch"):                              # wait for a real price before acting
                still.append(t)
                continue
            if t["target"] and now >= t["target"]:          # the 1-day listing sells, even while you're away
                act, price, why = "SELL", t["target"], "Listing sold at the target price"
            elif now_ts - t.get("last_check", t["opened"]) >= self.cfg["checkin_hours"] * 3600:
                t["last_check"] = now_ts                     # one of your check-ins
                rules = {**self.cfg, "max_hold_hours": t.get("hold_h", self.cfg["max_hold_hours"])}
                act, price, why = exit_check(t["buy"], t["target"], t["opened"], now, now_ts, rules)
            else:
                act = "HOLD"
            if act == "HOLD":
                still.append(t)
            else:
                p["closed"].append({**t, "sold": int(price), "closed": now_ts, "reason": why,
                                    "net": after_tax(price) - t["buy"]})
        p["open"] = still
        have = {(t["scout"], t["card"]) for t in p["open"]}
        per = {}
        for t in p["open"]:
            per[t["scout"]] = per.get(t["scout"], 0) + 1
        for key, cid, price, target, hold_h in picks:
            if (key, cid) in have or per.get(key, 0) >= 25:
                continue
            p["open"].append({"id": uuid.uuid4().hex[:10], "scout": key, "card": cid, "buy": int(price),
                              "target": int(target), "opened": now_ts, "last_check": now_ts,
                              **({"hold_h": hold_h} if hold_h else {})})
            p["first"].setdefault(key, now_ts)
            per[key] = per.get(key, 0) + 1
            have.add((key, cid))
        p["closed"] = [t for t in p["closed"] if t["closed"] >= now_ts - 30 * 86400][-4000:]

    # ------------------------------------------------------------------- run
    def run(self, fetched=True):
        m = self.market
        now_ts = m.fine_ts[-1] if m.fine_ts else time.time()
        feats = {cid: x for cid in m.fine if (x := features(m, cid))}
        mood = market_mood(m, feats)
        event = ea_event(time.time())
        stats = self.strategy_stats(now_ts)
        allowance = self.cfg["daily_limit"]
        held_ids = {h["card_id"] for h in self.holdings}

        # 0. context for the timed and SBC scouts
        CTX.update(now=time.time(), meta=self.meta, demand={}, cheap={}, twins={})
        # identical cards (same name, rating and type) where one version is priced far above the one people trade:
        # FUT.GG's price for the rarely traded version is usually a single odd listing, not a real market price
        same = {}
        for c, x in feats.items():
            mt = self.meta.get(str(c)) or {}
            if mt.get("name") and mt.get("ovr"):
                same.setdefault((mt["name"], mt["ovr"], mt.get("rname") or mt.get("rarity")), []).append((x["now"], c))
        for lst in same.values():
            if len(lst) > 1:
                lo = min(p for p, _ in lst)
                for p, c in lst:
                    if lo and p >= 2 * lo:
                        CTX["twins"][c] = lo
        before = (len(self.paper["open"]), len(self.paper["closed"]))
        self.paper["open"] = [t for t in self.paper["open"] if t["card"] not in CTX["twins"]]
        self.paper["closed"] = [t for t in self.paper["closed"] if t["card"] not in CTX["twins"]]
        voided = before[0] - len(self.paper["open"]) + before[1] - len(self.paper["closed"])
        if voided:
            self.paper["voided"] = self.paper.get("voided", 0) + voided
            log(f"Removed {voided} paper trades on cards with fake prices")
        stats = self.strategy_stats(now_ts)
        recent = [v for v in self.sbcs if v.get("created")]
        try:
            CTX["sbc_new"] = any(time.time() - datetime.fromisoformat(v["created"].replace("Z", "+00:00")).timestamp() < 48 * 3600 for v in recent)
        except Exception:
            CTX["sbc_new"] = any(v.get("new") for v in self.sbcs)
        groups = {}
        for c, x in feats.items():
            mt = self.meta.get(str(c)) or {}
            if 75 <= (mt.get("ovr") or 0) <= 91 and (mt.get("rname") or "") in ("Rare", "Common") and not x["status"]:
                groups.setdefault(mt["ovr"], []).append((x["now"], c, x["ch6h"]))
        for o, lst in groups.items():
            lst.sort()
            cheap = lst[:15]
            ch = [c6 for _, _, c6 in cheap if c6 is not None]
            if len(ch) >= 5:
                CTX["demand"][o] = statistics.median(ch)
            CTX["cheap"][o] = {c for _, c, _ in cheap}

        # 1. scouts flag cards
        flagged, counts = {}, {s["key"]: 0 for s in SCOUTS}
        for cid, x in feats.items():
            if cid in CTX["twins"]:
                continue
            for s in SCOUTS:
                r = s["fn"](cid, x, mood)
                if r:
                    r["scout"], r["key"] = s["name"], s["key"]
                    flagged.setdefault(cid, []).append(r)
                    counts[s["key"]] += 1

        # 2. the director decides; every strategy version is paper-tested on its own calls
        out = {"BUY": [], "WATCH": [], "REJECT": []}
        picks = []
        for cid, flags in flagged.items():
            x = feats[cid]
            vstats = [stats[vkey(f["key"], tag)] for f in flags for tag, _, _ in VARIANTS]
            live = sorted([v for v in vstats if v["status"] == "LIVE"], key=lambda v: -v["net"])
            k = live[0]["k"] if live else 1.0
            dec, notes, buy, target, net, roi, score, qty = director(cid, x, scaled(flags, x["now"], k), self.cfg,
                                                                     held_ids, allowance, mood, event)
            if dec == "BUY" and all(v["status"] == "OFF" for v in vstats):
                dec, notes = "REJECT", ["Its strategy is switched off: it lost coins in paper trading"]
            out[dec].append({"card": cid, "notes": notes, "buy": buy, "target": target, "net": net,
                             "roi": round(roi, 4), "score": score, "live": bool(live),
                             "strategy": (f"{live[0]['name']} · {live[0]['variant']}" if live else None),
                             "scouts": [f["scout"] for f in flags], "why": [f["why"] for f in flags],
                             "hold": flags[0]["hold"], "hold_h": max((f.get("hold_h") or 0) for f in flags) or None,
                             "now": x["now"], "ch24h": x["ch24h"]})
            for f in flags:
                for tag, kk, _ in VARIANTS:
                    d1 = director(cid, x, scaled([f], x["now"], kk), self.cfg, set(), allowance, mood, event)
                    if d1[0] == "BUY":
                        picks.append((vkey(f["key"], tag), cid, x["now"], d1[3], f.get("hold_h")))
        out["BUY"].sort(key=lambda r: (not r["live"], -r["score"]))
        out["WATCH"].sort(key=lambda r: -r["score"])
        out["REJECT"].sort(key=lambda r: -r["roi"])
        out = {"BUY": out["BUY"][:60], "WATCH": out["WATCH"][:30], "REJECT": out["REJECT"][:40]}

        # 3. paper trades
        if fetched:
            self.paper_step(feats, picks, now_ts)
            stats = self.strategy_stats(now_ts)

        # 4. names for everything the website will show
        need = ([r["card"] for k2 in ("BUY", "WATCH") for r in out[k2]] + [t["card"] for t in self.paper["open"]]
                + list(held_ids))
        if not SIM:
            self.lookup_names(list(dict.fromkeys(need)))
            self.crawl_catalog()

        # 5. extras for the website
        if mood.get("ch24h") is not None and (not self.mood_hist or now_ts - self.mood_hist[-1][0] >= 3000):
            self.mood_hist.append([int(now_ts), round(mood["ch24h"], 4)])
            self.mood_hist = [r for r in self.mood_hist if r[0] >= now_ts - 14 * 86400]
        chart_ids = list(dict.fromkeys([r["card"] for r in out["BUY"][:40]] + [r["card"] for r in out["WATCH"][:20]]
                                       + [t["card"] for t in self.paper["open"][:60]] + list(held_ids)))
        state = {
            "updated": now_ts, "generated": time.time(), "status": self.status,
            "platform": PLATFORM.upper(), "hours": round(m.history_hours(), 1), "cards": len(feats),
            "mood": mood, "mood_hist": self.mood_hist, "event": event, "events": next_events(time.time()),
            "rules": {k2: self.cfg[k2] for k2 in ("min_roi", "min_profit", "daily_limit", "max_copies",
                                                  "stop_loss", "max_hold_hours", "checkin_hours")},
            "trial": {"days": TRIAL_DAYS, "min_trades": TRIAL_MIN_TRADES, "min_winrate": TRIAL_MIN_WINRATE,
                      "fast_days": FAST_DAYS, "fast_trades": FAST_MIN_TRADES, "fast_winrate": FAST_MIN_WINRATE},
            "scouts": [{**stats[vkey(s["key"], tag)], "flagged": counts[s["key"]]} for s in SCOUTS for tag, _, _ in VARIANTS],
            "buy": self.rows(out["BUY"]), "watch": self.rows(out["WATCH"]), "reject": self.rows(out["REJECT"]),
            "paper_open": self.paper_rows(sorted(self.paper["open"], key=lambda t: -t["opened"])[:100], feats, stats),
            "paper_closed": self.paper_rows(self.paper["closed"][-120:][::-1], feats, stats),
            "charts": {str(c): self.chart(c) for c in chart_ids if c in feats},
            "fodder": self.fodder(feats), "movers": self.movers(feats), "sbcs": self.sbcs,
            "synced": len(self.holdings), "fake_prices": len(CTX["twins"]), "voided": self.paper.get("voided", 0), "alerts_topic": self.conf.get("alerts_topic"),
            "prices": {str(c): x["now"] for c, x in feats.items()},
        }
        market = {"t": now_ts, "c": {str(c): [self.meta.get(str(c), {}).get("name") or "",
                                              self.meta.get(str(c), {}).get("ovr") or 0,
                                              self.card_info(c)["rarity"], x["now"],
                                              round(x["ch24h"] * 1000) if x["ch24h"] is not None else None,
                                              x["lo7"], x["hi7"]] for c, x in feats.items() if c not in CTX["twins"]}}
        self.send_alerts(state, feats, now_ts)
        return state, market

    def rows(self, rows):
        return [{**r, **self.card_info(r["card"])} for r in rows]

    def paper_rows(self, rows, feats, stats):
        res = []
        for t in rows:
            info = self.card_info(t["card"])
            st = stats.get(t["scout"], {})
            v = {**t, "name": info["name"], "url": info["url"], "ovr": info["ovr"],
                 "strategy": f"{st.get('name', t['scout'])}" + (f" · {st['variant']}" if st.get("k", 1) != 1 else "")}
            if "sold" not in t:
                x = feats.get(t["card"])
                v["now"], v["pl"] = (x["now"], after_tax(x["now"]) - t["buy"]) if x else (None, None)
            res.append(v)
        return res

    def chart(self, cid):
        m = self.market
        mid = m.data["mid"].get(cid, array("I"))
        hr = m.data["hourly"].get(cid, array("I"))
        return {"m": list(mid[-288:]), "h": list(hr[-168:])}

    def fodder(self, feats):
        best = {}
        for c, x in feats.items():
            mt = self.meta.get(str(c)) or {}
            ovr, r = mt.get("ovr"), (mt.get("rname") or "")
            if not ovr or not (75 <= ovr <= 91) or r not in ("Rare", "Common") or x["status"] or c in CTX["twins"]:
                continue
            cur = best.get(ovr)
            if not cur or x["now"] < cur["price"]:
                best[ovr] = {"ovr": ovr, "price": x["now"], "prev": x["p24h"] or None, "name": mt.get("name"),
                             "card": c, "rarity": r}
        return [best[k] for k in sorted(best, reverse=True)]

    def movers(self, feats):
        pool = [(c, x) for c, x in feats.items() if 2000 <= x["now"] <= 200000 and x["ch24h"] is not None
                and not x["status"] and c not in CTX["twins"] and (self.meta.get(str(c)) or {}).get("name") and x.get("moves24", 0) >= 3]
        pool.sort(key=lambda cx: cx[1]["ch24h"])

        def row(c, x):
            return {**self.card_info(c), "now": x["now"], "ch24h": round(x["ch24h"], 4)}
        return {"up": [row(c, x) for c, x in pool[::-1][:10]], "down": [row(c, x) for c, x in pool[:10]]}

    # ---------------------------------------------------------------- Jarvis
    def send_alerts(self, state, feats, now_ts):
        topic = self.conf.get("alerts_topic")
        if not topic:
            return
        sent = self.alerts.setdefault("sent", {})
        cutoff = time.time() - 3 * 86400
        for k2 in [k2 for k2, t in sent.items() if t < cutoff]:
            del sent[k2]
        # new proven picks
        for r in [r for r in state["buy"] if r["live"]][:5]:
            key = f"buy:{r['card']}"
            if key in sent and time.time() - sent[key] < 12 * 3600:
                continue
            qty = max(1, min(self.cfg["max_copies"], int(self.cfg["daily_limit"] // r["buy"])))
            if ntfy_post(topic, f"Bid up to {r['buy']:,}, then list at {r['target']:,} for 1 day. "
                                f"About +{r['net']:,} each after tax ({r['roi']:.0%}). Up to {qty} copies, within today's limit.",
                         title=f"Buy: {r['name']}" + (f" {r['ovr']}" if r.get('ovr') else ""),
                         tags="moneybag", click=SITE_URL):
                sent[key] = time.time()
        # your cards
        for h in self.holdings:
            x = feats.get(h["card_id"])
            if not x or x.get("glitch"):
                continue
            rules = {**self.cfg, "max_hold_hours": h.get("hold_h") or self.cfg["max_hold_hours"]}
            act, price, why = exit_check(h["buy"], h["target"], h["bought_at"], x["now"], now_ts, rules)
            if act == "HOLD":
                continue
            key = f"{act}:{h['id']}"
            if key in sent:
                continue
            name = self.card_info(h["card_id"])["name"]
            verb = "Sell" if act == "SELL" else "Cut your loss on"
            if ntfy_post(topic, f"{why}. Now {x['now']:,}, you paid {h['buy']:,}. "
                                f"Profit after tax: {(after_tax(x['now']) - h['buy']) * h['qty']:+,}.",
                         title=f"{verb} {name}", tags="rotating_light" if act == "CUT" else "white_check_mark",
                         click=SITE_URL, priority=4):
                sent[key] = time.time()
        # strategies switching on or off
        prev = self.alerts.setdefault("status", {})
        for s in state["scouts"]:
            old = prev.get(s["key"])
            if old == "LIVE" and s["status"] == "TRIAL":
                ntfy_post(topic, "Its record changed after a data correction, so it's back on trial. Don't buy its picks until it passes again.",
                          title=f"{s['name']}{'' if s['k'] == 1 else ' (' + s['variant'] + ')'} is back on trial", tags="warning", click=SITE_URL)
            if old and old != s["status"] and s["status"] in ("LIVE", "OFF"):
                label = s["name"] + ("" if s["k"] == 1 else f" ({s['variant']})")
                msg = (f"Passed its test: {s['trades']} paper trades, {round((s['winrate'] or 0) * 100)}% wins, {s['net']:+,} coins."
                       if s["status"] == "LIVE" else f"Switched off after losing in paper trading ({s['net']:+,} coins).")
                ntfy_post(topic, msg, title=f"{label} is {'LIVE' if s['status'] == 'LIVE' else 'OFF'}",
                          tags="trophy" if s["status"] == "LIVE" else "no_entry", click=SITE_URL)
            prev[s["key"]] = s["status"]
        # morning briefing, about 9am UAE (05:00 UTC)
        today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        if datetime.now(timezone.utc).hour >= 5 and self.alerts.get("brief") != today:
            live = [s for s in state["scouts"] if s["status"] == "LIVE"]
            best = [r for r in state["buy"] if r["live"]][:3]
            mk = state["mood"].get("ch24h")
            lines = [f"Market: {'no reading yet' if mk is None else f'{mk:+.1%} in 24h'}.",
                     f"Proven strategies: {len(live)}." + (" " + ", ".join(s["name"] + ("" if s["k"] == 1 else f" ({s['variant']})") for s in live[:4]) if live else " Still testing; don't buy yet."),
                     ("Top picks: " + "; ".join(f"{r['name']} at {r['buy']:,} -> {r['target']:,}" for r in best)) if best else "No proven picks right now."]
            nxt = state["events"][0] if state["events"] else None
            if nxt:
                lines.append(f"Next: {nxt['name']} ({nxt['note']}).")
            if ntfy_post(topic, "\n".join(lines), title="Jarvis morning briefing", tags="sunrise", click=SITE_URL):
                self.alerts["brief"] = today

    def save(self, state, market):
        save_json("paper.json", self.paper)
        save_json("cards.json", self.meta)
        save_json("alerts.json", self.alerts)
        save_json("mood.json", self.mood_hist)
        save_json("state.json", state)
        save_json("market.json", market)
        self.market.save(os.path.join(DATA_DIR, "history.pkl.gz"))


def main():
    eng = Engine()
    fetched = False
    try:
        fetched = eng.fetch()
    except Exception as e:
        reason = getattr(e, "reason", None) or e
        eng.status = {"state": "error", "message": f"Couldn't read FUT.GG prices on the last run ({reason}). "
                                                    "The next run will try again."}
        traceback.print_exc()
    eng.read_holdings()
    if not SIM:
        eng.fetch_sbcs()                 # before the scouts, so SBC Sniper can see new SBCs
    state, market = eng.run(fetched)
    eng.save(state, market)
    log(f"Done: {len(state['buy'])} buys, {len(state['watch'])} watching, "
        f"{len(state['paper_open'])} open paper trades, {state['hours']} h of history, {len(eng.meta)} names")


if __name__ == "__main__":
    main()
