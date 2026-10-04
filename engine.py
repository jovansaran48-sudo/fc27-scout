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
    "max_hold_hours": 30,        # daily trades: sell by the next evening
    "watchlist": [],             # card ids you always want checked
    "v": 2,
}

# A strategy goes live only after its paper trades prove it
TRIAL_DAYS = 3
TRIAL_MIN_TRADES = 10
TRIAL_MIN_WINRATE = 0.60

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
    return {
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


SCOUTS = [
    {"key": "daily", "name": "Daily Swing", "focus": "5k-30k cards near today's low that bounced back on 2 of the last 3 days", "fn": scout_daily},
    {"key": "dip", "name": "Dip Hunter", "focus": "Cards trading well below their usual weekly price", "fn": scout_dip},
    {"key": "crash", "name": "Crash Buyer", "focus": "Quality cards hit hardest on market-wide crash days", "fn": scout_crash},
    {"key": "momentum", "name": "Momentum Rider", "focus": "Cards on a steady climb that hasn't stalled", "fn": scout_momentum},
    {"key": "fodder", "name": "Fodder Scout", "focus": "Cheap cards (1k-30k) where SBC demand starts", "fn": scout_fodder},
    {"key": "rebound", "name": "Rebound Spotter", "focus": "Big fallers that have started bouncing", "fn": scout_rebound},
]
SCOUT_NAMES = {s["key"]: s["name"] for s in SCOUTS}


# ---------------------------------------------------------------- director --
def director(cid, x, flags, cfg, held_ids, allowance):
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
    climbers = all(f.get("key") in ("momentum", "fodder") for f in flags)
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
    if now_price <= buy * (1 - cfg["stop_loss"]):
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


def save_json(name, data):
    path = os.path.join(DATA_DIR, name)
    with open(path + ".tmp", "w") as f:
        json.dump(data, f, separators=(",", ":"))
    os.replace(path + ".tmp", path)


class Engine:
    def __init__(self):
        os.makedirs(DATA_DIR, exist_ok=True)
        self.cfg = dict(DEFAULTS)
        self.cfg.update(load_json("settings.json", {}))
        self.market = Market()
        self.meta = load_json("cards.json", {})
        self.paper = load_json("paper.json", {"open": [], "closed": [], "first": {}})
        self.ids = []
        self.rarities = load_json("rarities.json", {})
        self.status = {"state": "live", "message": "Live"}
        try:
            self.market.load(os.path.join(DATA_DIR, "history.pkl.gz"))
        except FileNotFoundError:
            pass
        except Exception as e:
            log("Could not read price history, starting fresh:", e)

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

    def lookup_names(self, cids, limit=40):
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
                    self.meta[str(v["eaId"])] = {
                        "name": v.get("nickname") or v.get("commonName") or
                                f"{v.get('firstName', '')} {v.get('lastName', '')}".strip(),
                        "ovr": v.get("overall"), "rarity": v.get("rarityEaId"),
                        "pos": POSITIONS.get(v.get("position"), ""),
                    }
                self.meta.setdefault(str(cid), {"name": None, "failed": time.time()})
            except Exception as e:
                log("Name lookup failed for", cid, "-", e)
                self.meta.setdefault(str(cid), {"name": None, "failed": time.time()})
                if done == 0 and isinstance(e, urllib.error.HTTPError) and e.code in (401, 403, 429):
                    log("FUT.GG is refusing name lookups from here; cards will show their ID")
                    break
            done += 1
            time.sleep(1.0)
        save_json("cards.json", self.meta)

    def card_info(self, cid):
        m = self.meta.get(str(cid)) or {}
        r = m.get("rarity")
        return {"id": cid, "url": card_url(cid), "name": m.get("name") or f"Card {cid}",
                "ovr": m.get("ovr"), "pos": m.get("pos") or "",
                "rarity": self.rarities.get(str(r), "") if r is not None else ""}

    def strategy_stats(self, now_ts):
        out = {}
        for s in SCOUTS:
            k = s["key"]
            closed = [t for t in self.paper["closed"] if t["scout"] == k and t["closed"] >= now_ts - 7 * 86400]
            n = len(closed)
            wins = sum(1 for t in closed if t["net"] > 0)
            net = sum(t["net"] for t in closed)
            first = self.paper["first"].get(k)
            days = (now_ts - first) / 86400 if first else 0
            wr = wins / n if n else None
            if n >= TRIAL_MIN_TRADES and days >= TRIAL_DAYS:
                status = "LIVE" if wr >= TRIAL_MIN_WINRATE and net > 0 else "OFF"
            else:
                status = "TRIAL"
            out[k] = {"key": k, "name": s["name"], "focus": s["focus"], "status": status, "trades": n,
                      "wins": wins, "winrate": wr, "net": net, "days": round(days, 1),
                      "open": sum(1 for t in self.paper["open"] if t["scout"] == k)}
        return out

    def run(self, fetched=True):
        m = self.market
        now_ts = m.fine_ts[-1] if m.fine_ts else time.time()
        feats = {cid: x for cid in m.fine if (x := features(m, cid))}
        mood = market_mood(m, feats)
        stats = self.strategy_stats(now_ts)
        allowance = self.cfg["daily_limit"]

        # 1. scouts flag cards
        flagged, counts = {}, {s["key"]: 0 for s in SCOUTS}
        for cid, x in feats.items():
            for s in SCOUTS:
                r = s["fn"](cid, x, mood)
                if r:
                    r["scout"], r["key"] = s["name"], s["key"]
                    flagged.setdefault(cid, []).append(r)
                    counts[s["key"]] += 1

        # 2. the director decides; paper trading judges each scout on its own calls
        out = {"BUY": [], "WATCH": [], "REJECT": []}
        picks = []
        for cid, flags in flagged.items():
            x = feats[cid]
            dec, notes, buy, target, net, roi, score, qty = director(cid, x, flags, self.cfg, set(), allowance)
            if dec == "BUY" and all(stats[f["key"]]["status"] == "OFF" for f in flags):
                dec, notes = "REJECT", ["Its strategy is switched off: it lost coins in paper trading"]
            out[dec].append({"card": cid, "notes": notes, "buy": buy, "target": target, "net": net,
                             "roi": round(roi, 4), "score": score,
                             "live": any(stats[f["key"]]["status"] == "LIVE" for f in flags),
                             "scouts": [f["scout"] for f in flags], "why": [f["why"] for f in flags],
                             "hold": flags[0]["hold"], "now": x["now"]})
            for f in flags:
                d1 = director(cid, x, [f], self.cfg, set(), allowance)
                if d1[0] == "BUY":
                    picks.append((f["key"], cid, x["now"], d1[3]))
        out["BUY"].sort(key=lambda r: (not r["live"], -r["score"]))
        out["WATCH"].sort(key=lambda r: -r["score"])
        out["REJECT"].sort(key=lambda r: -r["roi"])
        out = {k: v[:n] for (k, v), n in zip(out.items(), (60, 30, 40))}

        # 3. paper trades: close what hit an exit, open the new picks
        if fetched:
            p, still = self.paper, []
            for t in p["open"]:
                x = feats.get(t["card"])
                act, price, why = exit_check(t["buy"], t["target"], t["opened"], x["now"], now_ts, self.cfg) if x else ("HOLD", None, "")
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
            for key, cid, price, target in picks:
                if (key, cid) in have or per.get(key, 0) >= 25:
                    continue
                p["open"].append({"id": uuid.uuid4().hex[:10], "scout": key, "card": cid,
                                  "buy": int(price), "target": int(target), "opened": now_ts})
                p["first"].setdefault(key, now_ts)
                per[key] = per.get(key, 0) + 1
                have.add((key, cid))
            p["closed"] = [t for t in p["closed"] if t["closed"] >= now_ts - 30 * 86400][-3000:]
            stats = self.strategy_stats(now_ts)

        # 4. names for everything the website will show
        need = [r["card"] for k in ("BUY", "WATCH") for r in out[k]] + [t["card"] for t in self.paper["open"]]
        if not SIM:
            self.lookup_names(list(dict.fromkeys(need)))

        def card_rows(rows):
            return [{**r, **self.card_info(r["card"])} for r in rows]

        def paper_rows(rows, closed):
            res = []
            for t in rows:
                info = self.card_info(t["card"])
                v = {**t, "name": info["name"], "url": info["url"], "ovr": info["ovr"],
                     "strategy": SCOUT_NAMES.get(t["scout"], t["scout"])}
                if not closed:
                    x = feats.get(t["card"])
                    v["now"], v["pl"] = (x["now"], after_tax(x["now"]) - t["buy"]) if x else (None, None)
                res.append(v)
            return res

        state = {
            "updated": now_ts, "generated": time.time(), "status": self.status,
            "platform": PLATFORM.upper(), "hours": round(m.history_hours(), 1), "cards": len(feats),
            "mood": mood, "rules": {k: self.cfg[k] for k in ("min_roi", "min_profit", "daily_limit", "max_copies",
                                                             "stop_loss", "max_hold_hours")},
            "trial": {"days": TRIAL_DAYS, "min_trades": TRIAL_MIN_TRADES, "min_winrate": TRIAL_MIN_WINRATE},
            "scouts": [{**stats[s["key"]], "flagged": counts[s["key"]]} for s in SCOUTS],
            "buy": card_rows(out["BUY"]), "watch": card_rows(out["WATCH"]), "reject": card_rows(out["REJECT"]),
            "paper_open": paper_rows(sorted(self.paper["open"], key=lambda t: -t["opened"])[:80], False),
            "paper_closed": paper_rows(self.paper["closed"][-80:][::-1], True),
            "prices": {str(c): x["now"] for c, x in feats.items()},
            "names": {k: v["name"] for k, v in self.meta.items() if v.get("name")},
        }
        return state

    def save(self, state):
        save_json("paper.json", self.paper)
        save_json("state.json", state)
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
    state = eng.run(fetched)
    eng.save(state)
    log(f"Done: {len(state['buy'])} buys, {len(state['watch'])} watching, "
        f"{sum(len(state[k]) for k in ('paper_open',))} open paper trades, {state['hours']} h of history")


if __name__ == "__main__":
    main()
