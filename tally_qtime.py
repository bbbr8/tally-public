"""Tally timing qubits — when something happened, as a state over days.

A record often fixes a time only to a window: a cheque's face date and the day it posted, a "July" meeting, a reading
date versus an event date. A time qubit is a distribution over days (exact decimal probabilities, amplitudes √p as
notation; no quantum computation is claimed). Order between two uncertain times is a probability, not a guess, and a
set of order constraints is solved exactly: the network shows what each event's time must be, how much the readings
strain against the constraints, and — when they cannot all be true — the smallest set of constraints that collide.

    moment(@2030-05-19) · moment(@a, @b) · moment(@a, @b, "business") · moment([[@a, 1], [@b, 3]]) · moment({day, time})
    t.p t.earliest t.latest t.mode t.mean t.entropy t.days t.settled t.ket
    t1 < t2                         true / false / maybe (comparisons work in rule guards: maybe makes a conclusion open)
    t2 - t1                         the range of days between them;  t + 3  shifts by three days
    p_before(a, b)                  {before, same_day, after, p}: p counts a same-day pair by its times, else as even
    p_within(a, b, days)            P(|b - a| <= days)
    time_gap(a, b)                  the distribution of b - a in days
    time_lag(t, lo, hi)             t followed by an even lag of lo..hi days (posting after writing, reading after sending)
    constrain(t, {not_before, not_after, weekdays})
    schedule({events: {...}, constraints: [{a, b, rel or min/max}]})
    which_clock(items, ["face_date", "posted"], "doc_date")   which clock a document's dates read
    coincidence(a, b, window, rate_per_day)                   how surprising it is that two events fell together
"""
import datetime as _dt
import itertools
import math
from decimal import Decimal

import tally as T

Q6 = Decimal("0.000001")
DAY = _dt.timedelta(days=1)


def _bits(ps):
    h = 0.0
    for p in ps:
        p = float(p)
        if p > 0:
            h -= p * math.log2(p)
    return Decimal(str(round(h + 0.0, 6)))


class TimeQubit:
    """a distribution over days; time of day kept only when the qubit is one day with a known time"""
    tally_type = "time qubit"

    def __init__(self, dist, time=""):
        dist = {d: Decimal(p) for d, p in dist.items() if p > 0}
        tot = sum(dist.values(), Decimal(0))
        if tot == 0:
            raise T.TallyError("a time qubit needs at least one day with weight", 0, 0)
        self.dist = {d: p / tot for d, p in sorted(dist.items())}
        self.time = time if len(self.dist) == 1 else ""

    def days(self):
        return list(self.dist)

    def mean(self):
        base = min(self.dist)
        off = sum(((d - base).days * p for d, p in self.dist.items()), Decimal(0))
        return base + _dt.timedelta(days=int(off.to_integral_value()))

    def ket(self, top=4):
        items = sorted(self.dist.items(), key=lambda kv: (-kv[1], kv[0]))
        parts = [f"{Decimal(str(math.sqrt(float(p)))).quantize(Decimal('0.001'))}|{d.isoformat()}"
                 f"{(' ' + self.time) if self.time else ''}⟩" for d, p in items[:top]]
        more = len(items) - top
        return " + ".join(parts) + (f" + … ({more} more days)" if more > 0 else "")

    def tally_show(self):
        if len(self.dist) == 1:
            d = next(iter(self.dist))
            return f"|{d.isoformat()}{(' ' + self.time) if self.time else ''}⟩"
        lo, hi = min(self.dist), max(self.dist)
        return f"{self.ket()}  [{lo.isoformat()}..{hi.isoformat()}, {len(self.dist)} days]"

    def tally_eq(self, other):
        return self.time == other.time and {d: p.quantize(Q6) for d, p in self.dist.items()} == \
            {d: p.quantize(Q6) for d, p in other.dist.items()}

    def tally_fields(self):
        mode = max(self.dist.items(), key=lambda kv: (kv[1], -kv[0].toordinal()))[0]
        return {"p": {d.isoformat(): p.quantize(Q6).normalize() for d, p in self.dist.items()},
                "earliest": min(self.dist), "latest": max(self.dist), "mode": mode, "mean": self.mean(),
                "entropy": _bits(self.dist.values()), "days": Decimal(len(self.dist)), "settled": len(self.dist) == 1,
                "time": self.time, "ket": self.ket()}

    # ---- operators: comparisons are true / false / maybe; t - t is a range of days; t + n shifts
    def tally_binop(self, op, a, b, interp, node):
        A, B = as_tq(a), as_tq(b)
        if op in ("<", "<=", ">", ">=") and A is not None and B is not None:
            # day resolution, exactly like comparing dates; decided from the earliest and latest possible days (no
            # sums of probabilities, which never add back to exactly 1): maybe when the days could go either way
            a0, a1, b0, b1 = min(A.dist), max(A.dist), min(B.dist), max(B.dist)
            if op == "<":
                return True if a1 < b0 else (False if a0 >= b1 else T.MAYBE)
            if op == "<=":
                return True if a1 <= b0 else (False if a0 > b1 else T.MAYBE)
            if op == ">":
                return True if a0 > b1 else (False if a1 <= b0 else T.MAYBE)
            return True if a0 >= b1 else (False if a1 < b0 else T.MAYBE)
        if op in ("==", "!="):
            same = A is not None and B is not None and A.tally_eq(B)
            return same if op == "==" else not same
        if op == "-" and A is not None and B is not None:
            lo = min(A.dist) - max(B.dist)
            hi = max(A.dist) - min(B.dist)
            return T.Interval(Decimal(lo.days), Decimal(hi.days))
        if op in ("+", "-") and isinstance(T.strip(a), TimeQubit) and isinstance(T.strip(b), Decimal):
            n = int(T.strip(b)) * (1 if op == "+" else -1)
            q = T.strip(a)
            return TimeQubit({d + _dt.timedelta(days=n): p for d, p in q.dist.items()}, q.time)
        raise interp.err(f"cannot apply '{op}' to {T.type_name(a)} and {T.type_name(b)}", node)


T.EXT_BINOP.add(TimeQubit)


def as_tq(x):
    v = T.strip(x)
    if isinstance(v, TimeQubit):
        return v
    if isinstance(v, _dt.date):
        return TimeQubit({v: Decimal(1)})
    return None


def order_probs(A, B):
    """P(A's day < B's day), P(same day), P(after) for independent A, B"""
    before = same = Decimal(0)
    bdays = sorted(B.dist.items())
    for da, pa in A.dist.items():
        for db, pb in bdays:
            if da < db:
                before += pa * pb
            elif da == db:
                same += pa * pb
    return {"before": before, "same_day": same, "after": 1 - before - same}


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def tq(x, node, what="a time qubit or a date"):
        q = as_tq(x)
        if q is None:
            v = T.strip(x)
            if isinstance(v, dict) and isinstance(T.strip(v.get("day")), _dt.date):
                return TimeQubit({T.strip(v["day"]): Decimal(1)}, str(T.strip(v.get("time", "")) or ""))
            raise it.err(f"expected {what}, got {T.type_name(x)}", node, hint="moment(@2030-05-19) or moment(@a, @b)")
        return q

    def day(x, node, what):
        v = T.strip(x)
        if not isinstance(v, _dt.date):
            raise it.err(f"{what} must be a date", node)
        return v

    @bi("moment", (1, 2, 3))
    def _moment(it_, node, a, b=None, mode=None):
        """a time qubit: moment(@d) settled; moment({day, time}) settled with a time; moment(@a, @b) even over the days a..b
        (inclusive); moment(@a, @b, "business") even over the weekdays only; moment([[@d, weight], …]) weighted"""
        v = T.strip(a)
        if b is None:
            if isinstance(v, list):
                dist = {}
                for pair in v:
                    pr = T.strip(pair)
                    if not isinstance(pr, list) or len(pr) != 2:
                        raise it_.err("moment([[@day, weight], …]) — each item is a [date, weight] pair", node)
                    d, w = day(pr[0], node, "the first item of a pair"), T.strip(pr[1])
                    if not isinstance(w, Decimal) or w < 0:
                        raise it_.err("moment: weights are non-negative numbers", node)
                    dist[d] = dist.get(d, Decimal(0)) + w
                return T.wrap(TimeQubit(dist), T.srcs(a))
            return T.wrap(tq(a, node), T.srcs(a))
        lo, hi = day(a, node, "the first day"), day(b, node, "the last day")
        if hi < lo:
            raise it_.err("moment(a, b): the last day is before the first", node)
        m = T.strip(mode)
        days = [lo + DAY * i for i in range((hi - lo).days + 1)]
        if m == "business":
            days = [d for d in days if d.weekday() < 5]
        elif m is not None:
            raise it_.err('moment: the third argument is "business" (weekdays only) or left out', node)
        if not days:
            raise it_.err("moment: no days in that window", node)
        return T.wrap(TimeQubit({d: Decimal(1) for d in days}), T.srcs(a, b))

    @bi("p_before", 2)
    def _p_before(it_, node, a, b):
        """P(a before b) for independent times: {before, same_day, after, p}; p counts a same-day pair by its times
        when both are known, else as an even chance"""
        A, B = tq(a, node), tq(b, node)
        r = order_probs(A, B)
        if r["same_day"] and A.time and B.time and len(A.dist) == len(B.dist) == 1:
            tie = Decimal(1) if A.time < B.time else Decimal(0)
        else:
            tie = Decimal("0.5")
        out = {k: v.quantize(Q6).normalize() for k, v in r.items()}
        out["p"] = (r["before"] + r["same_day"] * tie).quantize(Q6).normalize()
        return T.wrap(out, T.srcs(a, b))

    @bi("p_within", 3)
    def _p_within(it_, node, a, b, days):
        """P(the two times fall within `days` of each other)"""
        A, B = tq(a, node), tq(b, node)
        n = int(T.strip(days))
        p = sum((pa * pb for da, pa in A.dist.items() for db, pb in B.dist.items() if abs((db - da).days) <= n),
                Decimal(0))
        return T.wrap(p.quantize(Q6).normalize(), T.srcs(a, b))

    @bi("time_gap", 2)
    def _gap(it_, node, a, b):
        """the distribution of b - a in days: {p: {days: prob}, min, max, mean}"""
        A, B = tq(a, node), tq(b, node)
        dist = {}
        for da, pa in A.dist.items():
            for db, pb in B.dist.items():
                k = (db - da).days
                dist[k] = dist.get(k, Decimal(0)) + pa * pb
        mean = sum((Decimal(k) * p for k, p in dist.items()), Decimal(0))
        return T.wrap({"p": {str(k): v.quantize(Q6).normalize() for k, v in sorted(dist.items())},
                       "min": Decimal(min(dist)), "max": Decimal(max(dist)), "mean": mean.quantize(Q6).normalize()},
                      T.srcs(a, b))

    @bi("time_lag", 3)
    def _lag(it_, node, t, lo, hi):
        """t followed by an even lag of lo..hi days (negative lags look back): when a cheque posts after it is
        written, or a record is read after it is sent"""
        A = tq(t, node)
        l0, l1 = int(T.strip(lo)), int(T.strip(hi))
        if l1 < l0:
            raise it_.err("time_lag: hi must be at least lo", node)
        w = Decimal(1) / Decimal(l1 - l0 + 1)
        dist = {}
        for d, p in A.dist.items():
            for k in range(l0, l1 + 1):
                dd = d + _dt.timedelta(days=k)
                dist[dd] = dist.get(dd, Decimal(0)) + p * w
        return T.wrap(TimeQubit(dist), T.srcs(t))

    @bi("constrain", 2)
    def _constrain(it_, node, t, spec):
        """keep only the days a constraint allows and renormalize: {not_before, not_after, weekdays: true}"""
        A = tq(t, node)
        sp = {k: T.strip(v) for k, v in T.strip(spec).items()}
        unknown = set(sp) - {"not_before", "not_after", "weekdays"}
        if unknown:
            raise it_.err(f"constrain: unknown keys {sorted(unknown)} (not_before, not_after, weekdays)", node)
        keep = {}
        for d, p in A.dist.items():
            if "not_before" in sp and d < min(tq(sp["not_before"], node).dist):
                continue
            if "not_after" in sp and d > max(tq(sp["not_after"], node).dist):
                continue
            if sp.get("weekdays") is True and d.weekday() >= 5:
                continue
            keep[d] = p
        if not keep:
            raise it_.err("constrain: no day survives the constraint", node)
        return T.wrap(TimeQubit(keep), T.srcs(t, spec))

    # ------------------------------------------------------------ the constraint network
    REL = {"before": (1, None), "on_or_before": (0, None), "same_day": (0, 0), "after": (None, -1),
           "on_or_after": (None, 0)}

    def parse_constraints(cs, names, node):
        out = []
        for c in T.strip(cs):
            m = {k: T.strip(v) for k, v in T.strip(c).items()}
            a, b = m.get("a"), m.get("b")
            if a not in names or b not in names:
                raise it.err(f"schedule: constraint {m} names an event that is not in events ({sorted(names)})", node)
            rel = m.get("rel")
            if rel in REL:
                lo, hi = REL[rel]
            elif rel == "within":
                n = int(m.get("days", 0))
                lo, hi = -n, n
            elif rel is None:
                lo = None if m.get("min") is None else int(m["min"])
                hi = None if m.get("max") is None else int(m["max"])
            else:
                raise it.err(f"schedule: rel is one of {sorted(REL) + ['within']} or give min/max days", node)
            label = m.get("why") or (f"{a} {rel} {b}" if rel else f"{b} - {a} in {lo}..{hi} days")
            out.append({"a": a, "b": b, "lo": lo, "hi": hi, "label": str(label)})
        return out

    def ok(c, da, db):
        k = (db - da).days
        return (c["lo"] is None or k >= c["lo"]) and (c["hi"] is None or k <= c["hi"])

    def solve(evs, cons, cap=3_000_000):
        """exact posterior over joint assignments by backtracking with forward checking; returns (mass, marginals,
        pair order stats) — mass is the prior probability that every constraint holds"""
        names = list(evs)
        doms = {n: dict(evs[n].dist) for n in names}
        # arc consistency: drop days that no partner day can satisfy
        changed = True
        while changed:
            changed = False
            for c in cons:
                for x, y, fwd in ((c["a"], c["b"], True), (c["b"], c["a"], False)):
                    keep = {d: p for d, p in doms[x].items()
                            if any(ok(c, d, e) if fwd else ok(c, e, d) for e in doms[y])}
                    if len(keep) != len(doms[x]):
                        doms[x], changed = keep, True
        if any(not doms[n] for n in names):
            return Decimal(0), None
        order = sorted(names, key=lambda n: len(doms[n]))
        by = {n: [c for c in cons if n in (c["a"], c["b"])] for n in names}
        marg = {n: {} for n in names}
        mass = [Decimal(0)]
        steps = [0]
        assign = {}

        def rec(i, w):
            steps[0] += 1
            if steps[0] > cap:
                raise T.TallyError("schedule: too many joint assignments to enumerate exactly — narrow the windows",
                                   0, 0)
            if i == len(order):
                mass[0] += w
                for n, d in assign.items():
                    marg[n][d] = marg[n].get(d, Decimal(0)) + w
                return
            n = order[i]
            for d, p in doms[n].items():
                good = True
                for c in by[n]:
                    other = c["b"] if c["a"] == n else c["a"]
                    if other in assign:
                        da, db = (d, assign[other]) if c["a"] == n else (assign[other], d)
                        if not ok(c, da, db):
                            good = False
                            break
                if good:
                    assign[n] = d
                    rec(i + 1, w * p)
                    del assign[n]
        rec(0, Decimal(1))
        return mass[0], marg

    @bi("schedule", 1)
    def _schedule(it_, node, spec):
        """solve a network of uncertain times under order constraints, exactly. spec: {events: {name: time qubit or
        date}, constraints: [{a, b, rel: before | on_or_before | same_day | after | on_or_after | within (days), or
        min/max days for b - a, why}]}. Returns {consistent, p_consistent (prior chance every constraint holds),
        surprise_bits, marginals (each event's time qubit once the constraints are known), tension (bits each
        constraint costs), conflict (the smallest set of constraints that cannot all hold, when consistent is false)}"""
        sp = T.strip(spec)
        evs = {str(k): tq(v, node) for k, v in T.strip(sp.get("events", {})).items()}
        if not evs:
            raise it_.err("schedule: give events {name: time}", node)
        cons = parse_constraints(sp.get("constraints", []), set(evs), node)
        mass, marg = solve(evs, cons)
        out = {"consistent": mass > 0, "p_consistent": mass.quantize(Decimal("0.00000001")).normalize(),
               "surprise_bits": Decimal(str(round(-math.log2(float(mass)), 6))) if mass > 0 else None}
        if mass > 0:
            out["marginals"] = {n: TimeQubit(m) for n, m in marg.items()}
            tension = []
            for i, c in enumerate(cons):
                m2, _ = solve(evs, cons[:i] + cons[i + 1:])
                tension.append({"constraint": c["label"],
                                "bits": Decimal(str(round(math.log2(float(m2) / float(mass)), 6))) if m2 > 0 else
                                Decimal(0)})
            out["tension"] = sorted(tension, key=lambda x: -x["bits"])
            out["conflict"] = []
        else:
            core = list(cons)
            for c in list(core):
                trial = [x for x in core if x is not c]
                if solve(evs, trial)[0] == 0:
                    core = trial
            out["conflict"] = [c["label"] for c in core]
            out["marginals"] = {}
            out["tension"] = []
        return out

    @bi("which_clock", (3, 4))
    def _which_clock(it_, node, items, clocks, doc_field, error_rate=Decimal("0.05")):
        """which clock a document's dates read. items: maps carrying the document's date (doc_field) and each candidate
        clock's date (fields named in clocks). Each item where the clocks differ is evidence: a match is likely
        (1 - error_rate), a miss is a reading error (error_rate / number of other days). Returns {qubit over clocks,
        matches per clock, discriminating items, items}"""
        names = [str(T.strip(c)) for c in T.strip(clocks)]
        if len(names) < 2:
            raise it_.err("which_clock: name at least two clock fields", node)
        df = str(T.strip(doc_field))
        eps = T.strip(error_rate)
        if not isinstance(eps, Decimal) or not 0 < eps < 1:
            raise it_.err("which_clock: error_rate is between 0 and 1", node)
        w = {n: Decimal(1) for n in names}
        matches = {n: Decimal(0) for n in names}
        disc, rows = 0, []
        for x in T.strip(items):
            m = T.strip(x)
            m = m.vals if isinstance(m, T.Record) else m
            d = T.strip(m.get(df))
            vals = {n: T.strip(m.get(n)) for n in names}
            if not isinstance(d, _dt.date) or any(not isinstance(v, _dt.date) for v in vals.values()):
                raise it_.err(f"which_clock: every item needs dates in {df} and {names}", node)
            hit = [n for n in names if vals[n] == d]
            for n in hit:
                matches[n] += 1
            informative = len(set(vals.values())) > 1
            if informative:
                disc += 1
                for n in names:
                    w[n] *= (1 - eps) if vals[n] == d else eps
            rows.append({"doc": d, **{n: vals[n] for n in names}, "reads": hit, "informative": informative})
        from tally_qubit import Qubit
        return {"qubit": Qubit(list(w.items())), "matches": matches, "discriminating": Decimal(disc),
                "items": Decimal(len(rows)), "rows": rows}

    @bi("coincidence", 4)
    def _coincidence(it_, node, a, b, window, rate):
        """how surprising it is that two events fell within `window` days of each other, against a base rate of
        events of b's kind per day: {p_within, chance (P a random event of that kind lands in the window), lift,
        surprise_bits}"""
        n = int(T.strip(window))
        r = T.strip(rate)
        if not isinstance(r, Decimal) or r < 0:
            raise it_.err("coincidence: the base rate is events per day (a non-negative number)", node)
        pw = T.strip(_p_within(it_, node, a, b, window))
        chance = Decimal(str(1 - math.exp(-float(r) * (2 * n + 1))))
        lift = None if chance == 0 else (pw / chance).quantize(Q6).normalize()
        bits = None if chance == 0 else Decimal(str(round(-math.log2(float(chance)), 6)))
        return T.wrap({"p_within": pw, "chance": chance.quantize(Q6).normalize(), "lift": lift,
                       "surprise_bits": bits}, T.srcs(a, b))
