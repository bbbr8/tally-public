"""Tally's forensic math built-ins — exact cents throughout; every result carries the sources of what it used.

    share_bounds(events, day, amount, cls)   floor and ceiling of one class's share of an outflow that hold under
                                             EVERY tracing convention and same-day order (two-pool extremal argument)
    libr(events, cls)                        lowest-intermediate-balance trace: the most of cls that can still be in the
                                             account after each event (withdrawals charged to everyone else first)
    subset_sums(amounts, target, max_items)  every set of at most max_items amounts that adds to target exactly
    window_sums(series, target)              every run of consecutive items whose sum is target exactly
    round_trips(lines, days)                 an amount that leaves and the same amount that comes back within `days`
    benford(amounts)                         first-digit counts vs Benford, MAD, chi-square, conformity class; round-number share

Events are trace Events (day, amount, memo, page, cls) or maps with those fields; money is exact.

The extremal argument for share_bounds: with two pools — C (the class) and O (everyone else) — the class's share of an
outflow is smallest when every earlier withdrawal was charged to C first (O keeps the most), and largest when every
earlier withdrawal was charged to O first. Any convention charges each withdrawal somewhere in between, so its result
lies inside [floor, ceiling]. Same-day order is searched both ways and the envelope is reported.
"""
import itertools
from decimal import Decimal

import tally as T

CENT = Decimal("0.01")


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def as_list(x, node):
        x = T.strip(x)
        if not isinstance(x, list):
            raise it.err(f"expected a list, got {T.type_name(x)}", node)
        return x

    def fld(e, name, node):
        v = T.strip(e)
        if isinstance(v, dict):
            if name not in v:
                raise it.err(f"event has no field '{name}'", node)
            return v[name]
        if isinstance(v, T.Record):
            return v.vals[name]
        raise it.err(f"events must be records or maps, got {T.type_name(v)}", node)

    def cents(m, node):
        v = T.strip(m)
        if isinstance(v, T.Money):
            return v.cents
        raise it.err(f"expected money, got {T.type_name(v)}", node)

    def norm_events(events, node):
        out = []
        for e in as_list(events, node):
            page = T.strip(fld(e, "page", node))
            src = set(T.srcs(fld(e, "amount", node)))
            if isinstance(page, str) and page:
                src.add(page)
            out.append({"day": T.strip(fld(e, "day", node)), "c": cents(fld(e, "amount", node), node),
                        "cls": T.strip(fld(e, "cls", node)), "src": src})
        return out

    def by_day_order(evs, order):
        days = {}
        for i, e in enumerate(evs):
            days.setdefault(e["day"], []).append((i, e))
        out = []
        for d in sorted(days):
            ins = [x for x in days[d] if x[1]["c"] > 0]
            outs = [x for x in days[d] if x[1]["c"] < 0]
            out += (ins + outs) if order == "deposits_first" else (outs + ins)
        return out

    def two_pool(evs, order, cls, charge_first, stop):
        """replay with two pools; each withdrawal charged to `charge_first` pool first. Returns pools just before
        the stop event (index into evs) or the full trajectory when stop is None."""
        C = O = 0
        deficit = 0
        traj = []
        for i, e in by_day_order(evs, order):
            if stop is not None and i == stop:
                return C, O, traj
            amt = e["c"]
            if amt > 0:
                cover = min(deficit, amt)
                deficit -= cover
                amt -= cover
                if (e["cls"] in cls) if isinstance(cls, (set, frozenset)) else (e["cls"] == cls):
                    C += amt
                else:
                    O += amt
            else:
                need = -amt
                first, second = ("C", "O") if charge_first == "C" else ("O", "C")
                for pool in (first, second):
                    have = C if pool == "C" else O
                    take = min(have, need)
                    if pool == "C":
                        C -= take
                    else:
                        O -= take
                    need -= take
                deficit += need
            traj.append((e["day"], C, O))
        return C, O, traj

    def classes_of(cls, node):
        c = T.strip(cls)
        if isinstance(c, list):
            return {str(T.strip(x)) for x in c}
        return {str(c)}

    @bi("share_bounds", 4)
    def _share_bounds(it_, node, events, day, amount, cls):
        """floor and ceiling of cls's share of one outflow, valid under every tracing convention and same-day order"""
        evs = norm_events(events, node)
        d, tc = T.strip(day), cents(amount, node)
        c = classes_of(cls, node)
        if tc >= 0:
            raise it.err("share_bounds: the target amount must be an outflow (negative money)", node)
        idx = [i for i, e in enumerate(evs) if e["day"] == d and e["c"] == tc]
        if not idx:
            raise it.err(f"share_bounds: no outflow of {T.Money(tc)} on {d} in these events", node)
        t = -tc
        floors, ceils, detail = [], [], {}
        for order in ("deposits_first", "withdrawals_first"):
            C1, O1, _ = two_pool(evs, order, c, "C", idx[0])   # class spent first: least class left
            C2, O2, _ = two_pool(evs, order, c, "O", idx[0])   # others spent first: most class left
            floors.append(min(max(0, t - O1), C1))   # what the others cannot cover, capped by what the class has
            ceils.append(min(t, C2))
            detail[order] = {"class_left_if_spent_first": T.Money(C1), "others_left_then": T.Money(O1),
                             "class_left_if_others_spent_first": T.Money(C2)}
        src = set().union(*[e["src"] for e in evs[:idx[0] + 1]]) if evs else set()
        return T.wrap({"class": sorted(c) if len(c) > 1 else next(iter(c)), "outflow": T.Money(tc),
                       "floor": T.Money(min(floors)), "ceiling": T.Money(max(ceils)),
                       "range": T.Interval(T.Money(min(floors)), T.Money(max(ceils))),
                       "by_order": detail}, src)

    def set_replay(evs, order, cs, in_set, least):
        """two pools: K (the classes) and O. `least`: withdrawals outside the set drain K first and set withdrawals
        drain O first (the least K can reach the set); otherwise the reverse. Returns (K into set, total of set)."""
        K = O = 0
        deficit = 0
        k_in = total = 0
        for i, e in by_day_order(evs, order):
            amt = e["c"]
            if amt > 0:
                cover = min(deficit, amt)
                deficit -= cover
                amt -= cover
                if e["cls"] in cs:
                    K += amt
                else:
                    O += amt
                continue
            need = -amt
            target = in_set[i]
            if target:
                total += need
            k_first = (not target) if least else target
            for pool in (("K", "O") if k_first else ("O", "K")):
                have = K if pool == "K" else O
                take = min(have, need)
                if pool == "K":
                    K -= take
                    if target:
                        k_in += take
                else:
                    O -= take
                need -= take
            deficit += need
        return k_in, total

    @bi("set_bounds", 3)
    def _set_bounds(it_, node, events, in_set, classes):
        """floor and ceiling of how much of `classes` (a class or a list) went into ALL the outflows `in_set` picks,
        together — valid under every tracing convention and same-day order. (Adding per-outflow floors is not valid:
        each assumes a different worst case for the others.)"""
        evs = norm_events(events, node)
        cs = classes_of(classes, node)
        raw = as_list(events, node)
        flags = [False] * len(evs)
        for i, e in enumerate(raw):
            if evs[i]["c"] < 0:
                flags[i] = it_.truth(it_.call(in_set, [e], node), node)
        lo, hi, total = None, None, 0
        for order in ("deposits_first", "withdrawals_first"):
            k_lo, total = set_replay(evs, order, cs, flags, True)
            k_hi, _ = set_replay(evs, order, cs, flags, False)
            lo = k_lo if lo is None else min(lo, k_lo)
            hi = k_hi if hi is None else max(hi, k_hi)
        n = sum(flags)
        src = set().union(*[evs[i]["src"] for i in range(len(evs)) if flags[i]]) if n else set()
        return T.wrap({"outflows": T.Decimal(n), "total": T.Money(total), "floor": T.Money(lo), "ceiling": T.Money(hi),
                       "range": T.Interval(T.Money(lo), T.Money(hi))}, src)

    @bi("libr", (2, 3))
    def _libr(it_, node, events, cls, order="deposits_first"):
        """lowest intermediate balance: after each day, the most of cls that can still be in the account (every
        withdrawal charged to everyone else's money first). Default: end-of-day balances (deposits before withdrawals
        within a day); "withdrawals_first" also counts intraday dips. Returns [{day, class_left, balance}]"""
        evs = norm_events(events, node)
        c = str(T.strip(cls))
        o = str(T.strip(order))
        if o not in ("deposits_first", "withdrawals_first"):
            raise it.err("libr: order is deposits_first or withdrawals_first", node)
        _, _, traj = two_pool(evs, o, c, "O", None)
        out, last = [], None
        for day, C, O in traj:
            row = {"day": day, "class_left": T.Money(C), "balance": T.Money(C + O)}
            if last and last["day"] == day:
                out[-1] = row
            else:
                out.append(row)
            last = row
        return out

    @bi("subset_sums", (2, 3))
    def _subset_sums(it_, node, amounts, target, max_items=Decimal(4)):
        """every set of at most max_items amounts (by position) whose sum is exactly target — meet in the middle"""
        items = [cents(a, node) for a in as_list(amounts, node)]
        raw = as_list(amounts, node)
        t = cents(target, node)
        k = int(T.strip(max_items))
        if len(items) > 400:
            raise it.err("subset_sums: at most 400 amounts (filter the pool first)", node)
        n = len(items)
        sols = set()
        half = k // 2
        # all combinations of size <= half, indexed by sum
        small = {}
        for r in range(0, half + 1):
            for combo in itertools.combinations(range(n), r):
                small.setdefault(sum(items[i] for i in combo), []).append(combo)
        for r in range(0, k - half + 1):
            for combo in itertools.combinations(range(n), r):
                need = t - sum(items[i] for i in combo)
                for other in small.get(need, []):
                    if set(other) & set(combo):
                        continue
                    s = tuple(sorted(set(other) | set(combo)))
                    if 0 < len(s) <= k:
                        sols.add(s)
            if len(sols) > 500:
                break
        out = []
        for s in sorted(sols, key=lambda s: (len(s), s)):
            parts = [raw[i] for i in s]
            out.append(T.wrap({"positions": [Decimal(i) for i in s], "items": parts}, T.srcs(*parts)))
        return out

    @bi("window_sums", 2)
    def _window_sums(it_, node, series, target):
        """every run of consecutive items (start..end inclusive, by position) whose sum is exactly target"""
        items = [cents(a, node) for a in as_list(series, node)]
        raw = as_list(series, node)
        t = cents(target, node)
        out = []
        prefix = {0: [-1]}
        run = 0
        for j, v in enumerate(items):
            run += v
            for i in prefix.get(run - t, []):
                parts = raw[i + 1:j + 1]
                out.append(T.wrap({"start": Decimal(i + 1), "end": Decimal(j), "count": Decimal(j - i)}, T.srcs(*parts)))
            prefix.setdefault(run, []).append(j)
        return out

    @bi("round_trips", (1, 2))
    def _round_trips(it_, node, lines, days=Decimal(14)):
        """an outflow and an inflow of the same exact amount within `days` of each other (either order)"""
        evs = []
        for e in as_list(lines, node):
            evs.append((T.strip(fld(e, "day", node)), cents(fld(e, "amount", node), node), e))
        w = int(T.strip(days))
        out = []
        for i, (d1, c1, e1) in enumerate(evs):
            if c1 >= 0:
                continue
            for d2, c2, e2 in evs:
                if c2 == -c1 and abs((d2 - d1).days) <= w:
                    out.append(T.wrap({"out": e1, "back": e2, "gap_days": Decimal((d2 - d1).days),
                                       "amount": T.Money(-c1)}, T.srcs(fld(e1, "amount", node), fld(e2, "amount", node))))
        return out

    @bi("reconcile", (2, 3))
    def _reconcile(it_, node, a, b, opts=None):
        """match two lists one-to-one: same exact amount (field `amount`), dates (field `day`) at most `days` apart,
        nearest date first. opts {days: 0, amount: "amount", day: "day", sign: false}. Returns {matched: [{a, b, gap}],
        only_a, only_b}. sign: true compares amounts ignoring sign (a payment against its deposit)."""
        o = T.strip(opts) if opts is not None else {}
        days = int(T.strip(o.get("days", Decimal(0))))
        af, df = str(T.strip(o.get("amount", "amount"))), str(T.strip(o.get("day", "day")))
        ignore_sign = T.strip(o.get("sign", False)) is True
        A, B = as_list(a, node), as_list(b, node)
        def key(x):
            c = cents(fld(x, af, node), node)
            return abs(c) if ignore_sign else c
        pairs = []
        for i, x in enumerate(A):
            for j, y in enumerate(B):
                if key(x) == key(y):
                    gap = (T.strip(fld(y, df, node)) - T.strip(fld(x, df, node))).days
                    if abs(gap) <= days:
                        pairs.append((abs(gap), i, j, gap))
        pairs.sort()
        used_a, used_b, matched = set(), set(), []
        for _, i, j, gap in pairs:
            if i in used_a or j in used_b:
                continue
            used_a.add(i)
            used_b.add(j)
            matched.append(T.wrap({"a": A[i], "b": B[j], "gap": Decimal(gap)},
                                  T.srcs(fld(A[i], af, node), fld(B[j], af, node))))
        return {"matched": matched, "only_a": [x for i, x in enumerate(A) if i not in used_a],
                "only_b": [y for j, y in enumerate(B) if j not in used_b]}

    @bi("dwell", (2, 3))
    def _dwell(it_, node, events, cls, order="deposits_first"):
        """FIFO dwell time: for each dollar of `cls` that came in, how many days until an outflow took it.
        Returns {in, spent, still_in, dollar_days_mean, within_3_days, within_30_days} (shares of the spent money)"""
        evs = norm_events(events, node)
        cs = classes_of(cls, node)
        o = str(T.strip(order))
        layers = []  # [day, cents, is_class]
        deficit = 0
        spent = []  # (days, cents) for class money
        total_in = 0
        for _, e in by_day_order(evs, o):
            amt = e["c"]
            if amt > 0:
                cover = min(deficit, amt)
                deficit -= cover
                amt -= cover
                if amt:
                    layers.append([e["day"], amt, e["cls"] in cs])
                if e["cls"] in cs:
                    total_in += e["c"]
                continue
            need = -amt
            while need > 0 and layers:
                take = min(layers[0][1], need)
                if layers[0][2]:
                    spent.append(((e["day"] - layers[0][0]).days, take))
                layers[0][1] -= take
                need -= take
                if layers[0][1] == 0:
                    layers.pop(0)
            deficit += need
        sc = sum(c for _, c in spent)
        mean = (Decimal(sum(d * c for d, c in spent)) / sc).quantize(Decimal("0.1")) if sc else None
        def share(limit):
            return (Decimal(sum(c for d, c in spent if d <= limit)) / sc).quantize(Decimal("0.001")) if sc else None
        return {"in": T.Money(total_in), "spent": T.Money(sc), "still_in": T.Money(sum(l[1] for l in layers if l[2])),
                "dollar_days_mean": mean, "within_3_days": share(3), "within_30_days": share(30), "order": o}

    import re as _re
    _SUFFIX = _re.compile(r"\b(llc|l\.l\.c|inc|co|corp|company|companies|the|and|services|service)\b")

    def name_key_py(s_):
        s_ = _re.sub(r"\(.*?\)", " ", str(s_).lower())
        s_ = s_.replace("&", " and ").replace("+", " and ")
        s_ = _re.sub(r"[^a-z0-9 ]", " ", s_)
        s_ = _SUFFIX.sub(" ", s_)
        words = [w[:-1] if len(w) > 4 and w.endswith("s") else w for w in s_.split()]
        return " ".join(words)

    @bi("name_key", 1)
    def _name_key(it_, node, s_):
        """a payee name reduced for comparison: lower case, no punctuation, no notes in brackets, no LLC / Inc /
        Services, no plural s"""
        return T.wrap(name_key_py(T.strip(s_)), T.srcs(s_))

    @bi("similar", 2)
    def _similar(it_, node, a, b):
        """0..1 similarity of two names after name_key (1 = same key)"""
        import difflib
        x, y = name_key_py(T.strip(a)), name_key_py(T.strip(b))
        return Decimal(str(round(difflib.SequenceMatcher(None, x, y).ratio(), 3)))

    @bi("cluster_names", (1, 2))
    def _cluster_names(it_, node, names, threshold=Decimal("0.85")):
        """groups of names that are probably one party (same key, or similarity >= threshold), largest first"""
        import difflib
        lst = [T.strip(n) for n in as_list(names, node)]
        uniq = []
        for n in lst:
            if n not in uniq:
                uniq.append(n)
        th = float(T.strip(threshold))

        def same(x, y):
            dx, dy = _re.findall(r"\d+", x), _re.findall(r"\d+", y)
            if dx and dy and dx != dy:
                return False  # different numbers are different identifiers (loan, lot, account), however alike
            if x == y or difflib.SequenceMatcher(None, x, y).ratio() >= th:
                return True
            a_, b_ = x.split(), y.split()
            short, long_ = (a_, b_) if len(a_) <= len(b_) else (b_, a_)
            return bool(short) and len("".join(short)) >= 3 and long_[:len(short)] == short
        groups = []
        for n in uniq:
            k = name_key_py(n)
            for g in groups:
                if any(same(name_key_py(m), k) for m in g):
                    g.append(n)
                    break
            else:
                groups.append([n])
        return sorted([g for g in groups], key=lambda g: -len(g))

    BENFORD = [Decimal(0)] + [(Decimal(1) + Decimal(1) / d).ln() / Decimal(10).ln() for d in range(1, 10)]

    @bi("benford", 1)
    def _benford(it_, node, amounts):
        """first-digit counts vs Benford's law: MAD (Nigrini: <0.006 close, <0.012 acceptable, <0.015 marginal,
        else nonconforming), chi-square (8 df; 15.51 is the 5% line), and the share of round amounts (whole $100s)"""
        vals = []
        for a in as_list(amounts, node):
            v = T.strip(a)
            v = v.cents if isinstance(v, T.Money) else int(v * 100)
            if v != 0:
                vals.append(abs(v))
        n = len(vals)
        if n == 0:
            raise it.err("benford of no amounts", node)
        counts = [0] * 10
        for v in vals:
            counts[int(str(v)[0])] += 1
        rows, mad, chi = [], Decimal(0), Decimal(0)
        for dgt in range(1, 10):
            obs = Decimal(counts[dgt]) / n
            exp = BENFORD[dgt]
            mad += abs(obs - exp)
            chi += (Decimal(counts[dgt]) - exp * n) ** 2 / (exp * n)
            rows.append({"digit": Decimal(dgt), "count": Decimal(counts[dgt]), "share": obs.quantize(Decimal("0.001")),
                         "expected": exp.quantize(Decimal("0.001"))})
        mad = mad / 9
        cls = ("close" if mad < Decimal("0.006") else "acceptable" if mad < Decimal("0.012") else
               "marginal" if mad < Decimal("0.015") else "nonconforming")
        rnd = sum(1 for v in vals if v % 10000 == 0)
        return {"n": Decimal(n), "digits": rows, "mad": mad.quantize(Decimal("0.0001")), "conformity": cls,
                "chi_square": chi.quantize(Decimal("0.01")), "round_hundreds": Decimal(rnd),
                "round_share": (Decimal(rnd) / n).quantize(Decimal("0.001")),
                "small_sample": n < 100}
