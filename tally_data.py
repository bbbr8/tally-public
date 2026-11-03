"""Tally's data layer: native-store search, source tiers, proof strength, distinguishing facts, stats.

    stores()                          the native stores a search can reach (id, covers, present)
    search("deliver orders")          every hit across the stores: {store, cite, day, author, context}
    search_in("gmail", "…")           one store
    absent("…", ["gmail", …])         a documented absence: {phrase, stores_searched, hits: 0} or an error if found
    source_tier("DOC_10001")           native | derived | memory | rule
    strength(?Goal(...))              the weakest base-fact tier in the strongest proof (a proof ceiling)
    distinguishing_facts(?A, ?B)      base facts A's proofs use that B's never do, and the reverse
    stats([…])                        count, sum, min, max, mean, median (money or numbers)

A hit's `context` is the native text around the phrase. NOT FOUND means not in the stores listed — never
"never said". `absent()` refuses to document an absence when the phrase is found, so a program cannot assert
`fact not Said(...)` over a store that contains the words.
"""
import json
import os
import re
from decimal import Decimal

import tally as T

NATIVE_STORES = []
DEPO_DATES = {}
_DOCS = None


def norm_text(t):
    t = t.replace("’", "'").replace("‘", "'").replace("“", '"').replace("”", '"')
    t = t.replace("\r", " ")
    return re.sub(r"\s+", " ", t).lower().strip()


def mountain_time(iso):
    """HH:MM in Mountain time, or '' when the record carries no time"""
    try:
        from zoneinfo import ZoneInfo
        from datetime import datetime
        if not iso or len(iso) <= 10:
            return ""
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            return dt.strftime("%H:%M")
        return dt.astimezone(ZoneInfo("America/Denver")).strftime("%H:%M")
    except Exception:
        return ""


def mountain_day(iso):
    try:
        from zoneinfo import ZoneInfo
        from datetime import datetime
        return datetime.fromisoformat(iso.replace("Z", "+00:00")).astimezone(ZoneInfo("America/Denver")).date().isoformat()
    except Exception:
        return (iso or "")[:10]


def load_docs():
    """[(store_id, cite, day, author, text, spans_or_None, loan, time, to, raw)] — text is normalized for search,
    raw is the original wording for display"""
    global _DOCS
    if _DOCS is not None:
        return _DOCS
    docs = []
    for st in NATIVE_STORES:
        p = os.path.expanduser(st["path"])
        if not os.path.exists(p):
            continue
        if st["kind"] == "source":
            d = json.load(open(p, encoding="utf-8"))
            recs = [v for v in d.values() if isinstance(v, list) and v and isinstance(v[0], dict) and "body" in v[0]]
            for r in (recs[0] if recs else []):
                eml = r.get("source_eml", "")
                eml = eml[0] if isinstance(eml, list) and eml else str(eml)
                m = re.search(r"([^/'\]]+\.eml)", eml)
                loan = str(r.get("loan", ""))
                docs.append((st["id"], f"Source eml {m.group(1) if m else r.get('message_id', '')}",
                             mountain_day(r.get("iso_date", "")), r.get("from", ""), norm_text(r.get("body", "")), None,
                             loan, mountain_time(r.get("iso_date", "")), str(r.get("to", "")),
                             re.sub(r"\s+", " ", r.get("body", ""))))
        elif st["kind"] == "depo":
            d = json.load(open(p, encoding="utf-8"))
            for who, pages in d.items():
                text, spans = [], []
                for pg in sorted(pages, key=lambda x: int(x)):
                    for ln, t in pages[pg]:
                        spans.append((len(" ".join(text)), f"{pg}:{ln}"))
                        text.append(t)
                docs.append((st["id"], f"{who} deposition", DEPO_DATES.get(who, ""), who,
                             norm_text(" ".join(text)), spans, "", "", "", " ".join(text)))
        elif st["kind"] == "gmail":
            for fn in sorted(os.listdir(p)):
                if not fn.endswith(".json"):
                    continue
                d = json.load(open(os.path.join(p, fn), encoding="utf-8"))
                for m in d.get("messages", []):
                    body = m.get("plaintextBody") or m.get("snippet") or ""
                    docs.append((st["id"], f"Gmail {m.get('id', '')}", mountain_day(m.get("date", "")),
                                 m.get("sender", ""), norm_text(body), None, "", mountain_time(m.get("date", "")),
                                 str(m.get("toRecipients", "")), re.sub(r"\s+", " ", body)))
        elif st["kind"] == "texts":
            d = json.load(open(p, encoding="utf-8"))
            for m in d.get("messages", []):
                txt = m.get("production_text") or m.get("first_version_text") or ""
                if not txt.strip():
                    continue
                docs.append((st["id"], f"SMS {m.get('bates', m.get('evidence_unit_id', ''))}",
                             (m.get("datetime_mt") or "")[:10], m.get("speaker", ""), norm_text(txt), None, "",
                             (m.get("datetime_mt") or "")[11:16], str(m.get("production_to_raw", "")).replace("\n", " "),
                             re.sub(r"\s+", " ", txt)))
    _DOCS = docs
    return docs


def depo_cite(doc, pos):
    spans = doc[5]
    best = spans[0][1] if spans else ""
    for off, pl in spans or []:
        if off <= pos:
            best = pl
        else:
            break
    return best


def hits_for(phrase, store_ids=None):
    """whole-word matches only: "owes" must not match inside "lowest"."""
    q = norm_text(phrase)
    rx = re.compile(r"(?<![a-z0-9])" + re.escape(q) + r"(?![a-z0-9])")
    out = []
    for doc in load_docs():
        if store_ids and doc[0] not in store_ids:
            continue
        start = 0
        while True:
            m = rx.search(doc[4], start)
            if not m:
                break
            i = m.start()
            if doc[0] == "depositions":
                cite = f"{doc[1]} {depo_cite(doc, i)}"
                if int(depo_cite(doc, i).split(":")[1] or 0) > 25:
                    start = i + 1
                    continue  # transcript word index, not testimony
            else:
                cite = doc[1]
            out.append({"store": doc[0], "cite": cite, "day": doc[2], "author": doc[3][:60],
                        "loan": doc[6] or "",
                        "context": doc[4][max(0, i - 80):i + len(q) + 80]})
            start = i + 1
    return out


# ------------------------------------------------------------ timeline
def amount_regex(cents):
    """every way a message writes this amount: $55.00 / 55.00 / 55 / 55 (whole dollars only drop cents)"""
    whole, c = divmod(abs(cents), 100)
    comma = f"{whole:,}"
    forms = [f"{comma}.{c:02d}", f"{whole}.{c:02d}"]
    if c == 0:
        forms += [comma, str(whole)]
    alt = "|".join(re.escape(f) for f in sorted(set(forms), key=len, reverse=True))
    return re.compile(r"(?<![0-9.,])\$?\s?(?:" + alt + r")(?![0-9]|[.,][0-9])")


def snippet(raw, rx, width=160):
    m = rx.search(raw)
    if not m:
        return raw[:width]
    a = max(0, m.start() - width // 2)
    return ("…" if a else "") + raw[a:a + width] + ("…" if a + width < len(raw) else "")


def doc_event(doc, quote=None):
    return {"day": doc[2], "time": doc[7], "kind": doc[0], "who": doc[3][:60], "to": doc[8][:80],
            "what": quote if quote is not None else doc[9][:160], "cite": doc[1], "loan": doc[6] or ""}


BANK_DB = os.environ.get("TALLY_BANK_DB", "")


def bank_events(lo, hi):
    import sqlite3
    if not os.path.exists(BANK_DB):
        return []
    con = sqlite3.connect(f"file:{BANK_DB}?mode=ro", uri=True)
    try:
        rows = con.execute("select date, amount, sign, bates, desc_on_stmt from transactions where date between ? and ? "
                           "and type in ('deposit', 'check', 'debit') and bates is not null and bates != '' "
                           "order by date, rowid", [lo, hi]).fetchall()
    finally:
        con.close()
    out = []
    for d, amt, sign, bates, memo in rows:
        c = int((Decimal(str(amt)) * 100).to_integral_value()) * (-1 if sign == "-" else 1)
        out.append({"day": d, "time": "", "kind": "bank", "who": "BANK-DEMO", "to": "", "what": memo,
                    "cite": bates, "loan": "", "amount_cents": c})
    return out


# ------------------------------------------------------------ tiers and strength
TIER_RULES = [
    ("rule", re.compile(r"^rule ")),
    ("native", re.compile(r"(DOC_\d|SOURCE[- ]DEMO|SYN[_ ]\d|EXAMPLE[_ ]\d|Gmail |Source eml|deposition|depo |SMS SYN|\.eml|text 20\d\d|check \d|ENT \d)", re.I)),
    ("memory", re.compile(r"(memory|recollection|recalls|customer says|user_memory)", re.I)),
    ("derived", re.compile(r"(ledger|sheet|BD[123]|packet|workbook|register|cube|summary|sweep|search)", re.I)),
]
TIER_RANK = {"native": 3, "derived": 2, "memory": 1, "unknown": 0}


def source_tier(src):
    for name, rx in TIER_RULES:
        if rx.search(src):
            return name
    return "unknown"


def fact_tier(fact):
    tiers = [source_tier(s) for s in fact.src if not s.startswith("rule ")]
    if not tiers:
        return "unknown"
    return max(tiers, key=lambda t: TIER_RANK[t])


def strength(kb, fact):
    """max over proofs of (min over the proof's base facts of tier) — the strongest proof's weakest link."""
    import tally_logic as L
    facts = kb.all_facts()
    best, best_set = None, None
    for bs in L.base_sets(kb, fact):
        weakest = min((fact_tier(facts[i]) for i in bs), key=lambda t: TIER_RANK[t])
        if best is None or TIER_RANK[weakest] > TIER_RANK[best]:
            best, best_set = weakest, bs
    if best is None:
        return None
    return {"tier": best, "weakest_links": [facts[i].text() for i in sorted(best_set)
                                            if fact_tier(facts[i]) == best],
            "proof": [facts[i].text() for i in sorted(best_set)]}


def distinguishing(kb, fa, fb):
    import tally_logic as L
    facts = kb.all_facts()
    a_sets, b_sets = L.base_sets(kb, fa), L.base_sets(kb, fb)
    a_all = frozenset().union(*a_sets) if a_sets else frozenset()
    b_all = frozenset().union(*b_sets) if b_sets else frozenset()
    return {"only_in_first": [facts[i].text() for i in sorted(a_all - b_all)],
            "only_in_second": [facts[i].text() for i in sorted(b_all - a_all)],
            "shared": [facts[i].text() for i in sorted(a_all & b_all)]}


# ------------------------------------------------------------ builtins
def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def goal_fact(q, node):
        x = T.strip(q)
        if not (isinstance(x, dict) and "pred" in x):
            raise it.err("expected a fact pattern like ?P(a, b)", node)
        import tally_logic as L
        f = it.kb.all_facts().get(L.key_of(x["pred"], x["args"]))
        return f

    def hit_values(hits):
        return [T.wrap({k: v for k, v in h.items()}, {h["cite"]}) for h in hits]

    @bi("stores", 0)
    def _stores(it_, node):
        return [{"id": s["id"], "covers": s["covers"], "present": os.path.exists(os.path.expanduser(s["path"]))}
                for s in NATIVE_STORES]

    def apply_filters(hits, opts, node):
        """opts: {store: "gmail" | [..], author: "alex", from: @date, to: @date} — every key optional"""
        o = T.strip(opts) if opts is not None else {}
        if not isinstance(o, dict):
            raise it.err("search options must be a map like {author: \"alex\", from: @2030-05-01}", node)
        unknown = [k for k in o if k not in ("store", "author", "from", "to", "loan")]
        if unknown:
            raise it.err(f"unknown search option '{unknown[0]}' (store, author, from, to, loan)", node)
        loan = str(T.strip(o["loan"])) if "loan" in o else None
        stores_ = o.get("store")
        if stores_ is not None:
            stores_ = [str(T.strip(x)) for x in (T.strip(stores_) if isinstance(T.strip(stores_), list) else [stores_])]
        author = None
        if "author" in o:
            a_ = T.strip(o["author"])
            author = [str(T.strip(x)).lower() for x in (a_ if isinstance(a_, list) else [a_])]
        lo = T.strip(o.get("from")).isoformat() if o.get("from") is not None else None
        hi = T.strip(o.get("to")).isoformat() if o.get("to") is not None else None
        out = []
        for h in hits:
            if stores_ and h["store"] not in stores_:
                continue
            if loan and h["store"] == "source_eml" and h["loan"] != loan:
                continue
            if author and not any(a_ in h["author"].lower() for a_ in author):
                continue
            if lo and (not h["day"] or h["day"] < lo):
                continue
            if hi and (not h["day"] or h["day"] > hi):
                continue
            out.append(h)
        return out

    @bi("search", (1, 2))
    def _search(it_, node, phrase, opts=None):
        return hit_values(apply_filters(hits_for(str(T.strip(phrase))), opts, node))

    @bi("search_in", 2)
    def _search_in(it_, node, store, phrase):
        ids = [str(T.strip(x)) for x in (T.strip(store) if isinstance(T.strip(store), list) else [store])]
        bad = [i for i in ids if i not in {s["id"] for s in NATIVE_STORES}]
        if bad:
            raise it.err(f"no store named {bad[0]} (stores(): {[s['id'] for s in NATIVE_STORES]})", node)
        return hit_values(hits_for(str(T.strip(phrase)), ids))

    @bi("absent", (2, 3))
    def _absent(it_, node, phrase, stores, opts=None):
        ids = [str(T.strip(x)) for x in T.strip(stores)]
        missing = [i for i in ids if not os.path.exists(os.path.expanduser(
            next(s["path"] for s in NATIVE_STORES if s["id"] == i)))] if all(
            i in {s["id"] for s in NATIVE_STORES} for i in ids) else None
        if missing is None:
            raise it.err("absent(): unknown store id", node)
        if missing:
            raise it.err(f"absent(): store(s) not present on this machine: {missing} — an absence cannot be "
                         f"documented over a store that was not searched", node)
        hits = apply_filters(hits_for(str(T.strip(phrase)), ids), opts, node)
        if hits:
            raise it.err(f"absent(): \"{T.strip(phrase)}\" IS present — {len(hits)} hit(s), first: "
                         f"{hits[0]['cite']} [{hits[0]['day']}]", node,
                         hint="use search() to read the hits; an absence cannot be documented over a store that has it")
        filt = ""
        if opts is not None:
            o = T.strip(opts)
            filt = " where " + ", ".join(f"{k}={T.show(o[k])}" for k in o)
        n_docs = sum(1 for d in load_docs() if d[0] in ids)
        tag = f"absence: \"{T.strip(phrase)}\" not in {'+'.join(ids)}{filt} (searched {n_docs} docs)"
        return T.wrap({"phrase": T.strip(phrase), "stores_searched": ids, "hits": Decimal(0), "source": tag}, {tag})

    def opts_map(o, node, allowed):
        m = T.strip(o) if o is not None else {}
        if not isinstance(m, dict):
            raise it.err("options must be a map", node)
        bad = [k for k in m if k not in allowed]
        if bad:
            raise it.err(f"unknown option '{bad[0]}' ({', '.join(allowed)})", node)
        return m

    def to_value(ev):
        v = {k: x for k, x in ev.items() if k != "amount_cents"}
        v["day"] = T._dt.date.fromisoformat(ev["day"]) if ev["day"] else None
        if "amount_cents" in ev:
            v["amount"] = T.Money(ev["amount_cents"])
        return T.wrap(v, {ev["cite"]})

    def doc_ok(doc, m):
        if "store" in m:
            st = T.strip(m["store"])
            ids = [str(T.strip(x)) for x in (st if isinstance(st, list) else [st])]
            if doc[0] not in ids:
                return False
        if "author" in m:
            au = T.strip(m["author"])
            names = [str(T.strip(x)).lower() for x in (au if isinstance(au, list) else [au])]
            if not any(n in doc[3].lower() for n in names):
                return False
        if "loan" in m and doc[0] == "source_eml" and (doc[6] or "") != str(T.strip(m["loan"])):
            return False
        return True

    @bi("mentions", (1, 2))
    def _mentions(it_, node, amount, opts=None):
        """every native message that writes this exact amount ($55.00 / 55 / 55 …), with time, sender,
        recipients and the original wording around it. opts {store, author, loan, from, to}"""
        m = opts_map(opts, node, ("store", "author", "loan", "from", "to"))
        v = T.strip(amount)
        if not isinstance(v, T.Money):
            raise it.err("mentions needs money", node)
        rx = amount_regex(v.cents)
        lo = T.strip(m["from"]).isoformat() if "from" in m else ""
        hi = T.strip(m["to"]).isoformat() if "to" in m else "9999"
        out = []
        for doc in load_docs():
            if doc[0] == "depositions" or not doc_ok(doc, m) or not (lo <= (doc[2] or "") <= hi):
                continue
            if rx.search(doc[9]):
                out.append(to_value(doc_event(doc, snippet(doc[9], rx))))
        return sorted(out, key=lambda x: (str(T.strip(x)["day"]), T.strip(x)["time"]))

    @bi("messages", (2, 3))
    def _messages(it_, node, a, b, opts=None):
        """every native message (Source mail, Gmail, SMS) dated a..b, in time order. opts {store, author, loan}"""
        m = opts_map(opts, node, ("store", "author", "loan"))
        lo, hi = T.strip(a).isoformat(), T.strip(b).isoformat()
        out = [doc_event(d) for d in load_docs() if d[0] != "depositions" and lo <= (d[2] or "") <= hi and doc_ok(d, m)]
        out.sort(key=lambda e: (e["day"], e["time"] or "99:99"))
        return [to_value(e) for e in out]

    def merged(lo, hi, m):
        evs = bank_events(lo, hi) + [doc_event(d) for d in load_docs()
                                      if d[0] != "depositions" and lo <= (d[2] or "") <= hi and doc_ok(d, m)]
        about = m.get("about")
        if about is not None:
            terms = [T.strip(x) for x in (T.strip(about) if isinstance(T.strip(about), list) else [about])]
            rxs = []
            for t in terms:
                if isinstance(t, T.Money):
                    rxs.append(amount_regex(t.cents))
                else:
                    rxs.append(re.compile(r"(?<![a-z0-9])" + re.escape(norm_text(str(t))) + r"(?![a-z0-9])", re.I))
            def hit(e):
                if e["kind"] == "bank":
                    return any((isinstance(t, T.Money) and abs(t.cents) == abs(e["amount_cents"])) or
                               (not isinstance(t, T.Money) and r.search(e["what"] or "")) for t, r in zip(terms, rxs))
                return any(r.search(e["what"] or "") or r.search(norm_text(e["what"] or "")) for r in rxs)
            full = {d[1]: d[9] for d in load_docs()}
            keep = []
            for e in evs:
                text = full.get(e["cite"], e["what"]) if e["kind"] != "bank" else e["what"]
                probe = dict(e, what=text)
                if hit(probe):
                    if e["kind"] != "bank":
                        r = next((r for r in rxs if r.search(text) or r.search(norm_text(text))), rxs[0])
                        e = dict(e, what=snippet(text, r))
                    keep.append(e)
            evs = keep
        kind_rank = {"bank": 1}
        evs.sort(key=lambda e: (e["day"], e["time"] or "99:99", kind_rank.get(e["kind"], 0)))
        return [to_value(e) for e in evs]

    @bi("timeline", (2, 3))
    def _timeline(it_, node, a, b, opts=None):
        """bank lines and native messages dated a..b in one sequence (within a day by time; bank lines carry no time
        and sort last). opts {store, author, loan, about: [payee names or amounts]}"""
        m = opts_map(opts, node, ("store", "author", "loan", "about"))
        return merged(T.strip(a).isoformat(), T.strip(b).isoformat(), m)

    @bi("around", (3, 4))
    def _around(it_, node, day, before, after, opts=None):
        """the timeline from `before` days before `day` to `after` days after it; opts as timeline"""
        m = opts_map(opts, node, ("store", "author", "loan", "about"))
        d = T.strip(day)
        lo = (d - T._dt.timedelta(days=int(T.strip(before)))).isoformat()
        hi = (d + T._dt.timedelta(days=int(T.strip(after)))).isoformat()
        return merged(lo, hi, m)

    @bi("source_tier", 1)
    def _tier(it_, node, s):
        return source_tier(str(T.strip(s)))

    @bi("strength", 1)
    def _strength(it_, node, q):
        f = goal_fact(q, node)
        return None if f is None else strength(it_.kb, f)

    @bi("distinguishing_facts", 2)
    def _dist(it_, node, qa, qb):
        fa, fb = goal_fact(qa, node), goal_fact(qb, node)
        if fa is None or fb is None:
            raise it.err("distinguishing_facts: both conclusions must be established first (run infer())", node)
        return distinguishing(it_.kb, fa, fb)

    @bi("stats", 1)
    def _stats(it_, node, xs):
        xs = T.strip(xs)
        if not isinstance(xs, list) or not xs:
            raise it.err("stats needs a non-empty list", node)
        vals = [T.strip(x) for x in xs]
        money = all(isinstance(v, T.Money) for v in vals)
        nums = [v.dec() if isinstance(v, T.Money) else v for v in vals]
        if not all(isinstance(v, Decimal) for v in nums):
            raise it.err("stats needs numbers or money", node)
        n = len(nums)
        s_ = sorted(nums)
        median = s_[n // 2] if n % 2 else (s_[n // 2 - 1] + s_[n // 2]) / 2
        mean = sum(nums) / n
        src = T.srcs(*xs)
        def out(v):
            return T.wrap(T.Money.from_decimal(v) if money and (v * 100) == (v * 100).to_integral_value() else v, src)
        return {"count": Decimal(n), "sum": out(sum(nums)), "min": out(min(nums)), "max": out(max(nums)),
                "mean": T.wrap(mean, src), "median": out(median)}
