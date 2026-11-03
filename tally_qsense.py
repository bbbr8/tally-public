"""Tally semantic qubits — what a word meant, where it was used, as a state over its senses.

A word like "deposit", "advance" or "credit" carries several senses. A sense qubit reads the words around each use of
the term and weighs each sense by the cue words (and phrases) a declared lexicon lists for it, plus an even prior of
½ per sense: the state is a measurement under that lexicon, and says so. Amplitudes √p are notation; no quantum
computation is claimed.

    let LEX = {vendor_deposit: ["windows", "slab", "appliances"], payment_to_builder: ["paid", "example company"]}
    sense(text, "deposit", LEX)              a qubit over senses; .cues says which words moved it
    fidelity(q1, q2)                         (Σ √(p q))²: 1 the same meaning, 0 nothing in common
    trace_distance(q1, q2)                   ½ Σ |p − q|: the largest difference in any sense's probability
    mixture([q1, q2], [w1, w2])                the blended state of several uses
    drift(docs, "deposit", LEX)              the sense over time: each use, the flips, and how much meaning depends on
                                             the document (context_bits = Holevo χ = I(document; sense))
    audiences(docs, "deposit", LEX, "author")  the sense per speaker / audience / channel, and their fidelity
"""
import math
import re
from decimal import Decimal

import tally as T
from tally_qubit import Qubit, _bits, Q6

PRIOR = Decimal("0.5")


class SenseQubit(Qubit):
    tally_type = "sense qubit"

    def __init__(self, states, term, cues, uses, cite=""):
        super().__init__(states)
        self.term, self.cues, self.uses, self.cite = term, cues, uses, cite

    def tally_fields(self):
        f = super().tally_fields()
        f.update({"term": self.term, "cues": self.cues, "uses": T.Decimal(self.uses), "cite": self.cite})
        return f


def norm(s):
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9$.,' ]", " ", str(s).lower())).strip()


def term_rx(term):
    t = re.escape(norm(term))
    return re.compile(r"(?<![a-z0-9])" + t + r"(?:s|es)?(?![a-z0-9])")


def read_sense(text, term, lex, window):
    """(weights per sense, cues hit per sense, number of uses) for one text"""
    t = norm(text)
    words = t.split(" ")
    rx = term_rx(term)
    # word index of every use of the term
    starts, pos = [], 0
    offsets = []
    for w in words:
        offsets.append(pos)
        pos += len(w) + 1
    uses = [m.start() for m in rx.finditer(t)]
    idx = []
    for u in uses:
        i = max(j for j, o in enumerate(offsets) if o <= u) if offsets else 0
        idx.append(i)
    weights = {s: PRIOR for s in lex}
    hits = {s: [] for s in lex}
    for i in idx:
        lo, hi = max(0, i - window), min(len(words), i + window + 1)
        ctx = " " + " ".join(words[lo:hi]) + " "
        own = norm(term)
        for s, cues in lex.items():
            for c in cues:
                c_ = norm(c)
                if not c_ or c_ == own:
                    continue
                n = len(re.findall(r"(?<![a-z0-9])" + re.escape(c_) + r"(?![a-z0-9])", ctx))
                if n:
                    weights[s] += n
                    if c not in hits[s]:
                        hits[s].append(c)
    return weights, hits, len(idx)


def as_q(x, node, it):
    v = T.strip(x)
    if isinstance(v, Qubit):
        return v
    raise it.err(f"expected a qubit, got {T.type_name(v)}", node)


def aligned(a, b):
    names = [n for n, _ in a.states] + [n for n, _ in b.states if a.p(n) is None]
    return [(a.p(n) or Decimal(0)) for n in names], [(b.p(n) or Decimal(0)) for n in names]


def fid(a, b):
    pa, pb = aligned(a, b)
    s = sum(math.sqrt(float(x) * float(y)) for x, y in zip(pa, pb))
    return Decimal(str(round(s * s, 6)))


def tdist(a, b):
    pa, pb = aligned(a, b)
    return (sum((abs(x - y) for x, y in zip(pa, pb)), Decimal(0)) / 2).quantize(Q6).normalize()


def mixture(qs, ws):
    tot = sum(ws, Decimal(0))
    names = []
    for q in qs:
        for n, _ in q.states:
            if n not in names:
                names.append(n)
    return Qubit([(n, sum(((q.p(n) or Decimal(0)) * w for q, w in zip(qs, ws)), Decimal(0)) / tot) for n in names])


def chi(qs, ws):
    """Holevo χ for diagonal states = S(mixture) − Σ w S(each) = I(which state; outcome)"""
    tot = sum(ws, Decimal(0))
    m = mixture(qs, ws)
    inner = sum((w / tot * q.entropy() for q, w in zip(qs, ws)), Decimal(0))
    return max(Decimal(0), (m.entropy() - inner)).quantize(Q6).normalize()


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def lexicon(lex, node):
        v = T.strip(lex)
        if not isinstance(v, dict) or len(v) < 2:
            raise it.err("a lexicon is a map of at least two senses to lists of cue words", node,
                         hint='{vendor_deposit: ["windows", "slab"], payment_to_builder: ["paid", "example company"]}')
        out = {}
        for s, cues in v.items():
            cl = T.strip(cues)
            if not isinstance(cl, list) or not cl:
                raise it.err(f"sense {s}: give a non-empty list of cue words", node)
            out[str(s)] = [str(T.strip(c)) for c in cl]
        return out

    def text_of(d, node):
        m = T.strip(d)
        m = m.vals if isinstance(m, T.Record) else m
        if isinstance(m, str):
            return m, {}
        if not isinstance(m, dict):
            raise it.err("each document is a text or a map with text / context / what", node)
        for k in ("text", "context", "what", "production_text"):
            if k in m and isinstance(T.strip(m[k]), str):
                return T.strip(m[k]), m
        raise it.err("a document map needs a text, context or what field", node)

    def one(text, term, lex, window, cite=""):
        w, h, n = read_sense(text, term, lex, window)
        return SenseQubit(list(w.items()), term, {s: c for s, c in h.items() if c}, n, cite)

    @bi("sense", (3, 4))
    def _sense(it_, node, text, term, lex, window=Decimal(12)):
        """the sense of a term in a text, as a qubit over the lexicon's senses: each sense starts at ½ and gains one per
        cue word or phrase within `window` words of a use of the term (plurals count as uses)"""
        t, m = text_of(text, node)
        L = lexicon(lex, node)
        q = one(t, str(T.strip(term)), L, int(T.strip(window)), str(T.strip(m.get("cite", ""))) if m else "")
        if q.uses == 0:
            raise it_.err(f"'{T.strip(term)}' is not used in that text", node)
        return T.wrap(q, T.srcs(text))

    @bi("fidelity", 2)
    def _fidelity(it_, node, a, b):
        """(Σ √(p·q))² over the outcomes of two qubits: 1 the same state, 0 nothing in common"""
        return T.wrap(fid(as_q(a, node, it_), as_q(b, node, it_)), T.srcs(a, b))

    @bi("trace_distance", 2)
    def _trace_distance(it_, node, a, b):
        """½ Σ |p − q|: how far apart two states are (0 same, 1 disjoint)"""
        return T.wrap(tdist(as_q(a, node, it_), as_q(b, node, it_)), T.srcs(a, b))

    @bi("mixture", (1, 2))
    def _mix(it_, node, qs, weights=None):
        """the blended state of several qubits (equal weights unless given)"""
        lst = [as_q(q, node, it_) for q in T.strip(qs)]
        if not lst:
            raise it_.err("mixture: give at least one qubit", node)
        ws = [Decimal(1)] * len(lst) if weights is None else [T.strip(w) for w in T.strip(weights)]
        if len(ws) != len(lst) or any(not isinstance(w, Decimal) or w < 0 for w in ws) or sum(ws) == 0:
            raise it_.err("mixture: one non-negative weight per qubit, not all zero", node)
        return T.wrap(mixture(lst, ws), T.srcs(*T.strip(qs)))

    def read_docs(docs, term, L, window, node):
        out = []
        for d in T.strip(docs):
            t, m = text_of(d, node)
            q = one(t, term, L, window, str(T.strip(m.get("cite", ""))) if m else "")
            if q.uses:
                out.append((m, q, T.srcs(d)))
        return out

    @bi("drift", (3, 4))
    def _drift(it_, node, docs, term, lex, window=Decimal(12)):
        """the sense of a term across documents in time order: per use {day, cite, author, top, p_top, fidelity_prev,
        flip, cues}, the flips (top sense changed), the blended state, mean_entropy (how vague each use is) and
        context_bits (Holevo χ = I(document; sense): how much the meaning depends on which document)"""
        L = lexicon(lex, node)
        rows = read_docs(docs, str(T.strip(term)), L, int(T.strip(window)), node)
        rows.sort(key=lambda r: (str(T.strip(r[0].get("day", ""))), str(T.strip(r[0].get("time", "")))))
        steps, flips, prev = [], [], None
        for m, q, s in rows:
            top = max(q.states, key=lambda x: x[1])
            st = {"day": T.strip(m.get("day")), "cite": T.strip(m.get("cite", "")),
                  "author": T.strip(m.get("author", m.get("who", ""))), "top": top[0],
                  "p_top": top[1].quantize(Q6).normalize(),
                  "fidelity_prev": None if prev is None else fid(prev, q),
                  "flip": prev is not None and max(prev.states, key=lambda x: x[1])[0] != top[0],
                  "cues": {k: v for k, v in q.cues.items()}, "qubit": q}
            steps.append(T.wrap(st, s))
            if st["flip"]:
                flips.append({"day": st["day"], "cite": st["cite"], "from": max(prev.states, key=lambda x: x[1])[0],
                              "to": top[0], "fidelity": st["fidelity_prev"]})
            prev = q
        qs = [q for _, q, _ in rows]
        ws = [Decimal(1)] * len(qs)
        return {"term": str(T.strip(term)), "uses": T.Decimal(len(rows)), "steps": steps, "flips": flips,
                "mixture": mixture(qs, ws) if qs else None,
                "mean_entropy": (sum((q.entropy() for q in qs), Decimal(0)) / len(qs)).quantize(Q6).normalize()
                if qs else None,
                "context_bits": chi(qs, ws) if qs else None}

    @bi("audiences", (4, 5))
    def _audiences(it_, node, docs, term, lex, field, window=Decimal(12)):
        """the sense of a term per group (speaker, audience, channel — the document field named), the fidelity and
        trace distance between every two groups, and context_bits = I(group; sense)"""
        L = lexicon(lex, node)
        f = str(T.strip(field))
        rows = read_docs(docs, str(T.strip(term)), L, int(T.strip(window)), node)
        groups = {}
        for m, q, _ in rows:
            groups.setdefault(str(T.strip(m.get(f, ""))), []).append(q)
        states = {k: mixture(v, [Decimal(1)] * len(v)) for k, v in groups.items()}
        names = list(states)
        pairs = []
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                a, b = states[names[i]], states[names[j]]
                pairs.append({"a": names[i], "b": names[j], "fidelity": fid(a, b), "trace_distance": tdist(a, b)})
        pairs.sort(key=lambda x: x["fidelity"])
        ws = [Decimal(len(groups[k])) for k in names]
        return {"term": str(T.strip(term)), "groups": {k: states[k] for k in names},
                "uses": {k: Decimal(len(groups[k])) for k in names}, "pairs": pairs,
                "context_bits": chi([states[k] for k in names], ws) if names else None}
