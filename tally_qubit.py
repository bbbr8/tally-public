"""Tally qubit layer — conclusions as states over outcomes, with amplitudes as notation over exact probabilities.

No quantum computation is claimed. A qubit here is a finite distribution over named outcomes, written in Dirac notation
with amplitudes √p; its entropy says how unsettled it is (0 bits settled, 1 bit an even split of two outcomes). A
register is a joint state over several conclusions, built from the record-failure model behind p_stands: conclusions
that rest on the same records are statistically dependent. This is a classical model, distinct from tally_quantum.

    qubit({advance: 0.7, price: 0.3})        a state; qubit(["a", "b"]) is the even split
    prob(q, "advance") · entropy(q) · purity(q) · ket(q)
    observe(q, {advance: 3, price: 1})       evidence: multiply by likelihoods, renormalize (partial collapse)
    measure(q, "advance")                    full collapse to one outcome
    truth_qubit(?G, rates, unit)             |stands⟩ / |falls⟩ for a conclusion, exact from its records
    register([?G1, ?G2], rates, unit)        the joint state of several conclusions; .marginals .mutual .joint
    given(reg, ?G1, "falls")                 collapse one conclusion and see what the others become
    given_record(reg, "DOC_00164", false)     collapse one record (checked: holds or fails)
    best_check(reg)                          which record to check first: expected bits of uncertainty removed
    belnap(?G)                               T / F / B (both: conflicted) / N (neither)
"""
import itertools
import math
import random
from decimal import Decimal

import tally as T

Q6 = Decimal("0.000001")


def _d(x):
    return x if isinstance(x, Decimal) else Decimal(str(x))


def _bits(ps):
    h = 0.0
    for p in ps:
        p = float(p)
        if p > 0:
            h -= p * math.log2(p)
    return Decimal(str(round(h + 0.0, 6)))


class Qubit:
    """a state over named outcomes; probabilities are exact decimals that add to 1"""
    tally_type = "qubit"

    def __init__(self, states):
        states = [(n, _d(p)) for n, p in states]
        tot = sum((p for _, p in states), Decimal(0))
        self.states = [(n, (p / tot)) for n, p in states]

    def p(self, name):
        for n, p in self.states:
            if n == name:
                return p
        return None

    def entropy(self):
        return _bits(p for _, p in self.states)

    def purity(self):
        return sum(p * p for _, p in self.states).quantize(Q6).normalize()

    def ket(self):
        parts = []
        for n, p in self.states:
            if p > 0:
                parts.append(f"{Decimal(str(math.sqrt(float(p)))).quantize(Decimal('0.001'))}|{n}⟩")
        return " + ".join(parts) if parts else "0"

    def tally_show(self):
        return self.ket()

    def tally_eq(self, other):
        return [(n, p.quantize(Q6)) for n, p in self.states] == [(n, p.quantize(Q6)) for n, p in other.states]

    def tally_fields(self):
        top = max(self.states, key=lambda s: s[1])
        return {"p": {n: p.quantize(Q6).normalize() for n, p in self.states},
                "states": [n for n, _ in self.states], "entropy": self.entropy(), "purity": self.purity(),
                "ket": self.ket(), "top": top[0], "settled": self.entropy() == 0}


class Register:
    """the joint state of several conclusions over a common set of record events"""
    tally_type = "register"

    def __init__(self, labels, worlds, events, rates, method, diagnostics=None):
        # worlds: list of (alive frozenset of events, weight Decimal, outcome tuple of bools)
        self.labels, self.worlds, self.events, self.rates, self.method = labels, worlds, events, rates, method
        self.diagnostics = dict(diagnostics or {})
        self.support_sources = set()

    def joint(self):
        out = {}
        for _, w, o in self.worlds:
            out[o] = out.get(o, Decimal(0)) + w
        tot = sum(out.values()) or Decimal(1)
        return {o: p / tot for o, p in out.items()}

    def marginal(self, i):
        j = self.joint()
        s = sum((p for o, p in j.items() if o[i]), Decimal(0))
        return Qubit([("stands", s), ("falls", 1 - s)])

    def entropy(self):
        return _bits(self.joint().values())

    def mutual(self):
        j = self.joint()
        out = []
        for a, b in itertools.combinations(range(len(self.labels)), 2):
            pab = {}
            for o, p in j.items():
                pab[(o[a], o[b])] = pab.get((o[a], o[b]), Decimal(0)) + p
            pa = {v: sum(p for (x, _), p in pab.items() if x == v) for v in (True, False)}
            pb = {v: sum(p for (_, y), p in pab.items() if y == v) for v in (True, False)}
            mi = 0.0
            for (x, y), p in pab.items():
                if p > 0 and pa[x] > 0 and pb[y] > 0:
                    mi += float(p) * math.log2(float(p) / (float(pa[x]) * float(pb[y])))
            # correlation of the two stands-indicators
            ea, eb, eab = pa[True], pb[True], pab.get((True, True), Decimal(0))
            va, vb = ea * (1 - ea), eb * (1 - eb)
            corr = None if va == 0 or vb == 0 else Decimal(str(round(float(eab - ea * eb) / math.sqrt(float(va * vb)), 6)))
            out.append({"a": self.labels[a], "b": self.labels[b], "bits": Decimal(str(round(max(mi, 0.0), 6))),
                        "correlation": corr, "dependent": mi > 1e-9, "entangled": mi > 1e-9})
        return out

    def condition(self, keep):
        ws = [(a, w, o) for a, w, o in self.worlds if keep(a, o)]
        if not ws or sum(w for _, w, _ in ws) == 0:
            return None
        info = dict(self.diagnostics, conditioned=True, retained_worlds=Decimal(len(ws)))
        out = Register(self.labels, ws, self.events, self.rates, self.method, info)
        out.support_sources = set(self.support_sources)
        return out

    def tally_show(self):
        return "register(" + ", ".join(f"{l}: {self.marginal(i).ket()}" for i, l in enumerate(self.labels)) + ")"

    def tally_eq(self, other):
        return self is other

    def tally_fields(self):
        j = self.joint()
        rows = []
        for o, p in sorted(j.items(), key=lambda kv: -kv[1]):
            rows.append({"outcome": {l: ("stands" if v else "falls") for l, v in zip(self.labels, o)},
                         "p": p.quantize(Q6).normalize()})
        return {"goals": list(self.labels), "joint": rows,
                "marginals": {l: self.marginal(i) for i, l in enumerate(self.labels)},
                "all_stand": sum((p for o, p in j.items() if all(o)), Decimal(0)).quantize(Q6).normalize(),
                "entropy": self.entropy(), "mutual": self.mutual(), "events": Decimal(len(self.events)),
                "method": self.method, "diagnostics": dict(self.diagnostics)}


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def as_qubit(x, node, what="a qubit"):
        v = T.strip(x)
        if isinstance(v, Qubit):
            return v
        raise it.err(f"expected {what}, got {T.type_name(v)}", node, hint="make one with qubit({a: 0.5, b: 0.5})")

    def goal_key(q, node):
        import tally_logic as L
        x = T.strip(q)
        if not (isinstance(x, dict) and "pred" in x and "args" in x) or x.get("vars"):
            raise it.err("expected a ground pattern like ?P(a, b)", node)
        args = [it.kb.canon(a) for a in x["args"]]
        label = x["pred"] + "(" + ",".join(T.show(a, True) for a in args) + ")"
        return L.key_of(x["pred"], args), label

    @bi("qubit", 1)
    def _qubit(it_, node, spec):
        """a state over named outcomes: qubit({advance: 0.7, price: 0.3}) (weights are normalized) or qubit(["a", "b"])
        for an even split"""
        v = T.strip(spec)
        if isinstance(v, list):
            names = [str(T.strip(x)) for x in v]
            if not names or len(set(names)) != len(names):
                raise it_.err("qubit: give distinct outcome names", node)
            return T.wrap(Qubit([(n, Decimal(1)) for n in names]), T.all_sources(spec))
        if isinstance(v, dict):
            st = []
            for k, w in v.items():
                w = T.strip(w)
                if not isinstance(w, Decimal) or not w.is_finite() or w < 0:
                    raise it_.err(f"qubit: the weight of {k} must be a non-negative number", node)
                st.append((str(k), w))
            if not st or sum(w for _, w in st) == 0:
                raise it_.err("qubit: the weights must not all be zero", node)
            return T.wrap(Qubit(st), T.all_sources(spec))
        raise it_.err("qubit takes a map of weights or a list of outcome names", node)

    @bi("prob", 2)
    def _prob(it_, node, q, state):
        """the probability of one outcome of a qubit"""
        qb = as_qubit(q, node)
        p = qb.p(str(T.strip(state)))
        if p is None:
            raise it_.err(f"the qubit has no outcome '{T.strip(state)}' (it has {[n for n, _ in qb.states]})", node)
        return T.wrap(p.quantize(Q6).normalize(), T.all_sources([q, state]))

    @bi("entropy", 1)
    def _entropy(it_, node, q):
        """bits of uncertainty: 0 settled, 1 an even split of two outcomes (qubit or register)"""
        v = T.strip(q)
        if isinstance(v, Register):
            return T.wrap(v.entropy(), T.all_sources(q))
        return T.wrap(as_qubit(q, node, "a qubit or register").entropy(), T.all_sources(q))

    @bi("purity", 1)
    def _purity(it_, node, q):
        """Σ p² — 1 for a settled state, 1/n for an even split of n"""
        return T.wrap(as_qubit(q, node).purity(), T.all_sources(q))

    @bi("ket", 1)
    def _ket(it_, node, q):
        """the state in Dirac notation, amplitudes √p"""
        return T.wrap(as_qubit(q, node).ket(), T.all_sources(q))

    @bi("observe", 2)
    def _observe(it_, node, q, likelihoods):
        """evidence on a qubit: each outcome's weight times its likelihood (how expected the evidence is under that
        outcome), renormalized — a partial collapse. Outcomes not named keep likelihood 1"""
        qb = as_qubit(q, node)
        if not isinstance(T.strip(likelihoods), dict):
            raise it_.err("observe: likelihoods must be a map", node)
        lk = {str(k): T.strip(v) for k, v in T.strip(likelihoods).items()}
        for k, v in lk.items():
            if qb.p(k) is None:
                raise it_.err(f"observe: the qubit has no outcome '{k}'", node)
            if not isinstance(v, Decimal) or not v.is_finite() or v < 0:
                raise it_.err("observe: likelihoods are non-negative numbers", node)
        st = [(n, p * lk.get(n, Decimal(1))) for n, p in qb.states]
        if sum(p for _, p in st) == 0:
            raise it_.err("observe: the evidence is impossible under every outcome with weight", node)
        return T.wrap(Qubit(st), T.all_sources([q, likelihoods]))

    @bi("measure", 2)
    def _measure(it_, node, q, state):
        """full collapse: the qubit becomes the one outcome (an error if that outcome had probability 0)"""
        qb = as_qubit(q, node)
        s = str(T.strip(state))
        p = qb.p(s)
        if p is None or p == 0:
            raise it_.err(f"measure: outcome '{s}' has probability 0 or does not exist", node)
        return T.wrap(Qubit([(n, Decimal(1) if n == s else Decimal(0)) for n, _ in qb.states]), T.srcs(q, state))

    def build_register(it_, node, goals, rates, unit, options=None):
        import tally_experiments as X
        gl = T.strip(goals)
        if not isinstance(gl, list) or not gl:
            raise it_.err("register: give a list of goals like [?A(1), ?B(1)]", node)
        if len(gl) > 32:
            raise it_.err("register: at most 32 goals are supported", node)
        keys, labels = zip(*[goal_key(x, node) for x in gl])
        if len(set(labels)) != len(labels):
            raise it_.err("register: goals must be distinct", node)
        opts = T.strip(options) if T.strip(options) is not None else {}
        allowed = {"method", "max_exact_events", "runs", "seed"}
        if not isinstance(opts, dict) or set(opts) - allowed:
            raise it_.err("register: options are method, max_exact_events, runs, seed", node)
        method = T.strip(opts.get("method", "auto"))
        if method not in ("auto", "exact", "sampled"):
            raise it_.err('register: method must be "auto", "exact" or "sampled"', node)
        def whole(name, default, lo, hi):
            v = T.strip(opts.get(name, Decimal(default)))
            if not isinstance(v, Decimal) or not v.is_finite() or v != int(v) or not lo <= v <= hi:
                raise it_.err(f"register: {name} must be a whole number from {lo} to {hi}", node)
            return int(v)
        cap, runs, seed = whole("max_exact_events", 16, 0, 16), whole("runs", 20000, 1, 100000), whole("seed", 7, 0, 2**63 - 1)
        if not isinstance(T.strip(rates), dict):
            raise it_.err("register: rates must be a map", node)
        wm = X.WORLD_MODEL(it_, node, list(keys), rates, unit, exact_rates=True)
        evs = wm["keys"]
        if len(evs) > 256:
            raise it_.err("register: at most 256 record events are supported", node)
        rate = {e: _d(r) for e, r in wm["rate"].items()}
        varying = [e for e in evs if 0 < rate[e] < 1]
        fixed = {e for e in evs if rate[e] == 1}
        if method == "exact" and len(varying) > cap:
            raise it_.err(f"register: {len(varying)} uncertain events exceed max_exact_events {cap}; choose sampled", node)
        exact = method != "sampled" and len(varying) <= cap
        worlds = []
        if exact:
            for bits in itertools.product((True, False), repeat=len(varying)):
                it_.tick(node)
                w, alive = Decimal(1), set(fixed)
                for e, held in zip(varying, bits):
                    it_.tick(node)
                    w *= rate[e] if held else 1 - rate[e]
                    if held:
                        alive.add(e)
                worlds.append((frozenset(alive), w, tuple(wm["stands"](k, alive) for k in keys)))
            label = "exact"
        else:
            rr = random.Random(seed)
            for _ in range(runs):
                it_.tick(node)
                alive = set(fixed)
                for e in varying:
                    it_.tick(node)
                    if rr.random() < float(rate[e]):
                        alive.add(e)
                alive = frozenset(alive)
                worlds.append((alive, Decimal(1), tuple(wm["stands"](k, alive) for k in keys)))
            label = f"sampled ({runs} worlds)"
        info = {"schema": "tally.register_model.v1", "unit": wm["unit"], "exact": exact,
                "uncertain_events": Decimal(len(varying)), "worlds": Decimal(len(worlds)),
                "retained_worlds": Decimal(len(worlds)), "runs": None if exact else Decimal(runs),
                "seed": None if exact else Decimal(seed), "conditioned": False, "calibrated": False,
                "missing_goals": [l for k, l in zip(keys, labels) if k in wm["missing"]],
                "semantics": "survival of supplied proof supports under declared event hold rates",
                "assumptions": "independent record events, except explicit shared or derived_from dependencies",
                "scope": "fixed proof supports; does not recompute all rules, defeaters or new deductions per world"}
        out = Register(list(labels), worlds, evs, rate, label, info)
        out.support_sources = set().union(*(wm["facts"][k].src for k in wm["ids"]))
        return out

    @bi("truth_qubit", (2, 3, 4))
    def _truth_qubit(it_, node, q, rates, unit="source", options=None):
        """Classical stands/falls distribution from declared record rates. Optional exact/sampled controls."""
        r = build_register(it_, node, [q], rates, unit, options)
        return T.wrap(r.marginal(0), T.all_sources([q, rates, unit, options]) | r.support_sources)

    @bi("register", (2, 3, 4))
    def _register(it_, node, goals, rates, unit="source", options=None):
        """Classical joint proof-survival model; options: method, max_exact_events, runs, seed. See .diagnostics."""
        r = build_register(it_, node, goals, rates, unit, options)
        return T.wrap(r, T.all_sources([goals, rates, unit, options]) | r.support_sources)

    def as_reg(x, node):
        v = T.strip(x)
        if not isinstance(v, Register):
            raise it.err(f"expected a register, got {T.type_name(v)}", node, hint="register([?A(1), ?B(1)], rates)")
        return v

    @bi("given", 3)
    def _given(it_, node, reg, q, outcome):
        """collapse one conclusion of a register to stands or falls; the rest update with it"""
        r = as_reg(reg, node)
        _, label = goal_key(q, node)
        if label not in r.labels:
            raise it_.err(f"{label} is not in the register ({r.labels})", node)
        o = str(T.strip(outcome))
        if o not in ("stands", "falls"):
            raise it_.err("given: the outcome is \"stands\" or \"falls\"", node)
        i = r.labels.index(label)
        out = r.condition(lambda a, oc: oc[i] == (o == "stands"))
        if out is None:
            raise it_.err(f"given: {label} cannot {o[:-1]} under this model (probability 0)", node)
        return T.wrap(out, T.all_sources([reg, q, outcome]))

    @bi("given_record", 3)
    def _given_record(it_, node, reg, record, holds):
        """collapse one record: checked and it holds (true) or fails (false); every conclusion updates"""
        r = as_reg(reg, node)
        rec = str(T.strip(record))
        h = T.strip(holds)
        if not isinstance(h, bool):
            raise it_.err("given_record: holds is true or false", node)
        ev = [e for e in r.events if e[1] == rec or str(e[1]) == rec]
        if not ev:
            raise it_.err(f"given_record: no event for '{rec}' in the register",
                          node, hint="events are records with unit \"source\": " +
                          ", ".join(str(e[1]) for e in r.events[:8]))
        out = r.condition(lambda a, oc: (ev[0] in a) == h)
        if out is None:
            raise it_.err("given_record: impossible under this model", node)
        return T.wrap(out, T.all_sources([reg, record, holds]))

    @bi("marginal", 2)
    def _marginal(it_, node, reg, q):
        """one conclusion's qubit out of a register"""
        r = as_reg(reg, node)
        _, label = goal_key(q, node)
        if label not in r.labels:
            raise it_.err(f"{label} is not in the register ({r.labels})", node)
        return T.wrap(r.marginal(r.labels.index(label)), T.all_sources([reg, q]))

    @bi("best_check", (1, 2))
    def _best_check(it_, node, reg, costs=None):
        """which record to check first: for each record event, the expected bits of uncertainty about the register's
        conclusions removed by learning whether it holds — and what P(all stand) becomes either way. Largest first"""
        r = as_reg(reg, node)
        raw_costs = T.strip(costs) if T.strip(costs) is not None else {}
        names = {str(e[1]) for e in r.events}
        if not isinstance(raw_costs, dict) or set(raw_costs) - names:
            raise it_.err("best_check: costs must name existing events", node)
        prices = {k: T.strip(v) for k, v in raw_costs.items()}
        if any(not isinstance(v, Decimal) or not v.is_finite() or v <= 0 for v in prices.values()):
            raise it_.err("best_check: costs must be finite positive numbers", node)
        h0 = r.entropy()
        out = []
        for e in r.events:
            for _ in r.worlds:
                it_.tick(node)
            yes = r.condition(lambda a, oc, e=e: e in a)
            no = r.condition(lambda a, oc, e=e: e not in a)
            tot = sum(w for _, w, _ in r.worlds)
            py = sum(w for a, w, _ in r.worlds if e in a) / tot
            hy = yes.entropy() if yes else Decimal(0)
            hn = no.entropy() if no else Decimal(0)
            gain = max(Decimal(0), h0 - (py * hy + (1 - py) * hn))
            cost = prices.get(str(e[1]), Decimal(1))

            def all_p(x):
                if x is None:
                    return None
                return sum((p for o, p in x.joint().items() if all(o)), Decimal(0)).quantize(Q6).normalize()
            out.append({"record": e[1] if e[0] == "src" else str(e[1]), "holds_rate": py.quantize(Q6).normalize(),
                        "prior_rate": r.rates[e].normalize(), "cost": cost,
                        "gain_per_cost": (gain / cost).quantize(Q6).normalize(),
                        "gain_bits": gain.quantize(Q6).normalize(), "all_stand_if_holds": all_p(yes),
                        "all_stand_if_fails": all_p(no)})
        out.sort(key=lambda x: (-x["gain_per_cost"], -x["gain_bits"], str(x["record"])))
        return T.wrap(out, T.all_sources([reg, costs]))

    @bi("belnap", 1)
    def _belnap(it_, node, q):
        """Belnap's four values for a conclusion: "T" true, "F" false, "B" both (asserted both ways: conflicted),
        "N" neither (unknown or open)"""
        import tally_logic as L
        k, _ = goal_key(q, node)
        kb = it_.kb
        if kb.stale and not kb.inferring:
            L.infer(it_, kb)
        if k in kb.conflicted:
            return "B"
        facts = kb.all_facts()
        if k in facts:
            return T.wrap("T", facts[k].src)
        if k + "=false" in facts:
            return T.wrap("F", facts[k + "=false"].src)
        return "N"
