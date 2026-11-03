"""Tally's experimental workflows — the case's experiment patterns as built-in functions.

    let r = rng(7)                                   seeded randomness: rand_int(r, a, b), rand_choice(r, xs), shuffled(r, xs)
    shift_dates(rows, "day", r, 30, @2030-01-01, @2030-12-31)   circular calendar shift (the timing null)
    shuffled_field(rows, "cls", r)                   permute one field across rows (the label null)
    resample(rows, r)                                bootstrap resample

    experiment({                                     falsifiable experiment, pre-registered
      name: "…", question: "…", null: "…",
      measure: fn(world) => NUMBER,                  the statistic, on any world
      real: WORLD,                                   the record
      null_world: fn(r) => WORLD,                    one world drawn under the null
      holds_if: fn(x) => BOOL,                       decided BEFORE running: x = {observed, mean, sd, p, z, runs}
      runs: 1000, seed: 7,
      known_null: fn(r) => WORLD,                    optional known-answer test: a world where the effect is absent
      log: true                                      append to experiments/log.jsonl (default true)
    })  -> {verdict: "HOLDS" | "FAILS" | "INSTRUMENT_FAILS", observed, mean, sd, p, z, runs, seed, known_answer}

    grid({method: ["fifo", "pro_rata"], order: [...]})  every combination, as maps
    sensitivity(rows, "metric")                      per factor: how far the metric moves across its values
    knockout(?goal)                                  every base fact the goal rests on: remove it, re-infer, what falls
    p_stands(?goal, {native: 0.98, derived: 0.85, memory: 0.7}, runs, seed)
                                                     sample worlds where each base fact holds at its tier's rate

The verdict is computed from holds_if, never chosen after seeing the numbers; a FAILS is reported as plainly as a HOLDS.
"""
import datetime as _dt
import json
import os
import random
import time
from decimal import Decimal

import tally as T

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, "experiments", "log.jsonl")


class Rng:
    __slots__ = ("r", "seed")

    def __init__(self, seed):
        self.seed = seed
        self.r = random.Random(seed)


WORLD_MODEL = None


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    def rng_of(x, node):
        x = T.strip(x)
        if not isinstance(x, Rng):
            raise it.err(f"expected an rng (from rng(seed)), got {T.type_name(x)}", node)
        return x.r

    def as_list(x, node):
        x = T.strip(x)
        if not isinstance(x, list):
            raise it.err(f"expected a list, got {T.type_name(x)}", node)
        return x

    def get_field(row, field, node):
        r = T.strip(row)
        if isinstance(r, dict):
            if field not in r:
                raise it.err(f"row has no field '{field}'", node)
            return r[field]
        if isinstance(r, T.Record):
            if field not in r.vals:
                raise it.err(f"{r.type.name} has no field '{field}'", node)
            return r.vals[field]
        raise it.err(f"rows must be maps or records, got {T.type_name(r)}", node)

    def with_field(row, field, value):
        r = T.strip(row)
        if isinstance(r, dict):
            out = dict(r)
            out[field] = value
            return out
        out = T.Record(r.type, dict(r.vals))
        out.vals[field] = value
        return out

    @bi("rng", 1)
    def _rng(it_, node, seed):
        """seeded randomness: the same seed gives the same draws on every machine"""
        return Rng(int(T.strip(seed)))

    @bi("rand_int", 3)
    def _rand_int(it_, node, r, a, b):
        """a whole number from a to b inclusive"""
        return Decimal(rng_of(r, node).randint(int(T.strip(a)), int(T.strip(b))))

    @bi("rand_choice", 2)
    def _rand_choice(it_, node, r, xs):
        """one item of a list"""
        lst = as_list(xs, node)
        if not lst:
            raise it.err("rand_choice of an empty list", node)
        return rng_of(r, node).choice(lst)

    @bi("shuffled", 2)
    def _shuffled(it_, node, r, xs):
        """a shuffled copy of a list"""
        lst = list(as_list(xs, node))
        rng_of(r, node).shuffle(lst)
        return lst

    @bi("shift_dates", (4, 6))
    def _shift_dates(it_, node, rows, field, r, span, lo=None, hi=None):
        """the calendar null: every row's date moved by ONE random shift in -span..span days, wrapped inside lo..hi"""
        lst = as_list(rows, node)
        f = str(T.strip(field))
        k = rng_of(r, node).randint(-int(T.strip(span)), int(T.strip(span)))
        lo_d, hi_d = (T.strip(lo), T.strip(hi)) if lo is not None else (None, None)
        out = []
        for row in lst:
            d = T.strip(get_field(row, f, node))
            if not isinstance(d, _dt.date):
                raise it.err(f"field '{f}' must be a date", node)
            nd = d + _dt.timedelta(days=k)
            if lo_d is not None:
                width = (hi_d - lo_d).days + 1
                nd = lo_d + _dt.timedelta(days=(nd - lo_d).days % width)
            out.append(with_field(row, f, nd))
        return out

    @bi("shuffled_field", 3)
    def _shuffled_field(it_, node, rows, field, r):
        """the label null: one field's values permuted across the rows; everything else stays"""
        lst = as_list(rows, node)
        f = str(T.strip(field))
        vals = [get_field(x, f, node) for x in lst]
        rng_of(r, node).shuffle(vals)
        return [with_field(x, f, v) for x, v in zip(lst, vals)]

    @bi("resample", 2)
    def _resample(it_, node, rows, r):
        """bootstrap: as many rows, drawn with replacement"""
        lst = as_list(rows, node)
        rr = rng_of(r, node)
        return [rr.choice(lst) for _ in lst]

    @bi("grid", 1)
    def _grid(it_, node, spec):
        """every combination of the factor values, as maps: grid({a: [1, 2], b: ["x"]}) -> [{a: 1, b: "x"}, {a: 2, b: "x"}]"""
        sp = T.strip(spec)
        if not isinstance(sp, dict) or not sp:
            raise it.err("grid needs a map of factor -> list of values", node)
        combos = [{}]
        for k, vals in sp.items():
            vs = as_list(vals, node)
            combos = [dict(c, **{k: v}) for c in combos for v in vs]
        return combos

    @bi("sensitivity", 2)
    def _sensitivity(it_, node, rows, metric):
        """for each factor (every field except the metric): the metric's mean at each value and the spread"""
        lst = [T.strip(x) for x in as_list(rows, node)]
        m = str(T.strip(metric))
        if not lst:
            return []
        factors = [k for k in lst[0] if k != m and not isinstance(T.strip(lst[0][k]), (list, dict))]
        out = []
        for fct in factors:
            by = {}
            for row in lst:
                v = T.strip(row[m])
                v = v.dec() if isinstance(v, T.Money) else v
                by.setdefault(T.show(row[fct]), []).append(v)
            if len(by) < 2:
                continue
            means = {k: sum(v) / len(v) for k, v in by.items()}
            spread = max(means.values()) - min(means.values())
            out.append({"factor": fct, "spread": spread,
                        "means": {k: v.quantize(Decimal("0.01")) for k, v in means.items()}})
        return sorted(out, key=lambda x: -x["spread"])

    def stats_of(vals):
        n = len(vals)
        mean = sum(vals) / n
        var = sum((v - mean) ** 2 for v in vals) / (n - 1) if n > 1 else Decimal(0)
        return mean, var.sqrt() if var > 0 else Decimal(0)

    def as_num(v, node, what):
        v = T.strip(v)
        if isinstance(v, T.Money):
            return v.dec()
        if isinstance(v, bool) or not isinstance(v, Decimal):
            raise it.err(f"{what} must return a number or money, got {T.type_name(v)}", node)
        return v

    @bi("experiment", 1)
    def _experiment(it_, node, spec):
        """a falsifiable experiment: the statistic on the record against the same statistic on null worlds,
        verdict from a rule written before running, a known-answer check, and an append-only log"""
        sp = T.strip(spec)
        need = ["name", "question", "null", "measure", "real", "null_world", "holds_if"]
        missing = [k for k in need if k not in sp]
        if missing:
            raise it.err(f"experiment needs {missing} (pre-register the question, the null and holds_if)", node)
        runs = int(T.strip(sp.get("runs", Decimal(1000))))
        seed = int(T.strip(sp.get("seed", Decimal(7))))
        measure = sp["measure"]
        t0 = time.time()
        observed = as_num(it_.call(measure, [sp["real"]], node), node, "measure")
        r = Rng(seed)
        null_vals = [as_num(it_.call(measure, [it_.call(sp["null_world"], [r], node)], node), node, "measure")
                     for _ in range(runs)]
        mean, sd = stats_of(null_vals)
        ge = sum(1 for v in null_vals if v >= observed)
        p = Decimal(ge + 1) / Decimal(runs + 1)  # never 0: one more world than we drew
        z = (observed - mean) / sd if sd else None
        x = {"observed": observed, "mean": mean.quantize(Decimal("0.0001")), "sd": sd.quantize(Decimal("0.0001")),
             "p": p.quantize(Decimal("0.0001")), "z": z.quantize(Decimal("0.01")) if z is not None else None,
             "runs": Decimal(runs)}
        verdict_real = it_.truth(it_.call(sp["holds_if"], [dict(x)], node), node)
        known = None
        if "known_null" in sp:
            kr = Rng(seed + 1)
            kobs = as_num(it_.call(measure, [it_.call(sp["known_null"], [kr], node)], node), node, "measure")
            kvals = [as_num(it_.call(measure, [it_.call(sp["null_world"], [kr], node)], node), node, "measure")
                     for _ in range(runs)]
            km, ks = stats_of(kvals)
            kp = Decimal(sum(1 for v in kvals if v >= kobs) + 1) / Decimal(runs + 1)
            kx = {"observed": kobs, "mean": km, "sd": ks, "p": kp, "z": (kobs - km) / ks if ks else None,
                  "runs": Decimal(runs)}
            flags = it_.truth(it_.call(sp["holds_if"], [kx], node), node)
            known = {"observed": kobs, "p": kp.quantize(Decimal("0.0001")), "flagged": flags}
        if known is not None and known["flagged"]:
            verdict = "INSTRUMENT_FAILS"  # it also "finds" the effect where the effect was built to be absent
        else:
            verdict = "HOLDS" if verdict_real else "FAILS"
        out = dict(x, name=T.strip(sp["name"]), question=T.strip(sp["question"]), null=T.strip(sp["null"]),
                   verdict=verdict, seed=Decimal(seed), known_answer=known, seconds=round(time.time() - t0, 2))
        if T.strip(sp.get("log", True)) is not False and not os.environ.get("TALLY_NO_EXPERIMENT_LOG"):
            os.makedirs(os.path.dirname(LOG), exist_ok=True)
            row = {k: T.to_json(v) if not isinstance(v, dict) else {a: T.to_json(b) for a, b in v.items()}
                   for k, v in out.items() if v is not None}
            row.update({"at": _dt.datetime.now().isoformat(timespec="seconds"), "program": it_.path,
                        "interpreter": T.interpreter_pin()["sha256"].get("tally.py", "")[:16]})
            with open(LOG, "a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        return out

    # ---------------------------------------------------------------- reasoning experiments
    def goal_fact(q, node):
        import tally_logic as L
        x = T.strip(q)
        if not (isinstance(x, dict) and "pred" in x) or x.get("vars"):
            raise it.err("expected a ground pattern like ?P(a, b)", node)
        return L.key_of(x["pred"], x["args"])

    @bi("knockout", 1)
    def _knockout(it_, node, q):
        """every base fact the goal's proofs use: remove it alone, re-infer, and report whether the goal still stands
        and how many other derived facts fall with it"""
        import tally_logic as L
        k = goal_fact(q, node)
        kb = it_.kb
        L.infer(it_, kb)
        f = kb.all_facts().get(k)
        if f is None:
            return []
        base_ids = sorted(set().union(*L.base_sets(kb, f)))
        before = set(kb.derived)
        out = []
        for bid in base_ids:
            snap = L.snapshot(kb)
            fact = kb.base[bid]
            try:
                del kb.base[bid]
                L.infer(it_, kb)
                stands = k in kb.all_facts()
                fell = sorted(before - set(kb.derived))
            finally:
                L.restore(kb, snap)
            out.append({"fact": fact.text(), "sources": sorted(fact.src), "goal_stands": stands,
                        "also_falls": len([x for x in fell if x != k])})
        L.infer(it_, kb)
        return sorted(out, key=lambda r: (r["goal_stands"], -r["also_falls"]))

    def world_model(it_, node, goal_keys, rates, uncertainty="source_set", exact_rates=False):
        """the record-failure model behind p_stands and the qubit layer: events (records, source sets or facts) each
        holding at a declared rate, and for each goal a test of whether it is still derived when only some events hold.
        Returns {keys, rate, stands(goal_key, alive), sets, ids, facts, hold, unit, missing}"""
        import tally_logic as L
        import tally_data as D
        unc = T.strip(uncertainty)
        derived_from = {}
        if isinstance(unc, dict):
            derived_from = {str(T.strip(kk)): [str(T.strip(x)) for x in T.strip(v)]
                            for kk, v in T.strip(unc.get("derived_from", {})).items()}
            unc = T.strip(unc.get("unit", "source"))
        if unc not in ("source_set", "fact", "source"):
            raise it_.err("uncertainty must be source_set, fact or source (or {unit, derived_from})", node,
                          hint="source: one failure event per record; a fact stands while any record behind it stands")
        rt = {kk: T.strip(v) for kk, v in T.strip(rates).items()}
        kb = it_.kb
        L.infer(it_, kb)
        facts = kb.all_facts()
        sets, missing = {}, []
        for gk in goal_keys:
            f = facts.get(gk)
            if f is None:
                missing.append(gk)
                sets[gk] = []
            else:
                sets[gk] = L.base_sets(kb, f)
        ids = sorted(set().union(*[x for ss in sets.values() for x in ss])) if any(sets.values()) else []

        def rate_for(tier, label):
            if label in rt:
                tier = label  # a rate given for this exact record overrides its tier
            elif tier not in rt:
                raise it_.err(f"no rate for tier '{tier}' (give {sorted(set(D.fact_tier(facts[j]) for j in ids))})",
                              node)
            r = rt[tier]
            if not isinstance(r, Decimal) or not r.is_finite() or not 0 <= r <= 1:
                raise it_.err(f"rate for {tier} must be a finite number from 0 to 1", node)
            return r if exact_rates else float(r)

        hold = {i: rate_for(D.fact_tier(facts[i]), "") for i in ids}
        events, needs = {}, {}
        if unc == "source":
            def chain(src, seen=()):
                out = {("src", src)}
                for parent in derived_from.get(src, []):
                    if parent not in seen:
                        out |= chain(parent, seen + (src,))
                return out
            for i in ids:
                recs = [x for x in facts[i].src if not x.startswith("rule ") and not x.startswith("alias ")]
                cites = [x for x in recs if not x.startswith("file:")]
                if cites:
                    recs = cites  # a file is the container a record was read from, not a second witness to it
                if not recs:
                    events[("fact", i)] = hold[i]
                    needs[i] = [{("fact", i)}]
                    continue
                alts = []
                for r in recs:
                    c = chain(r)
                    for e in c:
                        events.setdefault(e, rate_for(D.source_tier(e[1]), e[1]))
                    alts.append(c)
                needs[i] = alts
        else:
            for i in ids:
                anchors = tuple(sorted(facts[i].src))
                key = ("sources", anchors) if unc == "source_set" and anchors else ("fact", i)
                events[key] = min(events.get(key, 1.0), hold[i])
                needs[i] = [{key}]

        def stands(gk, alive):
            ss = sets[gk]
            if not ss:
                return False
            ok = {i for i in set().union(*ss) if any(alt <= alive for alt in needs[i])}
            return any(x <= ok for x in ss)

        return {"keys": sorted(events, key=str), "rate": events, "stands": stands, "sets": sets, "ids": ids,
                "facts": facts, "hold": hold, "unit": unc, "missing": missing}

    global WORLD_MODEL
    WORLD_MODEL = world_model

    @bi("p_stands", (2, 3, 4, 5))
    def _p_stands(it_, node, q, rates, runs=Decimal(2000), seed=Decimal(7), uncertainty="source_set"):
        """sample worlds: each base fact the goal rests on holds with its source tier's rate (native / derived /
        memory / unknown); the share of worlds where the goal is still derived. uncertainty: "source_set" (facts with
        the same source set fail together), "fact" (every fact on its own), "source" (every record is one event; a
        fact stands while ANY of its records stands, so partly overlapping source sets share exactly the records they
        share), or {unit: "source", derived_from: {record: [records it was copied from]}} (a copy fails with its
        original). With 18 or fewer events the answer is also computed exactly ("exact")."""
        import itertools
        import tally_data as D
        run_count = T.strip(runs)
        if not isinstance(run_count, Decimal) or not run_count.is_finite() or run_count <= 0 or run_count != int(run_count):
            raise it_.err("runs must be a positive whole number", node)
        k = goal_fact(q, node)
        wm = world_model(it_, node, [k], rates, uncertainty)
        if wm["missing"]:
            return {"p": Decimal(0), "runs": runs, "note": "not established on the record as loaded"}
        keys, events, facts, ids, sets = wm["keys"], wm["rate"], wm["facts"], wm["ids"], wm["sets"][k]
        exact = None
        if len(keys) <= 18:
            tot = 0.0
            for bits in itertools.product((True, False), repeat=len(keys)):
                w, alive = 1.0, set()
                for kk, b_ in zip(keys, bits):
                    w *= events[kk] if b_ else 1 - events[kk]
                    if b_:
                        alive.add(kk)
                if w and wm["stands"](k, alive):
                    tot += w
            exact = Decimal(str(round(tot, 6)))
        rr = random.Random(int(T.strip(seed)))
        n = int(T.strip(runs))
        stood = 0
        for _ in range(n):
            alive = {kk for kk in keys if rr.random() < events[kk]}
            if wm["stands"](k, alive):
                stood += 1
        lev = []
        for i in ids:
            others = [x for x in sets if i not in x]
            lev.append({"fact": facts[i].text(), "tier": D.fact_tier(facts[i]), "rate": Decimal(str(wm["hold"][i])),
                        "in_every_proof": not others})
        assumptions = {"source_set": "identical source sets share one event at their minimum rate; other groups independent",
                       "fact": "every base fact fails independently",
                       "source": "one event per record (copies fail with their originals); a fact stands while any record behind it stands"}[wm["unit"]]
        return {"p": (Decimal(stood) / Decimal(n)).quantize(Decimal("0.0001")), "exact": exact, "runs": Decimal(n),
                "proofs": Decimal(len(sets)), "base_facts": lev,
                "uncertainty_unit": wm["unit"], "failure_groups": Decimal(len(events)),
                "assumptions": "declared hold rates; " + assumptions,
                "calibrated": False}
