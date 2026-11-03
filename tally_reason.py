"""Tally reasoning functions found missing by tests/reasoning_bench.tly.

    order_of(a, b)            "before" | "after" | "same time" | "same day, order unknown" — a, b: {day, time} maps,
                              dates, or timeline events (time "" or missing = unknown time of day)
    earlier(a, b)             true / false / maybe — the same question as a value a rule guard can use
    why_not(?Goal)            for every rule that could conclude the goal: how far its conditions get, the first one
                              that fails (with bound values), and whether a conflicted fact is what blocks it
    if_wrong("source")        remove every base fact that rests ONLY on that source, re-infer: what falls, what stands
    minimal_support(?Goal)    the smallest set of base facts that proves the goal (and its sources)
    rule_report()             per rule: how many facts it derived in the last infer, and for rules that derived none,
                              the condition predicates with no facts at all
    hypotheses({observations, rivals: {name: {explains: [...], conflicts: [...]}}})
                              rivals ranked by observations explained minus conflicts; for each, the observations
                              that separate it from the next one
    bayes(prior, [likelihood ratios])   posterior probability and odds; each ratio is P(record | claim) / P(record | not)
"""
import datetime as _dt
import re as _re
from decimal import Decimal

import tally as T


def install(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = T.Builtin(name, f, arity)
            return f
        return deco

    # ------------------------------------------------------------ time order
    def moment(x, node):
        v = T.strip(x)
        if isinstance(v, _dt.date):
            return v, ""
        if isinstance(v, dict):
            d = T.strip(v.get("day"))
            t = T.strip(v.get("time", "")) or ""
        elif isinstance(v, T.Record):
            d = T.strip(v.vals.get("day"))
            t = T.strip(v.vals.get("time", "")) or ""
        else:
            raise it.err(f"order needs dates or {{day, time}} maps, got {T.type_name(v)}", node)
        if not isinstance(d, _dt.date):
            raise it.err("order: the day must be a date", node)
        return d, str(t)

    def compare(a, b, node):
        (da, ta), (db, tb) = moment(a, node), moment(b, node)
        if da != db:
            return "before" if da < db else "after"
        if ta and tb:
            return "before" if ta < tb else ("after" if ta > tb else "same time")
        return "same day, order unknown"

    @bi("order_of", 2)
    def _order_of(it_, node, a, b):
        """before / after / same time / same day, order unknown — times compared only when both sides carry one"""
        return T.wrap(compare(a, b, node), T.srcs(a, b))

    @bi("earlier", 2)
    def _earlier(it_, node, a, b):
        """true if a is before b, false if after or at the same time, maybe if the same day with an unknown time"""
        r = compare(a, b, node)
        return T.wrap(True if r == "before" else (T.MAYBE if r == "same day, order unknown" else False), T.srcs(a, b))

    # ------------------------------------------------------------ why not
    def goal_parts(q, node):
        x = T.strip(q)
        if not (isinstance(x, dict) and "pred" in x) or x.get("vars"):
            raise it.err("expected a ground pattern like ?P(a, b)", node)
        return x["pred"], x["args"]

    def cond_text(c, binds, env):
        def arg(p):
            if p.k == "name" and p.a[0] in binds:
                return T.show(binds[p.a[0]], True)
            if p.k == "name":
                return p.a[0]
            return T.show(it.eval(p, env), True) if p.k == "lit" else T.show_src(p)
        if c["kind"] in ("pos", "neg"):
            return ("not " if c["kind"] == "neg" else "") + f"{c['pred']}({', '.join(arg(p) for p in c['args'])})"
        if c["kind"] == "let":
            return f"let {c['name']} = …"
        return T.join_tokens([]) or "a guard"

    @bi("why_not", 1)
    def _why_not(it_, node, q):
        """why a ground goal does not hold: per candidate rule, the conditions met and the first that fails"""
        import tally_logic as L
        pred, args = goal_parts(q, node)
        kb = it_.kb
        L.infer(it_, kb)
        view = L.View(kb)
        conflicted = kb.conflicted
        out = []
        for rule in kb.rules:
            for concl in rule.concls:
                if concl["pred"] != pred:
                    continue
                b0 = L.match_args(it_, concl["args"], args, rule.env, {})
                if b0 is None:
                    continue
                best = {"depth": -1, "binds": b0, "failed": None}

                def walk(i, binds):
                    if i > best["depth"]:
                        best.update(depth=i, binds=binds)
                    if i == len(rule.conds):
                        return True
                    c = rule.conds[i]
                    env = T.Env(rule.env)
                    env.vars.update(binds)
                    if c["kind"] == "pos":
                        found = False
                        for f in view.by_pred.get(c["pred"], []):
                            if not f.truth:
                                continue
                            b = L.match_args(it_, c["args"], f.args, rule.env, binds)
                            if b is not None:
                                found = True
                                if walk(i + 1, b):
                                    return True
                        return False
                    if c["kind"] == "neg":
                        for f in view.by_pred.get(c["pred"], []):
                            if f.truth and L.match_args(it_, c["args"], f.args, rule.env, binds) is not None:
                                return False
                        return walk(i + 1, binds)
                    if c["kind"] == "let":
                        b = dict(binds)
                        b[c["name"]] = it_.eval(c["expr"], env)
                        return walk(i + 1, b)
                    v = T.strip(it_.eval(c["expr"], env))
                    return v is True and walk(i + 1, binds)

                walk(0, b0)
                d = best["depth"]
                if d == len(rule.conds):
                    out.append({"rule": rule.name, "met": T.Decimal(d), "failed": None,
                                "note": "every condition is met — the conclusion is defeated, open or conflicted"})
                    continue
                c = rule.conds[d]
                env = T.Env(rule.env)
                env.vars.update(best["binds"])
                text = cond_text(c, best["binds"], env) if c["kind"] in ("pos", "neg", "let") else \
                    "guard " + T.show_src(c["expr"]) if c["expr"].k != "bin" else \
                    f"{T.show_src(c['expr'].a[1]) if False else ''}"
                if c["kind"] == "guard":
                    text = "guard: " + render_expr(c["expr"], best["binds"])
                blocked = []
                if c["kind"] == "pos":
                    for k, sides in conflicted.items():
                        f = sides["true"]
                        if f.pred == c["pred"] and L.match_args(it_, c["args"], f.args, rule.env, best["binds"]) is not None:
                            blocked.append({"fact": k, "true_sources": sorted(sides["true"].src),
                                            "false_sources": sorted(sides["false"].src)})
                out.append({"rule": rule.name, "met": T.Decimal(d), "of": T.Decimal(len(rule.conds)), "failed": text,
                            "conflicted": blocked})
        return sorted(out, key=lambda r: -r["met"])

    def render_expr(e, binds):
        def r(n):
            if n.k == "name" and n.a[0] in binds:
                return T.show(binds[n.a[0]], True)
            if n.k == "bin":
                return f"{r(n.a[1])} {n.a[0]} {r(n.a[2])}"
            if n.k == "lit":
                return T.show(n.a[0], True)
            if n.k == "name":
                return n.a[0]
            return T.show_src(n)
        return r(e)

    # ------------------------------------------------------------ counterfactual by source
    @bi("if_wrong", 1)
    def _if_wrong(it_, node, source):
        """remove every base fact that rests only on `source` (facts with another source keep it), re-infer, and
        report the derived facts that fall and those that stand"""
        from tally_audit import impact
        src = str(T.strip(source))
        result = impact(it_, src)
        return {"source": src, "removed": result["removed"], "falls": result["falls"], "stands": result["stands"]}

    # ------------------------------------------------------------ smallest explanation
    @bi("minimal_support", 1)
    def _minimal_support(it_, node, q):
        """the smallest set of base facts (fewest facts; then fewest sources) that proves a goal"""
        import tally_logic as L
        pred, args = goal_parts(q, node)
        kb = it_.kb
        L.infer(it_, kb)
        f = kb.all_facts().get(L.key_of(pred, args))
        if f is None:
            return None
        facts = kb.all_facts()
        sets = L.base_sets(kb, f)
        best = min(sets, key=lambda s: (len(s), len(set().union(*[facts[i].src for i in s]))))
        srcs = sorted(set().union(*[facts[i].src for i in best]))
        return T.wrap({"facts": sorted(facts[i].text() for i in best), "size": T.Decimal(len(best)), "sources": srcs,
                       "proofs": T.Decimal(len(sets))}, set(srcs))

    # ------------------------------------------------------------ rule audit
    @bi("suggest_aliases", (0, 1))
    def _suggest_aliases(it_, node, threshold=Decimal("0.85")):
        """names used in base facts that are probably one party (cluster_names over every string argument), with
        how many facts use each name and a ready alias line naming the most-used one first. Suggests only: nothing
        is merged until an alias statement says so"""
        kb = it_.kb
        uses = {}
        for f in list(kb.base.values()) + [c["true"] for c in kb.conflicted.values() if c.get("true")]:
            for a in f.args:
                v = T.strip(a)
                if isinstance(v, str) and any(ch.isalpha() for ch in v):
                    uses[v] = uses.get(v, 0) + 1
        groups = it_.builtins.vars["cluster_names"].fn(it_, node, list(uses), threshold)
        out = []
        for g in groups:
            g = [T.strip(x) for x in g]
            if len(g) < 2:
                continue
            canon_of = {kb.aliases.get(n, n) for n in g}
            if len(canon_of) < 2:
                continue  # already one party
            g.sort(key=lambda n: (-uses[n], n))
            line = "alias " + T.show(g[0], True) + " = " + ", ".join(T.show(n, True) for n in g[1:])
            joint = [n for n in g if _re.search(r"\bor\b", n.lower())]
            out.append({"names": g, "facts": {n: Decimal(uses[n]) for n in g}, "alias": line,
                        "review": ("a payee line names two parties: " + "; ".join(joint)) if joint else ""})
        return out

    @bi("span_relation", 2)
    def _span_relation(it_, node, a, b):
        """how two date spans {from, to} sit in time (Allen's relations): before, meets, overlaps, starts, during,
        finishes, equals, and the inverses (after, met by, overlapped by, started by, contains, finished by).
        A span with to = nil is open-ended"""
        def span(x):
            v = T.strip(x)
            if isinstance(v, _dt.date):
                return v, v
            if not isinstance(v, dict):
                raise it_.err("span_relation needs {from, to} maps or dates", node)
            f_, t_ = T.strip(v.get("from")), T.strip(v.get("to"))
            if not isinstance(f_, _dt.date):
                raise it_.err("a span's from must be a date", node)
            t_ = _dt.date.max if t_ is None else t_
            if not isinstance(t_, _dt.date) or t_ < f_:
                raise it_.err("a span's to must be a date on or after from (or nil for open-ended)", node)
            return f_, t_
        (a1, a2), (b1, b2) = span(a), span(b)
        if a2 < b1:
            r = "before" if (b1 - a2).days > 1 else "meets"
        elif b2 < a1:
            r = "after" if (a1 - b2).days > 1 else "met by"
        elif (a1, a2) == (b1, b2):
            r = "equals"
        elif a1 == b1:
            r = "starts" if a2 < b2 else "started by"
        elif a2 == b2:
            r = "finishes" if a1 > b1 else "finished by"
        elif b1 < a1 and a2 < b2:
            r = "during"
        elif a1 < b1 and b2 < a2:
            r = "contains"
        else:
            r = "overlaps" if a1 < b1 else "overlapped by"
        return T.wrap(r, T.srcs(a, b))

    @bi("closed", 2)
    def _closed(it_, node, pred, source):
        """declare a predicate complete on a source (e.g. every BANK-DEMO line 2030-01-22..2031-04-30 is loaded): then
        not P(…) holds when no P fact matches, and a missing P is false instead of unknown. The declaration is the fact
        Complete("P") from that source, so every conclusion that uses it cites it and falls with if_wrong(source)"""
        import tally_logic as L
        p_ = str(T.strip(pred))
        if not p_[:1].isupper():
            raise it_.err("closed: give the predicate name, e.g. closed(\"PaidTo\", \"source\")", node)
        sv = T.strip(source)
        src = {str(T.strip(x)) for x in sv} if isinstance(sv, list) else {str(sv)}
        it_.kb.add_base(L.Fact("Complete", [p_], True, src, node.line))
        return None

    @bi("allocate", 2)
    def _allocate(it_, node, total, weights):
        """split money by weights to the cent (largest remainder; ties go to the earlier share): the shares always add
        up to the total exactly"""
        t = T.strip(total)
        if not isinstance(t, T.Money):
            raise it_.err("allocate: the total is money", node)
        ws = []
        for w in T.strip(weights):
            v = T.strip(w)
            v = Decimal(v.cents) if isinstance(v, T.Money) else v
            if not isinstance(v, Decimal) or v < 0:
                raise it_.err("allocate: weights are non-negative numbers or money", node)
            ws.append(v)
        tw = sum(ws)
        if not ws or tw == 0:
            raise it_.err("allocate: the weights must not all be zero", node)
        sign = -1 if t.cents < 0 else 1
        cents = abs(t.cents)
        exact = [Decimal(cents) * w / tw for w in ws]
        base = [int(x) for x in exact]
        left = cents - sum(base)
        order = sorted(range(len(ws)), key=lambda i: (-(exact[i] - base[i]), i))
        for i in order[:left]:
            base[i] += 1
        s_ = T.srcs(total, *T.strip(weights))
        return [T.wrap(T.Money(sign * b), s_) for b in base]

    @bi("disagreements", (1, 2))
    def _disagreements(it_, node, pred, value_pos=None):
        """facts of one predicate that agree on every other argument but differ in one (default: the last) — the same
        thing stated with different values, with the sources of each value"""
        import tally_logic as L
        L.infer(it_, it_.kb)
        p_ = str(T.strip(pred))
        groups = {}
        for f in it_.kb.all_facts().values():
            if f.pred != p_ or not f.truth:
                continue
            n = len(f.args)
            vp = n - 1 if value_pos is None else int(T.strip(value_pos))
            if not 0 <= vp < n:
                raise it_.err(f"disagreements: value position {vp} is outside {p_}'s {n} arguments", node)
            key = tuple(T.show(a, True) for i, a in enumerate(f.args) if i != vp)
            groups.setdefault(key, {"same": [a for i, a in enumerate(f.args) if i != vp], "values": {}})
            v = f.args[vp]
            slot = groups[key]["values"].setdefault(T.show(v, True), {"value": T.strip(v), "sources": set()})
            slot["sources"] |= {x for x in f.src if not x.startswith("rule ")} or set(f.src)
        out = []
        for g in groups.values():
            if len(g["values"]) > 1:
                vals = [{"value": v["value"], "sources": sorted(v["sources"])} for v in g["values"].values()]
                out.append({"same": g["same"], "values": vals, "count": Decimal(len(vals))})
        return out

    @bi("abduce", (1, 2))
    def _abduce(it_, node, q, limit=Decimal(10)):
        """what would have to be true for a goal to follow: per rule, the smallest sets of missing facts (and facts
        that would have to be false) that complete a proof, using the facts already on the record for the rest.
        Fewest missing first. A missing fact some rule could derive is marked derivable"""
        import tally_logic as L
        pred, args = goal_parts(q, node)
        kb = it_.kb
        L.infer(it_, kb)
        view = L.View(kb)
        derivable = {c["pred"] for r in kb.rules for c in r.concls}
        found, seen = [], set()
        cap = 2000
        for rule in kb.rules:
            for concl in rule.concls:
                if concl["pred"] != pred:
                    continue
                b0 = L.match_args(it_, concl["args"], args, rule.env, {})
                if b0 is None:
                    continue
                steps = [0]

                def walk(i, binds, needs):
                    steps[0] += 1
                    if steps[0] > cap:
                        return
                    if i == len(rule.conds):
                        key = (rule.name, tuple(sorted(needs)))
                        if key not in seen:
                            seen.add(key)
                            found.append((rule.name, sorted(needs)))
                        return
                    c = rule.conds[i]
                    env = T.Env(rule.env)
                    env.vars.update(binds)
                    if c["kind"] == "pos":
                        for f in view.by_pred.get(c["pred"], []):
                            if f.truth:
                                b = L.match_args(it_, c["args"], f.args, rule.env, binds)
                                if b is not None:
                                    walk(i + 1, b, needs)
                        t = cond_text(c, binds, env)
                        walk(i + 1, binds, needs + [t + (" (derivable)" if c["pred"] in derivable else "")])
                        return
                    if c["kind"] == "neg":
                        blocked = any(f.truth and L.match_args(it_, c["args"], f.args, rule.env, binds) is not None
                                      for f in view.by_pred.get(c["pred"], []))
                        t = cond_text(c, binds, env)
                        walk(i + 1, binds, needs + [t + " must be false (a fact says it is true)"] if blocked else needs)
                        return
                    try:
                        if c["kind"] == "let":
                            b = dict(binds)
                            b[c["name"]] = it_.eval(c["expr"], env)
                            walk(i + 1, b, needs)
                            return
                        v = T.strip(it_.eval(c["expr"], env))
                        if v is True:
                            walk(i + 1, binds, needs)
                        elif v is T.MAYBE:
                            walk(i + 1, binds, needs + ["undecided: " + render_expr(c["expr"], binds)])
                        # a guard that is false on these values closes this path
                    except T.LimitError:
                        raise
                    except T.TallyError:
                        walk(i + 1, binds, needs + ["guard: " + render_expr(c["expr"], binds)])

                walk(0, b0, [])
        # keep only minimal need-sets per rule (drop any that contain a smaller one)
        best = []
        for name, needs in sorted(found, key=lambda x: (len(x[1]), x[0])):
            if any(n2 == name and set(nd2) <= set(needs) for n2, nd2 in best):
                continue
            best.append((name, needs))
        lim = int(T.strip(limit))
        return [{"rule": n, "needs": nd, "missing": Decimal(len(nd))} for n, nd in best[:lim]]

    @bi("rule_report", 0)
    def _rule_report(it_, node):
        """after infer(): each rule's derived-fact count; for a rule that derived nothing, its condition predicates
        that have no facts at all (what it is waiting on)"""
        import tally_logic as L
        kb = it_.kb
        L.infer(it_, kb)
        have = {f.pred for f in kb.all_facts().values()}
        out = []
        for r in kb.rules:
            n = getattr(kb, "fired", {}).get(r.name, 0)
            missing = sorted({c["pred"] for c in r.conds if c["kind"] == "pos" and c["pred"] not in have})
            out.append({"rule": r.name, "fired": T.Decimal(n), "missing": missing,
                        "open": T.Decimal(sum(1 for o in kb.open if o["rule"] == r.name)),
                        "defeated": T.Decimal(sum(1 for d in kb.defeated if d["rule"] == r.name))})
        return out

    # ------------------------------------------------------------ rival hypotheses
    @bi("hypotheses", 1)
    def _hypotheses(it_, node, spec):
        """rank rival explanations of the same observations: explained minus conflicts; `separates` lists the
        observations that tell each rival from the next one (explained by one and not the other, or conflicting)"""
        sp = T.strip(spec)
        obs = [str(T.strip(o)) for o in T.strip(sp.get("observations", []))]
        rivals = T.strip(sp.get("rivals", {}))
        if not obs or not rivals:
            raise it.err("hypotheses needs observations: [...] and rivals: {name: {explains: [...], conflicts: [...]}}",
                         node)
        rows = []
        for name, r in rivals.items():
            r = T.strip(r)
            ex = [str(T.strip(x)) for x in T.strip(r.get("explains", []))]
            co = [str(T.strip(x)) for x in T.strip(r.get("conflicts", []))]
            bad = [x for x in ex + co if x not in obs]
            if bad:
                raise it.err(f"hypotheses: '{bad[0]}' in rival {name} is not one of the observations", node)
            rows.append({"name": name, "explains": ex, "conflicts_with": co, "explained": T.Decimal(len(ex)),
                         "conflicts": T.Decimal(len(co)), "unexplained": [o for o in obs if o not in ex and o not in co],
                         "score": T.Decimal(len(ex) - len(co))})
        rows.sort(key=lambda r: (-r["score"], -r["explained"], r["name"]))
        for i, r in enumerate(rows):
            other = rows[i + 1] if i + 1 < len(rows) else (rows[i - 1] if i else None)
            if other is None:
                r["separates"] = []
                continue
            sep = [o for o in obs if (o in r["explains"]) != (o in other["explains"])
                   or (o in r["conflicts_with"]) != (o in other["conflicts_with"])]
            r["separates"] = sep
            r["compared_with"] = other["name"]
        return rows

    # ------------------------------------------------------------ weight of evidence
    @bi("bayes", (2, 3))
    def _bayes(it_, node, prior, ratios, overlap=Decimal(1)):
        """prior probability updated by likelihood ratios (each = P(record | claim) / P(record | not claim)). A ratio may
        be a map {ratio, family}: records of one family (copies, one witness, one source document) are not independent
        — the strongest counts in full and the rest count (1 - overlap) of their weight (overlap 1, the default: only
        the strongest; 0: treated as independent). Returns {prior, odds, posterior, steps, families}"""
        import math
        p = T.strip(prior)
        if isinstance(p, T.Money) or not isinstance(p, Decimal) or not (0 < p < 1):
            raise it.err("bayes: the prior is a probability strictly between 0 and 1", node)
        rho = T.strip(overlap)
        if not isinstance(rho, Decimal) or not 0 <= rho <= 1:
            raise it.err("bayes: overlap is a number from 0 to 1", node)
        fams, order = {}, []
        for n_, lr in enumerate(T.strip(ratios)):
            v = T.strip(lr)
            fam = f"record {n_ + 1}"
            if isinstance(v, dict):
                fam = str(T.strip(v.get("family", fam)))
                v = T.strip(v.get("ratio"))
            if not isinstance(v, Decimal) or v <= 0:
                raise it.err("bayes: every likelihood ratio is a positive number", node)
            if fam not in fams:
                order.append(fam)
            fams.setdefault(fam, []).append(v)
        odds = p / (1 - p)
        steps, families = [], []
        for fam in order:
            rs = fams[fam]
            if len(rs) == 1:
                eff = rs[0]
            else:
                # strongest in either direction counts fully; the rest are discounted in log space
                logs = sorted((Decimal(str(math.log(float(r)))) for r in rs), key=lambda x: -abs(x))
                tot = logs[0] + (1 - rho) * sum(logs[1:])
                eff = Decimal(str(math.exp(float(tot)))).quantize(Decimal("0.000001"))
            odds = odds * eff
            families.append({"family": fam, "records": Decimal(len(rs)), "ratio": eff})
            steps.append({"ratio": eff, "posterior": (odds / (1 + odds)).quantize(Decimal("0.0001"))})
        return {"prior": p, "odds": odds.normalize(), "posterior": odds / (1 + odds), "steps": steps,
                "families": families}
