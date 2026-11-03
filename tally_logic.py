"""Tally's reasoning layer: facts, rules, inference, explanation, counterfactuals.

    fact Knows("Alex", "service", @2030-04-30) from "SOURCE-DEMO 001234"
    fact not Disclosed("Customer", "service", @2030-05-08) from "search of Gmail 2030-05"
    rule omission {
      when Knows(a, p, t1), Requests(a, "Customer", money, t2), t1 <= t2, not Disclosed("Customer", p, t2)
      => Omission(a, p, money)
    }
    infer()                         # run every rule to a fixpoint
    holds(Omission("Alex", "service", $25.00))   # true / false / nil (unknown)
    facts("Omission")               # every fact with that predicate
    why(Omission(...))              # the derivation tree, down to base facts and their sources
    single_points(Omission(...))    # base facts every derivation depends on — remove one, the conclusion falls
    open_conclusions()              # conclusions blocked only by an UNKNOWN (a `not` with no fact either way)
    conflicts()                     # Conflict(...) facts the rules derived
    suppose { retract Knows("Alex", "service", @2030-04-30) } then { … }   # what-if, then restore

Three-valued truth. A fact is TRUE or FALSE when asserted; otherwise UNKNOWN. `not P(x)` is satisfied by an
explicit FALSE fact; on UNKNOWN the rule's conclusion is recorded as OPEN (with the condition that keeps it
open) and is not usable by other rules. Derived facts carry the union of the sources of the facts that
produced them, plus the rule name.
"""
import copy

import tally as T


def key_of(pred, args):
    return pred + "(" + ",".join(T.show(a, True) for a in args) + ")"


class Fact:
    __slots__ = ("pred", "args", "truth", "src", "supports", "id", "line")

    def __init__(self, pred, args, truth, src, line=0):
        self.pred, self.args, self.truth = pred, list(args), truth
        self.src = frozenset(src)
        self.supports = []  # [(rule_name, [fact ids])] for derived facts
        self.id = key_of(pred, args) + ("" if truth else "=false")
        self.line = line

    def to_map(self):
        return {"pred": self.pred, "args": list(self.args), "truth": self.truth, "sources": sorted(self.src),
                "derived": bool(self.supports)}

    def text(self):
        return key_of(self.pred, self.args) + ("" if self.truth else " = false")


class Rule:
    def __init__(self, name, conds, concls, env, node):
        self.name, self.conds, self.concls, self.env, self.node = name, conds, concls, env, node
        self.unless = []  # defeaters: [{"pred", "args"}]; any TRUE match defeats this rule's conclusion


class QVar:
    """a query variable inside ?P(...) — an unbound lowercase name."""
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name


class KB:
    def __init__(self):
        self.base = {}      # id -> Fact
        self.derived = {}   # id -> Fact
        self.rules = []
        self.open = []      # {"rule", "conclusion", "open_on", "sources"}
        self.defeated = []  # {"rule", "conclusion", "by", "by_sources", "still_established"}
        self.conflicted = {}  # key -> {"true": Fact, "false": Fact}: asserted both ways; neither side is usable
        self.aliases = {}     # other name -> canonical name
        self.stale = False    # a fact, rule or alias changed since the last infer: the next question re-infers
        self.inferring = False

    def all_facts(self):
        d = dict(self.base)
        d.update(self.derived)
        return d

    def lookup(self, pred):
        return [f for f in self.all_facts().values() if f.pred == pred]

    def add_base(self, fact):
        """a second source for the same fact adds to its sources. A fact asserted both true and false is moved
        out of the usable base into `conflicted` with both sides' sources; rules then see it as unknown."""
        self.stale = True
        k = key_of(fact.pred, fact.args)
        side = "true" if fact.truth else "false"
        if k in self.conflicted:
            have = self.conflicted[k][side]
            if have is None:
                self.conflicted[k][side] = fact
            else:
                have.src = have.src | fact.src
            return
        if fact.id in self.base:
            self.base[fact.id].src = self.base[fact.id].src | fact.src
            return
        other = k + ("=false" if fact.truth else "")
        if other in self.base:
            opp = self.base.pop(other)
            self.conflicted[k] = {side: fact, ("false" if fact.truth else "true"): opp}
            return
        self.base[fact.id] = fact

    def canon(self, v):
        """a string argument under its canonical name (sources kept)"""
        x = T.strip(v)
        if isinstance(x, str) and x in self.aliases:
            return T.wrap(self.aliases[x], T.srcs(v))
        return v

    def add_alias(self, canon, names):
        self.stale = True
        for n in names:
            if n == canon:
                continue
            if n in self.aliases and self.aliases[n] != canon:
                raise T.TallyError(f"alias: '{n}' is already an alias of '{self.aliases[n]}'", 0, 0)
            self.aliases[n] = canon
        # facts asserted before the alias are renamed too, and say so
        for k in list(self.base):
            f = self.base[k]
            new_args, renamed = [], []
            for a in f.args:
                x = T.strip(a)
                if isinstance(x, str) and x in self.aliases:
                    renamed.append(x)
                    new_args.append(self.aliases[x])
                else:
                    new_args.append(a)
            if renamed:
                del self.base[k]
                nf = Fact(f.pred, new_args, f.truth, set(f.src) | {f"alias {r} = {self.aliases[r]}" for r in renamed},
                          f.line)
                self.add_base(nf)

    def retract(self, pred, args):
        self.stale = True
        k = key_of(pred, args)
        n = 0
        for kk in (k, k + "=false"):
            if kk in self.base:
                del self.base[kk]
                n += 1
        if k in self.conflicted:
            del self.conflicted[k]
            n += 2
        return n


# ------------------------------------------------------------ pattern matching over values
def is_var(node):
    return node.k == "name" and (node.a[0][:1].islower() or node.a[0] == "_")


def match_args(interp, pats, args, env, binds):
    if len(pats) != len(args):
        return None
    b = dict(binds)
    for p, v in zip(pats, args):
        if is_var(p):
            name = p.a[0]
            if name == "_":
                continue
            if name in b:
                if not T.equal(b[name], v):
                    return None
            else:
                b[name] = v
        else:
            if not T.equal(interp.kb.canon(interp.eval(p, env)), v):
                return None
    return b


class View:
    """the fact base for inference: id -> fact, pred -> facts, and lazily built argument indexes
    (pred, position) -> {value key -> facts}, kept current as facts are added."""
    __slots__ = ("facts", "by_pred", "idx")

    def __init__(self, kb):
        self.facts = kb.all_facts()
        self.by_pred = {}
        self.idx = {}
        for f in self.facts.values():
            self.by_pred.setdefault(f.pred, []).append(f)

    def add(self, f):
        self.facts[f.id] = f
        self.by_pred.setdefault(f.pred, []).append(f)
        for (pred, pos), table in self.idx.items():
            if pred == f.pred and pos < len(f.args):
                table.setdefault(vkey(f.args[pos]), []).append(f)

    def lookup(self, pred, pos, value):
        k = (pred, pos)
        table = self.idx.get(k)
        if table is None:
            table = {}
            for f in self.by_pred.get(pred, []):
                if pos < len(f.args):
                    table.setdefault(vkey(f.args[pos]), []).append(f)
            self.idx[k] = table
        return table.get(vkey(value), [])


def vkey(v):
    """an index key under which T.equal values coincide"""
    v = T.strip(v)
    if isinstance(v, bool):
        return ("b", v)
    if isinstance(v, T.Decimal):
        return ("n", v.normalize())
    return (type(v).__name__, T.show(v, True))


def plan(rule, first):
    """condition order for a semi-naive pass: the delta condition goes first unless a `not` precedes it
    (moving it ahead of a negation could bind a variable the negation meant to leave open)."""
    conds = list(rule.conds)
    if first is None or first == 0:
        return conds
    if any(c["kind"] == "neg" for c in conds[:first]):
        return conds
    return [conds[first]] + conds[:first] + conds[first + 1:]


def run_rule(interp, kb, rule, view=None, delta=None):
    """yields (binds, status, open_on, support_ids) for every way the rule's conditions are met.
    With `delta` (a set of fact ids new in the last round), only matches that use at least one delta fact are
    produced — one pass per positive condition, that condition restricted to the delta (semi-naive)."""
    view = view or View(kb)
    if delta is None:
        yield from walk_conds(interp, rule, list(rule.conds), view, None)
        return
    for idx, c in enumerate(rule.conds):
        if c["kind"] != "pos" or not any(fid in delta for fid in (f.id for f in view.by_pred.get(c["pred"], []))):
            continue
        conds = plan(rule, idx)
        yield from walk_conds(interp, rule, conds, view, (id(c), delta))


def walk_conds(interp, rule, conds, view, restrict):
    by_pred = view.by_pred
    env = T.Env(rule.env)  # reused: guards and lets only read it

    def walk(i, binds, open_on, support):
        interp.tick(rule.node)
        if i == len(conds):
            yield binds, ("OPEN" if open_on else "TRUE"), open_on, support
            return
        c = conds[i]
        kind = c["kind"]
        if kind == "let":
            env.vars = binds
            v = interp.eval(c["expr"], env)
            if c["name"] in binds:
                if T.equal(binds[c["name"]], v):
                    yield from walk(i + 1, binds, open_on, support)
                return
            b = dict(binds)
            b[c["name"]] = v
            yield from walk(i + 1, b, open_on, support)
            return
        if kind == "guard":
            env.vars = binds
            v = interp.eval(c["expr"], env)
            if isinstance(T.strip(v), T.Maybe):  # undecided (a range, or a same-day order): the conclusion is open
                yield from walk(i + 1, binds, open_on + [f"undecided: {T.show_src(c['expr']) if c['expr'].k != 'call' else c['expr'].a[0].a[0] + '(…)'}"],
                                support)
                return
            if interp.truth(v, c["expr"]):
                guarded = dict(binds)
                guarded["__tally_guard_sources__"] = set(binds.get("__tally_guard_sources__", ())) | T.srcs(v)
                yield from walk(i + 1, guarded, open_on, support)
            return
        pats = c["args"]
        if kind == "pos":
            only = restrict[1] if restrict is not None and restrict[0] == id(c) else None
            cands = None
            for pos, p in enumerate(pats):  # an argument already known narrows the candidates through an index
                if is_var(p):
                    if p.a[0] != "_" and p.a[0] in binds:
                        cands = view.lookup(c["pred"], pos, binds[p.a[0]])
                        break
                elif p.k in ("lit",):
                    cands = view.lookup(c["pred"], pos, p.a[0])
                    break
            for f in (cands if cands is not None else by_pred.get(c["pred"], [])):
                interp.tick(rule.node)
                if not f.truth or (only is not None and f.id not in only):
                    continue
                b = match_args(interp, pats, f.args, rule.env, binds)
                if b is not None:
                    yield from walk(i + 1, b, open_on, support + [f.id])
            return
        # negated: satisfied by an explicit false fact; a true fact blocks; nothing either way = OPEN
        matched_true = matched_false = None
        for f in by_pred.get(c["pred"], []):
            b = match_args(interp, pats, f.args, rule.env, binds)
            if b is None:
                continue
            if f.truth:
                matched_true = f
                break
            matched_false = (f, b)
        if matched_true is not None:
            return
        if matched_false is not None:
            f, b = matched_false
            yield from walk(i + 1, b, open_on, support + [f.id])
            return
        # a predicate declared complete (fact Complete("P") from "…") makes absence a fact: not P(…) holds, and
        # the conclusion rests on the completeness claim, so it shows in explain and falls with if_wrong
        for f in by_pred.get("Complete", []):
            if f.truth and T.strip(f.args[0]) == c["pred"] if f.args else False:
                yield from walk(i + 1, binds, open_on, support + [f.id])
                return
        # unknown: carry on with the variables we have, mark open
        env.vars = binds
        desc = c["pred"] + "(" + ", ".join(
            (p.a[0] if is_var(p) else T.show(interp.eval(p, env), True)) if not (is_var(p) and p.a[0] in binds)
            else T.show(binds[p.a[0]], True) for p in pats) + ")"
        yield from walk(i + 1, binds, open_on + [f"not {desc} (unknown)"], support)

    yield from walk(0, {}, [], [])


def conclusion_facts(interp, rule, binds, support_ids, kb, facts=None):
    env = T.Env(rule.env)
    env.vars.update(binds)
    facts = facts if facts is not None else kb.all_facts()
    src = set(binds.get("__tally_guard_sources__", ()))
    for sid in support_ids:
        src |= facts[sid].src
    src.add("rule " + rule.name)
    out = []
    for c in rule.concls:
        args = []
        for p in c["args"]:
            if is_var(p) and p.a[0] in binds:
                args.append(binds[p.a[0]])
            elif is_var(p):
                raise T.TallyError(f"rule {rule.name}: '{p.a[0]}' in the conclusion is not bound by any condition",
                                   p.line, p.col)
            else:
                args.append(interp.eval(p, env))
        out.append(Fact(c["pred"], args, c["truth"], src, rule.node.line))
    return out


MAX_ROUNDS = 1_000_000   # a recursive chain needs one round per link; the fact cap below is the real safeguard
MAX_FACTS = 2_000_000


def infer(interp, kb, max_rounds=MAX_ROUNDS):
    """forward chaining with defeat. A rule with `unless D(...)` has its conclusion withdrawn whenever a defeater
    holds for the same bindings; the world is re-derived until the set of defeats stops changing."""
    kb.stale = True
    kb.inferring = True
    try:
        _infer(interp, kb, max_rounds)
        kb.stale = False
    finally:
        kb.inferring = False


def _infer(interp, kb, max_rounds):
    blocked = {}
    for _ in range(30):
        infer_once(interp, kb, set(blocked), max_rounds)
        found = defeats(interp, kb)
        if set(found) == set(blocked):
            facts = kb.all_facts()
            kb.defeated = []
            for (rname, fid), info in found.items():
                kb.defeated.append(dict(info, rule=rname, still_established=fid in facts))
            return
        blocked = found
    raise T.TallyError("infer(): defeats did not settle — a defeater depends on the conclusion it defeats", 0, 0)


def defeats(interp, kb):
    """{(rule name, conclusion id): {conclusion, by, by_sources}} for every defeater that holds right now."""
    facts = kb.all_facts()
    by_pred = {}
    for f in facts.values():
        if f.truth:
            by_pred.setdefault(f.pred, []).append(f)
    out = {}
    for rule in kb.rules:
        if not rule.unless:
            continue
        for binds, status, open_on, support in run_rule(interp, kb, rule):
            if status != "TRUE":
                continue
            for f in conclusion_facts(interp, rule, binds, support, kb):
                for u in rule.unless:
                    for d in by_pred.get(u["pred"], []):
                        if match_args(interp, u["args"], d.args, rule.env, binds) is not None:
                            out.setdefault((rule.name, f.id), {"conclusion": f.text(), "by": d.text(),
                                                               "by_sources": sorted(d.src)})
                            break
    return out


def goal_preds(node, out):
    """predicates named by ?P(...) goals inside an expression (aggregates and queries in a rule's let/guard)."""
    if node is None:
        return out
    if getattr(node, "k", None) == "goal":
        out.add(node.a[0])
    for x in getattr(node, "a", ()) or ():
        if isinstance(x, T.N):
            goal_preds(x, out)
        elif isinstance(x, (list, tuple)):
            for y in x:
                if isinstance(y, T.N):
                    goal_preds(y, out)
                elif isinstance(y, (list, tuple)):
                    for z in y:
                        if isinstance(z, T.N):
                            goal_preds(z, out)
    return out


def strata(kb):
    """rule -> stratum. A rule that negates, aggregates over, or is defeated by predicate P runs after every
    rule that derives P; a rule that uses P positively runs no earlier than P's rules. A cycle through
    negation or aggregation has no stratification and is an error naming the rules."""
    derives = {}
    for r in kb.rules:
        for c in r.concls:
            derives.setdefault(c["pred"], []).append(r)
    pos, neg = {}, {}
    for r in kb.rules:
        p, n = set(), set()
        for c in r.conds:
            if c["kind"] == "pos":
                p.add(c["pred"])
            elif c["kind"] == "neg":
                n.add(c["pred"])
            else:
                goal_preds(c["expr"], n)
        for u in r.unless:
            n.add(u["pred"])
        pos[r.name], neg[r.name] = p, n
    level = {r.name: 0 for r in kb.rules}
    limit = len(kb.rules) + 1
    changed = True
    while changed:
        changed = False
        for r in kb.rules:
            need = level[r.name]
            for pred in pos[r.name]:
                for q in derives.get(pred, []):
                    need = max(need, level[q.name])
            for pred in neg[r.name]:
                for q in derives.get(pred, []):
                    need = max(need, level[q.name] + 1)
            if need != level[r.name]:
                if need > limit:
                    cyc = sorted(n for n, v in level.items() if v >= limit - 1)
                    raise T.TallyError("rules depend on their own conclusions through `not`, `unless` or an "
                                       f"aggregate, so they have no order: {cyc}", r.node.line, r.node.col)
                level[r.name] = need
                changed = True
    return level


def infer_once(interp, kb, blocked, max_rounds=MAX_ROUNDS):
    kb.derived = {}
    kb.open = []
    seen_open = set()
    level = strata(kb)
    kb.fired = {r.name: 0 for r in kb.rules}
    for stratum in sorted(set(level.values())):
        rules_here = [r for r in kb.rules if level[r.name] == stratum]
        infer_stratum(interp, kb, blocked, rules_here, seen_open, max_rounds)


def infer_stratum(interp, kb, blocked, rules_here, seen_open, max_rounds):
    """semi-naive: round 1 joins everything; each later round only joins matches that use a fact that was new
    (or gained a source) in the round before."""
    delta = None
    view = View(kb)  # kept current as facts are derived: a round costs what is new, not the whole base
    for _ in range(max_rounds):
        interp.tick()
        new = False
        changed = set()
        for rule in rules_here:
            for binds, status, open_on, support in run_rule(interp, kb, rule, view, delta):
                for f in conclusion_facts(interp, rule, binds, support, kb, view.facts):
                    if status == "OPEN":
                        k = (rule.name, f.id, tuple(open_on))
                        if k not in seen_open:
                            seen_open.add(k)
                            kb.open.append({"rule": rule.name, "conclusion": f.text(), "open_on": open_on,
                                            "sources": sorted(f.src)})
                        continue
                    if f.id in kb.base or (rule.name, f.id) in blocked:
                        continue
                    existing = kb.derived.get(f.id)
                    sup = (rule.name, sorted(support))
                    if existing is None:
                        f.supports.append(sup)
                        kb.derived[f.id] = f
                        new = True
                        changed.add(f.id)
                        kb.fired[rule.name] = kb.fired.get(rule.name, 0) + 1
                    elif sup not in existing.supports:
                        existing.supports.append(sup)
                        if not f.src <= existing.src:
                            existing.src = existing.src | f.src
                            changed.add(f.id)
        if not changed:
            return
        for fid in changed:
            if fid not in view.facts:
                view.add(kb.derived[fid])
        if len(kb.derived) > MAX_FACTS:
            raise T.TallyError(f"infer(): more than {MAX_FACTS:,} derived facts — a rule keeps producing new ones", 0, 0)
        delta = changed
    raise T.TallyError(f"infer() did not settle after {max_rounds:,} rounds (a rule keeps producing new facts)", 0, 0)


# ------------------------------------------------------------ explanation
def why_tree(kb, fact, depth=0, seen=()):
    """derivation tree. Proofs that use the same rule over the same base facts (the premises reordered, or a
    symmetric rule firing both ways) are shown once, with how many times they occurred."""
    facts = kb.all_facts()
    node = {"fact": fact.text(), "sources": sorted(fact.src - {s for s in fact.src if s.startswith("rule ")}),
            "proofs": []}
    if fact.id in seen or depth > 40:
        node["cycle"] = True
        return node
    shown = {}
    for rule_name, ids in fact.supports:
        base = frozenset().union(*[frozenset(b) for i in ids for b in base_sets(kb, facts[i])] or [frozenset()])
        k = (rule_name, base)
        if k in shown:
            shown[k]["times"] += 1
            continue
        p = {"rule": rule_name, "times": 1,
             "premises": [why_tree(kb, facts[i], depth + 1, seen + (fact.id,)) for i in ids]}
        shown[k] = p
        node["proofs"].append(p)
    return node


def base_sets(kb, fact, seen=(), cap=500):
    """every way to prove `fact` as a set of base-fact ids (one per distinct proof tree)."""
    if not fact.supports:
        return [frozenset([fact.id])]
    if fact.id in seen:
        return []
    facts = kb.all_facts()
    out = []
    for rule_name, ids in fact.supports:
        combos = [frozenset()]
        for i in ids:
            subs = base_sets(kb, facts[i], seen + (fact.id,), cap)
            combos = [c | s for c in combos for s in subs][:cap]
        out.extend(combos)
    uniq = []
    for c in out:
        if c not in uniq:
            uniq.append(c)
    return uniq[:cap]


def single_points(kb, fact):
    sets = base_sets(kb, fact)
    if not sets:
        return []
    common = frozenset.intersection(*sets)
    facts = kb.all_facts()
    return [{"fact": facts[i].text(), "sources": sorted(facts[i].src)} for i in sorted(common)]


def render_why(tree, indent=0):
    pad = "  " * indent
    s = pad + tree["fact"]
    if tree["sources"]:
        s += "   [" + ", ".join(tree["sources"]) + "]"
    if tree.get("cycle"):
        s += "   (cycle)"
    lines = [s]
    for p in tree["proofs"]:
        times = f" (×{p['times']}, same base facts)" if p.get("times", 1) > 1 else ""
        lines.append(pad + "  by rule " + p["rule"] + times + ":")
        for q in p["premises"]:
            lines.append(render_why(q, indent + 2))
    return "\n".join(lines)


# ------------------------------------------------------------ builtins
def install(it):
    g = it.builtins.vars
    it.kb = KB()

    def bi(name, arity=None):
        def deco(f):
            if name in ("infer", "retract_all"):
                g[name] = T.Builtin(name, f, arity)
                return f

            def fresh(it_, node, *args):
                if it_.kb.stale and not it_.kb.inferring:
                    infer(it_, it_.kb)  # a question never answers from inferences made before the last change
                return f(it_, node, *args)
            fresh.__doc__ = f.__doc__
            g[name] = T.Builtin(name, fresh, arity)
            return f
        return deco

    def goal(x, node):
        x = T.strip(x)
        if not (isinstance(x, dict) and "pred" in x and "args" in x):
            raise it.err("expected a fact pattern like P(a, b) (use the `?P(a, b)` form)", node)
        if x.get("vars"):
            raise it.err(f"?{x['pred']}(…) has unbound names {x['vars']} — use query() to search with variables", node)
        return x["pred"], x["args"]

    def q_match(pattern, fact):
        if fact.pred != pattern["pred"] or len(fact.args) != len(pattern["args"]):
            return None
        b = {}
        for p, v in zip(pattern["args"], fact.args):
            if isinstance(p, QVar):
                if p.name == "_":
                    continue
                if p.name in b:
                    if not T.equal(b[p.name], v):
                        return None
                else:
                    b[p.name] = v
            elif not T.equal(p, v):
                return None
        return b

    @bi("query", 1)
    def _query(it_, node, q):
        """every TRUE fact matching ?P(x, "lit", _): a list of {var: value} maps, each carrying its fact's sources"""
        pat = T.strip(q)
        if not (isinstance(pat, dict) and "pred" in pat):
            raise it.err("query needs a pattern like ?P(x, \"lit\", _)", node)
        out = []
        for f in sorted(it_.kb.all_facts().values(), key=lambda f: f.id):
            if not f.truth:
                continue
            b = q_match(pat, f)
            if b is not None:
                out.append(T.wrap(dict(b), f.src))
        return out

    def agg_rows(q, flt, node):
        pat = T.strip(q)
        if not (isinstance(pat, dict) and "pred" in pat):
            raise it.err("an aggregate needs a pattern like ?Paid(\"Customer\", m, t)", node)
        rows, src = [], set()
        for f in sorted(it.kb.all_facts().values(), key=lambda f: f.id):
            if not f.truth:
                continue
            b = q_match(pat, f)
            if b is None:
                continue
            if flt is not None and not it.truth(it.call(flt, [dict(b)], node), node):
                continue
            rows.append(b)
            src |= f.src
        return pat, rows, src

    @bi("count_of", (1, 2))
    def _count_of(it_, node, q, flt=None):
        """how many TRUE facts match; an optional fn(b) filter sees the bindings"""
        _, rows, src = agg_rows(q, flt, node)
        return T.wrap(T.Decimal(len(rows)), src)

    def agg_values(q, var, flt, node):
        pat, rows, src = agg_rows(q, flt, node)
        v = str(T.strip(var))
        if v not in (pat.get("vars") or []):
            raise it.err(f"'{v}' is not a variable of ?{pat['pred']}(…) (variables: {pat.get('vars') or []})", node)
        return [r[v] for r in rows], src

    @bi("sum_of", (2, 3))
    def _sum_of(it_, node, q, var, flt=None):
        vals, src = agg_values(q, var, flt, node)
        if not vals:
            return T.wrap(T.Decimal(0), src)
        total = vals[0]
        for v in vals[1:]:
            total = it_.binop("+", total, v, node)
        return T.wrap(T.strip(total), src | T.srcs(total))

    @bi("min_of", (2, 3))
    def _min_of(it_, node, q, var, flt=None):
        vals, src = agg_values(q, var, flt, node)
        if not vals:
            return None
        best = vals[0]
        for v in vals[1:]:
            if T.strip(it_.binop("<", v, best, node)):
                best = v
        return T.wrap(T.strip(best), src)

    @bi("max_of", (2, 3))
    def _max_of(it_, node, q, var, flt=None):
        vals, src = agg_values(q, var, flt, node)
        if not vals:
            return None
        best = vals[0]
        for v in vals[1:]:
            if T.strip(it_.binop(">", v, best, node)):
                best = v
        return T.wrap(T.strip(best), src)

    @bi("defeated", 0)
    def _defeated(it_, node):
        """conclusions a rule reached and an `unless` defeater withdrew"""
        return [dict(d) for d in it_.kb.defeated]

    @bi("infer", 0)
    def _infer(it_, node):
        try:
            infer(it_, it_.kb)
        except T.LimitError:
            raise
        except T.TallyError as e:
            if not e.line:
                raise it_.err(e.msg, node)
            if not e.path:
                e.path = it_.path
            raise
        return T.Decimal(len(it_.kb.derived))

    @bi("holds", 1)
    def _holds(it_, node, q):
        pred, args = goal(q, node)
        k = key_of(pred, args)
        facts = it_.kb.all_facts()
        if k in facts:
            return T.wrap(True, facts[k].src)
        if k + "=false" in facts:
            return T.wrap(False, facts[k + "=false"].src)
        return None

    @bi("facts", (0, 1))
    def _facts(it_, node, pred=None):
        fs = it_.kb.all_facts().values() if pred is None else it_.kb.lookup(str(T.strip(pred)))
        return [T.wrap(f.to_map(), f.src) for f in fs]

    @bi("why", 1)
    def _why(it_, node, q):
        pred, args = goal(q, node)
        k = key_of(pred, args)
        facts = it_.kb.all_facts()
        f = facts.get(k) or facts.get(k + "=false")
        if f is None:
            return None
        return why_tree(it_.kb, f)

    def render_plain(tree, depth=0):
        def src_note(t):
            return f" (record: {', '.join(t['sources'])})" if t["sources"] else ""
        if not tree["proofs"]:
            return tree["fact"] + src_note(tree)
        p = tree["proofs"][0]
        parts = [render_plain(q, depth + 1) for q in p["premises"]]
        more = f"; it also follows {len(tree['proofs']) - 1} other way(s)" if len(tree["proofs"]) > 1 else ""
        body = " and ".join(parts)
        return f"{tree['fact']} because {body}{more}" if depth else f"{tree['fact']} is established because {body}{more}."

    @bi("explain", (1, 2))
    def _explain(it_, node, q, style="tree"):
        """the derivation as a tree (default) or, with "plain", as sentences a reader without rules can follow"""
        t = _why(it_, node, q)
        if t is not None:
            return render_plain(t) if T.strip(style) == "plain" else render_why(t)
        k = key_of(*goal(q, node))
        d = [x for x in it_.kb.defeated if x["conclusion"] == k]
        if d:
            return "not established: " + k + "\n" + "\n".join(
                f"  rule {x['rule']} reached it, but it is defeated by {x['by']}   [{', '.join(x['by_sources'])}]"
                for x in d)
        if k in it_.kb.conflicted:
            sd = it_.kb.conflicted[k]
            return ("conflicted: " + k + "\n  asserted true by  [" + ", ".join(sorted(sd["true"].src)) + "]\n"
                    "  asserted false by [" + ", ".join(sorted(sd["false"].src)) + "]\n  OPEN_RESOLUTION_REQUIRED")
        o = [x for x in it_.kb.open if x["conclusion"] == k]
        if o:
            return "open: " + k + "\n" + "\n".join(f"  rule {x['rule']} waits on {x['open_on'][0]}" for x in o)
        lines = ["not established: " + k]
        wn = it_.builtins.vars.get("why_not")
        if wn is not None:
            for r in wn.fn(it_, node, q):
                if r.get("failed") is None:
                    continue
                lines.append(f"  rule {r['rule']}: {r['met']} of {r['of']} conditions met; fails at {r['failed']}")
                for c in r.get("conflicted") or []:
                    lines.append(f"    blocked by a conflicted fact: {c['fact']} — asserted true by "
                                 f"[{', '.join(c['true_sources'])}], false by [{', '.join(c['false_sources'])}]")
        return "\n".join(lines)

    @bi("single_points", 1)
    def _single(it_, node, q):
        pred, args = goal(q, node)
        f = it_.kb.all_facts().get(key_of(pred, args))
        return [] if f is None else single_points(it_.kb, f)

    @bi("proofs", 1)
    def _proofs(it_, node, q):
        """distinct ways a conclusion rests on base facts: [{facts: [...], sources: [...]}]"""
        pred, args = goal(q, node)
        f = it_.kb.all_facts().get(key_of(pred, args))
        if f is None:
            return []
        facts = it_.kb.all_facts()
        out = []
        for bs in base_sets(it_.kb, f):
            src = set()
            for i in bs:
                src |= facts[i].src
            out.append({"facts": [facts[i].text() for i in sorted(bs)], "sources": sorted(src)})
        return out

    @bi("open_conclusions", 0)
    def _open(it_, node):
        return [dict(o) for o in it_.kb.open]

    @bi("decisive_unknowns", 0)
    def _decisive(it_, node):
        """the unknown facts (and undecided comparisons) that hold conclusions open, ranked by how many conclusions
        knowing each one would settle — the record to pull next"""
        infer(it_, it_.kb)
        tally_ = {}
        for o in it_.kb.open:
            for w in o["open_on"]:
                key = w[4:-10] if w.startswith("not ") and w.endswith(" (unknown)") else w
                key = key.replace(", ", ",")
                tally_.setdefault(key, []).append(o["conclusion"])
        rows = [{"fact": k, "settles": T.Decimal(len(set(v))), "conclusions": sorted(set(v))} for k, v in tally_.items()]
        return sorted(rows, key=lambda r: (-r["settles"], r["fact"]))

    @bi("conflicts", 0)
    def _conflicts(it_, node):
        """source conflicts (a fact asserted true by one record and false by another) and Conflict(...) facts
        a rule derived"""
        out = []
        for k, sides in sorted(it_.kb.conflicted.items()):
            src = sides["true"].src | sides["false"].src
            out.append(T.wrap({"kind": "source", "fact": k, "true_sources": sorted(sides["true"].src),
                               "false_sources": sorted(sides["false"].src),
                               "status": "OPEN_RESOLUTION_REQUIRED"}, src))
        for f in it_.kb.lookup("Conflict"):
            out.append(T.wrap(dict(f.to_map(), kind="rule"), f.src))
        return out

    @bi("status", 1)
    def _status(it_, node, q):
        """true | false | conflicted | defeated | open | unknown — one word for where a conclusion stands"""
        pred, args = goal(q, node)
        k = key_of(pred, args)
        facts = it_.kb.all_facts()
        if k in it_.kb.conflicted:
            return "conflicted"
        if k in facts:
            return T.wrap("true", facts[k].src)
        if k + "=false" in facts:
            return T.wrap("false", facts[k + "=false"].src)
        if any(d["conclusion"] == k for d in it_.kb.defeated):
            return "defeated"
        if any(o["conclusion"] == k for o in it_.kb.open):
            return "open"
        for f in it_.kb.lookup("Complete"):
            if f.truth and f.args and T.strip(f.args[0]) == pred:
                return T.wrap("false", f.src)  # absent from a predicate declared complete
        return "unknown"

    @bi("rules", 0)
    def _rules(it_, node):
        return [r.name for r in it_.kb.rules]

    @bi("retract_all", 0)
    def _retract_all(it_, node):
        it_.kb = KB()
        return None


def snapshot(kb):
    base = {k: copy.copy(f) for k, f in kb.base.items()}
    conf = {k: {s: copy.copy(f) for s, f in v.items()} for k, v in kb.conflicted.items()}
    return base, kb.rules[:], conf, dict(kb.aliases)


def restore(kb, snap):
    kb.base, kb.rules, kb.conflicted, kb.aliases = snap
    kb.derived, kb.open, kb.defeated = {}, [], []
    kb.stale = True
