"""Exact record reconciliation and ledger checks, with explicit competing assignments.

Matching is maximum-cardinality. A pair is confirmed only when every maximum
assignment contains it. Dates rank the reproducible proposal; they never resolve
an evidentiary tie. Callers choose identity/stage fields and input coverage.
"""
from collections import deque
from datetime import date
from decimal import Decimal

import tally as T


def augment(adj, ma, mb, roots, tick, forbidden=None):
    """Add one alternating path, iteratively; return whether cardinality grew."""
    queue = deque(roots)
    seen_a, parents = set(queue), {}
    while queue:
        i = queue.popleft()
        for j in adj[i]:
            tick()
            if (i, j) == forbidden or j in parents:
                continue
            parents[j] = i
            if j not in mb:
                while j is not None:
                    i = parents[j]
                    prior = ma.get(i)
                    ma[i], mb[j] = j, i
                    j = prior
                return True
            other = mb[j]
            if other not in seen_a:
                seen_a.add(other)
                queue.append(other)
    return False


def assignment_analysis(adj, tick=lambda: None):
    """Maximum matching plus edges present in every maximum matching."""
    ma, mb = {}, {}
    for i in range(len(adj)):
        tick()
        augment(adj, ma, mb, [i], tick)
    forced = set()
    for i, j in sorted(ma.items()):
        trial_a, trial_b = dict(ma), dict(mb)
        del trial_a[i]
        del trial_b[j]
        roots = [k for k in range(len(adj)) if k not in trial_a]
        if not augment(adj, trial_a, trial_b, roots, tick, forbidden=(i, j)):
            forced.add((i, j))
    return ma, forced


def install(it):
    def fail(message, node):
        raise it.err(message, node)

    def options(raw, allowed, node):
        o = {} if raw is None else T.strip(raw)
        if not isinstance(o, dict):
            fail("audit options must be a map", node)
        unknown = set(o) - allowed
        if unknown:
            fail("unknown audit option: " + ", ".join(sorted(unknown)), node)
        return {k: T.strip(v) for k, v in o.items()}

    def field_name(v, node):
        if not isinstance(v, str) or not v:
            fail("audit field names must be nonempty strings", node)
        return v

    def rows(v, node):
        v = T.strip(v)
        if not isinstance(v, list):
            fail("audit needs a list of records", node)
        if len(v) > 2000:
            fail("audit accepts at most 2000 records per side", node)
        for r in v:
            if not isinstance(T.strip(r), (dict, T.Record)):
                fail("audit rows must be maps or records", node)
        return v

    def field(row, key, node):
        v = T.strip(row)
        vals = v.vals if isinstance(v, T.Record) else v
        if key not in vals:
            fail("audit row has no field '" + key + "'", node)
        # Row-level citations apply to selected fields as well.
        return T.wrap(T.strip(vals[key]), T.srcs(row) | T.srcs(vals[key]))

    def amount(row, key, node):
        v = field(row, key, node)
        if not isinstance(T.strip(v), T.Money):
            fail("audit amount must be money", node)
        return v

    def atom(v, node):
        v = T.strip(v)
        if v is None or v == "":
            return None
        if not isinstance(v, (str, Decimal, bool, date, T.Money)):
            fail("audit identity fields must be scalar values", node)
        return (T.type_name(v), v.cents if isinstance(v, T.Money) else v)

    def sourced(v, *inputs):
        src = set()
        for x in inputs:
            src.update(T.all_sources(x))
        return T.wrap(v, src)

    def reconcile_audit(it_, node, left, right, opts=None):
        """Maximum one-to-one exact-money reconciliation; expose ambiguous assignments.
        opts {days: 0, keys: [], amount: "amount", day: "day", sign: false}.
        matched contains only pairs shared by every maximum assignment;
        assignment is one deterministic proposal, unresolved_* retains every other row.
        Empty/nil keys or dates remain unresolved. At most 2000 rows/side and 20000 edges.
        """
        o = options(opts, {"days", "keys", "amount", "day", "sign"}, node)
        days = o.get("days", Decimal(0))
        if not isinstance(days, Decimal) or days != days.to_integral_value() or not 0 <= days <= 3660:
            fail("audit days must be a whole number from 0 to 3660", node)
        days = int(days)
        sign = o.get("sign", False)
        if type(sign) is not bool:
            fail("audit sign must be a boolean", node)
        keys = o.get("keys", [])
        if not isinstance(keys, list):
            fail("audit keys must be a list of field names", node)
        keys = [field_name(T.strip(k), node) for k in keys]
        if len(set(keys)) != len(keys):
            fail("audit keys must be distinct", node)
        af = field_name(o.get("amount", "amount"), node)
        df = field_name(o.get("day", "day"), node)
        A, B = rows(left, node), rows(right, node)

        def norm(rs):
            out = []
            for r in rs:
                it_.tick(node)
                cents = T.strip(amount(r, af, node)).cents
                d = T.strip(field(r, df, node))
                if d is not None and type(d) is not date:
                    fail("audit day must be a date or nil", node)
                ks = tuple(atom(field(r, k, node), node) for k in keys)
                key = (abs(cents) if sign else cents, ks)
                incomplete = d is None or any(k is None for k in ks)
                out.append((key, d, incomplete))
            return out

        an, bn = norm(A), norm(B)
        buckets = {}
        for j, (key, d, incomplete) in enumerate(bn):
            if not incomplete:
                buckets.setdefault(key, []).append(j)
        adj, edges, degrees_b = [], 0, [0] * len(B)
        for key, d, incomplete in an:
            candidates = []
            for j in ([] if incomplete else buckets.get(key, [])):
                it_.tick(node)
                gap = (bn[j][1] - d).days
                if abs(gap) <= days:
                    candidates.append((abs(gap), j))
                    degrees_b[j] += 1
                    edges += 1
                    if edges > 20000:
                        fail("audit candidate graph exceeds 20000 edges; add identity keys", node)
            adj.append([j for _, j in sorted(candidates)])
        ma, forced = assignment_analysis(adj, lambda: it_.tick(node))

        def pair(i, j):
            # The decision used both records, the amount, dates and explicit keys.
            return sourced({"a_index": Decimal(i), "b_index": Decimal(j), "a": A[i], "b": B[j],
                            "gap": Decimal((bn[j][1] - an[i][1]).days),
                            "status": "confirmed" if (i, j) in forced else "ambiguous"}, A[i], B[j], opts)

        forced_a, forced_b = {i for i, j in forced}, {j for i, j in forced}

        def unresolved(rs, ns, degrees, confirmed):
            return [sourced({"index": Decimal(i), "row": r, "candidate_count": Decimal(degrees[i]),
                              "reason": "incomplete_identity_or_day" if ns[i][2] else
                              "no_candidate" if degrees[i] == 0 else "competing_assignment"}, r, opts)
                    for i, r in enumerate(rs) if i not in confirmed]

        result = {"schema": "tally.reconcile_audit.v1", "policy": "maximum_cardinality_required_pairs",
                  "maximum_pairs": Decimal(len(ma)), "confirmed_pairs": Decimal(len(forced)),
                  "complete": len(forced) == len(A) == len(B), "candidate_edges": Decimal(edges),
                  "assignment": [pair(i, j) for i, j in sorted(ma.items())],
                  "matched": [pair(i, j) for i, j in sorted(forced)],
                  "unresolved_a": unresolved(A, an, [len(x) for x in adj], forced_a),
                  "unresolved_b": unresolved(B, bn, degrees_b, forced_b),
                  "confirmed_amount": sourced(T.Money(sum(T.strip(amount(A[i], af, node)).cents
                                                           for i in sorted(forced_a))), left, right, opts)}
        # Counts and completeness depend on the entire inspected pool, including competitors.
        return sourced(result, left, right, opts)

    def ledger_audit(it_, node, opening, entries, closing, opts=None):
        """Exact opening + signed transactions = closing, with duplicate-ID diagnostics.
        opts {amount: "amount", id: "id"}; omit id to skip identifier checks.
        balanced checks arithmetic; clean additionally requires complete unique IDs.
        Every input must be a transaction, with opening/closing balances supplied separately.
        """
        o = options(opts, {"amount", "id"}, node)
        af = field_name(o.get("amount", "amount"), node)
        idf = field_name(o["id"], node) if "id" in o else None
        op, cl = T.strip(opening), T.strip(closing)
        if not isinstance(op, T.Money) or not isinstance(cl, T.Money):
            fail("ledger opening and closing must be money", node)
        rs, ins, outs, groups, missing = rows(entries, node), [], [], {}, []
        for i, r in enumerate(rs):
            it_.tick(node)
            a = amount(r, af, node)
            (ins if T.strip(a).cents >= 0 else outs).append(a)
            if idf is not None:
                key = atom(field(r, idf, node), node)
                if key is None:
                    missing.append(Decimal(i))
                else:
                    groups.setdefault(key, []).append(i)
        duplicates = [sourced({"id": field(rs[ix[0]], idf, node),
                               "indices": [Decimal(i) for i in ix], "rows": [rs[i] for i in ix]},
                              [rs[i] for i in ix]) for ix in groups.values() if len(ix) > 1]
        credits = sum(T.strip(a).cents for a in ins)
        debits = sum(T.strip(a).cents for a in outs)
        computed = op.cents + credits + debits
        gap = computed - cl.cents
        return sourced({"schema": "tally.ledger_audit.v1", "rows": Decimal(len(rs)),
                        "opening": opening, "credits": T.Money(credits), "debits": T.Money(debits),
                        "net": T.Money(credits + debits), "computed_closing": T.Money(computed),
                        "reported_closing": closing, "gap": T.Money(gap), "balanced": gap == 0,
                        "identity_checked": idf is not None, "duplicates": duplicates, "missing_ids": missing,
                        "clean": gap == 0 and idf is not None and not duplicates and not missing},
                       opening, entries, closing, opts)

    it.builtins.vars["reconcile_audit"] = T.Builtin("reconcile_audit", reconcile_audit, (2, 3))
    it.builtins.vars["ledger_audit"] = T.Builtin("ledger_audit", ledger_audit, (3, 4))
