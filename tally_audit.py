"""Structured, bounded proof graphs and reversible source-withdrawal analysis.

Graphs encode supplied facts and rule derivations. They do not verify sources.
Withdrawal changes asserted fact support; it does not rewrite program variables,
rule definitions, source files, or external stores.
"""
import hashlib
from collections import deque
from decimal import Decimal

import tally as T
import tally_logic as L


def state(kb, pred, args):
    key = L.key_of(pred, args)
    if key in kb.conflicted:
        return "conflicted"
    facts = kb.all_facts()
    if key in facts:
        return "true"
    if key + "=false" in facts:
        return "false"
    if any(d["conclusion"] == key for d in kb.defeated):
        return "defeated"
    if any(o["conclusion"] == key for o in kb.open):
        return "open"
    if any(f.truth and f.args and T.strip(f.args[0]) == pred for f in kb.lookup("Complete")):
        return "false"
    return "unknown"


def goal(q, node, it):
    q = T.strip(q)
    if not isinstance(q, dict) or "pred" not in q or q.get("vars"):
        raise it.err("expected a ground pattern like ?Paid(\"Alex\", $100.00)", node)
    return q["pred"], q["args"]


def statuses(kb):
    """Index explicit and latent conclusions once for counterfactual comparison."""
    values = {}
    for entries, status in ((kb.open, "open"), (kb.defeated, "defeated")):
        for entry in entries:
            key = entry["conclusion"]
            if key.endswith(" = false"):
                key = key[:-8]
            values[key] = status
    facts = kb.all_facts()
    for truth in (False, True):
        for f in facts.values():
            if f.truth == truth:
                values[L.key_of(f.pred, f.args)] = "true" if truth else "false"
    values.update({key: "conflicted" for key in kb.conflicted})
    complete = {T.strip(f.args[0]) for f in facts.values()
                if f.pred == "Complete" and f.truth and f.args}
    return values, complete


def indexed_status(index, key):
    values, complete = index
    return values.get(key, "false" if key.split("(", 1)[0] in complete else "unknown")


def proof_graph(it, pred, args, max_nodes=5000):
    """Iterative traversal retains alternative proofs and explicit truncation."""
    L.infer(it, it.kb)
    kb, nodes, edges = it.kb, {}, set()
    facts = kb.all_facts()
    key = L.key_of(pred, args)
    root = key if key in facts else key + "=false" if key + "=false" in facts else key
    pending, visited = deque([root]), set()
    truncated = False

    def add(ident, **fields):
        nonlocal truncated
        if ident not in nodes and len(nodes) >= max_nodes:
            truncated = True
            return False
        nodes.setdefault(ident, dict(id=ident, **fields))
        return True

    def link(a, b, kind):
        if a in nodes and b in nodes:
            edges.add((a, b, kind))

    def ident(kind, *parts):
        return kind + ":" + hashlib.sha256(repr(parts).encode()).hexdigest()[:24]

    add(root, kind="fact", label=key, status=state(kb, pred, args), sources=[])
    if root not in facts and state(kb, pred, args) == "false":
        for f in kb.lookup("Complete"):
            if f.truth and f.args and T.strip(f.args[0]) == pred:
                if add(f.id, kind="fact", label=f.text(), status="true", sources=[]):
                    link(f.id, root, "closed_world")
                    pending.append(f.id)
    while pending:
        fid = pending.popleft()
        if fid in visited:
            continue
        visited.add(fid)
        it.tick()
        f = facts.get(fid)
        if f is None:
            continue
        if not add(fid, kind="fact", label=f.text(), status="true" if f.truth else "false", sources=[]):
            continue
        nodes[fid].update(sources=sorted(f.src), base=fid in kb.base, line=f.line)
        for src in sorted(f.src):
            sid = ident("source", src)
            if add(sid, kind="source", label=src):
                link(sid, fid, "cites")
        for rule, premises in sorted(f.supports):
            pid = ident("proof", fid, rule, tuple(sorted(premises)))
            if not add(pid, kind="proof", label=rule):
                continue
            link(pid, fid, "derives")
            for premise in sorted(premises):
                pf = facts.get(premise)
                if pf is not None and add(premise, kind="fact", label=pf.text(),
                                          status="true" if pf.truth else "false", sources=[]):
                    link(premise, pid, "premise")
                    pending.append(premise)
    if key in kb.conflicted:
        for side, f in sorted(kb.conflicted[key].items()):
            sid = ident("assertion", key, side)
            if f and add(sid, kind="assertion", label=f.text(), sources=sorted(f.src), truth=f.truth):
                link(sid, root, "disputes")
    for entry in sorted((o for o in kb.open if o["conclusion"] == key), key=lambda o: o["rule"]):
        for reason in entry["open_on"]:
            rid = ident("unknown", entry["rule"], reason)
            if add(rid, kind="unknown", label=reason, rule=entry["rule"]):
                link(rid, root, "blocks")
    for entry in sorted((d for d in kb.defeated if d["conclusion"] == key), key=lambda d: d["rule"]):
        did = ident("defeater", entry["rule"], entry["by"])
        if add(did, kind="defeater", label=entry["by"], rule=entry["rule"], sources=entry["by_sources"]):
            link(did, root, "defeats")
    return {"schema": "tally.proof_graph.v1", "root": root, "status": state(kb, pred, args),
            "nodes": [nodes[k] for k in sorted(nodes)],
            "edges": [{"from": a, "to": b, "kind": k} for a, b, k in sorted(edges)],
            "truncated": truncated, "max_nodes": max_nodes,
            "semantics": "supplied facts and rule derivations; source labels are not source verification"}


def withdraw(kb, sources):
    removed = []
    for fid, f in list(kb.base.items()):
        if not f.src.intersection(sources):
            continue
        f.src = f.src - sources
        if not f.src:
            removed.append(f.text())
            del kb.base[fid]
    # Resolve a conflict when one assertion loses all its support.
    for key, sides in list(kb.conflicted.items()):
        for side, f in list(sides.items()):
            if f is not None and f.src.intersection(sources):
                f.src = f.src - sources
                if not f.src:
                    removed.append(f.text())
                    sides[side] = None
        surviving = [f for f in sides.values() if f is not None]
        if len(surviving) < 2:
            del kb.conflicted[key]
            for f in surviving:
                kb.base[f.id] = f
    kb.stale = True
    return sorted(removed)


def impact(it, sources):
    if isinstance(T.strip(sources), str):
        sources = [T.strip(sources)]
    else:
        sources = T.strip(sources)
    if not isinstance(sources, list) or not all(isinstance(T.strip(s), str) for s in sources):
        raise T.TallyError("impact needs a source name or a list of source names", 0, 0)
    sources = set(T.strip(s) for s in sources)
    kb = it.kb
    L.infer(it, kb)
    before = statuses(kb)
    derived = {k: f.text() for k, f in kb.derived.items()}
    known = set().union(*(f.src for f in kb.base.values())) if kb.base else set()
    for sides in kb.conflicted.values():
        for f in sides.values():
            if f:
                known.update(f.src)
    snap = L.snapshot(kb)
    try:
        removed = withdraw(kb, sources)
        L.infer(it, kb)
        after_derived = set(kb.derived)
        after = statuses(kb)
        changes = [{"fact": k, "before": indexed_status(before, k), "after": indexed_status(after, k)}
                   for k in sorted(set(before[0]) | set(after[0]))
                   if indexed_status(before, k) != indexed_status(after, k)]
        result = {"schema": "tally.impact.v1", "sources": sorted(sources), "removed": removed,
                  "unknown_sources": sorted(sources - known), "changes": changes,
                  "falls": sorted(derived[k] for k in derived if k not in after_derived),
                  "stands": sorted(derived[k] for k in derived if k in after_derived),
                  "scope": "asserted fact support only; program variables and rule definitions are unchanged"}
    finally:
        L.restore(kb, snap)
        # Avoid a second inference on a depleted execution budget; the next query refreshes it.
    return result


def install(it):
    def graph(it_, node, q, max_nodes=Decimal(5000)):
        size = T.strip(max_nodes)
        if isinstance(size, bool) or not isinstance(size, (Decimal, int)) or size != int(size) or not 1 <= size <= 100000:
            raise it_.err("proof_graph max_nodes must be a whole number between 1 and 100000", node)
        return proof_graph(it_, *goal(q, node, it_), max_nodes=int(size))

    def analyze(it_, node, sources):
        return impact(it_, sources)

    it.builtins.vars["proof_graph"] = T.Builtin("proof_graph", graph, (1, 2))
    it.builtins.vars["impact"] = T.Builtin("impact", analyze, 1)
