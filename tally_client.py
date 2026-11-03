"""Drive a Tally session from Python (for agents and scripts).

    from tally_client import Tally
    with Tally() as t:
        t.exec('fact Paid("Customer", $55.00, @2040-02-13) from "DOC_10001"')
        t.eval('$1.00 + $2.00')                    # {"ok": True, "value": "$3.00", "type": "money", ...}
        t.query('Paid("Customer", m, d)')             # [{"m": "$55.00", "d": "2040-02-13"}]
        t.help("sum_of")

Every call returns the response dict; nothing raises on a Tally error — check r["ok"] and r["error"]["code"].
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


class Tally:
    def __init__(self):
        self.p = subprocess.Popen([sys.executable, os.path.join(HERE, "tally.py"), "serve"], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1, cwd=HERE)
        self.hello = json.loads(self.p.stdout.readline())
        self.n = 0

    def call(self, op, **kw):
        self.n += 1
        self.p.stdin.write(json.dumps(dict(kw, id=self.n, op=op)) + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError("tally serve ended")
        return json.loads(line)

    def exec(self, code):
        return self.call("exec", code=code)

    def eval(self, code):
        return self.call("eval", code=code)

    def query(self, pattern):
        r = self.call("query", pattern=pattern)
        return r["value"] if r["ok"] else r

    def explain(self, pattern):
        r = self.call("explain", pattern=pattern)
        return r["value"] if r["ok"] else r

    def status(self, pattern):
        r = self.call("status", pattern=pattern)
        return r["value"] if r["ok"] else r

    def proof_graph(self, pattern, max_nodes=5000):
        return self.call("proof_graph", pattern=pattern, max_nodes=max_nodes)

    def impact(self, sources):
        return self.call("impact", sources=sources)

    def help(self, name):
        return self.call("help", name=name)

    def check(self, code):
        return self.call("check", code=code)

    def batch(self, requests, atomic=True):
        """run several requests; with atomic=True a failure rolls the whole batch back"""
        return self.call("batch", requests=[dict(r, id=i) for i, r in enumerate(requests, 1)], atomic=atomic)

    def checkpoint(self):
        return self.call("checkpoint")["value"]["checkpoint"]

    def rollback(self, to):
        return self.call("rollback", to=to)

    def close(self):
        if self.p.poll() is None:
            self.p.stdin.close()
            self.p.wait(timeout=10)
        self.p.stdout.close()

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()
