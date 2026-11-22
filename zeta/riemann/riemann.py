#!/usr/bin/env python3
"""Riemann — generation 3 branch of the Zeta vine, with tabulated zeros and the explicit formula.

    riemann run FILE [--json] · riemann check FILE · riemann selftest · riemann describe [--json] · riemann version
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zeta"))
import zeta  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(zeta.dialect_main(os.path.join(HERE, "dialect.json"), sys.argv[1:]))
