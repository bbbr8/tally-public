#!/usr/bin/env python3
"""Mertens — generation 4 branch of the Zeta vine, with Möbius and Mertens functions.

    mertens run FILE [--json] · mertens check FILE · mertens selftest · mertens describe [--json] · mertens version
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zeta"))
import zeta  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(zeta.dialect_main(os.path.join(HERE, "dialect.json"), sys.argv[1:]))
