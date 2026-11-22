#!/usr/bin/env python3
"""Gauss — generation 2 dialect in the Zeta language family, with prime counting and the logarithmic integral.

    gauss run FILE [--json] · gauss check FILE · gauss selftest · gauss describe [--json] · gauss version
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zeta"))
import zeta  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(zeta.dialect_main(os.path.join(HERE, "dialect.json"), sys.argv[1:]))
