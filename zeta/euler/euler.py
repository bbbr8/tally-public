#!/usr/bin/env python3
"""Euler — generation 1 dialect in the Zeta language family, with finite Euler products and primes.

    euler run FILE [--json] · euler check FILE · euler selftest · euler describe [--json] · euler version
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zeta"))
import zeta  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(zeta.dialect_main(os.path.join(HERE, "dialect.json"), sys.argv[1:]))
