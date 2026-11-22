#!/usr/bin/env python3
"""Hardy — generation 5 dialect in the Zeta language family, with Hardy's Z-function and theta function.

    hardy run FILE [--json] · hardy check FILE · hardy selftest · hardy describe [--json] · hardy version
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zeta"))
import zeta  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(zeta.dialect_main(os.path.join(HERE, "dialect.json"), sys.argv[1:]))
