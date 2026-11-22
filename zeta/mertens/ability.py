#!/usr/bin/env python3
"""Mertens — namesake ability (Franz Mertens, 1897).

The Moebius function and its running total M(n), the Mertens function. The Riemann hypothesis is the statement that
M(n) grows no faster than n^(1/2 + e) for every e > 0.
Loaded by the Zeta interpreter for the Mertens language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Mertens",
    "namesake": "Franz Mertens, 1897: the running total of the Moebius function",
    "ability": "the Mertens function built in",
    "builtins": {
        "mobius": "mobius(n): the Moebius function, n <= 10000000",
        "mertens": "mertens(n): M(n) = mobius(1) + ... + mobius(n), n <= 10000000",
        "mertens_extreme": "mertens_extreme(lo, hi): [m, M(m)] where |M(m)| / sqrt(m) is largest for lo <= m <= hi"
    }
}


def whole(x, what):
    if not isinstance(x, F) or x.denominator != 1:
        raise ValueError(what + " must be a whole number")
    return x.numerator


def number(x, what):
    if isinstance(x, bool) or not isinstance(x, F):
        raise ValueError(what + " must be a number")
    return x


def install(reg):
    reg("mobius", 1, lambda n: F(zm.moebius(whole(n, "n"))))
    reg("mertens", 1, lambda n: F(zm.mertens(whole(n, "n"))))
    reg("mertens_extreme", 2, lambda lo, hi: [F(v) for v in zm.mertens_extreme(whole(lo, "lo"), whole(hi, "hi"))])
