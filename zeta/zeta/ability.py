#!/usr/bin/env python3
"""Zeta — namesake ability (the zeta function itself).

zeta(s) on the real line: exact at 0 and the negative whole numbers, exact as a fraction of a power of pi at the
positive even numbers, and to 30 decimals elsewhere.
Loaded by the Zeta interpreter for the Zeta language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Zeta",
    "namesake": "the Riemann zeta function, zeta(s) = 1 + 1/2^s + 1/3^s + ...",
    "ability": "values of zeta on the real line",
    "builtins": {
        "zeta": "zeta(s): s any fraction but 1, between -60 and 60; exact at 0, -1, -2, ...; 30 decimals elsewhere",
        "zeta_over_pi": "zeta_over_pi(k): the exact fraction zeta(2k) / pi^(2k), k = 1, 2, 3, ...",
        "bernoulli": "bernoulli(n): the Bernoulli number B_n exactly (B_1 = -1/2)"
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
    def zeta(s):
        kind, v = zm.zeta_real(number(s, "s"))
        return v if kind == "exact" else zm.frac(v, zm.WORK)
    reg("zeta", 1, zeta)
    reg("zeta_over_pi", 1, lambda k: zm.zeta_over_pi(whole(k, "k")))
    reg("bernoulli", 1, lambda n: zm.bernoulli(whole(n, "n")))
