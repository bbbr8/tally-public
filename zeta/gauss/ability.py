#!/usr/bin/env python3
"""Gauss — namesake ability (Carl Friedrich Gauss, 1792-1849).

Counting primes against Gauss's estimate: prime_count(x) is the exact number of primes up to x, and li(x) is the
logarithmic integral Gauss proposed for it.
Loaded by the Zeta interpreter for the Gauss language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Gauss",
    "namesake": "Carl Friedrich Gauss: the number of primes up to x is close to the logarithmic integral li(x)",
    "ability": "the prime count and Gauss's estimate of it",
    "builtins": {
        "prime_count": "prime_count(x): how many primes are <= x, exactly (x <= 20000000)",
        "li": "li(x): the logarithmic integral, x > 1, to 30 decimals"
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
    reg("prime_count", 1, lambda x: F(zm.prime_count(number(x, "x"))))
    reg("li", 1, lambda x: zm.frac(zm.li_fx(number(x, "x")), zm.WORK))
