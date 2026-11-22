#!/usr/bin/env python3
"""Riemann — namesake ability (Bernhard Riemann, 1859).

The explicit formula: the prime-power staircase psi(x) rebuilt from the zeros of zeta,
x - sum over zeros of x^rho / rho - ln(2 pi) - (1/2) ln(1 - 1/x^2), cut off after n zeros.
Loaded by the Zeta interpreter for the Riemann language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Riemann",
    "namesake": "Bernhard Riemann, 1859: the primes are determined by the zeros of zeta",
    "ability": "the explicit formula: primes rebuilt from zeros",
    "builtins": {
        "zeta_zeros": "zeta_zeros(n): approximate critical-line zero heights from sign changes of the Riemann–Siegel approximation, 1 <= n <= 200, rounded to 12 decimal places",
        "chebyshev_psi": "chebyshev_psi(x): the sum of ln p over prime powers p^k <= x, to 30 decimals",
        "explicit_psi": "explicit_psi(x, n): the explicit formula for psi(x) using the first n zeros, x > 1, n <= 200"
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
    def zeta_zeros(n):
        return [F(round(g * 10 ** 12), 10 ** 12) for g in zm.zeta_zeros(whole(n, "n"))]
    reg("zeta_zeros", 1, zeta_zeros)
    reg("chebyshev_psi", 1, lambda x: zm.frac(zm.chebyshev_psi_fx(number(x, "x")), zm.WORK))
    reg("explicit_psi", 2, lambda x, n: zm.frac(zm.explicit_psi_fx(number(x, "x"), whole(n, "n")), zm.WORK))
