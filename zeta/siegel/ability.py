#!/usr/bin/env python3
"""Siegel — namesake ability (Carl Ludwig Siegel, 1932).

The Riemann-Siegel formula with its correction terms C0..C4, which Siegel recovered from Riemann's unpublished notes.
siegel_z(t, k) uses the terms up to C_k, so the gain from each term can be measured.
Loaded by the Zeta interpreter for the Siegel language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Siegel",
    "namesake": "Carl Ludwig Siegel, 1932: the Riemann-Siegel formula and its correction terms",
    "ability": "the Riemann-Siegel correction terms",
    "builtins": {
        "siegel_z": "siegel_z(t, k): Z(t) with correction terms C0..Ck, t >= 7, k = 0, 1, 2, 3, 4; the remainder shrinks with k and with t",
        "siegel_term": "siegel_term(k, p): the correction term C_k at p, 0 <= p <= 1, k = 0, 1, 2, 3, 4"
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
    reg("siegel_z", 2, lambda t, k: zm.frac(zm.siegel_z_fx(number(t, "t"), whole(k, "k")), zm.WORK))

    def siegel_term(k, p):
        p = number(p, "p")
        if not 0 <= p <= 1:
            raise ValueError("p must be between 0 and 1")
        return zm.frac(zm.siegel_term_fx(whole(k, "k"), zm.fx(p, zm.WORK), zm.WORK), zm.WORK)
    reg("siegel_term", 2, siegel_term)
