#!/usr/bin/env python3
"""Hardy — namesake ability (G. H. Hardy, 1914).

Hardy's Z-function: real for real t, and zero exactly where zeta has a zero on the critical line. Hardy used it to
prove that infinitely many zeros lie on the line.
Loaded by the Zeta interpreter for the Hardy language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Hardy",
    "namesake": "G. H. Hardy, 1914: infinitely many zeros of zeta lie on the critical line",
    "ability": "the Z-function built in",
    "builtins": {
        "hardy_z": "hardy_z(t): Z(t) for t >= 7 by the Riemann-Siegel formula with terms C0..C4; right to about 5 decimals at t = 10, 7 at t = 100, 15 at t = 100000",
        "hardy_theta": "hardy_theta(t): the Riemann-Siegel theta function for t >= 5"
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
    reg("hardy_z", 1, lambda t: zm.frac(zm.siegel_z_fx(number(t, "t"), 4), zm.WORK))
    reg("hardy_theta", 1, lambda t: zm.frac(zm.theta_fx(number(t, "t")), zm.WORK))
