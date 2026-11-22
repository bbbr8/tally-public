#!/usr/bin/env python3
"""Euler — namesake ability (Leonhard Euler, 1737).

The Euler product: the product over primes p <= P of 1 / (1 - p^-s), as one exact fraction. Euler showed it equals the
sum of 1/n^s, which ties the primes to zeta.
Loaded by the Zeta interpreter for the Euler language only (install_ability in zeta.py). The arithmetic is in
zeta/zeta_math.py: whole numbers and exact fractions, no float, no outside library. Values that are not rational
come back as exact fractions rounded to 30 decimals.
"""
from fractions import Fraction as F

import zeta_math as zm

ABOUT = {
    "language": "Euler",
    "namesake": "Leonhard Euler, 1737: the product over the primes equals the sum over the whole numbers",
    "ability": "the Euler product as an exact fraction",
    "builtins": {
        "euler_product": "euler_product(s, P): product over primes p <= P of 1/(1 - p^-s), exact; s = 2, 3, ..., 60; P <= 100000",
        "primes_to": "primes_to(P): the list of primes up to P (P <= 1000000)"
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
    def euler_product(s, P):
        s, P = whole(s, "s"), whole(P, "P")
        if not 2 <= s <= 60:
            raise ValueError("s must be a whole number from 2 to 60")
        if not 1 <= P <= 100000:
            raise ValueError("P must be between 1 and 100000")
        num = den = 1
        for p in zm.primes_upto(P):
            num *= p ** s
            den *= p ** s - 1
        return F(num, den)
    reg("euler_product", 2, euler_product)

    def primes_to(P):
        P = whole(P, "P")
        if P > 1000000:
            raise ValueError("P must be at most 1000000")
        return [F(p) for p in zm.primes_upto(P)]
    reg("primes_to", 1, primes_to)
