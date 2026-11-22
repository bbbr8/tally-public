#!/usr/bin/env python3
"""Number theory shared by the namesake abilities of the Zeta family (Zeta, Euler, Gauss, Riemann, Mertens, Hardy, Siegel).

Whole numbers and exact fractions only: no float and no outside library. A value that is not rational (a logarithm,
a cosine, zeta(3)) is worked to D decimals in scaled whole numbers and handed back as an exact Fraction rounded to OUT
decimals. Each ability.py beside a language file wraps a few of these as built-ins for that language alone.

Checked against mpmath by score_namesake.py in the Riemann test folder; nothing here imports mpmath.
"""
from bisect import bisect_right
from fractions import Fraction as F
from functools import lru_cache
from itertools import accumulate
from math import comb, factorial, isqrt

OUT = 30          # decimals in a returned value
WORK = 45         # decimals carried while working
GUARD = 10


def tq(a, b):
    """Whole-number division that rounds toward zero (so a shrinking series term reaches 0 from either side)."""
    if b < 0:
        a, b = -a, -b
    return a // b if a >= 0 else -((-a) // b)


def fx(x, D):
    """Fraction or whole number -> scaled whole number with D decimals (rounded toward zero)."""
    x = F(x)
    return tq(x.numerator * 10 ** D, x.denominator)


def frac(v, D, out=OUT):
    """Scaled whole number with D decimals -> Fraction rounded to `out` decimals."""
    if D <= out:
        return F(v, 10 ** D)
    q = 10 ** (D - out)
    return F((2 * v + q) // (2 * q), 10 ** out)


# ------------------------------------------------------------------ constants and elementary functions
@lru_cache(maxsize=None)
def pi_fx(D):
    D2 = D + GUARD

    def atan_inv(n):
        x = 10 ** D2 // n
        n2, tot, k, sign = n * n, x, 1, -1
        while x:
            x //= n2
            k += 2
            tot += sign * (x // k)
            sign = -sign
        return tot
    return (16 * atan_inv(5) - 4 * atan_inv(239)) // 10 ** GUARD


def _atanh(y, D):
    S = 10 ** D
    y2, term, tot, k = tq(y * y, S), y, 0, 1
    while term:
        tot += tq(term, k)
        term = tq(term * y2, S)
        k += 2
    return tot


@lru_cache(maxsize=None)
def ln2_fx(D):
    D2 = D + GUARD
    return 2 * _atanh(10 ** D2 // 3, D2) // 10 ** GUARD


@lru_cache(maxsize=4096)
def ln_fx(x, D):
    """Natural logarithm of a positive Fraction, scaled."""
    x = F(x)
    if x <= 0:
        raise ValueError("logarithm needs a positive number")
    D2 = D + GUARD
    k = 0
    if x >= 2:
        k = (x.numerator // x.denominator).bit_length() - 1
        x /= 2 ** k
    while x < 1:
        x *= 2
        k -= 1
    if x > F(4, 3):
        x /= 2
        k += 1
    v = 2 * _atanh(fx((x - 1) / (x + 1), D2), D2) + k * ln2_fx(D2)
    return tq(v, 10 ** GUARD)


@lru_cache(maxsize=None)
def lnpi_fx(D):
    return ln_fx(F(pi_fx(D + GUARD), 10 ** (D + GUARD)), D)


def exp_fx(v, D):
    """e**x for a scaled x."""
    D2 = D + GUARD
    S = 10 ** D2
    v *= 10 ** GUARD
    l2 = ln2_fx(D2)
    k = (2 * v + l2) // (2 * l2)
    r = v - k * l2
    term, tot, n = S, S, 1
    while term:
        term = tq(term * r, S * n)
        tot += term
        n += 1
    tot = tot * 2 ** k if k >= 0 else tq(tot, 2 ** (-k))
    return tq(tot, 10 ** GUARD)


def cos_sin_fx(v, D):
    """(cos x, sin x) for a scaled x."""
    D2 = D + GUARD
    S = 10 ** D2
    v *= 10 ** GUARD
    tp = 2 * pi_fx(D2)
    v %= tp
    if v > tp // 2:
        v -= tp
    x2 = tq(v * v, S)
    c, term, k = S, S, 0
    while term:
        k += 2
        term = -tq(term * x2, S * (k - 1) * k)
        c += term
    s, term, k = v, v, 1
    while term:
        k += 2
        term = -tq(term * x2, S * (k - 1) * k)
        s += term
    return tq(c, 10 ** GUARD), tq(s, 10 ** GUARD)


def sqrt_fx(x, D):
    x = F(x)
    if x < 0:
        raise ValueError("square root needs a number that is not negative")
    return isqrt(x.numerator * 10 ** (2 * D) // x.denominator)


def pow_fx(base, s, D):
    """base**(-s) scaled, for a positive whole base and a Fraction s."""
    s = F(s)
    if s.denominator == 1:
        return fx(F(base) ** (-s.numerator), D)
    return exp_fx(tq(-s.numerator * ln_fx(F(base), D + 5), s.denominator * 10 ** 5), D)


# ------------------------------------------------------------------ Bernoulli numbers and zeta on the real line
_BERN = [F(1)]


def bernoulli(n):
    """B_n exactly, with B_1 = -1/2."""
    n = int(n)
    if n < 0:
        raise ValueError("bernoulli needs a whole number that is not negative")
    while len(_BERN) <= n:
        m = len(_BERN)
        _BERN.append(-sum(comb(m + 1, k) * _BERN[k] for k in range(m)) / (m + 1))
    return _BERN[n]


def zeta_over_pi(k):
    """The exact fraction c with zeta(2k) = c * pi**(2k) (Euler, 1735 for k = 1)."""
    k = int(k)
    if k < 1:
        raise ValueError("zeta_over_pi(k) needs k = 1, 2, 3, ...")
    return (-1) ** (k + 1) * bernoulli(2 * k) * 2 ** (2 * k - 1) / factorial(2 * k)


def zeta_real(s, D=WORK):
    """zeta(s) for a real fraction s other than 1. Exact at 0 and the negative whole numbers; scaled otherwise."""
    s = F(s)
    if s == 1:
        raise ValueError("zeta has its pole at 1")
    if abs(s) > 60:
        raise ValueError("zeta(s) is offered for -60 <= s <= 60")
    if s.denominator == 1 and s <= 0:
        n = -s.numerator
        return ("exact", (-1) ** n * bernoulli(n + 1) / (n + 1))
    D2 = D + 15
    S = 10 ** D2
    N, K = 40, 30
    tot = sum(pow_fx(n, s, D2) for n in range(1, N))
    nms = pow_fx(N, s, D2)                                  # N**(-s)
    tot += tq(nms * N * (s - 1).denominator, (s - 1).numerator) + nms // 2
    rise, npow = s, F(1, N)                                 # s(s+1)...(s+2k-2) and N**(-(2k-1))
    for k in range(1, K + 1):
        c = bernoulli(2 * k) / factorial(2 * k) * rise * npow
        tot += tq(nms * c.numerator, c.denominator)
        rise *= (s + 2 * k - 1) * (s + 2 * k)
        npow /= N * N
    return ("decimal", tq(tot, 10 ** 15))


# ------------------------------------------------------------------ primes, Moebius, Mertens
_SIEVE = {"n": 1, "primes": []}


def primes_upto(n):
    n = int(n)
    if n > 20_000_000:
        raise ValueError("primes are offered up to 20,000,000")
    if n > _SIEVE["n"]:
        m = max(n, 2 * _SIEVE["n"], 1000)
        b = bytearray(b"\x01") * (m + 1)
        b[0:2] = b"\x00\x00"
        for p in range(2, isqrt(m) + 1):
            if b[p]:
                b[p * p::p] = bytes(len(range(p * p, m + 1, p)))
        _SIEVE["n"], _SIEVE["primes"] = m, [i for i in range(2, m + 1) if b[i]]
    ps = _SIEVE["primes"]
    return ps[:bisect_right(ps, n)]


def prime_count(x):
    x = F(x)
    if x < 2:
        return 0
    n = x.numerator // x.denominator
    primes_upto(n)
    return bisect_right(_SIEVE["primes"], n)


_MOB = {"n": 0, "mu": None, "M": None}
_FLIP = bytes([1, 0]) + bytes(254)


def _moebius_table(n):
    n = int(n)
    if n > 10_000_000:
        raise ValueError("the Moebius and Mertens tables are offered up to 10,000,000")
    if n > _MOB["n"]:
        m = max(n, 1000)
        par, sqf = bytearray(m + 1), bytearray(b"\x01") * (m + 1)
        for p in primes_upto(m):
            par[p::p] = par[p::p].translate(_FLIP)
            if p * p <= m:
                sqf[p * p::p * p] = bytes(len(range(p * p, m + 1, p * p)))
        mu = [0] + [(1 - 2 * par[i]) if sqf[i] else 0 for i in range(1, m + 1)]
        _MOB["n"], _MOB["mu"], _MOB["M"] = m, mu, list(accumulate(mu))
    return _MOB


def moebius(n):
    n = int(n)
    if n < 1:
        raise ValueError("mobius(n) needs n = 1, 2, 3, ...")
    return _moebius_table(n)["mu"][n]


def mertens(n):
    n = int(n)
    if n < 1:
        raise ValueError("mertens(n) needs n = 1, 2, 3, ...")
    return _moebius_table(n)["M"][n]


def mertens_extreme(lo, hi):
    """[m, M(m)] where |M(m)| / sqrt(m) is largest for lo <= m <= hi (first such m)."""
    lo, hi = int(lo), int(hi)
    if not 1 <= lo <= hi:
        raise ValueError("mertens_extreme(lo, hi) needs 1 <= lo <= hi")
    M = _moebius_table(hi)["M"]
    bm, bv = lo, M[lo]
    for m in range(lo + 1, hi + 1):
        v = M[m]
        if v * v * bm > bv * bv * m:
            bm, bv = m, v
    return [bm, bv]


# ------------------------------------------------------------------ Gauss: the logarithmic integral
@lru_cache(maxsize=None)
def euler_gamma_fx(D):
    D2 = D + GUARD
    n = 40
    h = sum(F(1, k) for k in range(1, n + 1)) - F(1, 2 * n)
    for k in range(1, 36):
        h += bernoulli(2 * k) / (2 * k * F(n) ** (2 * k))
    return tq(fx(h, D2) - ln_fx(F(n), D2), 10 ** GUARD)


def li_fx(x, D=WORK):
    """li(x) = gamma + ln ln x + sum (ln x)^k / (k k!), for x > 1."""
    x = F(x)
    if x <= 1:
        raise ValueError("li(x) is offered for x > 1")
    D2 = D + GUARD
    S = 10 ** D2
    L = ln_fx(x, D2)
    tot = euler_gamma_fx(D2) + ln_fx(F(L, S), D2)
    term, k = S, 0
    while True:
        k += 1
        term = tq(term * L, S * k)                           # (ln x)^k / k!
        if term == 0:
            break
        tot += tq(term, k)
    return tq(tot, 10 ** GUARD)


def chebyshev_psi_fx(x, D=WORK):
    """psi(x) = sum of ln p over prime powers p^k <= x."""
    x = F(x)
    n = x.numerator // x.denominator
    tot = 0
    for p in primes_upto(n):
        k, q = 0, p
        while q <= n:
            k += 1
            q *= p
        tot += k * ln_fx(F(p), D)
    return tot


# ------------------------------------------------------------------ Hardy and Siegel: theta, the correction terms, Z
def theta_fx(t, D=WORK):
    """Riemann-Siegel theta(t) for t >= 5 from its Stirling series."""
    t = F(t)
    if t < 5:
        raise ValueError("theta(t) is offered for t >= 5")
    D2 = D + GUARD
    lt = ln_fx(t, D2) - ln2_fx(D2) - lnpi_fx(D2)             # ln(t / 2 pi)
    v = tq(t.numerator * lt, 2 * t.denominator) - fx(t / 2, D2) - pi_fx(D2) // 8
    prev = None
    for k in range(1, 40):
        c = (2 ** (2 * k - 1) - 1) * abs(bernoulli(2 * k)) / (2 ** (2 * k + 1) * k * (2 * k - 1) * t ** (2 * k - 1))
        term = fx(c, D2)
        if term == 0 or (prev is not None and term >= prev):
            break
        v += term
        prev = term
    return tq(v, 10 ** GUARD)


_PSI = {}


def _psi_series():
    """Coefficients q_i of psi = cos(pi z^2/2 + 3 pi/8) / cos(pi z) = sum q_i z^(2i), with z = 2p - 1, at 170 decimals."""
    if _PSI:
        return _PSI
    Dc, M = 170, 76
    S = 10 ** Dc
    pi = pi_fx(Dc)
    c38, s38 = cos_sin_fx(3 * pi // 8, Dc)
    half = pi // 2
    hp = [S]                                                 # (pi/2)^j
    for _ in range(2 * M + 2):
        hp.append(tq(hp[-1] * half, S))
    pp = [S]                                                 # pi^(2j)
    pi2 = tq(pi * pi, S)
    for _ in range(M + 1):
        pp.append(tq(pp[-1] * pi2, S))
    a = [0] * (M + 1)                                        # numerator in w = z^2
    for j in range(M + 1):
        if 2 * j <= M:
            a[2 * j] += (-1) ** j * tq(tq(c38 * hp[2 * j], S), factorial(2 * j))
        if 2 * j + 1 <= M:
            a[2 * j + 1] -= (-1) ** j * tq(tq(s38 * hp[2 * j + 1], S), factorial(2 * j + 1))
    d = [(-1) ** j * tq(pp[j], factorial(2 * j)) for j in range(M + 1)]   # cos(pi z) in w
    q = []
    for i in range(M + 1):
        acc = a[i] - sum(tq(d[j] * q[i - j], S) for j in range(1, i + 1))
        q.append(acc)                                        # d[0] = 1
    _PSI.update(Dc=Dc, q=q)
    return _PSI


@lru_cache(maxsize=None)
def _psi_derivative_coefs(m, D):
    tab = _psi_series()
    drop = 10 ** (tab["Dc"] - D)
    lo = (m + 1) // 2
    return lo, [tq(q * (factorial(2 * i) // factorial(2 * i - m)), drop) for i, q in enumerate(tab["q"]) if i >= lo]


def psi_derivative_fx(m, p_fx, D):
    """The m-th derivative of psi with respect to p, at a scaled p in [0, 1]."""
    S = 10 ** D
    z = 2 * p_fx - S
    w = tq(z * z, S)
    lo, coefs = _psi_derivative_coefs(m, D)
    tot = 0
    for c in reversed(coefs):                                # Horner in w = z^2
        tot = tq(tot * w, S) + c
    if 2 * lo - m == 1:
        tot = tq(tot * z, S)
    return tot * 2 ** m


_CTERMS = {
    0: [(0, F(1), 0)],
    1: [(3, F(-1, 96), 2)],
    2: [(6, F(1, 18432), 4), (2, F(1, 64), 2)],
    3: [(9, F(-1, 5308416), 6), (5, F(-1, 3840), 4), (1, F(-1, 64), 2)],
    4: [(12, F(1, 2038431744), 8), (8, F(11, 5898240), 6), (4, F(19, 24576), 4), (0, F(1, 128), 2)],
}


def siegel_term_fx(k, p_fx, D):
    """C_k(p): the k-th Riemann-Siegel correction term, k = 0..4 (derivative order, rational factor, power of pi)."""
    if k not in _CTERMS:
        raise ValueError("correction terms are offered for k = 0, 1, 2, 3, 4")
    S = 10 ** D
    pi = pi_fx(D)
    tot = 0
    for m, c, e in _CTERMS[k]:
        v = psi_derivative_fx(m, p_fx, D)
        for _ in range(e):
            v = tq(v * S, pi)
        tot += tq(v * c.numerator, c.denominator)
    return tot


def siegel_z_fx(t, k=4, D=WORK):
    """Hardy's Z(t) from the Riemann-Siegel formula with correction terms C_0..C_k, for t >= 7."""
    t = F(t)
    k = int(k)
    if t < 7:
        raise ValueError("Z(t) is offered for t >= 7")
    if not 0 <= k <= 4:
        raise ValueError("the number of correction terms beyond C0 is 0, 1, 2, 3 or 4")
    S = 10 ** D
    a = isqrt(tq(fx(t, D) * S, 2 * pi_fx(D)) * S)                # sqrt(t / 2 pi), scaled
    N = a // S
    p = a - N * S
    th = theta_fx(t, D)
    main = 0
    for n in range(1, N + 1):
        c, _ = cos_sin_fx(th - tq(t.numerator * ln_fx(F(n), D), t.denominator), D)
        main += tq(c * S, sqrt_fx(n, D))
    corr, apow = 0, S
    for j in range(k + 1):
        corr += tq(siegel_term_fx(j, p, D) * S, apow)
        apow = tq(apow * a, S)
    corr = tq(corr * S, isqrt(a * S))
    return 2 * main + (corr if N % 2 == 1 else -corr)


_ZEROS = []


def zeta_zeros(n, D=30):
    """Heights of the first n zeros on the critical line (n <= 200), by sign changes of Z with four correction terms."""
    n = int(n)
    if not 1 <= n <= 200:
        raise ValueError("zeros are offered for n = 1 .. 200")
    if len(_ZEROS) < n:
        t = _ZEROS[-1] + F(1, 16) if _ZEROS else F(10)
        f = siegel_z_fx(t, 4, D)
        while len(_ZEROS) < n:
            u = t + F(1, 8)
            g = siegel_z_fx(u, 4, D)
            if (f < 0) != (g < 0):
                x, y, fx_ = t, u, f
                for _ in range(40):
                    m = (x + y) / 2
                    fm = siegel_z_fx(m, 4, D)
                    if (fx_ < 0) != (fm < 0):
                        y = m
                    else:
                        x, fx_ = m, fm
                _ZEROS.append((x + y) / 2)
            t, f = u, g
    return _ZEROS[:n]


def explicit_psi_fx(x, n, D=WORK):
    """Riemann's explicit formula cut off after n zeros: x - sum over zeros - ln 2 pi - (1/2) ln(1 - x^-2)."""
    x = F(x)
    if x <= 1:
        raise ValueError("the explicit formula is offered for x > 1")
    S = 10 ** D
    L = ln_fx(x, D)
    rootx = sqrt_fx(x, D)
    tot = 0
    for g in zeta_zeros(n):
        c, s = cos_sin_fx(tq(g.numerator * L, g.denominator), D)
        num = c // 2 + tq(g.numerator * s, g.denominator)        # (1/2) cos + gamma sin
        den = F(1, 4) + g * g
        tot += tq(num * den.denominator, den.numerator)
    tot = tq(2 * rootx * tot, S)
    return fx(x, D) - tot - (ln2_fx(D) + lnpi_fx(D)) - ln_fx(1 - 1 / (x * x), D) // 2
