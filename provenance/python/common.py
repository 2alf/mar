"""Common exact arithmetic for genus of X0(N) and Atkin-Lehner quotients.

All counts are exact (integers / Fractions).  No floating point except where
explicitly marked (analytic bounds).
"""
from fractions import Fraction
from math import gcd, isqrt
from functools import lru_cache


# ---------------------------------------------------------------- arithmetic
@lru_cache(maxsize=None)
def factor(n):
    """Return tuple of (p, k) with n = prod p^k (trial division; n >= 1)."""
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            k = 0
            while n % d == 0:
                n //= d
                k += 1
            out.append((d, k))
        d += 1 if d == 2 else 2
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def divisors(n):
    ds = [1]
    for p, k in factor(n):
        ds = [d * p ** i for d in ds for i in range(k + 1)]
    return sorted(ds)


def phi(n):
    r = n
    for p, _ in factor(n):
        r = r // p * (p - 1)
    return r


def is_prime(n):
    return n >= 2 and factor(n) == ((n, 1),)


def exact_divisors(n):
    """Hall divisors Q || n (gcd(Q, n/Q) = 1)."""
    return [q for q in divisors(n) if gcd(q, n // q) == 1]


def kron(D, p):
    """Kronecker symbol (D/p) for a prime p."""
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 in (1, 7) else -1
    r = D % p
    if r == 0:
        return 0
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1


# ------------------------------------------------------- quadratic forms / h
def reduced_forms(D):
    """All reduced positive definite forms (a,b,c), b^2-4ac = D < 0
    (including non-primitive ones).  |b| <= a <= c, b >= 0 if |b| = a or a = c."""
    assert D < 0 and D % 4 in (0, 1)
    n = -D
    out = []
    for a in range(1, isqrt(n // 3) + 1):
        for b in range(-a + 1, a + 1):
            if (b * b + n) % (4 * a):
                continue
            c = (b * b + n) // (4 * a)
            if c < a or (b < 0 and c == a):
                continue
            out.append((a, b, c))
    return out


def class_number_slow(D):
    return sum(1 for (a, b, c) in reduced_forms(D) if gcd(gcd(a, b), c) == 1)


class ClassNumbers:
    """Fast h(D) for many D via per-a residue tables of b with b^2 = -n mod 4a."""

    def __init__(self, nmax):
        self.nmax = nmax
        self.amax = isqrt(nmax // 3) + 1
        self.T = [None]
        for a in range(1, self.amax + 1):
            m = 4 * a
            d = {}
            for b in range(-a + 1, a + 1):
                d.setdefault((-b * b) % m, []).append(b)
            self.T.append(d)
        self.cache = {}

    def h(self, D):
        """Number of primitive reduced forms of discriminant D < 0."""
        if D in self.cache:
            return self.cache[D]
        n = -D
        assert 0 < n <= self.nmax and D % 4 in (0, 1)
        cnt = 0
        T = self.T
        for a in range(1, isqrt(n // 3) + 1):
            lst = T[a].get(n % (4 * a))
            if not lst:
                continue
            for b in lst:
                c = (b * b + n) // (4 * a)
                if c < a or (b < 0 and c == a):
                    continue
                if gcd(gcd(a, b), c) != 1:
                    continue
                cnt += 1
        self.cache[D] = cnt
        return cnt


# --------------------------------------------------------------- X0(N) genus
def x0_data(N):
    """(mu, nu2, nu3, cusps, genus) for X0(N)."""
    f = factor(N)
    mu = N
    for p, _ in f:
        mu = mu // p * (p + 1)
    if N % 4 == 0:
        nu2 = 0
    else:
        nu2 = 1
        for p, _ in f:
            nu2 *= 1 + kron(-4, p)
    if N % 9 == 0:
        nu3 = 0
    else:
        nu3 = 1
        for p, _ in f:
            nu3 *= 1 + kron(-3, p)
    cusps = sum(phi(gcd(d, N // d)) for d in divisors(N))
    g = 1 + Fraction(mu, 12) - Fraction(nu2, 4) - Fraction(nu3, 3) - Fraction(cusps, 2)
    assert g.denominator == 1
    return mu, nu2, nu3, cusps, int(g)


def genus_x0(N):
    return x0_data(N)[4]


# ------------------------------------------------- Atkin-Lehner fixed points
def fixed_terms(Q):
    """Elliptic elements W of the coset w_Q*Gamma0(N): trace t (Q | t, t^2<4Q),
    fixed-point form f = g*f0 with f0 primitive of discriminant D0,
    g^2*D0 = t^2-4Q, gcd(g,Q)=1 (proved: p|g, p|Q contradicts det W = Q).
    Returns list of (t, g, D0)."""
    out = []
    ts = [0] + ([Q, -Q] if Q < 4 else [])
    for t in ts:
        disc = t * t - 4 * Q
        for g in range(1, isqrt(-disc) + 1):
            if disc % (g * g):
                continue
            D0 = disc // (g * g)
            if D0 % 4 not in (0, 1):
                continue
            if gcd(g, Q) != 1:
                continue
            out.append((t, g, D0))
    return out


def aut_weight(D0):
    """1/|Aut(f0)/{+-1}| for primitive f0 of discriminant D0."""
    return Fraction(1, 3) if D0 == -3 else Fraction(1, 2) if D0 == -4 else Fraction(1)


def local_factor(p, k, g, D0, Q):
    """Closed-form local count L_p: number of (a:c) in P^1(Z/p^k) such that
    (g*f0) o gamma has p^k | A' (and, for p | Q, B' = t mod p^k resp. 2^(k+1)).
    Derivation in RESULTS.md; verified against brute force (verify_local.py)."""
    if Q % p == 0:
        return 1 if g % p else 0
    if p != 2:
        return 1 + kron(D0, p)  # p odd, p does not divide g*D0
    # p = 2, Q odd
    if g == 1 and D0 == -4 * Q:
        if k == 1:
            return 1
        if k == 2:
            return 2 if Q % 4 == 3 else 0
        return 4 if Q % 8 == 7 else 0
    if g == 2 and D0 == -Q:
        if k == 1:
            return 3
        return 2 * (1 + kron(D0, 2))
    if g == 1 and D0 == -3:   # Q = 3, t = +-3
        return 0
    raise ValueError((p, k, g, D0, Q))


def cusp_fixed_formula(N, Q):
    """Number of cusps of X0(N) fixed by w_Q (brute force shows: only Q = 4,
    where it equals the number of cusps of X0(N/4)), see verify_cusps.py."""
    if Q != 4:
        return 0
    M = N // 4
    return sum(phi(gcd(d, M // d)) for d in divisors(M))


def nu_formula(N, Q, hfun):
    """Number of fixed points of w_Q on X0(N) (Q || N, Q > 1)."""
    M = N // Q
    fM = factor(M)
    tot = Fraction(0)
    for (t, g, D0) in fixed_terms(Q):
        loc = 1
        for p, k in fM:
            loc *= local_factor(p, k, g, D0, Q)
            if loc == 0:
                break
        if loc:
            tot += aut_weight(D0) * hfun(D0) * loc
    tot += cusp_fixed_formula(N, Q)
    assert tot.denominator == 1, (N, Q, tot)
    return int(tot)


def al_mult(Q1, Q2):
    g = gcd(Q1, Q2)
    return Q1 * Q2 // (g * g)


def al_closure(N, gens):
    W = {1}
    for q in gens:
        assert N % q == 0 and gcd(q, N // q) == 1, (N, q)
        W |= {al_mult(w, q) for w in W}
    # close
    changed = True
    while changed:
        changed = False
        for a in list(W):
            for b in list(W):
                c = al_mult(a, b)
                if c not in W:
                    W.add(c)
                    changed = True
    return sorted(W)


def genus_quotient(N, W, nu):
    """Genus of X0(N)/W (W a list of Hall divisors incl. 1, a group);
    nu(N,Q) = number of fixed points of w_Q.  Returns Fraction (should be int)."""
    g = genus_x0(N)
    s = sum(nu(N, Q) for Q in W if Q != 1)
    return 1 + Fraction(2 * g - 2 - s, 2 * len(W))


def genus_plus(N, hfun):
    W = exact_divisors(N)
    return genus_quotient(N, W, lambda n, q: nu_formula(n, q, hfun))


# ------------------------------------------------------------------ sporadics
SPORADIC = {
    "M11": {2: 4, 3: 2, 5: 1, 11: 1},
    "M12": {2: 6, 3: 3, 5: 1, 11: 1},
    "M22": {2: 7, 3: 2, 5: 1, 7: 1, 11: 1},
    "M23": {2: 7, 3: 2, 5: 1, 7: 1, 11: 1, 23: 1},
    "M24": {2: 10, 3: 3, 5: 1, 7: 1, 11: 1, 23: 1},
    "J1": {2: 3, 3: 1, 5: 1, 7: 1, 11: 1, 19: 1},
    "J2": {2: 7, 3: 3, 5: 2, 7: 1},
    "J3": {2: 7, 3: 5, 5: 1, 17: 1, 19: 1},
    "J4": {2: 21, 3: 3, 5: 1, 7: 1, 11: 3, 23: 1, 29: 1, 31: 1, 37: 1, 43: 1},
    "Co1": {2: 21, 3: 9, 5: 4, 7: 2, 11: 1, 13: 1, 23: 1},
    "Co2": {2: 18, 3: 6, 5: 3, 7: 1, 11: 1, 23: 1},
    "Co3": {2: 10, 3: 7, 5: 3, 7: 1, 11: 1, 23: 1},
    "Fi22": {2: 17, 3: 9, 5: 2, 7: 1, 11: 1, 13: 1},
    "Fi23": {2: 18, 3: 13, 5: 2, 7: 1, 11: 1, 13: 1, 17: 1, 23: 1},
    "Fi24'": {2: 21, 3: 16, 5: 2, 7: 3, 11: 1, 13: 1, 17: 1, 23: 1, 29: 1},
    "HS": {2: 9, 3: 2, 5: 3, 7: 1, 11: 1},
    "McL": {2: 7, 3: 6, 5: 3, 7: 1, 11: 1},
    "He": {2: 10, 3: 3, 5: 2, 7: 3, 17: 1},
    "Ru": {2: 14, 3: 3, 5: 3, 7: 1, 13: 1, 29: 1},
    "Suz": {2: 13, 3: 7, 5: 2, 7: 1, 11: 1, 13: 1},
    "O'N": {2: 9, 3: 4, 5: 1, 7: 3, 11: 1, 19: 1, 31: 1},
    "HN": {2: 14, 3: 6, 5: 6, 7: 1, 11: 1, 19: 1},
    "Ly": {2: 8, 3: 7, 5: 6, 7: 1, 11: 1, 31: 1, 37: 1, 67: 1},
    "Th": {2: 15, 3: 10, 5: 3, 7: 2, 13: 1, 19: 1, 31: 1},
    "B": {2: 41, 3: 13, 5: 6, 7: 2, 11: 1, 13: 1, 17: 1, 19: 1, 23: 1, 31: 1, 47: 1},
    "M": {2: 46, 3: 20, 5: 9, 7: 6, 11: 2, 13: 3, 17: 1, 19: 1, 23: 1, 29: 1,
          31: 1, 41: 1, 47: 1, 59: 1, 71: 1},
}
# decimal orders as remembered from the ATLAS, used as a consistency check
SPORADIC_ORDER = {
    "M11": 7920, "M12": 95040, "M22": 443520, "M23": 10200960, "M24": 244823040,
    "J1": 175560, "J2": 604800, "J3": 50232960, "J4": 86775571046077562880,
    "Co1": 4157776806543360000, "Co2": 42305421312000, "Co3": 495766656000,
    "Fi22": 64561751654400, "Fi23": 4089470473293004800,
    "Fi24'": 1255205709190661721292800, "HS": 44352000, "McL": 898128000,
    "He": 4030387200, "Ru": 145926144000, "Suz": 448345497600,
    "O'N": 460815505920, "HN": 273030912000000, "Ly": 51765179004000000,
    "Th": 90745943887872000, "B": 4154781481226426191177580544000000,
    "M": 808017424794512875886459904961710757005754368000000000,
}


def sporadic_check():
    bad = []
    for k, f in SPORADIC.items():
        v = 1
        for p, e in f.items():
            v *= p ** e
        if v != SPORADIC_ORDER[k]:
            bad.append(k)
    return bad
