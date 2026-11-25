"""Pure-stdlib zero-float exact-Fp Laurent polynomial, Cartier operator, and pin-matrix engine.
Author: Lluis Eriksson
"""
from __future__ import annotations

from typing import Dict, List, Sequence

LaurentFp = Dict[int, int]  # exponent -> nonzero coeff in [1, p-1]


def is_prime_exact(p: int) -> bool:
    if p < 2:
        return False
    if p == 2:
        return True
    if p % 2 == 0:
        return False
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def normalize_laurent(poly: Dict[int, int], p: int) -> LaurentFp:
    out: LaurentFp = {}
    for exp, coeff in poly.items():
        c = coeff % p
        if c != 0:
            out[exp] = c
    return out


def laurent_add(a: LaurentFp, b: LaurentFp, p: int) -> LaurentFp:
    out = dict(a)
    for exp, coeff in b.items():
        out[exp] = (out.get(exp, 0) + coeff) % p
    return normalize_laurent(out, p)


def laurent_mul(a: LaurentFp, b: LaurentFp, p: int) -> LaurentFp:
    out: Dict[int, int] = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = e1 + e2
            out[e] = (out.get(e, 0) + c1 * c2) % p
    return normalize_laurent(out, p)


def laurent_pow_naive(a: LaurentFp, exp: int, p: int) -> LaurentFp:
    """Exact repeated-squaring power in F_p[t, t^{-1}]."""
    res: LaurentFp = {0: 1}
    base = normalize_laurent(a, p)
    k = exp
    while k > 0:
        if k & 1:
            res = laurent_mul(res, base, p)
        base = laurent_mul(base, base, p)
        k >>= 1
    return res


def laurent_frobenius_p(a: LaurentFp, p: int) -> LaurentFp:
    """Frobenius p-th power on F_p[t, t^{-1}]: (sum a_k t^k)^p = sum a_k t^{p*k} (since a_k^p = a_k mod p)."""
    return normalize_laurent({e * p: c for e, c in a.items()}, p)


def cartier_operator_fp(eta: LaurentFp, p: int) -> LaurentFp:
    """Exact Cartier operator C_p on F_p[t, t^{-1}] dt:
    C_p(sum_j v_j t^j dt) = sum_i v_{p*i + p - 1}^{1/p} t^i dt,
    where v^{1/p} = v over the prime field F_p by Fermat's little theorem.
    """
    out: Dict[int, int] = {}
    for j, v in eta.items():
        if (j - (p - 1)) % p == 0:
            i = (j - (p - 1)) // p
            out[i] = v % p
    return normalize_laurent(out, p)


def residue_fp(eta: LaurentFp, p: int) -> int:
    """Exact algebraic residue Res(eta) = coeff of t^{-1} dt mod p."""
    return eta.get(-1, 0) % p


def mat_vec_fp(M: Sequence[Sequence[int]], v: Sequence[int], p: int) -> List[int]:
    return [sum(M[i][j] * v[j] for j in range(len(v))) % p for i in range(len(M))]
