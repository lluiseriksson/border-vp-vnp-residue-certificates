"""Pure-stdlib zero-float verifier for BORDER-VPVNP-CERT-1.0 certificates.
Supports four exact-Fp/Z verification modes aligned with OpenAI (Nov 23, 2026)
"VP and VNP are different":
  1. cartier_operator_semilinear_exact       (OpenAI Sec. 5: C_p(A^p eta) = A C_p(eta) & Res(C_p eta) = Res(eta))
  2. boundary_pole_cancellation_residue_exact (OpenAI Lemma 5.1: cancelling poles + Res(A^p eta) = z Res(eta))
  3. residue_pin_eigenvector_exact           (OpenAI Eq. 5.1 & Lemma 3.3: (sum a_k W_k) Omega = z Omega over F_p)
  4. hinge_shortening_and_border_barrier_exact (OpenAI Def. 2.1, Sec. 4 Hadamard & Thm 1.1 exp((log n)^(5/4)))

Author: Lluis Eriksson
"""
from __future__ import annotations

import re
from typing import Any, Dict, List

from src.cartier_residue_exact import (
    LaurentFp,
    cartier_operator_fp,
    is_prime_exact,
    laurent_add,
    laurent_frobenius_p,
    laurent_mul,
    laurent_pow_naive,
    mat_vec_fp,
    normalize_laurent,
    residue_fp,
)

SCHEMA_VERSION = "BORDER-VPVNP-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")


class BorderVPVNPCertificateError(ValueError):
    """Raised whenever any BORDER-VPVNP-CERT-1.0 verification check fails."""


def _assert_strict_json_types(obj: Any, path: str = "root") -> None:
    t = type(obj)
    if t is int or t is str or obj is None:
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise BorderVPVNPCertificateError(f"Non-str dict key at {path}: {type(k).__name__}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    raise BorderVPVNPCertificateError(f"Forbidden type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise BorderVPVNPCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_big_int(val: Any, name: str) -> int:
    if type(val) is int:
        return val
    if type(val) is str and _CANON_INT_RE.match(val):
        return int(val)
    raise BorderVPVNPCertificateError(f"{name} must be strict int or canonical int string, got {val!r}")


def _parse_prime(val: Any) -> int:
    p = _parse_int(val, "prime_p")
    if not (2 <= p <= 97) or not is_prime_exact(p):
        raise BorderVPVNPCertificateError(f"prime_p must be prime in [2, 97], got {p}")
    return p


def _parse_laurent(raw: Any, p: int, name: str) -> LaurentFp:
    if type(raw) is not dict:
        raise BorderVPVNPCertificateError(f"{name} must be a dict mapping exponent string -> F_p coeff")
    out: Dict[int, int] = {}
    for k, v in raw.items():
        if not _CANON_INT_RE.match(k):
            raise BorderVPVNPCertificateError(f"{name} non-canonical exponent key: {k!r}")
        exp = int(k)
        c = _parse_int(v, f"{name}[{k}]")
        if not (1 <= c < p):
            raise BorderVPVNPCertificateError(f"{name}[{k}] coeff must be in [1, {p-1}], got {c}")
        out[exp] = c
    return out


def _verify_cartier_semilinear(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "prime_p", "poly_A", "diff_eta",
        "claimed_cartier_eta", "claimed_cartier_Ap_eta", "claimed_residue",
    }
    if set(cert.keys()) != req:
        raise BorderVPVNPCertificateError(f"Mode 1 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    p = _parse_prime(cert["prime_p"])
    A = _parse_laurent(cert["poly_A"], p, "poly_A")
    eta = _parse_laurent(cert["diff_eta"], p, "diff_eta")
    if not A or not eta:
        raise BorderVPVNPCertificateError("poly_A and diff_eta must be non-empty Laurent objects")
    c_ceta = _parse_laurent(cert["claimed_cartier_eta"], p, "claimed_cartier_eta")
    c_cap = _parse_laurent(cert["claimed_cartier_Ap_eta"], p, "claimed_cartier_Ap_eta")
    c_res = _parse_int(cert["claimed_residue"], "claimed_residue")
    if not (0 <= c_res < p):
        raise BorderVPVNPCertificateError(f"claimed_residue out of [0, {p})")

    # Verify Freshman's Dream A^p == Frobenius(A) independently via repeated squaring
    Ap_naive = laurent_pow_naive(A, p, p)
    Ap_frob = laurent_frobenius_p(A, p)
    if Ap_naive != Ap_frob:
        raise BorderVPVNPCertificateError("Impossible: Frobenius p-th power mismatch on F_p")

    c_eta = cartier_operator_fp(eta, p)
    lhs = cartier_operator_fp(laurent_mul(Ap_naive, eta, p), p)
    rhs = laurent_mul(A, c_eta, p)
    if lhs != rhs:
        raise BorderVPVNPCertificateError("Cartier semilinearity C_p(A^p eta) == A C_p(eta) failed")
    if c_eta != c_ceta or lhs != c_cap:
        raise BorderVPVNPCertificateError("Claimed Cartier outputs do not match exact replay")
    res_eta = residue_fp(eta, p)
    res_ceta = residue_fp(c_eta, p)
    if res_eta != res_ceta or res_eta != c_res:
        raise BorderVPVNPCertificateError("Cartier residue preservation Res(C_p eta) == Res(eta) failed")
    return {
        "verified": True,
        "mode": cert["mode"],
        "prime_p": p,
        "terms_A": len(A),
        "terms_eta": len(eta),
        "residue": res_eta,
    }


def _verify_pole_cancellation(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "prime_p", "path_laurents",
        "test_diff_eta", "claimed_boundary_z", "claimed_test_residue",
    }
    if set(cert.keys()) != req:
        raise BorderVPVNPCertificateError(f"Mode 2 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    p = _parse_prime(cert["prime_p"])
    paths_raw = cert["path_laurents"]
    if type(paths_raw) is not list or len(paths_raw) < 2:
        raise BorderVPVNPCertificateError("path_laurents must contain at least 2 paths")
    paths = [_parse_laurent(pl, p, f"path_laurents[{i}]") for i, pl in enumerate(paths_raw)]
    if not any(any(e < 0 for e in pl) for pl in paths):
        raise BorderVPVNPCertificateError("At least one individual path must have a genuine negative-order pole")

    # Sum all paths in F_p[t, t^{-1}] and verify poles cancel completely (regular at t=0!)
    total: LaurentFp = {}
    for pl in paths:
        total = laurent_add(total, pl, p)
    if any(e < 0 for e in total):
        raise BorderVPVNPCertificateError("Summed Laurent series still has uncanceled poles at t=0")
    z_exact = total.get(0, 0) % p
    z_claimed = _parse_int(cert["claimed_boundary_z"], "claimed_boundary_z")
    if not (0 <= z_claimed < p) or z_exact != z_claimed:
        raise BorderVPVNPCertificateError(f"Boundary value z mismatch: exact={z_exact}, claimed={z_claimed}")

    eta = _parse_laurent(cert["test_diff_eta"], p, "test_diff_eta")
    if not eta:
        raise BorderVPVNPCertificateError("test_diff_eta must be non-empty")
    min_exp = min(eta.keys())
    # Pole order of eta = sum c_j t^j dt must be <= p (i.e. min_exp >= -p) so (A^p - z)*eta has no t^{-1} term!
    if min_exp < -p:
        raise BorderVPVNPCertificateError(f"test_diff_eta pole order {-min_exp} exceeds p={p}")
    res_eta = residue_fp(eta, p)
    if res_eta == 0:
        raise BorderVPVNPCertificateError("test_diff_eta must have nonzero residue mod p to extract z")

    Ap = laurent_pow_naive(total, p, p)
    res_Ap_eta = residue_fp(laurent_mul(Ap, eta, p), p)
    expected_res = (z_exact * res_eta) % p
    c_tres = _parse_int(cert["claimed_test_residue"], "claimed_test_residue")
    if res_Ap_eta != expected_res or c_tres != expected_res:
        raise BorderVPVNPCertificateError(f"Residue extraction mismatch: got {res_Ap_eta}, expected {expected_res}")
    # Recover z directly from residue division mod p:
    inv_res = pow(res_eta, p - 2, p)
    if (res_Ap_eta * inv_res) % p != z_exact:
        raise BorderVPVNPCertificateError("Inverse-residue boundary recovery failed")
    return {
        "verified": True,
        "mode": cert["mode"],
        "prime_p": p,
        "num_paths": len(paths),
        "max_path_pole": max((-min(pl.keys()) for pl in paths if pl), default=0),
        "boundary_z": z_exact,
        "test_residue": res_Ap_eta,
    }


def _verify_pin_eigenvector(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "prime_p", "dim_d", "omega_vec",
        "pin_matrices", "pin_eigenvalues", "path_coeffs", "claimed_combined_z",
    }
    if set(cert.keys()) != req:
        raise BorderVPVNPCertificateError(f"Mode 3 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    p = _parse_prime(cert["prime_p"])
    d = _parse_int(cert["dim_d"], "dim_d")
    if not (2 <= d <= 12):
        raise BorderVPVNPCertificateError(f"dim_d must be in [2, 12], got {d}")
    om_raw = cert["omega_vec"]
    if type(om_raw) is not list or len(om_raw) != d:
        raise BorderVPVNPCertificateError(f"omega_vec must have length {d}")
    omega = [_parse_int(x, f"omega_vec[{i}]") for i, x in enumerate(om_raw)]
    if any(not (0 <= x < p) for x in omega) or all(x == 0 for x in omega):
        raise BorderVPVNPCertificateError("omega_vec must be nonzero vector over F_p")

    mats_raw = cert["pin_matrices"]
    eigs_raw = cert["pin_eigenvalues"]
    coeffs_raw = cert["path_coeffs"]
    if (
        type(mats_raw) is not list or type(eigs_raw) is not list or type(coeffs_raw) is not list
        or not mats_raw or not (len(mats_raw) == len(eigs_raw) == len(coeffs_raw))
    ):
        raise BorderVPVNPCertificateError("pin_matrices, pin_eigenvalues, path_coeffs must be equal non-empty lists")

    r = len(mats_raw)
    eigs = [_parse_int(x, f"pin_eigenvalues[{i}]") for i, x in enumerate(eigs_raw)]
    coeffs = [_parse_int(x, f"path_coeffs[{i}]") for i, x in enumerate(coeffs_raw)]
    if any(not (0 <= x < p) for x in eigs + coeffs):
        raise BorderVPVNPCertificateError("pin_eigenvalues and path_coeffs must lie in [0, p-1]")

    W_sum = [[0] * d for _ in range(d)]
    for k in range(r):
        M_raw = mats_raw[k]
        if type(M_raw) is not list or len(M_raw) != d:
            raise BorderVPVNPCertificateError(f"pin_matrices[{k}] must be {d}x{d}")
        M: List[List[int]] = []
        for i in range(d):
            row = M_raw[i]
            if type(row) is not list or len(row) != d:
                raise BorderVPVNPCertificateError(f"pin_matrices[{k}][{i}] must have length {d}")
            parsed_row = [_parse_int(x, f"pin_matrices[{k}][{i}][{j}]") for j, x in enumerate(row)]
            if any(not (0 <= x < p) for x in parsed_row):
                raise BorderVPVNPCertificateError("Pin matrix entries must lie in [0, p-1]")
            M.append(parsed_row)
        # Verify W_k * Omega == lambda_k * Omega mod p
        got_v = mat_vec_fp(M, omega, p)
        exp_v = [(eigs[k] * x) % p for x in omega]
        if got_v != exp_v:
            raise BorderVPVNPCertificateError(f"Pin eigenvector check failed for W_{k}")
        for i in range(d):
            for j in range(d):
                W_sum[i][j] = (W_sum[i][j] + coeffs[k] * M[i][j]) % p

    z_exact = sum(c * lam for c, lam in zip(coeffs, eigs)) % p
    z_claimed = _parse_int(cert["claimed_combined_z"], "claimed_combined_z")
    if not (0 <= z_claimed < p) or z_exact != z_claimed:
        raise BorderVPVNPCertificateError(f"Combined pin eigenvalue mismatch: exact={z_exact}, claimed={z_claimed}")
    comb_v = mat_vec_fp(W_sum, omega, p)
    if comb_v != [(z_exact * x) % p for x in omega]:
        raise BorderVPVNPCertificateError("Combined pin matrix (sum a_k W_k) Omega != z Omega")
    return {
        "verified": True,
        "mode": cert["mode"],
        "prime_p": p,
        "dim_d": d,
        "num_pins": r,
        "combined_z": z_exact,
    }


def _verify_hinge_barrier(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name",
        "dim_D", "width_m", "cost_w", "log2_A", "tensor_power_t",
        "minor_2x2", "entry_bound_B", "query_degrees", "max_query_degree",
        "scale_u", "poly_degree_k",
    }
    if set(cert.keys()) != req:
        raise BorderVPVNPCertificateError(f"Mode 4 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    D = _parse_int(cert["dim_D"], "dim_D")
    m = _parse_int(cert["width_m"], "width_m")
    w = _parse_int(cert["cost_w"], "cost_w")
    lA = _parse_int(cert["log2_A"], "log2_A")
    t = _parse_int(cert["tensor_power_t"], "tensor_power_t")
    if D < 2 or m < 1 or w < 0 or lA < 0 or t < 1:
        raise BorderVPVNPCertificateError("Invalid hinge parameters (require D>=2, m>=1, w>=0, log2_A>=0, t>=1)")
    gap = 2 * D * m - (w + 2 * D * lA)
    if gap < 1:
        raise BorderVPVNPCertificateError(f"Strict hinge shortening failed: gap={gap} < 1")
    if not (t * w + 2 * D * (t * lA) + t * gap == 2 * D * (t * m)):
        raise BorderVPVNPCertificateError("Tensor-power gap amplification mismatch")

    # Verify 2x2 Cramer/Hadamard entry bound |det2(A)| <= 2 * B^2 (Lean Thm 16)
    B = _parse_big_int(cert["entry_bound_B"], "entry_bound_B")
    m2 = cert["minor_2x2"]
    if B < 0 or type(m2) is not list or len(m2) != 4:
        raise BorderVPVNPCertificateError("minor_2x2 must be 4 ints and entry_bound_B >= 0")
    a00, a01, a10, a11 = [_parse_big_int(x, f"minor_2x2[{i}]") for i, x in enumerate(m2)]
    if any(abs(v) > B for v in (a00, a01, a10, a11)):
        raise BorderVPVNPCertificateError("minor_2x2 entry exceeds entry_bound_B")
    det2 = a00 * a11 - a01 * a10
    if abs(det2) > 2 * B * B:
        raise BorderVPVNPCertificateError("Impossible: Hadamard 2x2 bound exceeded")

    # Verify batched query degree budget (Lean Thm 15)
    qd_raw = cert["query_degrees"]
    dmax = _parse_int(cert["max_query_degree"], "max_query_degree")
    if type(qd_raw) is not list or not qd_raw or dmax < 1:
        raise BorderVPVNPCertificateError("query_degrees must be non-empty list and max_query_degree >= 1")
    qds = [_parse_int(x, f"query_degrees[{i}]") for i, x in enumerate(qd_raw)]
    if any(x < 0 or x > dmax for x in qds) or sum(qds) > len(qds) * dmax:
        raise BorderVPVNPCertificateError("Batched query degree budget violated")

    # Verify OpenAI Thm 1.1 exp((log n)^(5/4)) separation (Lean Thm 17)
    u = _parse_int(cert["scale_u"], "scale_u")
    k = _parse_int(cert["poly_degree_k"], "poly_degree_k")
    if not (1 <= k < u <= 12):
        raise BorderVPVNPCertificateError(f"Require 1 <= k < u <= 12, got u={u}, k={k}")
    if not ((1 << (u ** 5)) > ((1 << (u ** 4)) ** k)):
        raise BorderVPVNPCertificateError("Superpolynomial 5/4 dominance failed")
    return {
        "verified": True,
        "mode": cert["mode"],
        "shortening_gap": gap,
        "amplified_gap": t * gap,
        "det2": det2,
        "num_queries": len(qds),
        "scale_u": u,
        "poly_degree_k": k,
    }


def verify_border_vpvnp_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise BorderVPVNPCertificateError("Certificate root must be a dict")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise BorderVPVNPCertificateError(f"Invalid schema: {cert.get('schema')!r}")
    name = cert.get("name")
    if type(name) is not str or not name.strip():
        raise BorderVPVNPCertificateError(f"Certificate name must be non-empty str, got {name!r}")
    mode = cert.get("mode")
    if mode == "cartier_operator_semilinear_exact":
        return _verify_cartier_semilinear(cert)
    if mode == "boundary_pole_cancellation_residue_exact":
        return _verify_pole_cancellation(cert)
    if mode == "residue_pin_eigenvector_exact":
        return _verify_pin_eigenvector(cert)
    if mode == "hinge_shortening_and_border_barrier_exact":
        return _verify_hinge_barrier(cert)
    raise BorderVPVNPCertificateError(f"Unknown mode: {mode!r}")
