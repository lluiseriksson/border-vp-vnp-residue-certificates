"""Generate 16 exact-Fp/Z BORDER-VPVNP-CERT-1.0 certificates and 4 reproducible experiments for Paper 21.
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
import math
import pathlib
import sys
import time
from typing import Any, Dict, List

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.cartier_certifier import SCHEMA_VERSION, verify_border_vpvnp_certificate_exact
from src.cartier_residue_exact import (
    LaurentFp,
    cartier_operator_fp,
    laurent_add,
    laurent_mul,
    laurent_pow_naive,
    normalize_laurent,
    residue_fp,
)

RESULTS = ROOT / "results"
CERTS = RESULTS / "certificates"
CERTS.mkdir(parents=True, exist_ok=True)


def _laurent_json(poly: LaurentFp) -> Dict[str, int]:
    return {str(k): int(v) for k, v in sorted(poly.items())}


def _build_mode1_cert(name: str, p: int, salt: int) -> Dict[str, Any]:
    A = normalize_laurent({-2: 1 + (salt % (p - 1)), 0: 1 + ((salt + 1) % (p - 1)), 1: 1 + ((salt + 2) % (p - 1)), 3: 1}, p)
    eta = normalize_laurent({
        -p - 1: 1,
        -1: 1 + (salt % (p - 1)),
        p - 1: 1 + ((salt + 1) % (p - 1)),
        2 * p - 1: 1,
        p: 1,
    }, p)
    c_eta = cartier_operator_fp(eta, p)
    c_ap_eta = cartier_operator_fp(laurent_mul(laurent_pow_naive(A, p, p), eta, p), p)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "cartier_operator_semilinear_exact",
        "name": name,
        "prime_p": p,
        "poly_A": _laurent_json(A),
        "diff_eta": _laurent_json(eta),
        "claimed_cartier_eta": _laurent_json(c_eta),
        "claimed_cartier_Ap_eta": _laurent_json(c_ap_eta),
        "claimed_residue": residue_fp(eta, p),
    }


def _build_mode2_cert(name: str, p: int, n_paths: int, max_pole: int, z_target: int) -> Dict[str, Any]:
    # Construct n_paths Laurent series with genuine poles up to t^{-max_pole} that cancel identically in the sum!
    paths: List[LaurentFp] = []
    pole_sum: Dict[int, int] = {}
    for idx in range(n_paths - 1):
        pl: Dict[int, int] = {}
        for k in range(1, max_pole + 1):
            c = 1 + ((idx * 3 + k + 1) % (p - 1))
            pl[-k] = c
            pole_sum[-k] = (pole_sum.get(-k, 0) + c) % p
        pl[0] = (1 + idx) % p or 1
        pl[1] = 1
        pl[2] = 1 + (idx % (p - 1))
        paths.append(normalize_laurent(pl, p))
    # Final path cancels all negative poles exactly and adjusts constant term to hit z_target
    last: Dict[int, int] = {}
    for k in range(1, max_pole + 1):
        rem = (-pole_sum.get(-k, 0)) % p
        if rem != 0:
            last[-k] = rem
    cur_z = sum(pl.get(0, 0) for pl in paths) % p
    need_z = (z_target - cur_z) % p
    if need_z != 0:
        last[0] = need_z
    last[1] = 1
    paths.append(normalize_laurent(last, p))

    total: LaurentFp = {}
    for pl in paths:
        total = laurent_add(total, pl, p)
    assert all(e >= 0 for e in total)
    assert total.get(0, 0) == z_target % p

    # Test differential eta = c_{-1} t^{-1} + t^{-min(p, 3)} + t^0 dt (pole order <= p!)
    pole_test = min(p, 3)
    eta_raw = {-1: 1 + (z_target % (p - 1)), 0: 1}
    if pole_test > 1:
        eta_raw[-pole_test] = 1
    eta = normalize_laurent(eta_raw, p)
    res_ap = residue_fp(laurent_mul(laurent_pow_naive(total, p, p), eta, p), p)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "boundary_pole_cancellation_residue_exact",
        "name": name,
        "prime_p": p,
        "path_laurents": [_laurent_json(pl) for pl in paths],
        "test_diff_eta": _laurent_json(eta),
        "claimed_boundary_z": z_target % p,
        "claimed_test_residue": res_ap,
    }


def _build_mode3_cert(name: str, p: int, d: int, r_pins: int, salt: int) -> Dict[str, Any]:
    # Nonzero eigenvector Omega = [1, 1, ..., 1] mod p; build matrices W_k with row sums == lambda_k mod p
    omega = [1] * d
    eigs = [1 + ((salt + k * 2) % (p - 1)) for k in range(r_pins)]
    coeffs = [1 + ((salt + k * 3 + 1) % (p - 1)) for k in range(r_pins)]
    mats = []
    for k, lam in enumerate(eigs):
        M = []
        for i in range(d):
            row = [((salt + k * 5 + i * 3 + j) % p) for j in range(d - 1)]
            last_entry = (lam - sum(row)) % p
            row.append(last_entry)
            M.append(row)
        mats.append(M)
    comb_z = sum(c * lam for c, lam in zip(coeffs, eigs)) % p
    return {
        "schema": SCHEMA_VERSION,
        "mode": "residue_pin_eigenvector_exact",
        "name": name,
        "prime_p": p,
        "dim_d": d,
        "omega_vec": omega,
        "pin_matrices": mats,
        "pin_eigenvalues": eigs,
        "path_coeffs": coeffs,
        "claimed_combined_z": comb_z,
    }


def _build_mode4_cert(
    name: str, D: int, m: int, w: int, lA: int, t: int, minor: List[int], B: int,
    qds: List[int], dmax: int, u: int, k: int
) -> Dict[str, Any]:
    return {
        "schema": SCHEMA_VERSION,
        "mode": "hinge_shortening_and_border_barrier_exact",
        "name": name,
        "dim_D": D,
        "width_m": m,
        "cost_w": w,
        "log2_A": lA,
        "tensor_power_t": t,
        "minor_2x2": minor,
        "entry_bound_B": B,
        "query_degrees": qds,
        "max_query_degree": dmax,
        "scale_u": u,
        "poly_degree_k": k,
    }


def main() -> None:
    certs: List[tuple[str, Dict[str, Any]]] = [
        # Mode 1: Exact Cartier semilinearity C_p(A^p eta) = A C_p(eta) & Res preservation (p = 3, 5, 7, 13)
        ("cartier_semilin_p3.cert.json", _build_mode1_cert("cartier_semilin_p3", 3, 1)),
        ("cartier_semilin_p5.cert.json", _build_mode1_cert("cartier_semilin_p5", 5, 2)),
        ("cartier_semilin_p7.cert.json", _build_mode1_cert("cartier_semilin_p7", 7, 3)),
        ("cartier_semilin_p13.cert.json", _build_mode1_cert("cartier_semilin_p13", 13, 4)),
        # Mode 2: Boundary pole-cancellation residue extraction (OpenAI Lemma 5.1)
        ("pole_cancel_p5_k3.cert.json", _build_mode2_cert("pole_cancel_p5_k3", 5, 3, 2, 3)),
        ("pole_cancel_p7_k4.cert.json", _build_mode2_cert("pole_cancel_p7_k4", 7, 4, 3, 5)),
        ("pole_cancel_p11_k5.cert.json", _build_mode2_cert("pole_cancel_p11_k5", 11, 5, 4, 7)),
        ("pole_cancel_p17_k6.cert.json", _build_mode2_cert("pole_cancel_p17_k6", 17, 6, 5, 11)),
        # Mode 3: Exact F_p residue pin eigenvector recovery (OpenAI Eq. 5.1 & Lemma 3.3)
        ("pin_eigen_p5_d3.cert.json", _build_mode3_cert("pin_eigen_p5_d3", 5, 3, 3, 1)),
        ("pin_eigen_p7_d4.cert.json", _build_mode3_cert("pin_eigen_p7_d4", 7, 4, 4, 2)),
        ("pin_eigen_p11_d6.cert.json", _build_mode3_cert("pin_eigen_p11_d6", 11, 6, 5, 3)),
        ("pin_eigen_p19_d8.cert.json", _build_mode3_cert("pin_eigen_p19_d8", 19, 8, 6, 4)),
        # Mode 4: Hinge strict shortening, Hadamard 2x2 minor, batching & exp((log n)^(5/4)) barrier
        ("hinge_barrier_D2_u3.cert.json", _build_mode4_cert("hinge_barrier_D2_u3", 2, 10, 28, 2, 4, [7, -5, 4, 9], 10, [3, 4, 4, 2], 4, 3, 2)),
        ("hinge_barrier_D3_u4.cert.json", _build_mode4_cert("hinge_barrier_D3_u4", 3, 12, 50, 3, 6, [-15, 12, 11, 18], 20, [5, 6, 4, 6, 5], 6, 4, 3)),
        ("hinge_barrier_D4_u5.cert.json", _build_mode4_cert("hinge_barrier_D4_u5", 4, 15, 80, 4, 8, [40, -35, 30, 45], 50, [7, 8, 8, 6, 7, 8], 8, 5, 4)),
        ("hinge_barrier_D5_u6.cert.json", _build_mode4_cert("hinge_barrier_D5_u6", 5, 20, 130, 5, 10, [90, -85, 80, 95], 100, [9, 10, 10, 8, 9, 10, 10], 10, 6, 5)),
    ]

    # Experiment 1: Certified Atlas (16 exact-Fp/Z certificates)
    atlas_rows = []
    for fname, cert in certs:
        (CERTS / fname).write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        t0 = time.perf_counter()
        summary = verify_border_vpvnp_certificate_exact(cert)
        dt_ms = (time.perf_counter() - t0) * 1000.0
        atlas_rows.append({"file": fname, "mode": cert["mode"], "verify_ms": round(dt_ms, 4), "summary": summary})
    (RESULTS / "exp1_certified_atlas.json").write_text(
        json.dumps({"experiment": "exp1_certified_atlas", "count": len(atlas_rows), "rows": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Experiment 2: Cartier Semilinearity & Frobenius Verification Scaling Across Primes p = 3..29
    cartier_rows = []
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29):
        c = _build_mode1_cert(f"cartier_p{p}", p, p)
        t0 = time.perf_counter()
        res = verify_border_vpvnp_certificate_exact(c)
        dt_ms = (time.perf_counter() - t0) * 1000.0
        cartier_rows.append({
            "prime_p": p,
            "terms_A": res["terms_A"],
            "terms_eta": res["terms_eta"],
            "residue": res["residue"],
            "verify_ms": round(dt_ms, 4),
        })
    (RESULTS / "exp2_cartier_prime_scaling.json").write_text(
        json.dumps({"experiment": "exp2_cartier_prime_scaling", "rows": cartier_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Experiment 3: Pole-Cancellation Boundary Residue Recovery Across Pole Orders (p = 5..23)
    pole_rows = []
    for p, n_paths, max_pole in [(5, 3, 2), (7, 4, 3), (11, 5, 5), (13, 6, 6), (17, 7, 8), (23, 8, 10)]:
        c = _build_mode2_cert(f"pole_p{p}", p, n_paths, max_pole, (p // 2) + 1)
        t0 = time.perf_counter()
        res = verify_border_vpvnp_certificate_exact(c)
        dt_ms = (time.perf_counter() - t0) * 1000.0
        pole_rows.append({
            "prime_p": p,
            "num_paths": n_paths,
            "max_path_pole": max_pole,
            "boundary_z": res["boundary_z"],
            "test_residue": res["test_residue"],
            "verify_ms": round(dt_ms, 4),
        })
    (RESULTS / "exp3_pole_cancellation_scaling.json").write_text(
        json.dumps({"experiment": "exp3_pole_cancellation_scaling", "rows": pole_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Experiment 4: OpenAI Theorem 1.1 exp((log n)^(5/4)) Border Lower Bound vs Fixed Polynomials n^2, n^4
    asymp_rows = []
    for log2_n in [16, 32, 64, 128, 256, 512, 1024]:
        ln_n = log2_n * math.log(2.0)
        asymp_rows.append({
            "log2_n": log2_n,
            "log2_openai_5_4": round((ln_n ** 1.25) / math.log(2.0), 3),
            "log2_n2": 2 * log2_n,
            "log2_n4": 4 * log2_n,
        })
    (RESULTS / "exp4_border_five_fourths.json").write_text(
        json.dumps({"experiment": "exp4_border_five_fourths", "rows": asymp_rows}, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"[PASS] Generated {len(atlas_rows)} certificates and all 4 experiment JSONs.")


if __name__ == "__main__":
    main()
