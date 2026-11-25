"""Gate-2 verification, independent algebraic cross-checks, and 54-attack live red-team suite for Paper 21.
Author: Lluis Eriksson
"""
from __future__ import annotations

import copy
import json
import pathlib
import sys
from decimal import Decimal

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.cartier_certifier import BorderVPVNPCertificateError, verify_border_vpvnp_certificate_exact
from src.cartier_residue_exact import (
    cartier_operator_fp,
    laurent_frobenius_p,
    laurent_mul,
    laurent_pow_naive,
    residue_fp,
)

CERTS_DIR = ROOT / "results" / "certificates"


def test_cartier_and_frobenius_algebraic_identities_across_primes() -> None:
    """Independently cross-check Freshman's Dream, Cartier semilinearity, and residue preservation."""
    for p in (2, 3, 5, 7, 11):
        A = {-1: 1, 0: (2 % p) or 1, 2: (3 % p) or 1}
        eta = {-p: 1, -1: (2 % p) or 1, p - 1: 1, p + 1: 1}
        assert laurent_pow_naive(A, p, p) == laurent_frobenius_p(A, p)
        lhs = cartier_operator_fp(laurent_mul(laurent_pow_naive(A, p, p), eta, p), p)
        rhs = laurent_mul(A, cartier_operator_fp(eta, p), p)
        assert lhs == rhs
        assert residue_fp(cartier_operator_fp(eta, p), p) == residue_fp(eta, p)


def test_all_16_certificates_verify_cleanly() -> None:
    files = sorted(CERTS_DIR.glob("*.cert.json"))
    assert len(files) == 16
    for f in files:
        res = verify_border_vpvnp_certificate_exact(json.loads(f.read_text(encoding="utf-8")))
        assert res["verified"] is True


def test_54_live_adversarial_red_team_attacks_rejected() -> None:
    c1 = json.loads((CERTS_DIR / "cartier_semilin_p5.cert.json").read_text(encoding="utf-8"))
    c2 = json.loads((CERTS_DIR / "pole_cancel_p5_k3.cert.json").read_text(encoding="utf-8"))
    c3 = json.loads((CERTS_DIR / "pin_eigen_p5_d3.cert.json").read_text(encoding="utf-8"))
    c4 = json.loads((CERTS_DIR / "hinge_barrier_D2_u3.cert.json").read_text(encoding="utf-8"))

    attacks = []

    def add(name, base, fn):
        cand = copy.deepcopy(base)
        fn(cand)
        attacks.append((name, cand))

    # Group A: Schema, Types & Canonical Keys (16 attacks)
    attacks.append(("01_root_not_dict", ["bad"]))
    add("02_wrong_schema", c1, lambda x: x.__setitem__("schema", "BORDER-VPVNP-CERT-9.9"))
    add("03_unknown_mode", c1, lambda x: x.__setitem__("mode", "bogus"))
    add("04_extra_key", c1, lambda x: x.__setitem__("evil", 1))
    add("05_missing_key", c1, lambda x: x.pop("poly_A"))
    add("06_float_injection", c1, lambda x: x["poly_A"].__setitem__("0", 1.5))
    add("07_bool_injection", c1, lambda x: x.__setitem__("prime_p", True))
    add("08_decimal_injection", c4, lambda x: x.__setitem__("entry_bound_B", Decimal("10")))
    add("09_complex_injection", c3, lambda x: x["omega_vec"].__setitem__(0, 1 + 0j))
    add("10_tuple_injection", c3, lambda x: x.__setitem__("omega_vec", tuple(x["omega_vec"])))
    add("11_non_str_key", c1, lambda x: x.__setitem__(99, "bad"))
    add("12_non_canon_exp_key", c1, lambda x: x["poly_A"].__setitem__("01", 1))
    add("13_neg_zero_exp_key", c1, lambda x: x["poly_A"].__setitem__("-0", 1))
    add("14_non_prime_p_composite", c1, lambda x: x.__setitem__("prime_p", 9))
    add("15_non_str_name", c1, lambda x: x.__setitem__("name", 123))
    add("16_empty_name", c1, lambda x: x.__setitem__("name", "  "))

    # Group B: Mode 1 Cartier Semilinearity Forgeries (9 attacks)
    add("17_zero_coeff_in_laurent", c1, lambda x: x["poly_A"].__setitem__("0", 0))
    add("18_coeff_ge_p", c1, lambda x: x["poly_A"].__setitem__("0", 5))
    add("19_empty_poly_A", c1, lambda x: x.__setitem__("poly_A", {}))
    add("20_empty_diff_eta", c1, lambda x: x.__setitem__("diff_eta", {}))
    add("21_forged_cartier_eta", c1, lambda x: x["claimed_cartier_eta"].__setitem__("-1", (x["claimed_cartier_eta"]["-1"] % 4) + 1))
    add("22_forged_cartier_Ap_eta", c1, lambda x: x["claimed_cartier_Ap_eta"].__setitem__("99", 1))
    add("23_forged_residue", c1, lambda x: x.__setitem__("claimed_residue", (x["claimed_residue"] + 1) % 5))
    add("24_residue_out_of_range", c1, lambda x: x.__setitem__("claimed_residue", -1))
    add("25_prime_too_large", c1, lambda x: x.__setitem__("prime_p", 101))

    # Group C: Mode 2 Pole-Cancellation Boundary Residue Forgeries (10 attacks)
    add("26_single_path_only", c2, lambda x: x.__setitem__("path_laurents", [x["path_laurents"][0]]))
    add("27_no_poles_in_paths", c2, lambda x: x.__setitem__("path_laurents", [{"0": 1}, {"0": 2}]))
    add("28_uncanceled_pole", c2, lambda x: x["path_laurents"][0].__setitem__("-1", (x["path_laurents"][0]["-1"] % 4) + 1))
    add("29_forged_boundary_z", c2, lambda x: x.__setitem__("claimed_boundary_z", (x["claimed_boundary_z"] + 1) % 5))
    add("30_forged_test_residue", c2, lambda x: x.__setitem__("claimed_test_residue", (x["claimed_test_residue"] + 1) % 5))
    add("31_eta_pole_exceeds_p", c2, lambda x: x["test_diff_eta"].__setitem__("-6", 1))
    add("32_eta_zero_residue", c2, lambda x: x["test_diff_eta"].pop("-1"))
    add("33_empty_test_eta", c2, lambda x: x.__setitem__("test_diff_eta", {}))
    add("34_boundary_z_oob", c2, lambda x: x.__setitem__("claimed_boundary_z", 5))
    add("35_non_prime_mode2", c2, lambda x: x.__setitem__("prime_p", 4))

    # Group D: Mode 3 Pin Eigenvector Forgeries (9 attacks)
    add("36_zero_omega_vec", c3, lambda x: x.__setitem__("omega_vec", [0, 0, 0]))
    add("37_omega_wrong_len", c3, lambda x: x["omega_vec"].pop())
    add("38_omega_entry_ge_p", c3, lambda x: x["omega_vec"].__setitem__(0, 5))
    add("39_tampered_pin_matrix", c3, lambda x: x["pin_matrices"][0][0].__setitem__(0, (x["pin_matrices"][0][0][0] + 1) % 5))
    add("40_forged_pin_eigenvalue", c3, lambda x: x["pin_eigenvalues"].__setitem__(0, (x["pin_eigenvalues"][0] + 1) % 5))
    add("41_forged_combined_z", c3, lambda x: x.__setitem__("claimed_combined_z", (x["claimed_combined_z"] + 1) % 5))
    add("42_dim_d_below_2", c3, lambda x: x.__setitem__("dim_d", 1))
    add("43_mismatched_pin_list_lens", c3, lambda x: x["path_coeffs"].pop())
    add("44_wrong_pin_matrix_shape", c3, lambda x: x["pin_matrices"][0].pop())

    # Group E: Mode 4 Hinge Shortening, Hadamard & 5/4 Barrier Forgeries (10 attacks)
    add("45_dim_D_below_2", c4, lambda x: x.__setitem__("dim_D", 1))
    add("46_hinge_gap_closed", c4, lambda x: x.__setitem__("cost_w", 2 * x["dim_D"] * x["width_m"] - 2 * x["dim_D"] * x["log2_A"]))
    add("47_negative_cost_w", c4, lambda x: x.__setitem__("cost_w", -1))
    add("48_tensor_power_zero", c4, lambda x: x.__setitem__("tensor_power_t", 0))
    add("49_minor_exceeds_B", c4, lambda x: x["minor_2x2"].__setitem__(0, 999))
    add("50_negative_entry_bound", c4, lambda x: x.__setitem__("entry_bound_B", -1))
    add("51_query_exceeds_dmax", c4, lambda x: x["query_degrees"].__setitem__(0, x["max_query_degree"] + 1))
    add("52_empty_query_degrees", c4, lambda x: x.__setitem__("query_degrees", []))
    add("53_scale_u_le_k", c4, lambda x: x.__setitem__("scale_u", x["poly_degree_k"]))
    add("54_poly_k_zero", c4, lambda x: x.__setitem__("poly_degree_k", 0))

    assert len(attacks) == 54
    for name, cand in attacks:
        with pytest.raises(BorderVPVNPCertificateError):
            verify_border_vpvnp_certificate_exact(cand)
