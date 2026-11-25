"""Generate 3 publication-quality 300-DPI figures for Paper 21.
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
import pathlib

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.0,
    "axes.labelsize": 9.2,
    "legend.fontsize": 7.5,
    "xtick.labelsize": 8.4,
    "ytick.labelsize": 8.4,
    "axes.grid": True,
    "grid.alpha": 0.28,
    "grid.linestyle": "--",
})


def make_fig1() -> None:
    d2 = json.loads((RESULTS / "exp2_cartier_prime_scaling.json").read_text(encoding="utf-8"))
    d4 = json.loads((RESULTS / "exp4_border_five_fourths.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Exact Cartier semilinearity replay time across prime fields F_p (p = 3..29)
    r2 = d2["rows"]
    ps = [r["prime_p"] for r in r2]
    ax1.plot(ps, [r["verify_ms"] for r in r2], "o-", color="#1b6ca8", lw=2.1, ms=5.8,
             label=r"Exact-$\mathbb{F}_p$ $C_p(A^p\eta) = A\,C_p(\eta)$ replay")
    ax1.set_xticks(ps)
    ax1.set_xlabel(r"Prime field characteristic $p$")
    ax1.set_ylabel(r"Exact-$\mathbb{F}_p$ verification latency (ms)")
    ax1.set_title(r"(a) Cartier Semilinearity Replay Across $\mathbb{F}_p$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94)

    # Panel (b): OpenAI Thm 1.1 exp((log n)^(5/4)) border circuit lower bound vs n^2, n^4
    r4 = d4["rows"]
    xs = [r["log2_n"] for r in r4]
    ax2.plot(xs, [r["log2_openai_5_4"] for r in r4], "o-", color="#c1121f", lw=2.2, ms=5.8,
             label=r"OpenAI Thm. 1.1 ($c=1$): $(\ln n)^{5/4}/\ln 2$")
    ax2.plot(xs, [r["log2_n4"] for r in r4], "s--", color="#1b6ca8", lw=1.9, ms=5.2,
             label=r"Polynomial $n^4$ ($\log_2 = 4\log_2 n$)")
    ax2.plot(xs, [r["log2_n2"] for r in r4], "^:", color="#2a9d8f", lw=1.9, ms=5.2,
             label=r"Polynomial $n^2$ ($\log_2 = 2\log_2 n$)")
    ax2.set_xscale("log", base=2)
    ax2.set_xticks(xs)
    ax2.set_xticklabels([str(x) for x in xs])
    ax2.set_xlabel(r"Problem scale $\log_2 n$")
    ax2.set_ylabel(r"$\log_2(\text{border circuit size lower bound})$")
    ax2.set_title(r"(b) Border $\mathsf{VP}\neq\mathsf{VNP}$ Crossover ($\exp((\ln n)^{5/4})$)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.94)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_cartier_and_crossover.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((RESULTS / "exp3_pole_cancellation_scaling.json").read_text(encoding="utf-8"))
    rows = d3["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    ps = [r["prime_p"] for r in rows]
    l1 = ax1.plot(ps, [r["verify_ms"] for r in rows], "o-", color="#2a9d8f", lw=2.1, ms=5.8,
                  label=r"Pole-cancellation residue verify time (ms)")
    ax1.set_xticks(ps)
    ax1.set_xlabel(r"Prime field characteristic $p$")
    ax1.set_ylabel(r"Verification latency (ms)", color="#2a9d8f")
    ax1.tick_params(axis="y", labelcolor="#2a9d8f")
    ax1_r = ax1.twinx()
    l2 = ax1_r.plot(ps, [r["max_path_pole"] for r in rows], "s--", color="#c1121f", lw=1.9, ms=5.5,
                    label=r"Canceled path pole order $k_{\max}$")
    ax1_r.set_ylabel(r"Canceled path pole order $k_{\max}$", color="#c1121f")
    ax1_r.tick_params(axis="y", labelcolor="#c1121f")
    ax1_r.grid(False)
    lines = l1 + l2
    ax1.legend(lines, [l.get_label() for l in lines], loc="upper left", frameon=True, framealpha=0.94, fontsize=7.4)
    ax1.set_title(r"(a) Exact Boundary Value Extraction Under Poles")

    # Panel (b): Canceled paths & recovered boundary values z mod p
    x = np.arange(len(rows))
    w = 0.36
    ax2.bar(x - w / 2, [r["num_paths"] for r in rows], width=w, color="#1b6ca8", edgecolor="#222", lw=0.6,
            label=r"Canceling Laurent paths $m$")
    ax2.bar(x + w / 2, [r["boundary_z"] for r in rows], width=w, color="#e07a5f", edgecolor="#222", lw=0.6,
            label=r"Recovered boundary value $z \in \mathbb{F}_p$")
    ax2.set_xticks(x)
    ax2.set_xticklabels([f"p={r['prime_p']}" for r in rows], fontsize=8.0)
    ax2.set_xlabel(r"Prime characteristic $p$")
    ax2.set_ylabel(r"Count / residue value")
    ax2.set_title(r"(b) Exact Boundary Recovery (Lemma 5.1)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.94)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_pole_cancellation.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RESULTS / "exp1_certified_atlas.json").read_text(encoding="utf-8"))
    rows = d1["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.9), dpi=300, gridspec_kw={"width_ratios": [1.55, 1.0]})

    mode_colors = {
        "cartier_operator_semilinear_exact": "#1b6ca8",
        "boundary_pole_cancellation_residue_exact": "#2a9d8f",
        "residue_pin_eigenvector_exact": "#e07a5f",
        "hinge_shortening_and_border_barrier_exact": "#c1121f",
    }
    labels = [r["file"].replace(".cert.json", "") for r in rows]
    ms = [r["verify_ms"] for r in rows]
    cols = [mode_colors[r["mode"]] for r in rows]
    y = np.arange(len(rows))
    ax1.barh(y, ms, color=cols, edgecolor="#222", lw=0.6, height=0.68)
    ax1.set_yticks(y)
    ax1.set_yticklabels(labels, fontsize=6.8)
    ax1.invert_yaxis()
    ax1.set_xlabel(r"Exact-$\mathbb{F}_p/\mathbb{Z}$ verification latency (ms)")
    ax1.set_title(r"(a) Zero-Float Replay Latency Across 16 Certificates")

    counts = [
        sum(1 for r in rows if r["mode"] == "cartier_operator_semilinear_exact"),
        sum(1 for r in rows if r["mode"] == "boundary_pole_cancellation_residue_exact"),
        sum(1 for r in rows if r["mode"] == "residue_pin_eigenvector_exact"),
        sum(1 for r in rows if r["mode"] == "hinge_shortening_and_border_barrier_exact"),
    ]
    m_labels = ["Mode 1\nCartier\nSemilin.", "Mode 2\nPole\nCancel", "Mode 3\nPin\nEigen.", "Mode 4\nHinge\nBarrier"]
    bars = ax2.bar(range(4), counts, color=["#1b6ca8", "#2a9d8f", "#e07a5f", "#c1121f"], edgecolor="#222", lw=0.7)
    for b, c in zip(bars, counts):
        ax2.text(b.get_x() + b.get_width() / 2.0, c + 0.15, str(c), ha="center", va="bottom", fontweight="bold", fontsize=8.5)
    ax2.set_xticks(range(4))
    ax2.set_xticklabels(m_labels, fontsize=7.8)
    ax2.set_ylabel("Certified instances")
    ax2.set_ylim(0, 5.4)
    ax2.set_title("(b) Coverage Across All 4 Modes")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_atlas_summary.png", dpi=300)
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated all 3 publication figures in paper/figures/.")
