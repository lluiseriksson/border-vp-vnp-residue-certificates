# Exact-Fp/Z Cartier-Operator Boundary-Residue, Pin-Eigenvector, and Hinge-Shortening Certificates for Border VP != VNP

**Author:** Lluis Eriksson (with AI-assisted formal verification, code generation, and drafting via Google Antigravity)  
**License:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript)

## Overview
Inspired by OpenAI's November 23, 2026 breakthrough (*VP and VNP are different*, `openai/math`), this repository provides:
- **Zero-Dependency Lean 4 Kernel (`lean/BorderVPVNPResidues.lean`, Lean `v4.35.0`)**: 18 theorems with **0 warnings**, **0 `sorry`**, and **0 `Classical.choice`** mechanizing Frobenius Freshman's Dream integral quotients ($p=2,3,5$), Fermat's little theorem on $\mathbb{F}_3$ and $\mathbb{F}_5$, Cartier operator residue-index preservation ($p(-1)+(p-1)=-1$), injectivity, semilinear shift, and annihilation of non-$(p-1)$ exponents, cancelling-pole residue invariance, Eq. (5.1) $2\times 2$ residue pin eigenvector linearity, Definition 2.1 strict hinge shortening & tensor-power gap amplification, inductive batched query degree budgets, Section 4 $2\times 2$ Cramer/Hadamard entry bounds, and Theorem 1.1 $\exp((\log n)^{5/4})$ superpolynomial dominance.
- **Pure-Stdlib Zero-Float Verifier (`src/cartier_certifier.py`, `BORDER-VPVNP-CERT-1.0`)**: Independently replays 16 exact-$\mathbb{F}_p/\mathbb{Z}$ certificates across all four modes in `0.024`–`0.305 ms` (scaling Cartier semilinearity across primes $p=3\dots 29$ and pole-cancellation extraction up to order-$10$ poles), cross-checks Frobenius and Cartier identities across primes, and rejects **54/54** live adversarial red-team attacks.

## Reproduce Everything
```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
