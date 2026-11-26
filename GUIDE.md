# Reader & Auditor Guide (`stokes-vandermonde` `v3.3.0`)

This guide maps the repository into two clean layers—the **Core Resurgence Engine** and the **Flagship Theorems by Release Wave**—and gives exact commands to audit every claim from scratch.

---

## How to Audit a Claim in 30 Seconds

1. **Read the thin statement ledger** under [`Statements/`](Statements/) — each file re-exports exact Lean 4 theorem types verified by the kernel against the full proofs (no definitions hidden in proofs).
2. **Read the paired scope note** under [`docs/`](docs/) — each note states explicitly what is proved unconditionally, what takes an analytic data structure or hypothesis, and what is out of scope.
3. **Verify axioms & replay the kernel** using the commands at the bottom of this page.

---

## Layer 1: Core Resurgence & Transcendence Engine (`PakPrimes/`)

| Engine Module | Mathematical Mechanism | Coefficient Field |
| :--- | :--- | :--- |
| [`BorelStokesVandermonde.lean`](PakPrimes/BorelStokesVandermonde.lean) · [`AutonomousTransfer.lean`](PakPrimes/AutonomousTransfer.lean) · [`GeneralTheorem2.lean`](PakPrimes/GeneralTheorem2.lean) | Autonomous Borel–Stokes–Vandermonde criterion for meromorphic Borel transforms | $\mathbb{C}$ |
| [`HigherOrderStokes.lean`](PakPrimes/HigherOrderStokes.lean) | Non-autonomous rotated-ray ($\theta_0 \in \mathbb{R}$) Stokes–Vandermonde engine for arbitrary finite pole orders (`HigherOrderBorelData`) | $\mathbb{C}(u)$ |
| [`FishburnStrongDTrans.lean`](PakPrimes/FishburnStrongDTrans.lean) · [`HigherOrderStrongDTrans.lean`](PakPrimes/HigherOrderStrongDTrans.lean) | Universal strong differential transcendence lift over convergent meromorphic germs (`StronglyDTransOverMeromorphicGerms`) | $\mathbb{C}(\{t\})$ |
| [`BranchPointStokes.lean`](PakPrimes/BranchPointStokes.lean) | Half-integer Abel convolution & square-root branch-point Stokes–Vandermonde resurgence | $\mathbb{C}(u)$ |
| [`QuasipolynomialEulerParity.lean`](PakPrimes/QuasipolynomialEulerParity.lean) · [`QuasipolynomialIFF.lean`](PakPrimes/QuasipolynomialIFF.lean) | Period-$M$ quasipolynomial parity dichotomy, Ramanujan $(E_2, E_4, E_6)$ converse ($M = 1, 2$), and joint differential independence | $\mathbb{C}(q)$ |
| [`VolterraVirialDTrans.lean`](PakPrimes/VolterraVirialDTrans.lean) | Sibuya's Sub-Gevrey Convergence Theorem ($d/dx$ and Euler $x\,d/dx$) | $\mathbb{C}[x], \mathbb{C}(t)$ |
| [`PakNthPrimeEngine.lean`](PakPrimes/PakNthPrimeEngine.lean) · [`PakNthPrimeStokes.lean`](PakPrimes/PakNthPrimeStokes.lean) · [`PNTIntegration/`](PNTIntegration/) | Prime-pencil resurgence & `MediumPNT` (`PNT+`) bridge discharging `PNTAllOrders` | $\mathbb{C}(x)$ |

---

## Layer 2: Flagship Theorems by Release Wave

- **Wave 6 (`v3.3.0`) — Hyperbolic Geometry, All-CROSS Spectral Parity & Heat Traces, and Elementary RH-Independent Primes:**
  - **3D & 2D Compact Hyperbolic Selberg:** [`Statements/SelbergHyperbolic.lean`](Statements/SelbergHyperbolic.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
  - **All-CROSS Cartan Classification, Wave-EGF, ADE 3-Manifolds, & Unconditional Heat Traces:** [`Statements/RankOneSymmetric.lean`](Statements/RankOneSymmetric.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
  - **Elementary RH-Independent Prime Von Mangoldt Moments ($s_0 = 2$ & $s_0 = 1/2$):** [`Statements/UnconditionalPrimes.lean`](Statements/UnconditionalPrimes.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
- **Wave 5 (`v3.2.0`) — Digital Trees, Volterra Virial, Distinct-Density Primes, & Universal $\mathbb{C}(\{x\})$ Lift:**
  - **Flajolet–Richmond Digital Trees (BDR §2.2.6 #3):** [`Statements/FlajoletRichmond.lean`](Statements/FlajoletRichmond.lean) · [`docs/flajolet-richmond.md`](docs/flajolet-richmond.md)
  - **Sibuya Sub-Gevrey & Volterra Virial $\mu, \nu$:** [`Statements/VolterraVirial.lean`](Statements/VolterraVirial.lean) · [`docs/volterra-virial-and-sibuya.md`](docs/volterra-virial-and-sibuya.md)
  - **Distinct-Density Prime Towers, Universal Strong Lift, Conditional `RH → G_Λ`, & Certification Toolkit:** [`Statements/DistinctDensityPrimes.lean`](Statements/DistinctDensityPrimes.lean) · [`Statements/HigherOrderStrongAndRH.lean`](Statements/HigherOrderStrongAndRH.lean) · [`docs/distinct-density-and-strong-lift.md`](docs/distinct-density-and-strong-lift.md)
- **Wave 4 (`v3.1.0`) — Pak Conjecture 2.5 & Fishburn / Torus-Knot Series:**
  - **Unconditional Pak Conjecture 2.5 ($\sum p_n x^n$ & $\sum \pi(n) x^n$):** [`Statements/PakNthPrime.lean`](Statements/PakNthPrime.lean) · [`docs/pak-nth-prime.md`](docs/pak-nth-prime.md)
  - **Fishburn OGF (BDR §2.2.6 #1), Zagier (2001, Thm. 3), & Torus-Knot Kernels:** [`Statements/FishburnTorusKnots.lean`](Statements/FishburnTorusKnots.lean) · [`docs/fishburn-and-torus-knots.md`](docs/fishburn-and-torus-knots.md)
- **Wave 3 (`v3.0.0`) — Quasipolynomial Parity, Relativistic Gases & Spheres, & Mordell/Eichler/Stieltjes Integrals:**
  - [`Statements/QuasipolynomialParity.lean`](Statements/QuasipolynomialParity.lean) · [`docs/quasipolynomial-parity.md`](docs/quasipolynomial-parity.md)
  - [`Statements/ThermalGasAndSpheres.lean`](Statements/ThermalGasAndSpheres.lean) · [`docs/thermal-gas-and-spheres.md`](docs/thermal-gas-and-spheres.md)
  - [`Statements/MordellAndFalseThetaIntegrals.lean`](Statements/MordellAndFalseThetaIntegrals.lean) · [`docs/mordell-and-false-theta-integrals.md`](docs/mordell-and-false-theta-integrals.md)
- **Waves 1–2 (`v1.0–v2.0`) — Classical Hypertranscendence & Prime Counting:**
  - Hölder (`Gamma`), Ostrowski (`riemannZeta`), MacMahon, prime counting, & prime partitions: [`Statements/PrimesAndClassical.lean`](Statements/PrimesAndClassical.lean)

---

## Exact Verification Commands

Use Lean `v4.36.0` (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`):

```bash
# 1. Fetch Mathlib oleans and build all proof modules + PNTIntegration + Statements
lake exe cache get
lake build

# 2. Check zero escape hatches (no sorry, custom axiom, native_decide, implemented_by, @[extern)
grep -rnE '\b(sorry|sorry_using|axiom|native_decide|implemented_by)\b|@\[extern' \
  PakPrimes/ PakPrimes.lean PNTIntegration/ Statements/ vendor/PrimeNumberTheoremAnd/

# 3. Print exact axioms for all 169 audited declarations
lake env lean Verify.lean

# 4. Independent kernel replay from scratch via leanchecker
ulimit -s 65520   # use `ulimit -s unlimited` on Linux for single-threaded --fresh replays
lake env leanchecker --fresh Statements.SelbergHyperbolic
lake env leanchecker --fresh Statements.RankOneSymmetric
lake env leanchecker --fresh Statements.UnconditionalPrimes
lake env leanchecker --fresh Statements.All
```
