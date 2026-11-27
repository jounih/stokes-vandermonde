# Reader & Auditor Guide (`stokes-vandermonde` `v3.7.0`)

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
| [`FiniteContourStokes.lean`](PakPrimes/FiniteContourStokes.lean) | Growth-free finite-contour simple-pole transfer engine (scalar, joint multi-series, & universal entire `-E'/E`; zero growth at $\infty$, zero wedge, zero collinearity) | $\mathbb{C}(\{t\})$ |
| [`SpectralPositivity.lean`](PakPrimes/SpectralPositivity.lean) | Two-range RH/GRH-free Cramér spectral positivity & unified positive-weight Hankel positive-definiteness engine | $\mathbb{R}$ |
| [`BranchPointStokes.lean`](PakPrimes/BranchPointStokes.lean) | Half-integer Abel convolution & square-root branch-point Stokes–Vandermonde resurgence | $\mathbb{C}(u)$ |
| [`QuasipolynomialEulerParity.lean`](PakPrimes/QuasipolynomialEulerParity.lean) · [`QuasipolynomialIFF.lean`](PakPrimes/QuasipolynomialIFF.lean) | Period-$M$ quasipolynomial parity dichotomy, Ramanujan $(E_2, E_4, E_6)$ converse ($M = 1, 2$), and joint differential independence | $\mathbb{C}(q)$ |
| [`VolterraVirialDTrans.lean`](PakPrimes/VolterraVirialDTrans.lean) | Sibuya's Sub-Gevrey Convergence Theorem ($d/dx$ and Euler $x\,d/dx$) | $\mathbb{C}[x], \mathbb{C}(t)$ |
| [`PakNthPrimeEngine.lean`](PakPrimes/PakNthPrimeEngine.lean) · [`PakNthPrimeStokes.lean`](PakPrimes/PakNthPrimeStokes.lean) · [`PNTIntegration/`](PNTIntegration/) | Prime-pencil resurgence & `MediumPNT` (`PNT+`) bridge discharging `PNTAllOrders` | $\mathbb{C}(x)$ |
| [`BesicovitchCore.lean`](PakStokes/AllD/BesicovitchCore.lean) · [`UniversalThimble.lean`](PakStokes/AllD/UniversalThimble.lean) · [`ExtremeRayProjection.lean`](PakStokes/AllD/ExtremeRayProjection.lean) · [`TrackedWaves.lean`](PakStokes/AllD/TrackedWaves.lean) | All-$d$ Besicovitch radical independence ($r \ge 2$), LHP critical-value exclusion, extreme-ray projection, & generalized domain Marked Jacobian | $\mathbb{C}(q)$ |
| [`SquaresPartitionAnalytic.lean`](PakStokes/AllD/SquaresPartitionAnalytic.lean) · [`PowerPartitions.lean`](PakStokes/AllD/PowerPartitions.lean) · [`SquareQuotientsAndDivisors.lean`](PakStokes/AllD/SquareQuotientsAndDivisors.lean) | Zero-tilt constant-Vandermonde power-partition & unified `SqRayProfile` engine, Kolchin log-derivative & multiplicative quotient-rank / forest transfer, & exact $d=2$ Poisson identities | $\mathbb{C}(q)$ |
| [`Bec3DAnalytic.lean`](PakStokes/AllD/Bec3DAnalytic.lean) · [`Bec3DDiffTrans.lean`](PakStokes/AllD/Bec3DDiffTrans.lean) | 3D iterated Poisson summation + elementary $K_{1/2}$ identity for $F_{\mathrm{BEC}}^{(3)}$, 3D Bose/Fermi quotient-rank transfer, & Dirichlet-AP ($7 \bmod 8$ vs. $1 \bmod 4$) $(2J)\times(2J)$ prime-block decoupling | $\mathbb{C}(q)$ |
| [`JumpPointMultivariate.lean`](PakStokes/AllD/JumpPointMultivariate.lean) · [`BlackbodyPhotons3D.lean`](PakStokes/AllD/BlackbodyPhotons3D.lean) | Algebraic jump-point derivation engine (`monoidDeriv`, `hahnDeriv`), Wulff-ray infinite $\mathbb{Q}$-rank, collision-immune Hahn transseries elimination, & triangular square-free core separation (`r₂/r₃/r₄`, `Q² + 2`) | `AsympCoeff`, $\mathbb{C}[X]$ |
| [`MockModularAlgebraCore.lean`](PakStokes/AllD/MockModularAlgebraCore.lean) · [`DysonShadowRank.lean`](PakStokes/AllD/DysonShadowRank.lean) · [`PrimeDilationIsolation.lean`](PakStokes/AllD/PrimeDilationIsolation.lean) | Mock-modular jet Vandermonde determinant, translation-invariance collision killing, Bol/modular mixed-weight derivative independence, Maximum Modulus Watson uniqueness, all-moduli Dyson folded-cycle / trigonometric shadow rank $r_N$, & dual-ray prime-dilation block elimination | $\mathbb{C}[x], \mathbb{C}, K, \mathbb{R}$ |

---

## Layer 2: Flagship Theorems by Release Wave

- **Waves 12–13A (`v3.7.0`) — Relativistic 2D/3D/4D Blackbody Photons, Mock-Modular Algebraic & Watson Core, All-Moduli Dyson Shadow Rank $r_N$, & Dual-Ray Prime-Dilation Isolation (`5,471` new lines, 175 public decls / 135 theorems, 100% unconditional from Mathlib; companion mock-modular paper [`10.5281/zenodo.24590300`](https://doi.org/10.5281/zenodo.24590300)):**
  - **2D/3D/4D Blackbody Photon Gases (`BlackbodyPhotons3D.lean`, `1,530` lines, 57 public decls / 40 theorems)**: exact lattice-sphere counts `r2Count`/`r3Count`/`r4Count`, constructive $Q^2 + 2$ 3-square separation (`exists_new_sqf_mod_eight_eq_three_r3_pos`), exact analytic regrouping on $t > 0$ (`photonEnergyAnalytic_eq_tsum_sqrt`), triangular core-separation transseries engine (`triangular_core_transseries_diff_indep`), individual non-ADE (`photon2D_non_ade`, `photon3D_non_ade`, `photon4D_non_ade`), and joint differential independence of $(U_{\mathrm{photon}}^{(2)}, U_{\mathrm{photon}}^{(3)}, U_{\mathrm{photon}}^{(4)})$ and $(\log Z_{\mathrm{photon}}^{(2)}, \log Z_{\mathrm{photon}}^{(3)}, \log Z_{\mathrm{photon}}^{(4)})$ (`photon2D_photon3D_photon4D_joint_diff_indep`, `photon2D_photon3D_photon4D_all_derivs_diff_indep`, `photon2D_photon3D_photon4D_no_joint_poly_ade`, `photonLogZ_2D_3D_4D_joint_diff_indep`).
  - **Mock-Modular Algebraic, Bol/Modular Independence, & Watson Core (`MockModularAlgebraCore.lean`, `2,238` lines, 54 public decls / 44 theorems)**: symbolic mock-modular jet Vandermonde determinant (`mockModular_jet_det_eq`) & analytic mode derivatives (`iteratedDeriv_mockModular_mode`), translation-invariance minimality (`mockModular_translation_invariance_kills_linear_collisions`, `mockModular_minimal_annihilator_contradiction`, `mockModular_jump_induction_contradiction`), Bol/modular iterated-derivative law & Universal Positive-Weight Modular Differential Independence (`modular_iteratedDeriv_gamma`, `positiveWeight_modular_forms_diff_indep`, `positiveWeight_modular_thetaQ_diff_indep`), and Maximum Modulus Watson Uniqueness (`maxModulus_watson_uniqueness`).
  - **All-Moduli Dyson Folded-Cycle & Trigonometric Shadow Rank (`DysonShadowRank.lean`, `1,033` lines, 47 public decls / 34 theorems)**: Bringmann–Ono trigonometric shadow identity (`dyson_shadow_trig_identity`), folded-cycle graph connected-component count (`dysonFoldedGraph_connectedComponent_card`), exact shadow rank over any field $K$ (`dysonShadowRank_eq`: $\lfloor N/2 \rfloor$ if $3 \nmid N$, $N/3$ if $3 \mid N$), kernel characterization & single-residue non-vanishing (`mem_shadowKernel_iff_const_on_components`, `single_vertex_not_mem_shadowKernel`, `dysonShadowRank_six`, `dysonSix_triple_zero_shadow`), and real trigonometric sine-product shadow matrix rank (`dct_orthogonality`, `dysonTrigShadowRank_eq`).
  - **Dual-Ray Prime-Frequency Dilation Isolation (`PrimeDilationIsolation.lean`, `670` lines, 17 theorems)**: prime-square isolation (`no_sq_mul_eq_prime_sq_mul_of_gt`, `prime_dilation_freq_ne`), non-vanishing $\sin(\pi p/3) = \pm \sqrt{3}/2$ (`mockFalse_sine_factor_eq`, `mockFalse_sine_factor_ne_zero`), arbitrarily many isolated primes (`exists_isolated_primes_for_max_dilation`), symbolic/pointwise/weighted jet Vandermonde nonsingularity (`prime_dilation_jet_det_ne_zero`, `prime_dilation_weighted_jet_det_ne_zero`), descending block elimination (`prime_dilation_block_elimination`), and dual-ray mock/false-theta joint elimination (`dual_ray_prime_dilation_elimination`, `dual_ray_prime_dilation_constant`): [`PakStokesAllD.lean`](PakStokesAllD.lean) · [`docs/all-d-power-partitions-and-multivariate.md`](docs/all-d-power-partitions-and-multivariate.md)

- **Wave 11 (`v3.6.0`) — Unconditional 3D Ideal Bose–Einstein Condensate & 3D Fermi–Dirac Gas, Joint 1D+3D Quantum Gases, Square Divisors $L_{2,0}(q)$, & Quotient-Rank Forest:**
  - **Square Quotients, 1D Fermi Gas, & Square Divisors (`SquareQuotientsAndDivisors.lean`)**: **100% unconditional from Mathlib**: full-row-rank Laurent-monomial transfer (`squarePart_monomial_family_diff_indep`), forest quotients (`squarePart_forest_quotients_diff_indep`), joint independence of distinct squares & overpartitions (`distinctSquares_overpartSquares_joint_diff_indep`), distinct-square & 1D Fermi–Dirac dilations (`distinctSquares_dilations_diff_indep`, `fermi1D_dilations_diff_indep`), unified `SqRayProfile` engine, and exact Poisson identity + non-ADE + dilations for $L_{2,0}(q) = \sum_{N \ge 1} d_\square(N) q^N$ (`squareDivisor_analytic_identity`, `squareDivisor_non_ade`, `squareDivisor_dilations_diff_indep`).
  - **3D Ideal BEC, 3D Fermi–Dirac Gas, & Coupled 1D+3D Quantum Gases (`Bec3DAnalytic.lean` + `Bec3DDiffTrans.lean`)**: **100% unconditional from Mathlib** (periodic cubic boxes $\mathbb{T}^3$ & $\mathbb{T}^1$, unit fugacity $z = 1$): exact 3D iterated Poisson + $K_{1/2}$ identity (`bec3D_analytic_identity`), $Z_{\mathrm{BEC}}^{(3)}(q)$ non-ADE / nonzero integer powers / dilations, $Z_{\mathrm{FD}}^{(3)}(q)$ non-ADE / dilations, single-temperature $(Z_{\mathrm{BEC}}^{(3)}, Z_{\mathrm{FD}}^{(3)})$ joint independence, 3D Bose–Fermi quotient-rank & forest theorems, and Dirichlet-AP coupled 1D+3D joint differential independence including all four gases $(Z_{\mathrm{BEC}}^{(1)}, Z_{\mathrm{FD}}^{(1)}, Z_{\mathrm{BEC}}^{(3)}, Z_{\mathrm{FD}}^{(3)})$ (`bec1D_bec3D_dilations_diff_indep`, `quantumGases_1D_3D_bose_fermi_joint_diff_indep`, `bec1D_bec3D_joint_diff_indep`, `powerPart2_bec3D_joint_diff_indep`): [`PakStokesAllD.lean`](PakStokesAllD.lean) · [`docs/all-d-power-partitions-and-multivariate.md`](docs/all-d-power-partitions-and-multivariate.md)

- **Waves 8–10 (`v3.5.0`) — All-$d$ Marked-Wave Cubic Waring/Dilations, Unconditional Partitions into Squares $P_2(q)$, & Algebraic Jump-Point Multivariate Engine:**
  - **Wave 8 (`PakStokesAllD` / `AllDThetaDTrans.lean`)**: Unconditional Besicovitch radical independence ($r \ge 2$), LHP critical-value exclusion, extreme-ray projection, **unconditional cubic Waring powers** $\Theta_3(q)^k$ ($k \ge 1$) and **joint differential independence of all finite distinct cubic dilations** $\{\Theta_3(q^{a_i})\}$, plus `AllDStokesProfile`-parameterized all-$d$ ($d \ge 3$) master theorems (non-vacuous via `stokesProfileThree` at $d=3$).
  - **Wave 9 (`SquaresPartitionAnalytic.lean` + `PowerPartitions.lean`)**: **100% unconditional from Mathlib** closed-form Poisson/cotangent identity (`squares_partition_analytic_identity`), **partitions into squares** $P_2(q) = \prod_{n \ge 1}(1-q^{n^2})^{-1}$ non-ADE, every nonzero integer power $P_2(q)^k$ non-ADE, and joint differential independence of every finite family of distinct positive-integer dilations $\{P_2(q^{a_i})\}$; plus `PowerPartStokesProfile`-parameterized $d \ge 3$ master theorems.
  - **Wave 10 (`JumpPointMultivariate.lean`)**: **100% unconditional algebraic transseries engine** (`jumpPoints_exist`, `monoidDeriv`, `hahnDeriv`, `jumpPoint_minimal_relation_vandermonde`, `wulffRay_infinite_qrank`, `multivariate_jumpPoint_non_ade_over_poly`, `diagForm_transseries_non_ade`, `diagQuartic2D_non_ade`; connecting formal transseries to a specific analytic heat trace still requires the analytic hypothesis): [`PakStokesAllD.lean`](PakStokesAllD.lean) · [`docs/all-d-power-partitions-and-multivariate.md`](docs/all-d-power-partitions-and-multivariate.md)
- **Wave 7 (`v3.4.0`) — Unconditional Completed-$\xi$ Strong $\mathbb{C}(\{t\})$ D-Transcendence, Finite-Contour Engine, & RH/GRH-Free Spectral Positivity:**
  - **100% Unconditional Completed $\xi$ & Finite-Contour Simple-Pole Engine** *(Mathlib plus this repository's proved modules, with no extra hypotheses; ZERO RH, ZERO external data structures, ZERO growth at $\infty$)*: infinitude of nontrivial zeros, strong $\mathbb{C}(\{t\})$ D-transcendence in $t = 1/u$ for the factorial-moment / formal-Laplace series of $-\xi'/\xi$ at every real center $c \in \mathbb{R}$ (NOT for $\zeta(s)$ in $s$), joint multi-center differential independence, and real-axis Laplace `B_xi c u` ADE obstruction over $\mathbb{C}\{1/u\}$: [`Statements/CompletedXi.lean`](Statements/CompletedXi.lean) · [`docs/completed-xi-and-positivity.md`](docs/completed-xi-and-positivity.md)
  - **RH/GRH-Free Spectral Positivity & Strict Hankel Positive Definiteness** *(unconditional abstract core + explicitly parameterized `SpectralLowZeroData` with `γ_low : List ℝ` and arbitrary off-line critical-strip zeros $|\mathrm{Im}\,\gamma| < 1/2$ + parameterized `SubtractedHyperbolicSpectralData` for $d = 2, 3$; data structures are NOT connected in Lean to the zeros of `completedXi`, $L(s, \chi_{-4})$, $L(s, \Delta)$, or a concrete hyperbolic manifold's Laplace eigenvalues)*: [`Statements/SpectralPositivity.lean`](Statements/SpectralPositivity.lean) · [`docs/completed-xi-and-positivity.md`](docs/completed-xi-and-positivity.md)
- **Wave 6 (`v3.3.0`) — Hyperbolic Selberg Packages, All-CROSS Spectral Parity & Heat Traces, and Elementary RH-Independent Primes:**
  - **3D & 2D Compact Hyperbolic Selberg** *(given `CompactHyperbolic3DSelbergData` / `CompactHyperbolicSelbergData`; zero simplicity or spacing assumptions; no concrete manifold instantiated in Lean yet)*: [`Statements/SelbergHyperbolic.lean`](Statements/SelbergHyperbolic.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
  - **All-CROSS Bosonic Euler-Product Odd-Sphere Uniqueness over $\mathbb{C}(q)$, Wave-EGF Strong $\mathbb{C}(\{t\})$ D-Transcendence, ADE 3-Manifold Molien Parity, & Unconditional $\mathbb{C}(t)$ Heat-Trace D-Transcendence** *(on standard closed-form spectral-multiplicity quasipolynomials and heat sums)*: [`Statements/RankOneSymmetric.lean`](Statements/RankOneSymmetric.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
  - **Elementary RH-Independent Prime Von Mangoldt Moments ($s_0 = 2$ & $s_0 = 1/2$, driven by trivial zeros of `riemannZeta`):** [`Statements/UnconditionalPrimes.lean`](Statements/UnconditionalPrimes.lean) · [`docs/geometry-and-unconditional-primes.md`](docs/geometry-and-unconditional-primes.md)
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
  PakPrimes/ PakPrimes.lean PNTIntegration/ Statements/ PakStokes/ PakStokesAllD.lean vendor/PrimeNumberTheoremAnd/ vendor/pak-cubic-theta/

# 3. Print exact axioms for all 423 audited declarations
lake env lean Verify.lean

# 4. Independent kernel replay from scratch via leanchecker
ulimit -s 65520   # use `ulimit -s unlimited` on Linux for single-threaded --fresh replays
lake env leanchecker --fresh PakStokesAllD
lake env leanchecker --fresh Statements.CompletedXi
lake env leanchecker --fresh Statements.SpectralPositivity
lake env leanchecker --fresh Statements.SelbergHyperbolic
lake env leanchecker --fresh Statements.RankOneSymmetric
lake env leanchecker --fresh Statements.UnconditionalPrimes
lake env leanchecker --fresh Statements.All
```
