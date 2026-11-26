# Formal Resurgence and Differential Transcendence in Lean 4 (`stokes-vandermonde`)

This Lean 4 library (`v3.3.0`) formalizes the **Borel–Stokes–Vandermonde criterion** for differential transcendence—autonomous, non-autonomous over $\mathbb{C}(u)$ with rotated Stokes rays and arbitrary finite pole orders, universal strong $\mathbb{C}(\{t\})$ lifts over convergent meromorphic germs, half-integer Abel branch-point resurgence, Sibuya's sub-Gevrey convergence theorem, and shift-and-scale lacunary descent—and applies it to prove machine-checked differential transcendence and parity dichotomies across spectral geometry, analytic number theory, combinatorics, special functions, and mathematical physics.

All **169 audited declarations** depend strictly on the standard Lean axioms (`[propext, Classical.choice, Quot.sound]`, or a subset / zero axioms for purely algebraic identities), with zero `sorry`, zero custom axioms, zero `native_decide`, and independent kernel replay via `lake env leanchecker --fresh`.

> **New here or auditing?** Start with the 1-page [**Reader & Auditor Guide (`GUIDE.md`)**](GUIDE.md) mapping the Core Resurgence Engine, all six release waves, and exact verification commands.

## Quick Audit: Thin Statement Ledgers & Scope Notes

To make statement verification independent of proof length, every flagship theorem is re-stated with its exact type signature in a short audit ledger under [`Statements/`](Statements/) (verified by the Lean 4 kernel against the full proofs) and paired with an explicit scope note under [`docs/`](docs/) stating what is and is not formalized:

- **3D & 2D Compact Hyperbolic Selberg–Stokes–Vandermonde (`v3.3.0`):** [Spec](Statements/SelbergHyperbolic.lean) · [Scope note](docs/geometry-and-unconditional-primes.md)
- **All-CROSS Cartan Parity, Wave-EGF, ADE Spherical 3-Manifolds, & Unconditional Heat Traces (`v3.3.0`):** [Spec](Statements/RankOneSymmetric.lean) · [Scope note](docs/geometry-and-unconditional-primes.md)
- **Elementary RH-Independent Prime Von Mangoldt Moments ($s_0 = 2$ & $s_0 = 1/2$, `v3.3.0`):** [Spec](Statements/UnconditionalPrimes.lean) · [Scope note](docs/geometry-and-unconditional-primes.md)
- **Flajolet–Richmond Generalized Digital Trees (BDR §2.2.6 Example #3, `v3.2.0`):** [Spec](Statements/FlajoletRichmond.lean) · [Scope note](docs/flajolet-richmond.md)
- **Sibuya's Sub-Gevrey Theorem & Volterra Virial Functions $\mu, \nu$ (`v3.2.0`):** [Spec](Statements/VolterraVirial.lean) · [Scope note](docs/volterra-virial-and-sibuya.md)
- **Distinct-Density Prime Towers, Universal Strong $\mathbb{C}(\{x\})$ Lift, Conditional `RH → G_Λ`, & Analytic Certification Toolkit (`v3.2.0`):** [Distinct-Density Spec](Statements/DistinctDensityPrimes.lean) · [Strong Lift & RH Spec](Statements/HigherOrderStrongAndRH.lean) · [Scope note](docs/distinct-density-and-strong-lift.md)
- **Pak Conjecture 2.5 (`∑ p_n x^n` & `∑ π(n) x^n`) and Prime Corollaries (`v3.1.0`):** [Spec](Statements/PakNthPrime.lean) · [Scope note](docs/pak-nth-prime.md) *(Pak Conjecture 2.6, for $\sum x^{n^3}$, is proved separately in [pak-cubic-theta](https://doi.org/10.5281/zenodo.24492865))*
- **Fishburn Series (Bostan–Di Vizio–Raschel §2.2.6 Example #1) & Torus-Knot Kernel Series over $\mathbb{C}(x)$ and $\mathbb{C}(\{x\})$ (`v3.1.0`):** [Spec](Statements/FishburnTorusKnots.lean) · [Scope note](docs/fishburn-and-torus-knots.md)
- **Quasipolynomial Euler-Product Parity Dichotomy:** [Spec](Statements/QuasipolynomialParity.lean) · [Scope note](docs/quasipolynomial-parity.md)
- **Relativistic Ideal Gases, Equations of State, Casimir, & Spheres $S^s$:** [Spec](Statements/ThermalGasAndSpheres.lean) · [Scope note](docs/thermal-gas-and-spheres.md)
- **Mordell, Eichler, & Stieltjes Integrals over $\mathbb{C}(u)$:** [Spec](Statements/MordellAndFalseThetaIntegrals.lean) · [Scope note](docs/mordell-and-false-theta-integrals.md)
- **Wave 1–2 Primes, MacMahon, Hölder, & Ostrowski:** [Spec](Statements/PrimesAndClassical.lean)

## Summary of Kernel-Verified Theorems (`v3.3.0`)

| Status | Area | Mathematical Result | Main Lean 4 Declarations | Spec / Module |
| :--- | :--- | :--- | :--- | :--- |
| ✅ Unconditional (on `SelbergData`) | **3D & 2D Compact Hyperbolic Selberg (`v3.3`)** | Strong $\mathbb{C}(\{t\})$ D-transcendence of geodesic von Mangoldt OGFs & formal series, plus $\mathbb{C}\{1/u\}$ / $\mathbb{C}(u)$ Laplace ADE obstructions for compact hyperbolic 3-manifolds $\mathbb{H}^3/\Gamma$ (pure-polynomial reflection $+\frac{\mathrm{Vol}}{\pi}\xi^2$, zero trivial zeros) and genus $g \ge 2$ surfaces $\mathbb{H}^2/\Gamma$ | `selberg3D_ogf_stronglyDTrans`, `selberg3D_laplace_no_conv_ade`, `selberg_ogf_stronglyDTrans`, `func_eq_critical_shift` | [SelbergHyperbolic.lean](Statements/SelbergHyperbolic.lean) |
| ✅ Unconditional | **All-CROSS Parity, Wave-EGF, ADE 3-Manifolds, & Heat Traces (`v3.3`)** | Cartan CROSS Euler-product classification (`IFF` odd spheres / odd $\dim_\mathbb{R}$); strong $\mathbb{C}(\{t\})$ wave-EGF D-transcendence across $S^{2r}, \mathbb{CP}^n, \mathbb{HP}^n, \mathbb{OP}^2$; ADE spherical 3-manifold ($S^3/I^*, O^*, T^*, D_m^*$) Molien reciprocity (`oddPart = 0`, `borelAmp = 0`); unconditional $\mathbb{C}(t)$ heat-trace D-transcendence for every even-dimensional simply connected CROSS | `cross_simplyConnected_dAlg_iff`, `cross_all_dAlg_iff`, `poincareSphere_molien_identity`, `evenCROSS_heatTrace_no_rat_ade`, `op2_heatTrace_no_rat_ade` | [RankOneSymmetric.lean](Statements/RankOneSymmetric.lean) |
| ✅ Unconditional | **Elementary RH-Independent Prime Moments (`v3.3`)** | Elementary RH/GRH-independent strong $\mathbb{C}(\{t\})$ D-transcendence and $\mathbb{C}\{1/u\}$ / $\mathbb{C}(u)$ Laplace ADE obstructions for prime von Mangoldt moment series at asymmetric $s_0 = 2$ (literal Dirichlet moments $(-1)^n\sum \Lambda(m)(\log m)^n / m^2$) and $s_0 = 1/2$ (`G_Λ`) | `phiLambdaAtTwo_eq_LSeries_vonMangoldt`, `unconditional_G_Lambda_atTwo_ogf_stronglyDTrans`, `unconditional_G_Lambda_ogf_stronglyDTrans` | [UnconditionalPrimes.lean](Statements/UnconditionalPrimes.lean) |
| ✅ Unconditional | **Flajolet–Richmond Digital Trees (`v3.2`)** | Unconditional D-transcendence over $\mathbb{C}(t)$ of the EGF $f_b(t)$ and Poisson transform $e^{-t}f_b(t)$ for every integer $b \ge 2$ (closing the open $f$ half of BDR *AJM* 2024, §2.2.6 Example #3; BDR proved $G$ via Thm. 2), plus exact $b = 1$ collapse $f_1(t) = t e^t$ | `frEGFSeries_dTrans_over_ratFunc`, `frPoissonSeries_dTrans_over_ratFunc`, `frEGF_one_not_dTrans` | [FlajoletRichmond.lean](Statements/FlajoletRichmond.lean) |
| ✅ Unconditional | **Sibuya Sub-Gevrey & Volterra Virial (`v3.2`)** | Sibuya's Sub-Gevrey Convergence Theorem (both $d/dx$ and $x\,d/dx$); unconditional D-transcendence over $\mathbb{C}(t)$ of Volterra $\mu(t,\beta,\alpha)$, Volterra $\nu(t)$ (2D Fermi gas 2nd virial shift), and 1D 3-body 3rd virial shift (in both $t$ and $T > 0$); exact $\mathcal{L}[\nu](s) = (s\log s)^{-1}$ | `sibuya_subGevrey_convergent`, `volterraMu_no_rat_ade`, `volterraNu_no_rat_ade`, `fermiGas1D_virial3_temp_no_rat_ade`, `laplace_volterraNu` | [VolterraVirial.lean](Statements/VolterraVirial.lean) |
| ✅ Unconditional (given `HasDensityPNT`) | **Distinct-Density Prime Towers (`v3.2`)** | Joint differential independence over $\mathbb{C}(x)$ of any finite or countably infinite dyadic family of sequence OGFs obeying distinct-density PNT asymptotics (e.g. $p \equiv 1 \bmod 2^k$) | `distinctDensity_ogf_joint_algebraicIndependent`, `distinctDensity_dyadic_finite`, `distinctDensity_dyadic_countable` | [DistinctDensityPrimes.lean](Statements/DistinctDensityPrimes.lean) |
| ✅ Unconditional | **Universal Strong $\mathbb{C}(\{x\})$ Lift (`v3.2`)** | Lifts the entire arbitrary-pole-order rotated-ray `HigherOrderStokes` engine to strong D-transcendence over convergent meromorphic germs $\mathbb{C}(\{x\})$ (Bernoulli, $\tan$, $\sec^p$, Euler–Genocchi, trigamma, Lambert) | `ogf_stronglyDTrans_of_higherOrderBorel`, `bernOGF_stronglyDTrans`, `secPowOGF_stronglyDTrans`, `lambertOGF_stronglyDTrans` | [HigherOrderStrongAndRH.lean](Statements/HigherOrderStrongAndRH.lean) |
| 🔶 Conditional on `RH` | **Critical-Line `RH → G_Λ` Bridge (`v3.2`)** | Independent imaginary-axis ($\theta_0 = \pi/2$) Stokes proof showing `(RiemannHypothesis ∧ InfinitelyManyCriticalLineZeros) →` D-transcendence of $G_\Lambda$ over $\mathbb{C}(x)$ and strong D-transcendence over $\mathbb{C}(\{x\})$ | `riemannHypothesis_implies_G_Lambda_dTrans`, `riemannHypothesis_implies_G_Lambda_stronglyDTrans` | [HigherOrderStrongAndRH.lean](Statements/HigherOrderStrongAndRH.lean) |
| ✅ Unconditional | **Analytic Certification Toolkit (`v3.2`)** | Multi-scale geometric exponential filter bank Plancherel dominance ($K \ge 10$) and exact rational Collatz–Wielandt spectral-radius bounds | `multiscale_filter_spectral_dominance`, `collatz_wielandt_rat_upper_bound` | [HigherOrderStrongAndRH.lean](Statements/HigherOrderStrongAndRH.lean) |
| ✅ Unconditional | **Pak Conjecture 2.5 & Prime Corollaries (`v3.1`)** | Zero-hypothesis D-transcendence over $\mathbb{C}(x)$ of $\sum_{n \ge 1} p_n x^n$ via `MediumPNT` (`PNT+`), completing Pak's Conjecture 2.5 alongside $\sum \pi(n) x^n$, $\sum_p x^p$, and $\prod_p (1-x^p)^{-1}$ | `pak_2_5a`, `pak_conjecture_2_5_and_prime_corollaries` | [PakNthPrime.lean](Statements/PakNthPrime.lean) |
| ✅ Unconditional | **Fishburn & Torus-Knot Kernel Series (`v3.1`)** | Zagier (2001, Thm. 3) from scratch; D-transcendence over $\mathbb{C}(x)$ and strong D-transcendence over $\mathbb{C}(\{x\})$ of the literal divergent Fishburn OGF (BDR §2.2.6 Example #1), Glaisher's $T$-EGF, and torus-knot kernel series for all $p,q \ge 2$ | `zagier_2001_thm3`, `fishburn_ogf_dTrans_over_ratFunc`, `fishburn_ogf_stronglyDTrans_over_meromorphicGerms` | [FishburnTorusKnots.lean](Statements/FishburnTorusKnots.lean) |
| ✅ Unconditional | **Quasipolynomial Parity & Joint Independence (`v3.0`)** | Period-$M$ quasipolynomial parity dichotomy + complete `IFF` converse for $M = 1, 2$; 3-tuple joint independence of MacMahon & parts $\equiv 1, 2 \bmod 5$ | `quasipoly_bose_eventually_dTrans`, `period1_eulerProduct_iff`, `period2_eulerProduct_iff`, `macMahon_partsMod5One_partsMod5Two_joint_dIndep` | [QuasipolynomialParity.lean](Statements/QuasipolynomialParity.lean) |
| ✅ Unconditional | **Relativistic Gases, EOS, Casimir, & Spheres $S^s$ (`v3.0`)** | Conformal scalar on $S^s$ is D-algebraic iff $s$ is odd; 2D Bose/Fermi/Casimir D-algebraic vs. 1D/3D pressures, EOS $p(\varepsilon)$, and Casimir D-transcendental | `conformalScalar_allDim_sphere_iff`, `ideal_gas_dimensional_parity`, `bose_eos_3D_dTrans`, `casimir_3D_dTrans` | [ThermalGasAndSpheres.lean](Statements/ThermalGasAndSpheres.lean) |
| ✅ Unconditional | **Mordell, Eichler, & Stieltjes Integrals (`v3.0`)** | D-transcendence & 5-tuple joint independence over $\mathbb{C}(u)$ for Mordell/Eichler/Stieltjes integrals; formal Chazy ODE | `mockThetaF_mordell_dTrans`, `rogers_stieltjes_dTrans`, `five_mordell_joint_dIndep`, `chazy_ode_from_ramanujan` | [MordellAndFalseThetaIntegrals.lean](Statements/MordellAndFalseThetaIntegrals.lean) |
| ✅ Unconditional | **Classical Hypertranscendence & Prime Counting (`v1–v2`)** | Hölder (1887) on `Gamma`, Ostrowski (1920) on `riemannZeta`, MacMahon $M(q)$, prime counting $\sum \pi(n)q^n$, prime partitions $\prod_p (1 \mp q^p)^{-1}$ | `holder_gamma_dTrans`, `ostrowski_riemannZeta_dTrans`, `primeCounting_and_indicator_dTrans` | [PrimesAndClassical.lean](Statements/PrimesAndClassical.lean) |

*(Note: Pak's Conjecture 2.5 is completely proved in this library, and Pak's Conjecture 2.6—for the cubic theta series $\sum q^{n^3}$ of Chowla–Chowla 1984 / Lipshitz–Rubel 1991—is proved in the separate companion repository [pak-cubic-theta](https://doi.org/10.5281/zenodo.24492865).)*

## Unconditional `PNT+` Integration

The unconditional prime-counting and prime-partition theorems discharge `PNTAllOrders` (`|π(x) - li(x)| = O_M(x / (log x)^M)` for all `M`) directly from `MediumPNT` of the **PrimeNumberTheoremAnd (PNT+)** project led by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors** ([PNT+ repository](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) · [Transfer proof](PNTIntegration/PrimeCountingFromPsi.lean) · [Third-party credits](vendor/README.md)).

## Reproduce the Check

Use Lean `v4.36.0` (Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`):

```bash
lake exe cache get
lake build
lake env lean Verify.lean
```

For independent kernel replay of the entire transitive dependency graph (use `ulimit -s 65520` on macOS, or `ulimit -s unlimited` on Linux for single-threaded `--fresh` replays):

```bash
ulimit -s 65520
lake env leanchecker --fresh Statements.All
```

## Credits and License

The unconditional prime-counting and prime-partition theorems build directly on the `MediumPNT` formalization from the **PrimeNumberTheoremAnd (PNT+)** project by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors**, as well as **LeanArchitect**. Google Gemini, OpenAI Codex, and Anthropic Claude assisted with the mathematical investigation, adversarial auditing, drafting, and Lean 4 formalization. Independent specialist review is welcome. [License](LICENSE) · [Third-party credits and licenses](vendor/README.md)
