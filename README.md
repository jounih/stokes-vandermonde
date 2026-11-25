# Formal Resurgence and Differential Transcendence in Lean 4 (`stokes-vandermonde`)

This Lean 4 library (`v3.0.0`) formalizes the **Borel–Stokes–Vandermonde criterion** for differential transcendence—both autonomous and non-autonomous over $\mathbb{C}(u)$ with rotated Stokes rays and arbitrary finite pole orders—and applies it to prove **unconditional, machine-checked differential transcendence** and parity dichotomies across combinatorics, analytic number theory, special functions, and mathematical physics.

All **82 audited declarations** depend strictly on the standard Lean axioms (`[propext, Classical.choice, Quot.sound]`, or zero axioms for purely algebraic identities), with zero `sorry`, zero custom axioms, zero `native_decide`, and independent kernel replay via `lake env leanchecker --fresh`.

## Quick Audit: Thin Statement Ledgers & Scope Notes

To make statement verification independent of proof length, every flagship theorem is re-stated with its exact type signature in a short audit ledger under [`Statements/`](Statements/) (listing the project definitions used with file/line pointers and textbook-pinning `example` checks, verified by the Lean 4 kernel against the full proofs) and paired with an explicit scope note under [`docs/`](docs/) stating what is and is not formalized:

- **Quasipolynomial Euler-Product Parity Dichotomy:** [Spec](Statements/QuasipolynomialParity.lean) · [Scope note](docs/quasipolynomial-parity.md)
- **Relativistic Ideal Gases, Equations of State, Casimir, & Spheres $S^s$:** [Spec](Statements/ThermalGasAndSpheres.lean) · [Scope note](docs/thermal-gas-and-spheres.md)
- **Mordell, Eichler, & Stieltjes Integrals over $\mathbb{C}(u)$:** [Spec](Statements/MordellAndFalseThetaIntegrals.lean) · [Scope note](docs/mordell-and-false-theta-integrals.md)
- **Wave 1–2 Primes, MacMahon, Hölder, & Ostrowski:** [Spec](Statements/PrimesAndClassical.lean)

## Summary of Kernel-Verified Theorems (`v3.0.0`)

| Area | Mathematical Result | Main Lean 4 Declarations | Spec / Module |
| :--- | :--- | :--- | :--- |
| **Quasipolynomial Parity (`v3.0`)** | For any period-$M$ quasipolynomial $P$ with nonzero odd part $P^-$, both $H_w(q)$ and literal Bose–Euler products $\prod (1-q^n)^{-w(n)}$ (allowing finite perturbations) are D-transcendental over $\mathbb{C}(q)$; complete `IFF` converse proved for periods $M=1, 2$ via formal Ramanujan ODEs (even $P$ makes the logarithmic derivative $H_P$ quasimodular and hence $G_P$ D-algebraic, though for degree $D \ge 2$ the product $G_P$ is Liouvillian over modular forms rather than modular) | `quasipoly_bose_eventually_dTrans`, `period1_eulerProduct_iff`, `period2_eulerProduct_iff`, `partsMod5One_dTrans` | [QuasipolynomialParity.lean](Statements/QuasipolynomialParity.lean) |
| **Joint Independence (`v3.0`)** | Unconditional 3-tuple joint differential independence over $\mathbb{C}(q)$ of MacMahon's $M(q)$, parts $\equiv 1 \bmod 5$, and parts $\equiv 2 \bmod 5$ | `macMahon_partsMod5One_partsMod5Two_joint_dIndep` | [QuasipolynomialParity.lean](Statements/QuasipolynomialParity.lean) |
| **All-Dimension Conformal Scalar on $S^s$ (`v3.0`)** | For every spatial dimension $s \ge 2$, the thermal partition function $Z_{S^s}(q)$ of a free conformal scalar on $S^s$ is D-algebraic over $\mathbb{C}(q)$ **if and only if $s$ is odd** | `conformalScalar_allDim_sphere_iff` | [ThermalGasAndSpheres.lean](Statements/ThermalGasAndSpheres.lean) |
| **Relativistic Gases, EOS, & Casimir (`v3.0`)** | 2D Bose/Fermi pressures & massive Casimir are D-algebraic; 1D and 3D pressures, unconditional Bose/Fermi equations of state $p(\varepsilon)$ and squared sound speeds $c_s^2(\varepsilon)$, and 1D/3D massive Casimir are D-transcendental | `ideal_gas_dimensional_parity`, `bose_eos_3D_dTrans`, `fermi_eos_3D_dTrans`, `casimir_3D_dTrans` | [ThermalGasAndSpheres.lean](Statements/ThermalGasAndSpheres.lean) |
| **Mordell, Eichler, & Stieltjes Integrals (`v3.0`)** | Unconditional D-transcendence & 5-tuple joint independence over $\mathbb{C}(u)$ for Mordell/Eichler/Stieltjes integrals associated with mock and false thetas *(not directly the $q$-series in $\mathbb{C}[[q]]$)*; formal Chazy ODE | `mockThetaF_mordell_dTrans`, `mockThetaOmega_mordell_dTrans`, `rogers_stieltjes_dTrans`, `five_mordell_joint_dIndep`, `chazy_ode_from_ramanujan` | [MordellAndFalseThetaIntegrals.lean](Statements/MordellAndFalseThetaIntegrals.lean) |
| **General Stokes–Vandermonde Engine** | Autonomous simple-pole criterion (`GeneralTheorem2`) and non-autonomous $\mathbb{C}(u)$ rotated-ray higher-order pole criterion (`HigherOrderStokes`) | `no_autonomous_ade_of_meromorphic_borel`, `no_rat_ade_of_higher_order_borel` | [GeneralTheorem2.lean](PakPrimes/GeneralTheorem2.lean), [HigherOrderStokes.lean](PakPrimes/HigherOrderStokes.lean) |
| **Prime Counting & Prime Partitions (Pak Conj. 2.5, A000607, A000586)** | Unconditional D-transcendence over $\mathbb{C}(q)$ of the $\pi(n)$ series and the prime indicator series in Pak's Conjecture 2.5 ($\sum_p q^p$, $\sum \pi(n)q^n$), plus literal Euler products $\prod_p (1-q^p)^{-1}$ and $\prod_p (1+q^p)$, via `MediumPNT` (`PNT+`) | `primeCounting_and_indicator_dTrans`, `partitionPrimes_eulerProduct_dTrans`, `distinctPrimes_eulerProduct_dTrans` | [PrimesAndClassical.lean](Statements/PrimesAndClassical.lean) |
| **Classical Hypertranscendence & Combinatorics** | Hölder's theorem (1887) on `Complex.Gamma` / `Real.Gamma`; Hilbert (1900) / Ostrowski (1920) on `riemannZeta`; even divisor sums $L_{2m}(q)$, $L_0(q)$, literal MacMahon $M(q)$; meromorphic EGF-to-OGF bridge; weight-1 Eichler integrals | `holder_gamma_dTrans`, `ostrowski_riemannZeta_dTrans`, `macmahon_eulerProduct_dTrans`, `eichlerWeightOne_no_rat_ade` | [PrimesAndClassical.lean](Statements/PrimesAndClassical.lean), [PakYeliussizovEGF.lean](PakPrimes/PakYeliussizovEGF.lean), [MockModularWeightOne.lean](PakPrimes/MockModularWeightOne.lean) |

*(Note: A separate companion repository [pak-cubic-theta](https://doi.org/10.5281/zenodo.24492865) formalizes the cubic theta series $\sum q^{n^3}$ of Chowla–Chowla 1984 / Lipshitz–Rubel 1991 / Pak Conjecture 2.6. Additional modules—literal mock/false theta $q$-series, Selberg-class $L$-functions, Barnes/Faddeev quantum dilogarithms, and Pak Conjecture 2.5a—are staged for `v3.1.0` pending individual statement-spec review.)*

## Unconditional `PNT+` Integration

The unconditional prime-counting and prime-partition theorems discharge `PNTAllOrders` (`|π(x) - li(x)| = O_M(x / (log x)^M)` for all `M`) directly from `MediumPNT` of the **PrimeNumberTheoremAnd (PNT+)** project led by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors** ([PNT+ repository](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) · [Transfer proof](PNTIntegration/PrimeCountingFromPsi.lean) · [Third-party credits](vendor/README.md)).

## Reproduce the Check

Use Lean `v4.36.0` (Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`):

```bash
lake exe cache get
lake build
lake env lean Verify.lean
```

For independent kernel replay of the entire transitive dependency graph (use `ulimit -s 65520` on macOS/Linux for large modules):

```bash
ulimit -s 65520
lake env leanchecker --fresh Statements.All
```

## Credits and License

The unconditional prime-counting and prime-partition theorems build directly on the `MediumPNT` formalization from the **PrimeNumberTheoremAnd (PNT+)** project by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors**, as well as **LeanArchitect**. Google Gemini, OpenAI Codex, and Anthropic Claude assisted with the mathematical investigation, adversarial auditing, drafting, and Lean 4 formalization. Independent specialist review is welcome. [License](LICENSE) · [Third-party credits and licenses](vendor/README.md)
