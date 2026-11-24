# Formal Resurgence and Differential Transcendence in Lean 4 (`stokes-vandermonde`)

This Lean 4 library (`v2.0.0`) formalizes the **Borel–Stokes–Vandermonde criterion** for differential transcendence—both autonomous and non-autonomous over $\mathbb{C}(u)$ with rotated Stokes rays and arbitrary finite pole orders—and applies it to prove **unconditional, zero-hypothesis differential transcendence** for a broad suite of classical and modern generating functions, special functions, and mock modular Eichler integrals.

All **44 audited theorems** depend strictly on the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, zero custom axioms, zero `native_decide`, and independent kernel replay via `lake env leanchecker --fresh`.

## Summary of Kernel-Verified Theorems (`v2.0.0`)

| Area | Mathematical Result | Main Lean 4 Declarations | Module |
| :--- | :--- | :--- | :--- |
| **General Engine (Wave 1)** | Autonomous Borel–Stokes–Vandermonde criterion for simple poles on $[0,\infty)$ | `borel_stokes_vandermonde_no_autonomous_ade`, `no_autonomous_ade_of_meromorphic_borel` | [GeneralTheorem2.lean](PakPrimes/GeneralTheorem2.lean) |
| **General Engine (Wave 2)** | Full non-autonomous $\mathbb{C}(u)$ criterion on rotated rays $e^{i\theta_0}$ with arbitrary finite pole orders $m_k \ge 1$ | `higher_order_stokes_vandermonde_no_rat_ade`, `no_rat_ade_of_higher_order_borel` | [HigherOrderStokes.lean](PakPrimes/HigherOrderStokes.lean) |
| **Hölder's Theorem (1887)** | $\Gamma(z)$ satisfies no nonzero ADE over $\mathbb{C}(z)$ (nor $\Gamma(x)$ over $\mathbb{R}[x]$); $\psi_1(u)$ D-transcendental | `holder_gamma_no_rat_ade`, `holder_gamma_no_ade`, `holder_realGamma_no_ade`, `trigamma_no_rat_ade` | [HolderGamma.lean](PakPrimes/HolderGamma.lean) |
| **Hilbert (1900) / Ostrowski (1920)** | $\zeta(s)$ satisfies no nonzero ADE over $\mathbb{C}(s)$ directly on Mathlib's `riemannZeta` | `ostrowski_riemannZeta_no_rat_ade`, `ostrowski_riemannZeta_no_complex_ade` | [OstrowskiZeta.lean](PakPrimes/OstrowskiZeta.lean) |
| **Prime Counting (Pak Conj. 2.5b)** | $\sum_p q^p$, $\sum_{n \ge 0}\pi(n)q^n$, and $\sum_{n \ge 2} q^n/\log n$ are D-transcendental over $\mathbb{C}(q)$ | `primeCounting_and_indicator_independent`, `primeCounting_and_indicator_no_rationalADE`, `logReciprocal_algebraicIndependent` | [Final.lean](PNTIntegration/Final.lean), [ExplicitRat.lean](PNTIntegration/ExplicitRat.lean), [MainTheorem.lean](PakPrimes/MainTheorem.lean) |
| **Prime Partitions (A000607 & A000586)** | Unconditional D-transcendence of literal Euler products $\prod_p (1-q^p)^{-1}$ and $\prod_p (1+q^p)$ via `PNT+` | `partitionPrimesEulerProduct_algebraicIndependent`, `distinctPrimesEulerProduct_algebraicIndependent`, `hasProd_partitionPrimesEulerProduct`, `hasProd_distinctPrimesEulerProduct` | [PrimePartitions.lean](PNTIntegration/PrimePartitions.lean), [PrimeEulerProduct.lean](PakPrimes/PrimeEulerProduct.lean) |
| **Divisor Sums & MacMahon $M(q)$** | All even divisor sums $L_{2m}(q) = \sum \sigma_{2m}(n)q^n$ (incl. $L_0(q) = \sum d(n)q^n$) & literal MacMahon product $\prod_{n\ge 1}(1-q^n)^{-n}$ | `sigmaEvenSeries_algebraicIndependent`, `divisorSeries_algebraicIndependent`, `hasProd_macmahonEulerProduct`, `macmahonEulerProduct_algebraicIndependent` | [DivisorAndMacMahon.lean](PakPrimes/DivisorAndMacMahon.lean), [MacMahonEulerProduct.lean](PakPrimes/MacMahonEulerProduct.lean) |
| **Meromorphic EGF $\to$ OGF** | General EGF-to-OGF bridge & concrete witnesses (Bernoulli, $\tan$, $\sec$, $\sec^2$, $(1 - c e^{\lambda\xi})^{-p}$) | `ogf_algebraicIndependent_of_higherOrderBorel`, `bernOGF_algebraicIndependent`, `tanOGF_algebraicIndependent`, `secOGF_algebraicIndependent`, `ratExpOGF_algebraicIndependent` | [PakYeliussizovEGF.lean](PakPrimes/PakYeliussizovEGF.lean) |
| **Weight-1 Mock Modular / Eichler** | Split Stieltjes / Eichler integrals over $\mathbb{C}(u)$, incl. KRY/Duke–Li $E_1(\tau;\chi_{-3})$ and cusp shadow $\eta(\tau)\eta(23\tau)$ | `eichlerWeightOne_no_rat_ade`, `eichlerWeightOne_integral_no_rat_ade`, `kryEisenstein_no_rat_ade`, `cuspG23_no_rat_ade` | [MockModularWeightOne.lean](PakPrimes/MockModularWeightOne.lean) |

*(Note: The complementary $n$-th prime generating function $\sum p_n q^n$ in Pak's Conjecture 2.5 remains open. A separate companion repository [pak-cubic-theta](https://doi.org/10.5281/zenodo.24492865) formalizes the cubic theta series $\sum q^{n^3}$ of Chowla–Chowla 1984 / Lipshitz–Rubel 1991 / Pak Conjecture 2.6.)*

## Unconditional `PNT+` Integration

The unconditional prime-counting and prime-partition theorems discharge `PNTAllOrders` (`|π(x) - li(x)| = O_M(x / (log x)^M)` for all `M`) directly from the quantitative Chebyshev-$\psi$ prime number theorem `MediumPNT` of the **PrimeNumberTheoremAnd (PNT+)** project led by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors** ([PNT+ repository](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) · [Transfer proof](PNTIntegration/PrimeCountingFromPsi.lean) · [Third-party credits](vendor/README.md)).

## Reproduce the Check

Use Lean `v4.36.0` (Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`):

```bash
lake exe cache get
lake build
lake env lean Verify.lean
```

For independent kernel replay (use `ulimit -s 65520` on macOS/Linux for large modules):

```bash
ulimit -s 65520
for mod in \
  PNTIntegration.PrimeCountingFromPsi PNTIntegration.Final PNTIntegration.ExplicitADE \
  PNTIntegration.ExplicitRat PNTIntegration.PrimePartitions PakPrimes \
  PakPrimes.HigherOrderStokes PakPrimes.HolderGamma PakPrimes.OstrowskiZeta \
  PakPrimes.DivisorAndMacMahon PakPrimes.MacMahonEulerProduct \
  PakPrimes.PakYeliussizovEGF PakPrimes.PartitionsIntoPrimes \
  PakPrimes.PrimeEulerProduct PakPrimes.MockModularWeightOne; do
  lake env leanchecker --fresh "$mod"
done
```

## Credits and License

The unconditional prime-counting and prime-partition theorems build directly on the `MediumPNT` formalization from the **PrimeNumberTheoremAnd (PNT+)** project by **Alex Kontorovich, Terence Tao, and the PrimeNumberTheoremAnd contributors**, as well as **LeanArchitect**. Google Gemini, OpenAI Codex, and Anthropic Claude assisted with the mathematical investigation, adversarial auditing, drafting, and Lean 4 formalization. Independent specialist review is welcome. [License](LICENSE) · [Third-party credits and licenses](vendor/README.md)
