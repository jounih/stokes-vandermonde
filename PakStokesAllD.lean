module

public import PakStokes.AllD.BesicovitchCore
public import PakStokes.AllD.UniversalThimble
public import PakStokes.AllD.ExtremeRayProjection
public import PakStokes.AllD.AllDFormalTransfer
public import PakStokes.AllD.TrackedWaves
public import PakStokes.AllD.AllDThetaDTrans
public import PakStokes.AllD.PowerPartitions
public import PakStokes.AllD.JumpPointMultivariate

/-! # `PakStokesAllD`: All-`d` Marked-Wave Stokes Formalization (`d ≥ 2`, `d ≥ 3`)

Root aggregator re-exporting the entire strictly additive all-`d` formalization:

1. `PakStokes.AllD.BesicovitchCore` (100% unconditional from Mathlib):
   `rFreeCore`, Besicovitch's Theorem (1940) for all `r ≥ 2`, `ℚ`-linear independence
   of distinct prime-power actions `k^{d/(d-1)}` (`d ≥ 3`), and zero-tilt injectivity
   of `ActionKey d → ℂ`.
2. `PakStokes.AllD.UniversalThimble` (100% unconditional from Mathlib):
   8-line Critical-Value-Free LHP Theorem for `P_d(w) = w^d - d w + (d - 1)`, exact
   UHP saddle counts (`d/2` even, `2 * ((d+1)/4)` odd), exact rotated phase identity,
   Beta-averaged kernel bounds, and the universal `PowerClass (1/2)` wave scaling lemma.
3. `PakStokes.AllD.ExtremeRayProjection` (100% unconditional from Mathlib):
   Extreme ray `ℰ_d = ℝ_{≥ 0} A_0(d)`, exact extreme-ray prime-ideal algebra
   homomorphism `extremeRayProj`, `FiniteParities M`, `exp(c/p^r) ∈ PowerClass 0`,
   and the generalized domain Marked Jacobian theorem (`lex_nonZeroDivisor_of_unit` +
   `independent_of_marked_jacobian_domain`).
4. `PakStokes.AllD.AllDFormalTransfer` (100% unconditional from Mathlib):
   Formal power series `Θ_d(q)`, dilations `Θ_d(q^a)`, Waring powers `Θ_d(q)^k`,
   `allD_formal_transfer`, `waring_algebraicIndependent_of_base`, and the exact
   `q`-derivative chain rule `iterQDeriv_eq_sum`.
5. `PakStokes.AllD.TrackedWaves`:
   Minimal analytic interface `AllDStokesProfile d`, unified extreme-ray marked-wave
   engine `TrackedExpansion`, variable restriction `restrictVars`, and concrete
   unconditional `d = 3` non-vacuity witness `stokesProfileThree`.
6. `PakStokes.AllD.AllDThetaDTrans`:
   Master theorems `theta_d_marked_wave_non_ade`, `theta_d_waring_power_non_ade`,
   `theta_d_dilations_diff_indep`, `theta_d_dfree_dilations_diff_indep`, plus
   unconditional `d = 3` instantiations `theta_3_non_ade_via_allD`,
   `theta_3_waring_power_non_ade`, and `theta_3_dilations_diff_indep`.
7. `PakStokes.AllD.SquaresPartitionAnalytic` (100% unconditional from Mathlib):
   Exact closed-form Poisson-summation / cotangent-residue identity for partitions into
   squares (`d = 2`), `squares_partition_analytic_identity`.
8. `PakStokes.AllD.PowerPartitions`:
   Zero-tilt constant-Vandermonde differential transcendence for all `d`-th power
   partition products `P_d(q) = ∏_{n ≥ 1} (1 - q^{n^d})^{-1}` (`d ≥ 2`), Kolchin
   log-derivative transfer, prime multiplicity `c_d(p) = 1`, exact constant `J × J`
   prime Vandermonde non-vanishing, all-`d` master theorems (`logDerivPowerPart_non_ade`,
   `powerPart_non_ade`, `powerPart_zpow_non_ade`, `logDerivPowerPart_dilations_diff_indep`,
   `powerPart_dilations_diff_indep`), AND 100% UNCONDITIONAL `d = 2` (partitions into
   squares) theorems (`powerPart_2_non_ade`, `logDerivPowerPart_2_non_ade`,
   `powerPart_2_zpow_non_ade`, `logDerivPowerPart_2_dilations_diff_indep`,
   `powerPart_2_dilations_diff_indep`) via `powerPartStokesProfileTwo`.
9. `PakStokes.AllD.JumpPointMultivariate` (100% unconditional from Mathlib):
   Probe 268 Theorem 2.1 (Jump-Point Derivation Engine for Multivariate Non-Quadratic Forms),
   connecting `BesicovitchCore` Wulff rays (`wulffRay_infinite_qrank`) to `monoidDeriv`,
   `hahnDeriv`, `jumpPoint_minimal_relation_vandermonde`, `multivariate_evenForm_algebraic_dtrans`,
   `multivariate_jumpPoint_non_ade`, constructive positive-Hessian multiplicity, and concrete
   diagonal-form non-vacuity witnesses (`diagForm_transseries_non_ade`, `diagQuartic2D_non_ade`). -/
