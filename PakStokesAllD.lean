module

public import PakStokes.AllD.BesicovitchCore
public import PakStokes.AllD.UniversalThimble
public import PakStokes.AllD.ExtremeRayProjection
public import PakStokes.AllD.AllDFormalTransfer
public import PakStokes.AllD.TrackedWaves
public import PakStokes.AllD.AllDThetaDTrans
public import PakStokes.AllD.PowerPartitions
public import PakStokes.AllD.JumpPointMultivariate
public import PakStokes.AllD.SquareQuotientsAndDivisors
public import PakStokes.AllD.Bec3DAnalytic
public import PakStokes.AllD.Bec3DDiffTrans

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
   diagonal-form non-vacuity witnesses (`diagForm_transseries_non_ade`, `diagQuartic2D_non_ade`).
10. `PakStokes.AllD.SquareQuotientsAndDivisors` (100% unconditional from Mathlib):
    General multiplicative quotient-rank differential independence (`monomial_family_diff_indep_of_logDeriv`),
    Codex's square-partition quotient-rank & forest corollaries (`squarePart_monomial_family_diff_indep`,
    `distinctSquares_non_ade`, `overpartSquares_non_ade`, `distinctSquares_overpartSquares_joint_diff_indep`,
    `kRegularSquares_dilations_diff_indep`, `distinctSquares_dilations_diff_indep`, `fermi1D_non_ade`,
    `fermi1D_dilations_diff_indep`, `squarePart_forest_quotients_diff_indep`), unified `d = 2` zero-tilt
    wave-profile engine (`SqRayProfile`, `sqRayProfile_dilations_diff_indep`, `sqRayProfile_non_ade`),
    and the square-divisor generating function `L_{2, 0}(q) = ∑_{N ≥ 1} d_□(N) q^N`
    (`squareDivisor_analytic_identity`, `squareDivisor_non_ade`, `squareDivisor_dilations_diff_indep`).
11. `PakStokes.AllD.Bec3DAnalytic` (100% unconditional from Mathlib):
    Exact closed-form 3D iterated Poisson summation + elementary `K_{1/2}` identity
    `bec3D_analytic_identity` for the physical 3D ideal Bose–Einstein condensate internal energy
    `F_BEC^{(3)}(e^{-1/X²}) = ∑_{N ≥ 1} r_3(N) N / (exp(N / X²) - 1)`.
12. `PakStokes.AllD.Bec3DDiffTrans` (100% unconditional from Mathlib):
    Physical 3D ideal Bose–Einstein condensate `Z_BEC^{(3)}(q)` and 3D ideal Fermi–Dirac gas
    `Z_FD^{(3)}(q)` (`logDerivBec3D_non_ade`, `logDerivBec3D_dilations_diff_indep`, `bec3D_non_ade`,
    `bec3D_zpow_non_ade`, `bec3D_dilations_diff_indep`, `fermi3D_non_ade`, `fermi3D_dilations_diff_indep`,
    `bec3D_fermi3D_joint_diff_indep`, `bec3D_bose_fermi_quotient_rank`, `bec3D_forest_quotients_diff_indep`),
    plus joint differential independence of 1D and 3D ideal quantum gases
    (`logDeriv_bec1D_bec3D_dilations_diff_indep`, `bec1D_bec3D_dilations_diff_indep`,
    `bec1D_bec3D_joint_diff_indep`, `powerPart2_bec3D_joint_diff_indep`, and
    `quantumGases_1D_3D_bose_fermi_joint_diff_indep`). -/
