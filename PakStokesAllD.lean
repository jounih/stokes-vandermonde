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
public import PakStokes.AllD.BlackbodyPhotons3D
public import PakStokes.AllD.MockModularAlgebraCore
public import PakStokes.AllD.DysonShadowRank
public import PakStokes.AllD.PrimeDilationIsolation
public import PakStokes.AllD.DepthTwoCommutator
public import PakStokes.AllD.VafaWittenWitnesses
public import PakStokes.AllD.SquarePartitionsModN
public import PakStokes.AllD.MockModularRotatedRays
public import PakStokes.AllD.MockModularCuspDescent
public import PakStokes.AllD.UniqueSumAndJetIdealCore
public import PakStokes.AllD.DepthThreeSliceRankCore
public import PakStokes.AllD.HeckeRadiusPeelingAndBerndtEntry45
public import PakStokes.AllD.ExponentMeasureAndPolyCauchyCore

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
    `quantumGases_1D_3D_bose_fermi_joint_diff_indep`).
13. `PakStokes.AllD.BlackbodyPhotons3D` (100% unconditional from Mathlib):
    Physical relativistic massless blackbody photon gas (`ω(n) = ‖n‖`) in 2D, 3D, and 4D,
    exact lattice-sphere representation counts `r2Count`, `r3Count`, `r4Count`, elementary
    three-class arithmetic separation (`1 mod 4` Fermat two-square, constructive `Q² + 2`
    yielding infinitely many square-free cores `s ≡ 3 mod 8` with `r₃(k² s) ≥ 1` and
    `r₂(k² s) = 0`, and `7 mod 8` Lagrange four-square), analytic regrouping identity
    `photonEnergyAnalytic_eq_tsum_sqrt`, Hahn/transseries internal energy `U_photon^{(D)}`
    and grand potential `log Z_photon^{(D)}`, plus unconditional `photon2D_non_ade`,
    `photon3D_non_ade`, `photon4D_non_ade`, `photon2D_photon3D_photon4D_joint_diff_indep`,
    `photon2D_photon3D_photon4D_all_derivs_diff_indep`,
    `photon2D_photon3D_photon4D_no_joint_poly_ade`, and
    `photonLogZ_2D_3D_4D_joint_diff_indep`.
14. `PakStokes.AllD.MockModularAlgebraCore` (100% unconditional from Mathlib):
    Zero-black-box algebraic and analytic core for mock-modular and positive-weight modular
    differential transcendence:
    (a) Exact symbolic Mock-Modular Vandermonde determinant `mockModular_jet_det_eq` and
    analytic mode-derivative identity `iteratedDeriv_mockModular_mode`;
    (b) Exact polynomial translation-invariance minimality theorem
    `mockModular_translation_invariance_kills_linear_collisions`, Taylor expansion
    `mockModular_taylor_expansion`, `mockModular_minimal_annihilator_contradiction`, and
    `mockModular_jump_induction_contradiction`;
    (c) Exact Bol/modular iterated-derivative transformation law `modular_iteratedDeriv_gamma`
    and the universal positive-weight modular differential independence theorem
    (`positiveWeight_modular_diff_indep_abstract`, `positiveWeight_modular_forms_diff_indep`,
    `positiveWeight_modular_thetaQ_diff_indep`);
    (d) Maximum Modulus Watson Uniqueness Lemma (`maxModulus_watson_uniqueness`) on
    `{‖z‖ ≥ R₀, |arg z| ≤ 2π/3}`.
15. `PakStokes.AllD.DysonShadowRank` (100% unconditional from Mathlib):
    All-moduli Dyson rank-mod-`N` folded-cycle shadow graph theorem (`∀ N ≥ 2`):
    Bringmann–Ono trigonometric shadow identity (`dyson_shadow_trig_identity`), folding map
    `foldMod` with cosine invariance (`cos_two_pi_mul_foldMod`), undirected folded-cycle graph
    `dysonFoldedGraph` with exact component count (`dysonFoldedGraph_connectedComponent_card`:
    `1` when `¬ 3 ∣ N`, `N / 6 + 1` when `3 ∣ N`), exact linear rank over any field `K`
    (`dysonShadowRank_eq`: `N / 2` when `¬ 3 ∣ N`, `N / 3` when `3 ∣ N`), exact zero-shadow
    characterization (`mem_shadowKernel_iff_const_on_components`,
    `mem_shadowKernel_iff_const_on_reachable`), non-vanishing shadow for every single residue
    (`single_vertex_not_mem_shadowKernel`), explicit `N = 6` witness, and real trigonometric
    sine-product shadow matrix rank via discrete cosine orthogonality (`dysonTrigShadowRank_eq`).
16. `PakStokes.AllD.PrimeDilationIsolation` (100% unconditional from Mathlib):
    Paper #10 Appendix A Prime-Frequency Dilation Isolation Theorem across arbitrary finite sets
    of positive integer dilations: exact prime-square isolation (`no_sq_mul_eq_prime_sq_mul_of_gt`,
    `no_nat_eq_prime_mul_sqrt_ratio`, `prime_dilation_freq_ne`), exact non-vanishing sine residue
    factor `± √3 / 2` for primes `p > 3` (`mockFalse_sine_factor_eq`,
    `mockFalse_sine_factor_ne_zero`), existence of arbitrarily many strictly increasing isolated
    primes (`exists_isolated_primes_for_max_dilation`), symbolic/pointwise/weighted mock-modular
    jet Vandermonde nonsingularity (`prime_dilation_jet_det_ne_zero`,
    `prime_dilation_jet_eval_det_ne_zero`, `prime_dilation_weighted_jet_det_ne_zero`),
    descending block elimination (`prime_dilation_block_elimination`), and dual-ray mock/false-theta
    joint elimination (`dual_ray_prime_dilation_elimination`, `dual_ray_prime_dilation_constant`).
17. `PakStokes.AllD.DepthTwoCommutator` (100% unconditional from Mathlib):
    Formal-grading triangular automorphism group commutator (`triSub`, `triSubInv`,
    `triSub_commutator_lower`, `triSub_commutator_depth2`, `triSub_commutator_self_zero`,
    `triSub_commutator_symmetric_product_zero`, `triCommutatorAlgHom_fixes_lower_poly`),
    multi-sector triangular commutators, shifted & two-sector block Vandermonde determinants
    (`shiftedVandermonde_det_ne_zero`, `twoSector_blockVandermonde_det_ne_zero`), and abstract
    Wronskian / minimal-degree elimination (`minimal_degree_elimination_of_int_shifts`,
    `minimal_degree_elimination_twoSector_vandermonde`, `minimal_degree_elimination_field_vandermonde`).
18. `PakStokes.AllD.VafaWittenWitnesses` (100% unconditional from Mathlib):
    Exact arithmetic theta-channel representation multiplicities and antisymmetric commutator
    pairings (`vwPairing`) for rank-three Vafa–Witten flux sectors on `ℂℙ²`:
    all-`n` witnesses (`vwPairing_flux1_witness`, `vwPairing_flux0_vanishes_on_flux1_witness`,
    `vwPairing_flux0_witness`, `vwPairing_flux1_vanishes_on_flux0_witness`), `ν = -1` symmetry
    (`vwPairing_flux_neg1_eq_flux1`), equal-total collision separation (`(1/3, 9)` vs `(16/3, 4)`),
    all-order two-sector block Vandermonde nonsingularity (`vwWitness_blockMatrix_det_ne_zero`),
    and two-sector minimal-degree elimination (`vwWitness_twoSector_minimal_degree_contradiction`).
19. `PakStokes.AllD.SquarePartitionsModN` (100% unconditional from Mathlib):
    Partitions into squares split by number of parts modulo `N` and periodic-weight rank law:
    Dirichlet primes `p ≡ 1 (mod N)` (`exists_inf_primes_modN_one`), Besicovitch squarefree
    two-ray coordinate ring (`TwoRayRing`, `eulerDeriv`, `rayDerivX`), strong induction on
    `k ≥ 1` via `T_b ∂_{T_b}` (`squareModN_strong_induction`, `squareModN_wave_diff_indep`),
    general Kolchin log-derivative transfer (`diffAlg_kolchin_logDeriv_indep`,
    `squareModN_twistedProd_diff_indep`), invertible `N × N` DFT (`dftMatrix_det_ne_zero`,
    `squareModN_parts_diff_indep`, `squareEvenOdd_joint_diff_indep`), full periodic-weight
    full periodic-weight differential rank law (`squarePeriodicWeights_diff_rank_eq`), and the
    countably many multiples-of-`d` corollary (`squareMultiplesOfD_diff_indep`).
20. `PakStokes.AllD.MockModularRotatedRays` (100% unconditional from Mathlib):
    Analytic rotated-ray continuation, uniform Gevrey-1 asymptotics, and exact Hankel keyhole jump:
    bounded closed sector `sector34`, convergent germ subring `convergentSubring`, Gevrey-1 algebra
    closure and Watson uniqueness (`gevrey1_zero_imp_exp_decay`, `watson_of_gevrey1_zero`), exact
    `(1 + w)^{-α}` Taylor integral remainder (`cpow_taylor_integral_remainder`) and `PhiReal`
    iterated-derivative Gevrey-1 asymptotics (`PhiReal_iteratedDeriv_hasGevrey1Asymp`), rotated
    rays `gammaMinus`/`gammaPlus` and connected open sectors `UPlus`/`UMinus`, angle-invariance
    (`ray_integral_const_on_Icc`, `ray_integral_eq_real`), simultaneous lateral annihilation
    (`lateral_simultaneous_annihilation`), and exact single-mode/series Hankel reflection jump
    with termwise differentiation (`hankel_single_mode_jump`, `hankel_series_jump`,
    `hankel_series_jump_iteratedDeriv`).
21. `PakStokes.AllD.MockModularCuspDescent` (100% unconditional from Mathlib):
    Single-cusp `y = 1` Eichler integral split (`eichler_y1_split_cusp`, `eichler_y1_split_nonOne`,
    `eichler_y1_split_one`, `FHol_differentiableOn_ball`), uniform Cauchy `q₁`-tail bound
    (`cauchy_q1_tail_bound`), logarithmic/Puiseux scale separation & `q₁`-induction
    (`log_puiseux_scale_separation`, `half_parity_scale_separation`, `q1_induction_kill`),
    exact top-degree survival and minimal-total-degree descent into `ℂ{x}[Z]`
    (`top_degree_survival`, `minimal_degree_descent`), lateral annihilation of convergent
    polynomial relations and collision-free translation-invariance induction
    (`mvPoly_conv_lateral_simultaneous_annihilation`, `mockModular_translation_invariance_induction`),
    and the end-to-end Paper #10 assembly theorems (`mockModular_scalar_diff_trans_of_cuspSplit`,
    `mockModular_joint_shadow_rank_of_cuspSplit`, `mockModular_joint_diff_indep_of_q1Expansion`).
22. `PakStokes.AllD.UniqueSumAndJetIdealCore` (100% unconditional from Mathlib):
    Unique-sum isolation trees for accumulating reciprocal singularities (`HasUniqueRep`,
    `uniqueSum_extension_cofinite`, `uniqueSum_tree_exists`, `uniqueSum_no_lower_collision`,
    `uniqueSum_perm_collisions`, `uniqueSum_symm_sum_eq_factorial_mul`), symmetric multilinear
    polarization vanishing & Vandermonde tail-span (`polarization_vanish_of_cofinite_span`,
    `homogPolarize`, `homogPoly_eq_zero_of_cofinite_tree_vanish`, `vandermonde_tail_span_complex`,
    `reciprocal_accumulation_polarization_obstruction`), Stokes jet-rank ideal linearization
    (`StokesJetSystem`, `stokes_jet_ideal_linearization`, `stokes_jet_ideal_linearization_field`),
    and the single-singularity arbitrary-order-`d` family (`singleSingBeta_distinct_mod_int`,
    `singleSingJetMatrixCast_rank`, `singleSingOrderDOp_annihilates_nonneg`,
    `single_singularity_order_d_rank`).
23. `PakStokes.AllD.DepthThreeSliceRankCore` (100% unconditional from Mathlib):
    Depth-3 `S₃` Eulerian idempotents (`eulerianE1`, `eulerianE2`, `eulerianE3`,
    `eulerian_sum_eq_id`, faithful invariants `lieInvariant`/`mixedBilinear`, regular dimensions
    `6 = 2 + 3 + 1` in `eulerianReg_dim_decomposition_rat`), free depth-3 shuffle algebra
    identities (`depth3_shuffle_identity`, `depth3_alternating_shuffle_identity`,
    `depth3_e2_period_pairing`), exact cubic slice-rank = vanishing-on-codimension-`N`-subspace
    equivalence (`cubic_sliceRank_le_iff_vanishes_on_codim_subspace`,
    `symTensor_cubic_sliceRank_le_iff_vanishes_on_codim_subspace`), and Tao's diagonal cubic
    slice-rank lower bound (`tao_diagonal_cubic_sliceRank_exact`,
    `diag_cubic_symSliceRank_lower_bound`, `vCube_jet_poly_symSliceRank_lower_bound`).
24. `PakStokes.AllD.HeckeRadiusPeelingAndBerndtEntry45` (100% unconditional from Mathlib):
    Unconditional resolution of Bruce Berndt's open remark on Ramanujan's `Notebooks V Ch. 32
    Entry 45` (`entry45Perturb_abs_lt_weight`, `entry45Perturb_moment_zero`,
    `entry45_stieltjes_indeterminate`), exact `> 1.7×` Gross CM Hecke radius separation
    (`eisensteinE4_norm_bounds`, `grossRadius_consecutive_ratio_gt`, `grossRadius_strictMono`,
    `grossRadius_chain`), abstract multivariate natural-boundary radius peeling
    (`exists_minimal_relation_nonzero_separant`, `radius_peeling_joint_diff_indep`,
    `radius_peeling_over_baseField`, `grossCM_ten_series_radius_peeling`,
    `universal_pair_radius_peeling`), and Ramanujan's Lost Notebook p. 343 hidden units in
    `ℤ[⁵√2]^×` and `ℤ[⁷√2]^×` (`ln343_real_identity`, `ln343_unit_in_Z_adjoin_fifthRoot2`,
    `ln343_block2_seventhRoot2_units`).
25. `PakStokes.AllD.ExponentMeasureAndPolyCauchyCore` (100% unconditional from Mathlib):
    Paper #12 Section 7 exponent-measure rank core (`poly_ae_zero_imp_zero_of_infinite_support`,
    `poly_weight_rank_infinite_support`, `poly_weight_rank_complexMeasure_infinite_support`,
    `poly_weight_rank_finite_support_le`), exponent-atom Laurent operator `T = x ∂ - 1/x` &
    shift-band pushforward (`laurentT_add_smul_expAtom`, `finite_support_measure_annihilated`,
    `shift_band_iter_identity`, `shift_band_measure_identity`), and Komatsu's poly-Cauchy
    numbers of both kinds (`polyCauchy_log_density_moment`, `cauchy_first_second_kind_relation`,
    `polyCauchy_densities_poly_indep_of_not_both_one`, `polyCauchy_densities_both_one_relation`,
    `polyCauchy_jet_span_finrank`, `polyCauchy_nonpos_dfinite_poly`). -/
