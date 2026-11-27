import PakPrimes
import PakPrimes.HigherOrderStokes
import PakPrimes.HolderGamma
import PakPrimes.OstrowskiZeta
import PakPrimes.DivisorAndMacMahon
import PakPrimes.MacMahonEulerProduct
import PakPrimes.PakYeliussizovEGF
import PakPrimes.PartitionsIntoPrimes
import PakPrimes.PrimeEulerProduct
import PakPrimes.MockModularWeightOne
import PakPrimes.HarmonicTrapShift
import PakPrimes.QuasipolynomialEulerParity
import PakPrimes.ThermalGasParity
import PakPrimes.ThermalGasEOS
import PakPrimes.MockThetaAndHurwitz
import PakPrimes.FalseThetaDichotomy
import PakPrimes.QuasipolynomialIFF
import PNTIntegration.PrimePartitions
import Statements.QuasipolynomialParity
import Statements.ThermalGasAndSpheres
import Statements.MordellAndFalseThetaIntegrals
import Statements.PrimesAndClassical
import Statements.PakNthPrime
import Statements.FishburnTorusKnots
import Statements.FlajoletRichmond
import Statements.VolterraVirial
import Statements.DistinctDensityPrimes
import Statements.HigherOrderStrongAndRH
import Statements.SelbergHyperbolic
import Statements.RankOneSymmetric
import Statements.UnconditionalPrimes
import Statements.CompletedXi
import Statements.SpectralPositivity
import PakStokesAllD

-- Wave 1: Autonomous Stokes–Vandermonde & Unconditional Prime Counting
#check @PakPrimes.GeneralTheorem2.borel_stokes_vandermonde_no_autonomous_ade
#check @PakPrimes.GeneralTheorem2.no_autonomous_ade_of_meromorphic_borel
#check @PakPrimes.GeneralTheorem2.gHat_no_autonomous_ade_via_general_theorem_2
#check @PakPrimes.Main.logReciprocal_algebraicIndependent
#check @PakPrimes.Main.pak_conjecture_2_5b_of_pnt
#check @PakPrimes.Main.primeCounting_and_indicator_independent
#check @PakPrimes.Main.primeCounting_and_indicator_no_polynomialADE
#check @PakPrimes.Main.primeCounting_and_indicator_no_rationalADE

#print axioms PakPrimes.GeneralTheorem2.borel_stokes_vandermonde_no_autonomous_ade
#print axioms PakPrimes.GeneralTheorem2.no_autonomous_ade_of_meromorphic_borel
#print axioms PakPrimes.GeneralTheorem2.gHat_no_autonomous_ade_via_general_theorem_2
#print axioms PakPrimes.BorelStokesVandermonde.gHat_no_autonomous_ade
#print axioms PakPrimes.Main.logReciprocal_algebraicIndependent
#print axioms PakPrimes.Main.pak_conjecture_2_5b_of_pnt
#print axioms MediumPNT
#print axioms PakPrimes.Main.pntAllOrders
#print axioms PakPrimes.Main.primeCounting_and_indicator_independent
#print axioms PakPrimes.Main.primeCounting_and_indicator_no_polynomialADE
#print axioms PakPrimes.Main.primeCounting_and_indicator_no_rationalADE

-- Wave 2: Higher-Order Sectorial Non-Autonomous Stokes–Vandermonde over ℂ(u)
#check @PakPrimes.HigherOrderStokes.higher_order_stokes_vandermonde_no_ade
#check @PakPrimes.HigherOrderStokes.higher_order_stokes_vandermonde_no_rat_ade
#check @PakPrimes.HigherOrderStokes.no_rat_ade_of_higher_order_borel
#print axioms PakPrimes.HigherOrderStokes.higher_order_stokes_vandermonde_no_ade
#print axioms PakPrimes.HigherOrderStokes.higher_order_stokes_vandermonde_no_rat_ade
#print axioms PakPrimes.HigherOrderStokes.no_rat_ade_of_higher_order_borel

-- Wave 2: Hölder (1887), Ostrowski (1920), Divisor/MacMahon, EGF->OGF, Prime Partitions, Weight-1
#print axioms PakPrimes.HolderGamma.trigamma_no_rat_ade
#print axioms PakPrimes.HolderGamma.holder_gamma_no_ade
#print axioms PakPrimes.HolderGamma.holder_gamma_no_rat_ade
#print axioms PakPrimes.HolderGamma.holder_realGamma_no_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_complex_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_rat_ade
#print axioms PakPrimes.DivisorAndMacMahon.sigmaEvenSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.divisorSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.macmahonSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.hasProd_macmahonEulerProduct
#print axioms PakPrimes.DivisorAndMacMahon.macmahonEulerProduct_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.ogf_algebraicIndependent_of_higherOrderBorel
#print axioms PakPrimes.PakYeliussizovEGF.bernOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.tanOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.secOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.sec2OGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.ratExpOGF_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.hasProd_partitionPrimesEulerProduct
#print axioms PakPrimes.PartitionsIntoPrimes.hasProd_distinctPrimesEulerProduct
#print axioms PakPrimes.PartitionsIntoPrimes.partLogDeriv_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.partitionPrimes_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctLogDeriv_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctPrimes_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctPrimesEulerProduct_algebraicIndependent
#print axioms PakPrimes.MockModularWeightOne.eichlerWeightOne_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.eichlerWeightOne_integral_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.kryEisenstein_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.cuspG23_no_rat_ade

-- Wave 3 (v3.0.0): Quasipolynomial Euler-Product Parity Dichotomy, Converse (M=1,2), Joint Independence, & All-Dimension S^s
#print axioms Statements.QuasipolynomialParity.quasipoly_lambert_pure_dTrans
#print axioms Statements.QuasipolynomialParity.quasipoly_lambert_eventually_dTrans
#print axioms Statements.QuasipolynomialParity.quasipoly_eulerProduct_eventually_dTrans
#print axioms Statements.QuasipolynomialParity.quasipoly_bose_eventually_dTrans
#print axioms Statements.QuasipolynomialParity.partsMod5One_dTrans
#print axioms Statements.QuasipolynomialParity.period1_lambert_iff
#print axioms Statements.QuasipolynomialParity.period1_eulerProduct_iff
#print axioms Statements.QuasipolynomialParity.period2_lambert_iff
#print axioms Statements.QuasipolynomialParity.period2_eulerProduct_iff
#print axioms Statements.QuasipolynomialParity.macMahon_partsMod5One_partsMod5Two_joint_dIndep
#print axioms Statements.QuasipolynomialParity.conformalScalar_allDim_sphere_iff

-- Wave 3 (v3.0.0): Relativistic Ideal Gas Parity, Unconditional Bose/Fermi EOS, Casimir, & Spheres
#print axioms Statements.ThermalGasAndSpheres.ideal_gas_dimensional_parity
#print axioms Statements.ThermalGasAndSpheres.bose_eos_3D_dTrans
#print axioms Statements.ThermalGasAndSpheres.fermi_eos_3D_dTrans
#print axioms Statements.ThermalGasAndSpheres.casimir_2D_dAlgebraic
#print axioms Statements.ThermalGasAndSpheres.casimir_1D_dTrans
#print axioms Statements.ThermalGasAndSpheres.casimir_3D_dTrans
#print axioms Statements.ThermalGasAndSpheres.conformalScalar_sphere_allDim_iff
#print axioms PakPrimes.ThermalGasEOS.boseEOS1D_no_rat_ade
#print axioms PakPrimes.ThermalGasEOS.fermiEOS1D_no_rat_ade
#print axioms PakPrimes.ThermalGasEOS.casimirForce2D_dAlgebraic
#print axioms PakPrimes.ThermalGasEOS.casimirEnergy2D_dAlgebraic
#print axioms PakPrimes.ThermalGasEOS.casimir1D_no_rat_ade
#print axioms PakPrimes.ThermalGasEOS.conformalScalar_sphere_parity

-- Wave 3 (v3.0.0): Mordell, Eichler, and Stieltjes Integrals over ℂ(u)
#print axioms Statements.MordellAndFalseThetaIntegrals.mockThetaF_mordell_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.mockThetaOmega_mordell_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.hurwitz_eichler_shadow_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.falseThetaSinh_mordell_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.kontsevich_mordell_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.rogers_stieltjes_dTrans
#print axioms Statements.MordellAndFalseThetaIntegrals.five_mordell_joint_dIndep
#print axioms Statements.MordellAndFalseThetaIntegrals.chazy_ode_from_ramanujan

-- Wave 1-2 Statement Specs
#print axioms Statements.PrimesAndClassical.primeCounting_and_indicator_dTrans
#print axioms Statements.PrimesAndClassical.partitionPrimes_eulerProduct_dTrans
#print axioms Statements.PrimesAndClassical.distinctPrimes_eulerProduct_dTrans
#print axioms Statements.PrimesAndClassical.macmahon_eulerProduct_dTrans
#print axioms Statements.PrimesAndClassical.holder_gamma_dTrans
#print axioms Statements.PrimesAndClassical.ostrowski_riemannZeta_dTrans

-- Wave 4 (v3.1.0): Unconditional Pak 2.5 (∑ p_n x^n) & Fishburn / Torus-Knot Kernel Series
#print axioms Statements.PakNthPrime.pak_2_5a
#print axioms Statements.PakNthPrime.pak_conjecture_2_5_and_prime_corollaries
#print axioms Statements.FishburnTorusKnots.zagier_2001_thm3
#print axioms Statements.FishburnTorusKnots.fishburn_ogf_dTrans_over_ratFunc
#print axioms Statements.FishburnTorusKnots.glaisher_T_egf_dTrans_over_ratFunc
#print axioms Statements.FishburnTorusKnots.torusKnot_kernel_euler_dTrans_over_ratFunc
#print axioms Statements.FishburnTorusKnots.torusKnot_kernel_alternating_dTrans_over_ratFunc
#print axioms PakPrimes.FishburnStrongDTrans.isConvergentPS_iff_exists_analyticAt
#print axioms Statements.FishburnTorusKnots.fishburn_ogf_stronglyDTrans_over_meromorphicGerms
#print axioms Statements.FishburnTorusKnots.glaisher_T_egf_stronglyDTrans_over_meromorphicGerms
#print axioms Statements.FishburnTorusKnots.torusKnot_kernel_euler_stronglyDTrans_over_meromorphicGerms
#print axioms Statements.FishburnTorusKnots.torusKnot_kernel_alternating_stronglyDTrans_over_meromorphicGerms

-- Wave 5 (v3.2.0): Flajolet-Richmond (BDR §2.2.6 #3), Sibuya Sub-Gevrey & Volterra Virial, Distinct-Density Primes, Strong C({x}) Lift, Conditional RH -> G_Lambda, & Analytic Toolkit
#print axioms Statements.FlajoletRichmond.frEGF_diff_eq
#print axioms Statements.FlajoletRichmond.frEGF_init
#print axioms Statements.FlajoletRichmond.frEGF_one
#print axioms Statements.FlajoletRichmond.frEGF_one_not_dTrans
#print axioms Statements.FlajoletRichmond.K_b_pos
#print axioms Statements.FlajoletRichmond.frEGFSeries_dTrans_over_ratFunc
#print axioms Statements.FlajoletRichmond.frEGFSeries_algebraicIndependent
#print axioms Statements.FlajoletRichmond.frPoissonSeries_dTrans_over_ratFunc
#print axioms Statements.FlajoletRichmond.frEGF_no_ade
#print axioms Statements.VolterraVirial.sibuya_subGevrey_convergent
#print axioms Statements.VolterraVirial.sibuya_subGevrey_convergent_euler
#print axioms Statements.VolterraVirial.volterraMu_no_rat_ade
#print axioms Statements.VolterraVirial.volterraNu_no_rat_ade
#print axioms Statements.VolterraVirial.volterraNu_temp_no_rat_ade
#print axioms Statements.VolterraVirial.fermiGas1D_virial3_no_rat_ade
#print axioms Statements.VolterraVirial.fermiGas1D_virial3_temp_no_rat_ade
#print axioms Statements.VolterraVirial.laplace_volterraNu
#print axioms Statements.DistinctDensityPrimes.distinctDensity_branches_algebraicIndependent
#print axioms Statements.DistinctDensityPrimes.distinctDensity_ogf_joint_algebraicIndependent
#print axioms Statements.DistinctDensityPrimes.distinctDensity_dyadic_finite
#print axioms Statements.DistinctDensityPrimes.distinctDensity_dyadic_countable
#print axioms Statements.HigherOrderStrongAndRH.ogf_stronglyDTrans_of_higherOrderBorel
#print axioms Statements.HigherOrderStrongAndRH.bernOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.tanOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.secPowOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.eulerGenocchiPowOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.trigammaOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.lambertOGF_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.riemannHypothesis_implies_G_Lambda_dTrans
#print axioms Statements.HigherOrderStrongAndRH.riemannHypothesis_implies_G_Lambda_stronglyDTrans
#print axioms Statements.HigherOrderStrongAndRH.multiscale_filter_spectral_dominance
#print axioms Statements.HigherOrderStrongAndRH.collatz_wielandt_rat_upper_bound

-- Wave 6 (v3.3.0): 3D/2D Hyperbolic Selberg, All-CROSS Parity & Heat Traces, & Elementary RH-Independent Primes
#print axioms Statements.SelbergHyperbolic.selberg3D_func_eq_critical_shift
#print axioms Statements.SelbergHyperbolic.selberg3D_ogf_stronglyDTrans
#print axioms Statements.SelbergHyperbolic.selberg3D_formalSeries_stronglyDTrans
#print axioms Statements.SelbergHyperbolic.selberg3D_laplace_no_conv_ade
#print axioms Statements.SelbergHyperbolic.selberg3D_laplace_no_rat_ade
#print axioms Statements.SelbergHyperbolic.func_eq_critical_shift
#print axioms Statements.SelbergHyperbolic.selberg_ogf_stronglyDTrans
#print axioms Statements.SelbergHyperbolic.selberg_formalSeries_stronglyDTrans
#print axioms Statements.SelbergHyperbolic.selberg_laplace_no_conv_ade
#print axioms Statements.SelbergHyperbolic.selberg_laplace_no_rat_ade
#print axioms Statements.RankOneSymmetric.cross_simplyConnected_dAlg_iff
#print axioms Statements.RankOneSymmetric.cross_all_dAlg_iff
#print axioms Statements.RankOneSymmetric.evenSphere_waveEGF_ogf_stronglyDTrans
#print axioms Statements.RankOneSymmetric.cpn_waveEGF_ogf_stronglyDTrans
#print axioms Statements.RankOneSymmetric.hpn_waveEGF_ogf_stronglyDTrans
#print axioms Statements.RankOneSymmetric.op2_waveEGF_ogf_stronglyDTrans
#print axioms Statements.RankOneSymmetric.adeSphere3QP_oddPart_eq_zero
#print axioms Statements.RankOneSymmetric.adeSphere3QP_borelAmp_eq_zero
#print axioms Statements.RankOneSymmetric.poincareSphere_molien_identity
#print axioms Statements.RankOneSymmetric.poincareSphereQP_oddPart_eq_zero
#print axioms Statements.RankOneSymmetric.poincareSphereQP_borelAmp_eq_zero
#print axioms Statements.RankOneSymmetric.octahedralSphere_molien_identity
#print axioms Statements.RankOneSymmetric.octahedralSphereQP_oddPart_eq_zero
#print axioms Statements.RankOneSymmetric.tetrahedralSphere_molien_identity
#print axioms Statements.RankOneSymmetric.tetrahedralSphereQP_oddPart_eq_zero
#print axioms Statements.RankOneSymmetric.binaryDihedralSphere_molien_identity
#print axioms Statements.RankOneSymmetric.binaryDihedralSphereQP_oddPart_eq_zero
#print axioms Statements.RankOneSymmetric.baseHeatInt_no_rat_ade
#print axioms Statements.RankOneSymmetric.baseHeatHalf_no_rat_ade
#print axioms Statements.RankOneSymmetric.evenCROSS_heatTrace_no_rat_ade
#print axioms Statements.RankOneSymmetric.evenSphere_heatTrace_no_rat_ade
#print axioms Statements.RankOneSymmetric.cpn_heatTrace_no_rat_ade
#print axioms Statements.RankOneSymmetric.hpn_heatTrace_no_rat_ade
#print axioms Statements.RankOneSymmetric.op2_heatTrace_no_rat_ade
#print axioms Statements.UnconditionalPrimes.phiLambdaAtTwo_eq_LSeries_vonMangoldt
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_atTwo_ogf_stronglyDTrans
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_atTwo_formalSeries_stronglyDTrans
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_atTwo_laplace_no_conv_ade
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_atTwo_laplace_no_rat_ade
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_ogf_stronglyDTrans
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_formalSeries_stronglyDTrans
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_laplace_no_conv_ade
#print axioms Statements.UnconditionalPrimes.unconditional_G_Lambda_laplace_no_rat_ade

-- Wave 7 (v3.4.0): Unconditional Completed-ξ Strong ℂ({t}) D-Transcendence, Finite-Contour Engine, & Spectral Positivity / Hankel Positive Definiteness
#print axioms Statements.CompletedXi.completedXi_one_sub
#print axioms Statements.CompletedXi.completedXi_ne_zero_of_abs_im_le_half
#print axioms Statements.CompletedXi.completedXi_zero_mem_strip
#print axioms Statements.CompletedXi.completedXi_zeros_infinite
#print axioms Statements.CompletedXi.completedXi_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.completedXi_formalSeries_stronglyDTrans
#print axioms Statements.CompletedXi.phiXi_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.phiXi_formalSeries_stronglyDTrans
#print axioms Statements.CompletedXi.completedXi_joint_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.B_xi_hasAsympExp
#print axioms Statements.CompletedXi.completedXi_laplace_no_conv_ade
#print axioms Statements.CompletedXi.finite_contour_pole_count_bound
#print axioms Statements.CompletedXi.finite_contour_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.finite_contour_formalSeries_stronglyDTrans
#print axioms Statements.CompletedXi.finite_contour_joint_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.entireLogDeriv_ogf_stronglyDTrans
#print axioms Statements.CompletedXi.entireLogDeriv_formalSeries_stronglyDTrans
#print axioms Statements.SpectralPositivity.spectral_lower_from_estimates
#print axioms Statements.SpectralPositivity.xi_lower_from_estimates
#print axioms Statements.SpectralPositivity.dirichletBeta_lower_from_estimates
#print axioms Statements.SpectralPositivity.ramanujanDelta_lower_from_estimates
#print axioms Statements.SpectralPositivity.square_integral_pos
#print axioms Statements.SpectralPositivity.hankel_form
#print axioms Statements.SpectralPositivity.hankel_posDef_of_positive_weight
#print axioms Statements.SpectralPositivity.hankel_det_pos_of_positive_weight
#print axioms Statements.SpectralPositivity.xiDensity_pos
#print axioms Statements.SpectralPositivity.xiHankel_posDef
#print axioms Statements.SpectralPositivity.xiHankel_det_pos
#print axioms Statements.SpectralPositivity.dirichletBetaDensity_pos
#print axioms Statements.SpectralPositivity.dirichletBetaHankel_posDef
#print axioms Statements.SpectralPositivity.dirichletBetaHankel_det_pos
#print axioms Statements.SpectralPositivity.ramanujanDeltaDensity_pos
#print axioms Statements.SpectralPositivity.ramanujanDeltaHankel_posDef
#print axioms Statements.SpectralPositivity.ramanujanDeltaHankel_det_pos
#print axioms Statements.SpectralPositivity.hyperbolicSpectralDensity_pos
#print axioms Statements.SpectralPositivity.subtractedHyperbolicMoment_eq_tsum
#print axioms Statements.SpectralPositivity.subtractedHyperbolicHankel_posDef
#print axioms Statements.SpectralPositivity.subtractedHyperbolicHankel_det_pos

-- Wave 8 (v3.5.0): All-d Marked-Wave Stokes Engine, Besicovitch Core, Universal Thimble, & Unconditional Cubic Waring/Dilations
#print axioms CubicTheta.AllD.besicovitch_rfree_linearIndependent
#print axioms CubicTheta.AllD.universalPoly_no_nonzero_critValue_in_LHP
#print axioms CubicTheta.AllD.extremeRay_face_iff
#print axioms CubicTheta.AllD.independent_of_marked_jacobian_domain
#print axioms CubicTheta.AllD.allD_formal_transfer
#print axioms CubicTheta.AllD.waring_algebraicIndependent_of_base
#print axioms CubicTheta.AllD.iterQDeriv_eq_sum
#print axioms CubicTheta.AllD.theta_d_marked_wave_non_ade
#print axioms CubicTheta.AllD.theta_d_waring_power_non_ade
#print axioms CubicTheta.AllD.theta_d_dilations_diff_indep
#print axioms CubicTheta.AllD.theta_d_dfree_dilations_diff_indep
#print axioms CubicTheta.AllD.theta_3_non_ade_via_allD
#print axioms CubicTheta.AllD.theta_3_waring_power_non_ade
#print axioms CubicTheta.AllD.theta_3_dilations_diff_indep

-- Wave 9 (v3.5.0): 100% Unconditional Partitions into Squares P₂(q) & All-d Power Partitions
#print axioms CubicTheta.AllD.squares_partition_analytic_identity
#print axioms CubicTheta.AllD.powerPartMult_prime
#print axioms CubicTheta.AllD.logDerivPowerPart_non_ade
#print axioms CubicTheta.AllD.powerPart_non_ade
#print axioms CubicTheta.AllD.powerPart_zpow_non_ade
#print axioms CubicTheta.AllD.logDerivPowerPart_dilations_diff_indep
#print axioms CubicTheta.AllD.powerPart_dilations_diff_indep
#print axioms CubicTheta.AllD.logDerivPowerPart_2_non_ade
#print axioms CubicTheta.AllD.powerPart_2_non_ade
#print axioms CubicTheta.AllD.powerPart_2_zpow_non_ade
#print axioms CubicTheta.AllD.logDerivPowerPart_2_dilations_diff_indep
#print axioms CubicTheta.AllD.powerPart_2_dilations_diff_indep

-- Wave 10 (v3.5.0): Unconditional Algebraic Jump-Point Derivation Engine & Multivariate Diagonal Witnesses
#print axioms CubicTheta.AllD.jumpPoints_exist
#print axioms CubicTheta.AllD.jumpPoint_no_multi_pos_sum
#print axioms CubicTheta.AllD.monoidDeriv_aeval
#print axioms CubicTheta.AllD.hahnDeriv_aeval
#print axioms CubicTheta.AllD.jumpPoint_minimal_relation_vandermonde
#print axioms CubicTheta.AllD.jumpPoint_transseries_algebraicIndependent
#print axioms CubicTheta.AllD.jumpPoint_transseries_no_poly_ade
#print axioms CubicTheta.AllD.wulffRay_infinite_qrank
#print axioms CubicTheta.AllD.multivariate_evenForm_algebraic_dtrans
#print axioms CubicTheta.AllD.multivariate_jumpPoint_non_ade
#print axioms CubicTheta.AllD.multivariate_jumpPoint_non_ade_over_poly
#print axioms CubicTheta.AllD.diagQuartic2D_offray_collision
#print axioms CubicTheta.AllD.diagForm_algebraic_dtrans
#print axioms CubicTheta.AllD.diagForm_transseries_non_ade
#print axioms CubicTheta.AllD.diagQuartic2D_non_ade

-- Wave 11 (v3.6.0): Unconditional 3D Bose–Einstein Condensate, 3D Fermi–Dirac Gas, Joint 1D+3D Ideal Quantum Gases, Square Divisors L_{2,0}(q), & Quotient-Rank Forest
#print axioms CubicTheta.AllD.monomial_family_diff_indep_of_logDeriv
#print axioms CubicTheta.AllD.squarePart_monomial_family_diff_indep
#print axioms CubicTheta.AllD.kRegularSquares_eq_eulerProd
#print axioms CubicTheta.AllD.distinctSquaresPart_eq_eulerProd
#print axioms CubicTheta.AllD.overpartSquares_eq_mul
#print axioms CubicTheta.AllD.distinctSquares_overpartSquares_joint_diff_indep
#print axioms CubicTheta.AllD.distinctSquares_non_ade
#print axioms CubicTheta.AllD.overpartSquares_non_ade
#print axioms CubicTheta.AllD.fermi1D_non_ade
#print axioms CubicTheta.AllD.distinctSource_quotient_pow_diff_indep
#print axioms CubicTheta.AllD.squarePart_forest_quotients_diff_indep
#print axioms CubicTheta.AllD.kRegularSquares_dilations_diff_indep
#print axioms CubicTheta.AllD.distinctSquares_dilations_diff_indep
#print axioms CubicTheta.AllD.fermi1D_dilations_diff_indep
#print axioms CubicTheta.AllD.sqRayProfile_dilations_diff_indep
#print axioms CubicTheta.AllD.sqRayProfile_non_ade
#print axioms CubicTheta.AllD.squareDivisor_analytic_identity
#print axioms CubicTheta.AllD.squareDivisor_non_ade
#print axioms CubicTheta.AllD.squareDivisor_dilations_diff_indep
#print axioms CubicTheta.AllD.bec3D_analytic_identity
#print axioms CubicTheta.AllD.X_mul_deriv_bec3DDilated
#print axioms CubicTheta.AllD.X_mul_deriv_bec3DSeries
#print axioms CubicTheta.AllD.X_mul_deriv_bec3DZPow
#print axioms CubicTheta.AllD.fermi3DDilated_eq_eulerProd
#print axioms CubicTheta.AllD.fermi3DSeries_eq_eulerProd
#print axioms CubicTheta.AllD.logDerivBec3D_non_ade
#print axioms CubicTheta.AllD.logDerivBec3D_dilations_diff_indep
#print axioms CubicTheta.AllD.bec3D_non_ade
#print axioms CubicTheta.AllD.bec3D_zpow_non_ade
#print axioms CubicTheta.AllD.bec3D_dilations_diff_indep
#print axioms CubicTheta.AllD.bec3D_bose_fermi_quotient_rank
#print axioms CubicTheta.AllD.bec3D_fermi3D_joint_diff_indep
#print axioms CubicTheta.AllD.bec3D_forest_quotients_diff_indep
#print axioms CubicTheta.AllD.fermi3D_dilations_diff_indep
#print axioms CubicTheta.AllD.fermi3D_non_ade
#print axioms CubicTheta.AllD.logDeriv_bec1D_bec3D_dilations_diff_indep
#print axioms CubicTheta.AllD.bec1D_bec3D_dilations_diff_indep
#print axioms CubicTheta.AllD.quantumGases_1D_3D_bose_fermi_joint_diff_indep
#print axioms CubicTheta.AllD.bec1D_bec3D_joint_diff_indep
#print axioms CubicTheta.AllD.powerPart2_bec3D_joint_diff_indep

-- Wave 12 (v3.7.0) — BlackbodyPhotons3D.lean (40 public theorems / 57 public decls)
#print axioms CubicTheta.AllD.r2Count_le
#print axioms CubicTheta.AllD.r4Count_le
#print axioms CubicTheta.AllD.r2Count_pos_of_prime_mod_four_eq_one
#print axioms CubicTheta.AllD.r2Count_eq_zero_of_odd_val_prime_mod_four_eq_three
#print axioms CubicTheta.AllD.r2Count_sq_mul_eq_zero_of_prime_mod_four_eq_three
#print axioms CubicTheta.AllD.r2Count_sq_mul_eq_zero_of_mod_four_eq_three
#print axioms CubicTheta.AllD.r3Count_sq_mul_eq_zero_of_mod_eight_eq_seven
#print axioms CubicTheta.AllD.r3Count_sq_mul_eq_zero_of_prime_mod_eight_eq_seven
#print axioms CubicTheta.AllD.r4Count_pos
#print axioms CubicTheta.AllD.exists_new_sqf_mod_eight_eq_three_r3_pos
#print axioms CubicTheta.AllD.infinite_sqf_mod_eight_eq_three_r3_pos
#print axioms CubicTheta.AllD.infinite_prime_core_mod_four_eq_one
#print axioms CubicTheta.AllD.infinite_prime_core_mod_eight_eq_seven
#print axioms CubicTheta.AllD.sqrtSpectrum_pos
#print axioms CubicTheta.AllD.sqrtSpectrum_locallyFinite
#print axioms CubicTheta.AllD.sqrtSpectrum_isWF
#print axioms CubicTheta.AllD.sqrtSpectrum_isPWO
#print axioms CubicTheta.AllD.exists_core_functional
#print axioms CubicTheta.AllD.photonEnergyCoeff_nonneg
#print axioms CubicTheta.AllD.photonLogZCoeff_nonneg
#print axioms CubicTheta.AllD.photonEnergyCoeff_eq_sqrt_mul_logZCoeff
#print axioms CubicTheta.AllD.photonEnergyCoeff_pos_of_pos
#print axioms CubicTheta.AllD.photonLogZCoeff_pos_of_pos
#print axioms CubicTheta.AllD.photonEnergyCoeff_sq_mul_eq_zero_of_all_zero
#print axioms CubicTheta.AllD.photonLogZCoeff_sq_mul_eq_zero_of_all_zero
#print axioms CubicTheta.AllD.photonEnergyHahn_coeff_sqrt
#print axioms CubicTheta.AllD.photonEnergyTrans_coeff_sqrt
#print axioms CubicTheta.AllD.photonLogZTrans_coeff_sqrt
#print axioms CubicTheta.AllD.photonEnergyTrans_support_subset
#print axioms CubicTheta.AllD.photonLogZTrans_support_subset
#print axioms CubicTheta.AllD.transDerivX_photonLogZTrans
#print axioms CubicTheta.AllD.photonEnergyAnalytic_eq_tsum_sqrt
#print axioms CubicTheta.AllD.triangular_core_transseries_diff_indep
#print axioms CubicTheta.AllD.photon2D_non_ade
#print axioms CubicTheta.AllD.photon3D_non_ade
#print axioms CubicTheta.AllD.photon4D_non_ade
#print axioms CubicTheta.AllD.photon2D_photon3D_photon4D_joint_diff_indep
#print axioms CubicTheta.AllD.photon2D_photon3D_photon4D_all_derivs_diff_indep
#print axioms CubicTheta.AllD.photon2D_photon3D_photon4D_no_joint_poly_ade
#print axioms CubicTheta.AllD.photonLogZ_2D_3D_4D_joint_diff_indep

-- Wave 12 (v3.7.0) — MockModularAlgebraCore.lean (44 public theorems / 54 public decls)
#print axioms CubicTheta.AllD.mockJetQ_monic_and_natDegree
#print axioms CubicTheta.AllD.mockJetQ_monic
#print axioms CubicTheta.AllD.mockJetQ_natDegree
#print axioms CubicTheta.AllD.mockJetQAt_zero
#print axioms CubicTheta.AllD.mockJetQAt_succ
#print axioms CubicTheta.AllD.mockJetP_zero
#print axioms CubicTheta.AllD.mockJetP_recurrence
#print axioms CubicTheta.AllD.mockModular_jetQ_det_eq
#print axioms CubicTheta.AllD.mockModular_jet_det_eq
#print axioms CubicTheta.AllD.iteratedDeriv_mockModular_mode
#print axioms CubicTheta.AllD.dirDeriv_C
#print axioms CubicTheta.AllD.dirDeriv_X
#print axioms CubicTheta.AllD.dirDeriv_add
#print axioms CubicTheta.AllD.dirDeriv_mul
#print axioms CubicTheta.AllD.shiftPoly_C
#print axioms CubicTheta.AllD.shiftPoly_X
#print axioms CubicTheta.AllD.shiftPoly_add
#print axioms CubicTheta.AllD.shiftPoly_mul
#print axioms CubicTheta.AllD.derivative_shiftPoly
#print axioms CubicTheta.AllD.eval_zero_shiftPoly
#print axioms CubicTheta.AllD.aeval_shiftPoly
#print axioms CubicTheta.AllD.mvPoly_translation_invariant_of_dirDeriv_eq_zero
#print axioms CubicTheta.AllD.mockModular_translation_invariance_kills_linear_collisions
#print axioms CubicTheta.AllD.mockModular_taylor_expansion
#print axioms CubicTheta.AllD.dirDeriv_totalDegree_lt
#print axioms CubicTheta.AllD.mockModular_minimal_annihilator_contradiction
#print axioms CubicTheta.AllD.mockModular_jump_induction_contradiction
#print axioms CubicTheta.AllD.isOpen_upperHalfPlane
#print axioms CubicTheta.AllD.upperHalfPlane_ne_zero
#print axioms CubicTheta.AllD.gammaAction_mem_upperHalfPlane
#print axioms CubicTheta.AllD.gammaDen_mem_slitPlane
#print axioms CubicTheta.AllD.add_int_mem_upperHalfPlane
#print axioms CubicTheta.AllD.descFac_zero
#print axioms CubicTheta.AllD.descFac_succ
#print axioms CubicTheta.AllD.descFac_shift
#print axioms CubicTheta.AllD.Gamma_eq_descFac_mul_Gamma
#print axioms CubicTheta.AllD.descFac_eq_Gamma_div
#print axioms CubicTheta.AllD.descFac_halfInt_ne_zero
#print axioms CubicTheta.AllD.modular_iteratedDeriv_gamma
#print axioms CubicTheta.AllD.positiveWeight_modular_diff_indep_abstract
#print axioms CubicTheta.AllD.positiveWeight_modular_forms_diff_indep
#print axioms CubicTheta.AllD.positiveWeight_modular_thetaQ_diff_indep
#print axioms CubicTheta.AllD.watsonClosedSector_subset_slitPlane
#print axioms CubicTheta.AllD.maxModulus_watson_uniqueness

-- Wave 13A (v3.7.0) — DysonShadowRank.lean (34 public theorems / 47 public decls)
#print axioms CubicTheta.AllD.two_sin_mul_sin_six_add_one
#print axioms CubicTheta.AllD.dyson_shadow_trig_identity
#print axioms CubicTheta.AllD.foldMod_eq_of_emod_eq
#print axioms CubicTheta.AllD.foldMod_add_mul
#print axioms CubicTheta.AllD.foldMod_neg
#print axioms CubicTheta.AllD.foldMod_of_fin
#print axioms CubicTheta.AllD.foldMod_eq_or_neg_mod
#print axioms CubicTheta.AllD.cos_two_pi_mul_foldMod
#print axioms CubicTheta.AllD.dyson_vertices_sub_components
#print axioms CubicTheta.AllD.dysonNumComponents_of_dvd
#print axioms CubicTheta.AllD.dysonNumComponents_of_not_dvd
#print axioms CubicTheta.AllD.dysonCompId_compRoot
#print axioms CubicTheta.AllD.dysonCompId_three_mul_eq
#print axioms CubicTheta.AllD.exists_shadow_edge_consecutive
#print axioms CubicTheta.AllD.exists_shadow_edge_to_root_of_dvd
#print axioms CubicTheta.AllD.dysonFoldedGraph_reachable_root
#print axioms CubicTheta.AllD.dysonFoldedGraph_reachable_iff
#print axioms CubicTheta.AllD.dysonFoldedGraph_connectedComponent_card
#print axioms CubicTheta.AllD.dysonFoldedGraph_exists_adj
#print axioms CubicTheta.AllD.componentSumMap_surjective
#print axioms CubicTheta.AllD.shadowRowSpan_eq_ker_componentSumMap
#print axioms CubicTheta.AllD.dysonShadowRank_eq
#print axioms CubicTheta.AllD.dotProduct_shadowEdge
#print axioms CubicTheta.AllD.mem_shadowKernel_iff_dotProduct_zero
#print axioms CubicTheta.AllD.mem_shadowKernel_iff_const_on_components
#print axioms CubicTheta.AllD.mem_shadowKernel_iff_const_on_reachable
#print axioms CubicTheta.AllD.finrank_shadowKernel_eq
#print axioms CubicTheta.AllD.single_vertex_not_mem_shadowKernel
#print axioms CubicTheta.AllD.dysonShadowRank_six
#print axioms CubicTheta.AllD.dysonSix_triple_zero_shadow
#print axioms CubicTheta.AllD.dct_orthogonality
#print axioms CubicTheta.AllD.dctMap_injective
#print axioms CubicTheta.AllD.dctMap_shadowEdge
#print axioms CubicTheta.AllD.dysonTrigShadowRank_eq

-- Wave 13A (v3.7.0) — PrimeDilationIsolation.lean (17 public theorems / 17 public decls)
#print axioms CubicTheta.AllD.no_sq_mul_eq_prime_sq_mul_of_gt
#print axioms CubicTheta.AllD.no_int_sq_mul_eq_prime_sq_mul_of_gt
#print axioms CubicTheta.AllD.no_nat_eq_prime_mul_sqrt_ratio
#print axioms CubicTheta.AllD.prime_dilation_freq_ne
#print axioms CubicTheta.AllD.prime_mod_six_of_gt_three
#print axioms CubicTheta.AllD.mockFalse_sine_factor_eq
#print axioms CubicTheta.AllD.mockFalse_sine_factor_ne_zero
#print axioms CubicTheta.AllD.exists_strictMono_primes_gt
#print axioms CubicTheta.AllD.exists_isolated_primes_for_max_dilation
#print axioms CubicTheta.AllD.prime_freq_injective
#print axioms CubicTheta.AllD.prime_dilation_jet_det_ne_zero
#print axioms CubicTheta.AllD.prime_dilation_jet_eval_det_ne_zero
#print axioms CubicTheta.AllD.prime_dilation_weighted_jet_det_ne_zero
#print axioms CubicTheta.AllD.mvPoly_vec_eq_zero_of_det_ne_zero
#print axioms CubicTheta.AllD.prime_dilation_block_elimination
#print axioms CubicTheta.AllD.dual_ray_prime_dilation_elimination
#print axioms CubicTheta.AllD.dual_ray_prime_dilation_constant
