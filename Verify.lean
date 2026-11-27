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

-- Wave 13B (v3.8.0) — DepthTwoCommutator.lean (41 public theorems / 54 public decls)
#print axioms CubicTheta.AllD.triSub_zero
#print axioms CubicTheta.AllD.triSub_comp
#print axioms CubicTheta.AllD.triSub_comp_inv
#print axioms CubicTheta.AllD.triSub_inv_comp
#print axioms CubicTheta.AllD.triSub_inv
#print axioms CubicTheta.AllD.commutatorPairing_eq
#print axioms CubicTheta.AllD.commutatorPairing_self_zero
#print axioms CubicTheta.AllD.commutatorPairing_antisymm
#print axioms CubicTheta.AllD.triCommutator_eq_triSub
#print axioms CubicTheta.AllD.triSub_commutator_lower
#print axioms CubicTheta.AllD.triSub_commutator_depth2
#print axioms CubicTheta.AllD.triSub_commutator_self_zero
#print axioms CubicTheta.AllD.triSub_commutator_symmetric_product_zero
#print axioms CubicTheta.AllD.triCommutator_iterate
#print axioms CubicTheta.AllD.triCommutatorEquiv_apply
#print axioms CubicTheta.AllD.triCommutatorEquiv_zpow
#print axioms CubicTheta.AllD.multiTriSub_commutator_lower
#print axioms CubicTheta.AllD.multiTriSub_commutator_depth2
#print axioms CubicTheta.AllD.triSubAlgHom_comp
#print axioms CubicTheta.AllD.triCommutatorAlgHom_eq
#print axioms CubicTheta.AllD.triCommutatorAlgHom_fixes_lower_poly
#print axioms CubicTheta.AllD.shiftedVandermonde_apply
#print axioms CubicTheta.AllD.shiftedVandermonde_eq_vandermonde
#print axioms CubicTheta.AllD.shiftedVandermonde_det
#print axioms CubicTheta.AllD.shiftedVandermonde_det_ne_zero
#print axioms CubicTheta.AllD.scaledShiftedVandermonde_det_ne_zero
#print axioms CubicTheta.AllD.twoSector_blockVandermonde_det_ne_zero
#print axioms CubicTheta.AllD.linearShiftPoly_eval
#print axioms CubicTheta.AllD.linearShiftPoly_eval_zero
#print axioms CubicTheta.AllD.derivative_linearShiftPoly_eval_zero
#print axioms CubicTheta.AllD.linearShiftPoly_coeff_one
#print axioms CubicTheta.AllD.poly_eq_zero_of_forall_nat_eval_eq_zero
#print axioms CubicTheta.AllD.linear_shift_deriv_eq_zero_of_forall_nat_shift
#print axioms CubicTheta.AllD.linear_shift_deriv_eq_zero_of_forall_int_shift
#print axioms CubicTheta.AllD.all_pderiv_aeval_eq_zero_of_det_ne_zero
#print axioms CubicTheta.AllD.exists_pderiv_ne_zero_and_totalDegree_lt
#print axioms CubicTheta.AllD.minimal_degree_elimination_of_nonsingular_matrix
#print axioms CubicTheta.AllD.minimal_degree_elimination_of_int_shifts
#print axioms CubicTheta.AllD.minimal_degree_elimination_vandermonde
#print axioms CubicTheta.AllD.minimal_degree_elimination_twoSector_vandermonde
#print axioms CubicTheta.AllD.minimal_degree_elimination_field_vandermonde

-- Wave 13B (v3.8.0) — VafaWittenWitnesses.lean (37 public theorems / 46 public decls)
#print axioms CubicTheta.AllD.vwOuterForm_flux1_ch0
#print axioms CubicTheta.AllD.vwOuterForm_flux1_ch1
#print axioms CubicTheta.AllD.vwOuterForm_flux0_ch0
#print axioms CubicTheta.AllD.vwOuterForm_flux0_ch1
#print axioms CubicTheta.AllD.vwInnerForm_ch0
#print axioms CubicTheta.AllD.vwInnerForm_ch1
#print axioms CubicTheta.AllD.vwThetaSet_finite_and_card_le_two
#print axioms CubicTheta.AllD.vwPairing_eq_commutatorPairing
#print axioms CubicTheta.AllD.vwPairing_antisymm
#print axioms CubicTheta.AllD.vwPairing_self_zero
#print axioms CubicTheta.AllD.vwThetaCount_outer_neg1_eq_flux1
#print axioms CubicTheta.AllD.vwPairing_flux_neg1_eq_flux1
#print axioms CubicTheta.AllD.three_mul_sq_ne_sq_nat
#print axioms CubicTheta.AllD.three_mul_sq_ne_sq_int
#print axioms CubicTheta.AllD.vwThetaCount_inner0_sq
#print axioms CubicTheta.AllD.vwThetaCount_inner0_div_three
#print axioms CubicTheta.AllD.vwThetaCount_inner0_three
#print axioms CubicTheta.AllD.vwThetaCount_inner1_int
#print axioms CubicTheta.AllD.vwThetaCount_inner1_div_three
#print axioms CubicTheta.AllD.vwThetaCount_outer10_third
#print axioms CubicTheta.AllD.vwThetaCount_outer10_sixteen_thirds
#print axioms CubicTheta.AllD.vwThetaCount_outer10_int
#print axioms CubicTheta.AllD.vwThetaCount_outer00_three
#print axioms CubicTheta.AllD.vwThetaCount_outer00_div_three
#print axioms CubicTheta.AllD.vwThetaCount_outer00_sq
#print axioms CubicTheta.AllD.vwPairing_flux1_witness
#print axioms CubicTheta.AllD.vwPairing_flux0_vanishes_on_flux1_witness
#print axioms CubicTheta.AllD.vwPairing_flux0_witness
#print axioms CubicTheta.AllD.vwPairing_flux1_vanishes_on_flux0_witness
#print axioms CubicTheta.AllD.vwCollision_equal_total
#print axioms CubicTheta.AllD.vwCollision_distinct_addresses
#print axioms CubicTheta.AllD.vwCollision_both_flux1_eq_two
#print axioms CubicTheta.AllD.vwCollision_both_flux0_eq_zero
#print axioms CubicTheta.AllD.vwSquareSeq_injective
#print axioms CubicTheta.AllD.vwWitness_vandermonde_ne_zero
#print axioms CubicTheta.AllD.vwWitness_blockMatrix_det_ne_zero
#print axioms CubicTheta.AllD.vwWitness_twoSector_minimal_degree_contradiction

-- Wave 14 (v3.8.0) — SquarePartitionsModN.lean (47 public theorems / 63 public decls)
#print axioms CubicTheta.AllD.squarefree_decomp_pos
#print axioms CubicTheta.AllD.modN_squarefree_rep
#print axioms CubicTheta.AllD.modN_squarefree_rep_zmod
#print axioms CubicTheta.AllD.exists_inf_primes_modN_one
#print axioms CubicTheta.AllD.sqrt_core_pos
#print axioms CubicTheta.AllD.sqrt_core_injective
#print axioms CubicTheta.AllD.sqrt_core_linearIndependent
#print axioms CubicTheta.AllD.twoRay_exponent_injective
#print axioms CubicTheta.AllD.conj_rayDirections_linearIndependent
#print axioms CubicTheta.AllD.eulerDeriv_coeff
#print axioms CubicTheta.AllD.deriv_aeval_eq_sum_pderiv
#print axioms CubicTheta.AllD.monRate_zero
#print axioms CubicTheta.AllD.monRate_single
#print axioms CubicTheta.AllD.monRate_add
#print axioms CubicTheta.AllD.rayDerivX_coeff
#print axioms CubicTheta.AllD.rayDerivX_C
#print axioms CubicTheta.AllD.rayDerivX_iterate_coeff_eq_zero
#print axioms CubicTheta.AllD.rayDerivX_iterate_coeff_const
#print axioms CubicTheta.AllD.isSquareModNWave_squareModNWave
#print axioms CubicTheta.AllD.squareModN_strong_induction
#print axioms CubicTheta.AllD.squareModN_wave_diff_indep_fin
#print axioms CubicTheta.AllD.lift_diff_indep_all_orders
#print axioms CubicTheta.AllD.squareModN_wave_diff_indep
#print axioms CubicTheta.AllD.deriv_iterate_mul
#print axioms CubicTheta.AllD.diffAlg_kolchin_logDeriv_indep
#print axioms CubicTheta.AllD.squareModN_twistedProd_diff_indep
#print axioms CubicTheta.AllD.rootOfUnity_ne_zero
#print axioms CubicTheta.AllD.rootOfUnity_two
#print axioms CubicTheta.AllD.rootsOfUnity_filter
#print axioms CubicTheta.AllD.dftMatrix_mul_dftInvMatrix
#print axioms CubicTheta.AllD.dftInvMatrix_mul_dftMatrix
#print axioms CubicTheta.AllD.dftMatrix_det_ne_zero
#print axioms CubicTheta.AllD.deriv_iter_linearComb
#print axioms CubicTheta.AllD.linearComb_diff_indep_of_rightInv
#print axioms CubicTheta.AllD.linearComb_diff_indep_of_linearIndependent
#print axioms CubicTheta.AllD.squareModN_parts_diff_indep
#print axioms CubicTheta.AllD.squareModN_parts_diff_indep_of_wave
#print axioms CubicTheta.AllD.squareEvenOdd_formulas
#print axioms CubicTheta.AllD.squareEvenOdd_joint_diff_indep
#print axioms CubicTheta.AllD.periodic_mod_eq
#print axioms CubicTheta.AllD.commonPeriod_pos
#print axioms CubicTheta.AllD.squarePeriodicWeights_linearIndep_diff_indep
#print axioms CubicTheta.AllD.squarePeriodicWeights_diff_rank_eq
#print axioms CubicTheta.AllD.multInd_periodic
#print axioms CubicTheta.AllD.multInd_evalMatrix_det_eq_one
#print axioms CubicTheta.AllD.multInd_linearIndependent
#print axioms CubicTheta.AllD.squareMultiplesOfD_diff_indep

-- Wave 15 (v3.8.0) — MockModularRotatedRays.lean (68 public theorems / 86 public decls)
#print axioms CubicTheta.AllD.isOpen_slitDisk
#print axioms CubicTheta.AllD.isPreconnected_slitDisk
#print axioms CubicTheta.AllD.sector34_subset_slitDisk
#print axioms CubicTheta.AllD.hasRealAsymp_of_hasGevrey1Asymp
#print axioms CubicTheta.AllD.hasGevrey1Asymp_mono
#print axioms CubicTheta.AllD.hasGevrey1Asymp_congr
#print axioms CubicTheta.AllD.hasGevrey1Asymp_const
#print axioms CubicTheta.AllD.hasGevrey1Asymp_add
#print axioms CubicTheta.AllD.hasGevrey1Asymp_const_mul
#print axioms CubicTheta.AllD.hasGevrey1Asymp_coeff_le
#print axioms CubicTheta.AllD.hasGevrey1Asymp_mul
#print axioms CubicTheta.AllD.gevrey1_zero_imp_exp_decay
#print axioms CubicTheta.AllD.watson_of_gevrey1_zero
#print axioms CubicTheta.AllD.isConvergentOn_summable
#print axioms CubicTheta.AllD.psEval_differentiableOn
#print axioms CubicTheta.AllD.hasGevrey1Asymp_psEval
#print axioms CubicTheta.AllD.genBinom_zero
#print axioms CubicTheta.AllD.genBinom_succ
#print axioms CubicTheta.AllD.risingFac_zero
#print axioms CubicTheta.AllD.risingFac_succ
#print axioms CubicTheta.AllD.cpow_taylor_integral_remainder
#print axioms CubicTheta.AllD.sector34_one_add_norm_ge
#print axioms CubicTheta.AllD.norm_cpow_le_rpow_mul_exp
#print axioms CubicTheta.AllD.integral_pow_mul_exp_Ioi_le
#print axioms CubicTheta.AllD.one_add_mul_ofReal_mem_slitPlane
#print axioms CubicTheta.AllD.PhiReal_iteratedDeriv
#print axioms CubicTheta.AllD.norm_mul_genBinom_le
#print axioms CubicTheta.AllD.PhiReal_iteratedDeriv_hasGevrey1Asymp
#print axioms CubicTheta.AllD.exp_neg_I_pi_div_four_re
#print axioms CubicTheta.AllD.exp_neg_I_pi_div_four_im
#print axioms CubicTheta.AllD.exp_I_pi_div_four_re
#print axioms CubicTheta.AllD.exp_I_pi_div_four_im
#print axioms CubicTheta.AllD.gammaMinus_re
#print axioms CubicTheta.AllD.gammaMinus_im
#print axioms CubicTheta.AllD.gammaPlus_re
#print axioms CubicTheta.AllD.gammaPlus_im
#print axioms CubicTheta.AllD.star_gammaMinus
#print axioms CubicTheta.AllD.star_gammaPlus
#print axioms CubicTheta.AllD.isOpen_UPlus
#print axioms CubicTheta.AllD.isOpen_UMinus
#print axioms CubicTheta.AllD.mem_UMinus_iff_star
#print axioms CubicTheta.AllD.ofReal_mem_UPlus
#print axioms CubicTheta.AllD.neg_ofReal_mem_UPlus
#print axioms CubicTheta.AllD.ofReal_mem_UMinus
#print axioms CubicTheta.AllD.neg_ofReal_mem_UMinus
#print axioms CubicTheta.AllD.UPlus_eq_polar_image
#print axioms CubicTheta.AllD.isPreconnected_UPlus
#print axioms CubicTheta.AllD.isPreconnected_UMinus
#print axioms CubicTheta.AllD.one_add_mul_mem_slitPlane_UPlus
#print axioms CubicTheta.AllD.one_add_mul_mem_slitPlane_UMinus
#print axioms CubicTheta.AllD.one_sub_txy_norm_ge_gammaMinus
#print axioms CubicTheta.AllD.one_sub_txy_norm_ge_gammaPlus
#print axioms CubicTheta.AllD.ray_integral_const_on_Icc
#print axioms CubicTheta.AllD.integral_Ioi_zero_one_add
#print axioms CubicTheta.AllD.ray_integral_eq_real
#print axioms CubicTheta.AllD.PhiPlus_iteratedDeriv
#print axioms CubicTheta.AllD.PhiMinus_iteratedDeriv
#print axioms CubicTheta.AllD.PhiPlus_PhiMinus_eq_PhiReal_of_pos
#print axioms CubicTheta.AllD.moment_ray_eq_real
#print axioms CubicTheta.AllD.iteratedDeriv_comp_neg_ofReal
#print axioms CubicTheta.AllD.PhiPlus_PhiMinus_neg_iteratedDeriv_hasRealAsymp
#print axioms CubicTheta.AllD.lateral_simultaneous_annihilation
#print axioms CubicTheta.AllD.one_div_Gamma_ne_zero_nonBol
#print axioms CubicTheta.AllD.differentiable_inv_Gamma
#print axioms CubicTheta.AllD.hankel_single_mode_jump
#print axioms CubicTheta.AllD.norm_eval_mockJetQAt_le
#print axioms CubicTheta.AllD.hankel_series_jump
#print axioms CubicTheta.AllD.hankel_series_jump_iteratedDeriv

-- Wave 15 (v3.8.0) — MockModularCuspDescent.lean (49 public theorems / 63 public decls)
#print axioms CubicTheta.AllD.M_mul_tauOfU_add_one
#print axioms CubicTheta.AllD.gammaMobius_tauOfU
#print axioms CubicTheta.AllD.tauOfU_mem_upperHalfPlane
#print axioms CubicTheta.AllD.gammaTauOfU_mem_upperHalfPlane
#print axioms CubicTheta.AllD.iteratedDeriv_comp_tauOfU
#print axioms CubicTheta.AllD.theta_pullback_iteratedDeriv
#print axioms CubicTheta.AllD.cpow_I_mul_ofReal_pos
#print axioms CubicTheta.AllD.cpow_neg_I_mul_ofReal_pos
#print axioms CubicTheta.AllD.ofReal_mul_cpow_of_pos
#print axioms CubicTheta.AllD.ofReal_div_cpow_of_pos
#print axioms CubicTheta.AllD.intervalIntegral_comp_inv_mul
#print axioms CubicTheta.AllD.integral_add_cpow_neg_nonOne
#print axioms CubicTheta.AllD.integral_add_cpow_neg_one
#print axioms CubicTheta.AllD.eichler_y1_zero_mode_nonOne
#print axioms CubicTheta.AllD.eichler_y1_zero_mode_one
#print axioms CubicTheta.AllD.eichler_y1_split_cusp
#print axioms CubicTheta.AllD.eichler_y1_split_nonOne
#print axioms CubicTheta.AllD.eichler_y1_split_one
#print axioms CubicTheta.AllD.FHol_differentiableOn_ball
#print axioms CubicTheta.AllD.cauchy_product_poly_bound
#print axioms CubicTheta.AllD.summable_poly_mul_geom
#print axioms CubicTheta.AllD.pow_log_mul_exp_neg_div_le
#print axioms CubicTheta.AllD.cauchy_q1_tail_bound
#print axioms CubicTheta.AllD.log_puiseux_scale_separation
#print axioms CubicTheta.AllD.half_parity_scale_separation
#print axioms CubicTheta.AllD.q1_induction_kill
#print axioms CubicTheta.AllD.mvPoly_shift_top_coeff
#print axioms CubicTheta.AllD.top_degree_survival
#print axioms CubicTheta.AllD.minimal_degree_descent
#print axioms CubicTheta.AllD.convPolyEmb_injective
#print axioms CubicTheta.AllD.psEval_convPolyEmb
#print axioms CubicTheta.AllD.psEval_poly_mul
#print axioms CubicTheta.AllD.mvPoly_conv_common_radius
#print axioms CubicTheta.AllD.coeff_evalAtConv
#print axioms CubicTheta.AllD.aeval_evalAtConv
#print axioms CubicTheta.AllD.evalAtConv_pderiv
#print axioms CubicTheta.AllD.evalAtConv_dirDeriv_poly
#print axioms CubicTheta.AllD.evalAtConv_hasRealAsymp
#print axioms CubicTheta.AllD.mvPoly_conv_lateral_simultaneous_annihilation
#print axioms CubicTheta.AllD.nonBolWeight_inv_Gamma_ne_zero
#print axioms CubicTheta.AllD.nonBolWeight_x_power_eq
#print axioms CubicTheta.AllD.mockJetQAt_coeff_zero
#print axioms CubicTheta.AllD.mockJetP_coeff_le
#print axioms CubicTheta.AllD.norm_taylor_rem_le
#print axioms CubicTheta.AllD.mockModular_translation_invariance_induction
#print axioms CubicTheta.AllD.rename_pderiv_equiv
#print axioms CubicTheta.AllD.mockModular_scalar_diff_trans_of_cuspSplit
#print axioms CubicTheta.AllD.mockModular_joint_shadow_rank_of_cuspSplit
#print axioms CubicTheta.AllD.mockModular_joint_diff_indep_of_q1Expansion

-- Wave 16 (v3.9.0) — UniqueSumAndJetIdealCore.lean (52 public theorems / 72 public decls)
#print axioms CubicTheta.AllD.nat_seq_subseq_dichotomy
#print axioms CubicTheta.AllD.isCompact_range_union_zero
#print axioms CubicTheta.AllD.nat_tuple_subseq_dichotomy
#print axioms CubicTheta.AllD.multiset_eq_map_univ
#print axioms CubicTheta.AllD.multiset_map_univ_sum
#print axioms CubicTheta.AllD.uniqueSum_extension_cofinite
#print axioms CubicTheta.AllD.hasUniqueRep_sum_ne_zero
#print axioms CubicTheta.AllD.uniqueSum_extension_cofinite_distinct
#print axioms CubicTheta.AllD.isUniqueSumPrefix_zero
#print axioms CubicTheta.AllD.multiset_map_snoc
#print axioms CubicTheta.AllD.isUniqueSumPrefix_extend_cofinite
#print axioms CubicTheta.AllD.uniqueSum_tree_exists
#print axioms CubicTheta.AllD.uniqueSum_no_lower_collision
#print axioms CubicTheta.AllD.uniqueSum_perm_collisions
#print axioms CubicTheta.AllD.uniqueSum_symm_sum_eq_factorial_mul
#print axioms CubicTheta.AllD.polarization_vanish_of_cofinite_span
#print axioms CubicTheta.AllD.polarization_diag_vanish_of_cofinite_span
#print axioms CubicTheta.AllD.monomialPolar_symm
#print axioms CubicTheta.AllD.homogPolarize_symm
#print axioms CubicTheta.AllD.monomialPolar_diag
#print axioms CubicTheta.AllD.homogPolarize_diag
#print axioms CubicTheta.AllD.homogPoly_eq_zero_of_cofinite_tree_vanish
#print axioms CubicTheta.AllD.vandermonde_tail_span
#print axioms CubicTheta.AllD.vandermonde_tail_span_complex
#print axioms CubicTheta.AllD.reciprocal_accumulation_polarization_obstruction
#print axioms CubicTheta.AllD.totalDegree_pderiv_lt
#print axioms CubicTheta.AllD.mvPoly_eq_C_of_forall_pderiv_eq_zero
#print axioms CubicTheta.AllD.taylor_dominance_of_eval_grad_zero
#print axioms CubicTheta.AllD.pivot_algebraicIndependent_of_grad_annihilated
#print axioms CubicTheta.AllD.exists_pivots_and_nonpivots
#print axioms CubicTheta.AllD.nonPivotSubmatrix_det_ne_zero
#print axioms CubicTheta.AllD.ideal_eq_affine_linear_of_kernel_and_pivots
#print axioms CubicTheta.AllD.stokes_jet_ideal_linearization
#print axioms CubicTheta.AllD.stokes_jet_ideal_linearization_field
#print axioms CubicTheta.AllD.singleSingBeta_pos
#print axioms CubicTheta.AllD.singleSingBeta_lt_one
#print axioms CubicTheta.AllD.singleSingBeta_strictMono
#print axioms CubicTheta.AllD.singleSingBeta_distinct_mod_int
#print axioms CubicTheta.AllD.singleSingJetMatrix_det_ne_zero
#print axioms CubicTheta.AllD.singleSingJetMatrixCast_det_ne_zero
#print axioms CubicTheta.AllD.singleSingJetMatrix_rank
#print axioms CubicTheta.AllD.singleSingJetMatrixCast_rank
#print axioms CubicTheta.AllD.laurentT_add_beta_risingFacSeries
#print axioms CubicTheta.AllD.isNegLaurentPoly_neg_laurentNegOne
#print axioms CubicTheta.AllD.isNegLaurentPoly_laurentT
#print axioms CubicTheta.AllD.isNegLaurentPoly_add_beta
#print axioms CubicTheta.AllD.isNegLaurentPoly_add
#print axioms CubicTheta.AllD.isNegLaurentPoly_smul
#print axioms CubicTheta.AllD.laurentT_pow_risingFacSeries_tail
#print axioms CubicTheta.AllD.laurentTAdd_commute
#print axioms CubicTheta.AllD.singleSingOrderDOp_annihilates_nonneg
#print axioms CubicTheta.AllD.single_singularity_order_d_rank

-- Wave 16 (v3.9.0) — DepthThreeSliceRankCore.lean (58 public theorems / 89 public decls)
#print axioms CubicTheta.AllD.eulerian_sum_eq_id
#print axioms CubicTheta.AllD.eulerianE1_idem
#print axioms CubicTheta.AllD.eulerianE2_idem
#print axioms CubicTheta.AllD.eulerianE3_idem
#print axioms CubicTheta.AllD.eulerianE1_comp_E2
#print axioms CubicTheta.AllD.eulerianE2_comp_E1
#print axioms CubicTheta.AllD.eulerianE1_comp_E3
#print axioms CubicTheta.AllD.eulerianE3_comp_E1
#print axioms CubicTheta.AllD.eulerianE2_comp_E3
#print axioms CubicTheta.AllD.eulerianE3_comp_E2
#print axioms CubicTheta.AllD.mixedBilinear_skew
#print axioms CubicTheta.AllD.eulerianE1_eq_lieInvariant
#print axioms CubicTheta.AllD.lieInvariant_eulerianE1
#print axioms CubicTheta.AllD.lieInvariant_eq_zero_iff_eulerianE1_eq_zero
#print axioms CubicTheta.AllD.eulerianE2_eq_mixedBilinear
#print axioms CubicTheta.AllD.mixedBilinear_eulerianE2
#print axioms CubicTheta.AllD.mixedBilinear_eq_zero_iff_eulerianE2_eq_zero
#print axioms CubicTheta.AllD.lieInvariant_shuffleTensor12
#print axioms CubicTheta.AllD.eulerianE1_shuffleTensor12
#print axioms CubicTheta.AllD.mixedBilinear_shuffleTensor12
#print axioms CubicTheta.AllD.eulerianE3_shuffleTensor12
#print axioms CubicTheta.AllD.perm_fin3_cases
#print axioms CubicTheta.AllD.eulerianReg_sum_eq_id
#print axioms CubicTheta.AllD.eulerianRegE1_idem
#print axioms CubicTheta.AllD.eulerianRegE2_idem
#print axioms CubicTheta.AllD.eulerianRegE3_idem
#print axioms CubicTheta.AllD.eulerianRegE1_comp_E2
#print axioms CubicTheta.AllD.eulerianRegE2_comp_E1
#print axioms CubicTheta.AllD.eulerianRegE1_comp_E3
#print axioms CubicTheta.AllD.eulerianRegE3_comp_E1
#print axioms CubicTheta.AllD.eulerianRegE2_comp_E3
#print axioms CubicTheta.AllD.eulerianRegE3_comp_E2
#print axioms CubicTheta.AllD.eulerianRegE1_finrank
#print axioms CubicTheta.AllD.eulerianRegE2_finrank
#print axioms CubicTheta.AllD.eulerianRegE3_finrank
#print axioms CubicTheta.AllD.eulerianReg_dim_decomposition_rat
#print axioms CubicTheta.AllD.shuffleMul_single
#print axioms CubicTheta.AllD.wordShuffle_one_two
#print axioms CubicTheta.AllD.depth3_shuffle_identity_raw
#print axioms CubicTheta.AllD.depth3_shuffle_identity
#print axioms CubicTheta.AllD.depth3_alternating_shuffle_identity
#print axioms CubicTheta.AllD.depth3_e2_period_pairing
#print axioms CubicTheta.AllD.isHomogeneous_one_eq_sum
#print axioms CubicTheta.AllD.eval_linChangeVars
#print axioms CubicTheta.AllD.linChangeVars_comp
#print axioms CubicTheta.AllD.linChangeVars_id
#print axioms CubicTheta.AllD.linChangeVars_isHomogeneous
#print axioms CubicTheta.AllD.cubic_sliceRank_le_iff_vanishes_on_codim_subspace
#print axioms CubicTheta.AllD.cubicPolyOfTensor_isHomogeneous
#print axioms CubicTheta.AllD.symTensor_cubic_sliceRank_le_iff_vanishes_on_codim_subspace
#print axioms CubicTheta.AllD.exists_mem_support_ge_finrank
#print axioms CubicTheta.AllD.matrix_rank_sum_outer_le
#print axioms CubicTheta.AllD.matrix_rank_add_le
#print axioms CubicTheta.AllD.matrix_rank_diagonal_eq_card_ne_zero
#print axioms CubicTheta.AllD.tao_diagonal_cubic_sliceRank_lower_bound
#print axioms CubicTheta.AllD.tao_diagonal_cubic_sliceRank_exact
#print axioms CubicTheta.AllD.diag_cubic_symSliceRank_lower_bound
#print axioms CubicTheta.AllD.vCube_jet_poly_symSliceRank_lower_bound

-- Wave 17 (v3.9.0) — HeckeRadiusPeelingAndBerndtEntry45.lean (50 public theorems / 72 public decls)
#print axioms CubicTheta.AllD.entry45Weight_pos
#print axioms CubicTheta.AllD.entry45Perturb_abs_le_const_mul_weight
#print axioms CubicTheta.AllD.entry45_ratio_const_lt_one
#print axioms CubicTheta.AllD.entry45Perturb_abs_lt_weight
#print axioms CubicTheta.AllD.entry45Weight_moment_integrable
#print axioms CubicTheta.AllD.entry45Perturb_moment_integrable
#print axioms CubicTheta.AllD.entry45PerturbedWeight_moment_integrable
#print axioms CubicTheta.AllD.one_sub_I_pow_four
#print axioms CubicTheta.AllD.entry45Alpha_pow_four_mul_im_zero
#print axioms CubicTheta.AllD.entry45ComplexIntegral_eq
#print axioms CubicTheta.AllD.entry45Perturb_moment_zero
#print axioms CubicTheta.AllD.entry45PerturbedWeight_pos
#print axioms CubicTheta.AllD.entry45PerturbedWeight_moment_eq
#print axioms CubicTheta.AllD.entry45PerturbedWeight_ne_of_ne
#print axioms CubicTheta.AllD.entry45PerturbedWeight_measure_ne_of_ne
#print axioms CubicTheta.AllD.entry45_stieltjes_indeterminate
#print axioms CubicTheta.AllD.exp_five_gt_128
#print axioms CubicTheta.AllD.pi_mul_sqrt_eleven_gt_ten
#print axioms CubicTheta.AllD.grossS_lt_inv_16384
#print axioms CubicTheta.AllD.nat_cube_le_eight_pow
#print axioms CubicTheta.AllD.summable_eisensteinE4_terms
#print axioms CubicTheta.AllD.eisensteinE4_sub_one_norm_le
#print axioms CubicTheta.AllD.eisensteinE4_sub_one_norm_lt_inv_64
#print axioms CubicTheta.AllD.eisensteinE4_norm_bounds
#print axioms CubicTheta.AllD.norm_grossQ
#print axioms CubicTheta.AllD.norm_grossQ_lt_inv_16384
#print axioms CubicTheta.AllD.grossRadiusSqDivPiSq_mem_Ioo
#print axioms CubicTheta.AllD.grossRadius_pos
#print axioms CubicTheta.AllD.grossLower_div_grossUpper_ge
#print axioms CubicTheta.AllD.grossRadius_consecutive_ratio_gt
#print axioms CubicTheta.AllD.grossRadius_strictMono
#print axioms CubicTheta.AllD.grossRadius_chain
#print axioms CubicTheta.AllD.inVars_iff_mem_vars
#print axioms CubicTheta.AllD.inVars_iff_degreeOf_pos
#print axioms CubicTheta.AllD.mvPoly_pderiv_ne_zero_of_degreeOf_pos
#print axioms CubicTheta.AllD.mvPoly_pderiv_inVars
#print axioms CubicTheta.AllD.mvPoly_pderiv_degreeOf_lt
#print axioms CubicTheta.AllD.exists_minimal_relation_nonzero_separant
#print axioms CubicTheta.AllD.radius_peeling_joint_diff_indep
#print axioms CubicTheta.AllD.algebraicIndependent_intermediateField_adjoin_of_sum
#print axioms CubicTheta.AllD.radius_peeling_over_baseField
#print axioms CubicTheta.AllD.grossCM_ten_series_radius_peeling
#print axioms CubicTheta.AllD.universal_pair_radius_peeling
#print axioms CubicTheta.AllD.ln343_fifth_power_eq
#print axioms CubicTheta.AllD.ln343_unit_mul_inv
#print axioms CubicTheta.AllD.ln343_isUnit
#print axioms CubicTheta.AllD.ln343_inv_isUnit
#print axioms CubicTheta.AllD.ln343_real_identity
#print axioms CubicTheta.AllD.ln343_unit_in_Z_adjoin_fifthRoot2
#print axioms CubicTheta.AllD.ln343_block2_seventhRoot2_units

-- Wave 17 (v3.9.0) — ExponentMeasureAndPolyCauchyCore.lean (38 public theorems / 55 public decls)
#print axioms CubicTheta.AllD.poly_ae_zero_imp_zero_of_infinite_support
#print axioms CubicTheta.AllD.realPoly_ae_zero_imp_zero_of_infinite_support
#print axioms CubicTheta.AllD.poly_weight_rank_infinite_support
#print axioms CubicTheta.AllD.poly_weight_rank_complexMeasure_infinite_support
#print axioms CubicTheta.AllD.poly_weight_rank_finite_support_le
#print axioms CubicTheta.AllD.risingFact_eq_ascPochhammer
#print axioms CubicTheta.AllD.risingFact_succ_shift
#print axioms CubicTheta.AllD.neg_one_pow_mul_risingFact_neg
#print axioms CubicTheta.AllD.shift_band_coeff_identity
#print axioms CubicTheta.AllD.shift_band_iter_identity
#print axioms CubicTheta.AllD.shift_band_measure_identity
#print axioms CubicTheta.AllD.expAtomPS_diffEq
#print axioms CubicTheta.AllD.coeff_laurentT
#print axioms CubicTheta.AllD.laurentT_add_smul_expAtom
#print axioms CubicTheta.AllD.neg_single_neg_one_mem_negLaurentPoly
#print axioms CubicTheta.AllD.laurentT_mem_negLaurentPoly
#print axioms CubicTheta.AllD.laurentT_add_smul_mem_negLaurentPoly
#print axioms CubicTheta.AllD.laurentT_add_smul_comm
#print axioms CubicTheta.AllD.laurentT_pow_expAtom
#print axioms CubicTheta.AllD.annihOp_mem_negLaurentPoly
#print axioms CubicTheta.AllD.annihOp_comm_factor
#print axioms CubicTheta.AllD.annihOp_expAtom_mem_negLaurentPoly
#print axioms CubicTheta.AllD.finite_support_measure_annihilated
#print axioms CubicTheta.AllD.tendsto_rpow_mul_neg_log_pow_zero
#print axioms CubicTheta.AllD.tendsto_self_mul_neg_log_pow_zero
#print axioms CubicTheta.AllD.polyCauchyW_moment_integrable
#print axioms CubicTheta.AllD.polyCauchy_log_density_moment
#print axioms CubicTheta.AllD.cauchyFirstCoeff_succ
#print axioms CubicTheta.AllD.cauchy_first_second_kind_relation
#print axioms CubicTheta.AllD.poly_log_analytic_eq_zero
#print axioms CubicTheta.AllD.polyCauchy_densities_poly_indep
#print axioms CubicTheta.AllD.polyCauchy_densities_poly_indep_of_not_both_one
#print axioms CubicTheta.AllD.polyCauchy_densities_both_one_relation
#print axioms CubicTheta.AllD.polyCauchy_jet_span_finrank
#print axioms CubicTheta.AllD.polyCauchyEulerPoly_monic_and_natDegree
#print axioms CubicTheta.AllD.iterated_eulerDiffOp_exp
#print axioms CubicTheta.AllD.polyCauchy_nonpos_powerSeries
#print axioms CubicTheta.AllD.polyCauchy_nonpos_dfinite_poly
