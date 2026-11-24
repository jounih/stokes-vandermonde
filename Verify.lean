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
import PNTIntegration.PrimePartitions

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

-- Wave 2: Hölder's Theorem (1887) on Complex.Gamma & Real.Gamma
#check @PakPrimes.HolderGamma.trigamma_no_rat_ade
#check @PakPrimes.HolderGamma.holder_gamma_no_ade
#check @PakPrimes.HolderGamma.holder_gamma_no_rat_ade
#check @PakPrimes.HolderGamma.holder_realGamma_no_ade
#print axioms PakPrimes.HolderGamma.trigamma_no_rat_ade
#print axioms PakPrimes.HolderGamma.holder_gamma_no_ade
#print axioms PakPrimes.HolderGamma.holder_gamma_no_rat_ade
#print axioms PakPrimes.HolderGamma.holder_realGamma_no_ade

-- Wave 2: Hilbert (1900) / Ostrowski's Theorem (1920) on riemannZeta
#check @PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_complex_ade
#check @PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_ade
#check @PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_rat_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_complex_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_ade
#print axioms PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_rat_ade

-- Wave 2: Even Divisor Sums L_{2m}(q), L_0(q), & Literal MacMahon Euler Product M(q)
#check @PakPrimes.DivisorAndMacMahon.sigmaEvenSeries_algebraicIndependent
#check @PakPrimes.DivisorAndMacMahon.divisorSeries_algebraicIndependent
#check @PakPrimes.DivisorAndMacMahon.macmahonSeries_algebraicIndependent
#check @PakPrimes.DivisorAndMacMahon.hasProd_macmahonEulerProduct
#check @PakPrimes.DivisorAndMacMahon.macmahonEulerProduct_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.sigmaEvenSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.divisorSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.macmahonSeries_algebraicIndependent
#print axioms PakPrimes.DivisorAndMacMahon.hasProd_macmahonEulerProduct
#print axioms PakPrimes.DivisorAndMacMahon.macmahonEulerProduct_algebraicIndependent

-- Wave 2: Meromorphic EGF -> OGF (Pak–Yeliussizov families)
#check @PakPrimes.PakYeliussizovEGF.ogf_algebraicIndependent_of_higherOrderBorel
#check @PakPrimes.PakYeliussizovEGF.bernOGF_algebraicIndependent
#check @PakPrimes.PakYeliussizovEGF.tanOGF_algebraicIndependent
#check @PakPrimes.PakYeliussizovEGF.secOGF_algebraicIndependent
#check @PakPrimes.PakYeliussizovEGF.sec2OGF_algebraicIndependent
#check @PakPrimes.PakYeliussizovEGF.ratExpOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.ogf_algebraicIndependent_of_higherOrderBorel
#print axioms PakPrimes.PakYeliussizovEGF.bernOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.tanOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.secOGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.sec2OGF_algebraicIndependent
#print axioms PakPrimes.PakYeliussizovEGF.ratExpOGF_algebraicIndependent

-- Wave 2: Unconditional Partitions into Primes (A000607) & Distinct-Prime Partitions (A000586)
#check @PakPrimes.PartitionsIntoPrimes.hasProd_partitionPrimesEulerProduct
#check @PakPrimes.PartitionsIntoPrimes.hasProd_distinctPrimesEulerProduct
#check @PakPrimes.PartitionsIntoPrimes.partLogDeriv_algebraicIndependent
#check @PakPrimes.PartitionsIntoPrimes.partitionPrimes_algebraicIndependent
#check @PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent
#check @PakPrimes.PartitionsIntoPrimes.distinctLogDeriv_algebraicIndependent
#check @PakPrimes.PartitionsIntoPrimes.distinctPrimes_algebraicIndependent
#check @PakPrimes.PartitionsIntoPrimes.distinctPrimesEulerProduct_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.hasProd_partitionPrimesEulerProduct
#print axioms PakPrimes.PartitionsIntoPrimes.hasProd_distinctPrimesEulerProduct
#print axioms PakPrimes.PartitionsIntoPrimes.partLogDeriv_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.partitionPrimes_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctLogDeriv_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctPrimes_algebraicIndependent
#print axioms PakPrimes.PartitionsIntoPrimes.distinctPrimesEulerProduct_algebraicIndependent

-- Wave 2: Weight-1 Mock Modular / Eichler Integrals over ℂ(u)
#check @PakPrimes.MockModularWeightOne.eichlerWeightOne_no_rat_ade
#check @PakPrimes.MockModularWeightOne.eichlerWeightOne_integral_no_rat_ade
#check @PakPrimes.MockModularWeightOne.kryEisenstein_no_rat_ade
#check @PakPrimes.MockModularWeightOne.cuspG23_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.eichlerWeightOne_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.eichlerWeightOne_integral_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.kryEisenstein_no_rat_ade
#print axioms PakPrimes.MockModularWeightOne.cuspG23_no_rat_ade
