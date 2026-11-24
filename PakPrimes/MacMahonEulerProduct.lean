module

public import PakPrimes.DivisorAndMacMahon
public import PakPrimes.MacMahonEulerFactors

/-! # Differential transcendence of the classical MacMahon product

`MacMahonEulerFactors` and `MacMahonLogCoefficients` depend only on mathlib. They give
unconditional coefficientwise convergence and identify any normalized solution of the
formal differential equation with the classical product. This module applies them to
the recurrence and transcendence theorem in `PakPrimes.DivisorAndMacMahon`.

The prerequisite source at verification had SHA-256
`2feb3170411a77ecb32b9bbfd53def32acd4d70dbf0c78cb8204c0028ead772d`.
-/

public section
noncomputable section
namespace PakPrimes.DivisorAndMacMahon
open PowerSeries
open scoped PowerSeries.WithPiTopology Topology BigOperators

/-- All partial products containing the first `d` factors have the exact degree-`d` coefficient
of the recurrence-defined MacMahon series. -/
theorem coeff_macmahonEulerProduct (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    coeff d (∏ i ∈ s, macmahonEulerFactor i) = coeff d macmahonSeries :=
  coeff_macmahonEulerProduct_of_ode macmahonSeries_constantCoeff macmahonSeries_ode d s hs

/-- The ordinary Euler product, over all positive part sizes, converges to the recurrence. -/
theorem hasProd_macmahonEulerProduct :
    HasProd (fun i : ℕ => ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (i + 1))
      macmahonSeries :=
  hasProd_macmahonEulerProduct_of_ode macmahonSeries_constantCoeff macmahonSeries_ode

/-- The independent coordinates are the nome and every formal derivative of the literal product. -/
theorem macmahonEulerProduct_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates
      (∏' i : ℕ, ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (i + 1))) := by
  rw [hasProd_macmahonEulerProduct.tprod_eq]
  exact macmahonSeries_algebraicIndependent

end PakPrimes.DivisorAndMacMahon
