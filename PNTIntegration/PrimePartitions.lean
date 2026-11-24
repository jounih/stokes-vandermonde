module

public import PNTIntegration.Final
public import PakPrimes.PrimeEulerProduct

/-! # Unconditional Differential Transcendence of Prime Partitions (A000607 & A000586)

Discharges `PNTAllOrders` via `PakPrimes.Main.pntAllOrders` (proved from `MediumPNT` in the
`PrimeNumberTheoremAnd` project by Alex Kontorovich, Terence Tao, and contributors), yielding
zero-hypothesis differential transcendence over `ℂ(q)` for:

* `partLogDerivSeries`: `∑_{p prime} p q^p / (1 - q^p)`,
* `partitionPrimesSeries` and its literal Euler product `∏' p : Nat.Primes, (1 - q^p)⁻¹` (OEIS A000607),
* `distinctLogDerivSeries`: `∑_{p prime} p q^p / (1 + q^p)`,
* `distinctPrimesSeries` and its literal Euler product `∏' p : Nat.Primes, (1 + q^p)` (OEIS A000586).
-/

public section
namespace PakPrimes.PartitionsIntoPrimes

open PowerSeries PakPrimes.PrimeNome PakPrimes.Main
open scoped PowerSeries.WithPiTopology

/-- Unconditional differential transcendence of `∑_{p prime} p q^p / (1 - q^p)` over `ℂ(q)`. -/
theorem partLogDeriv_algebraicIndependent :
    AlgebraicIndependent ℂ partLogDerivCoordinates :=
  partLogDeriv_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

/-- Unconditional differential transcendence of partitions into primes (OEIS A000607) over `ℂ(q)`. -/
theorem partitionPrimes_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates partitionPrimesSeries) :=
  partitionPrimes_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

/-- Unconditional differential transcendence of the literal Euler product
`∏' p : Nat.Primes, (1 - q^p)⁻¹` (OEIS A000607) over `ℂ(q)`. -/
theorem partitionPrimesEulerProduct_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates
      (∏' p : Nat.Primes, (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)) :=
  partitionPrimesEulerProduct_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

/-- Unconditional differential transcendence of `∑_{p prime} p q^p / (1 + q^p)` over `ℂ(q)`. -/
theorem distinctLogDeriv_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates distinctLogDerivSeries) :=
  distinctLogDeriv_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

/-- Unconditional differential transcendence of distinct-prime partitions (OEIS A000586) over `ℂ(q)`. -/
theorem distinctPrimes_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates distinctPrimesSeries) :=
  distinctPrimes_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

/-- Unconditional differential transcendence of the literal Euler product
`∏' p : Nat.Primes, (1 + q^p)` (OEIS A000586) over `ℂ(q)`. -/
theorem distinctPrimesEulerProduct_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates
      (∏' p : Nat.Primes, (1 + (X : PowerSeries ℂ) ^ (p : ℕ)))) :=
  distinctPrimesEulerProduct_algebraicIndependent_of_pnt PakPrimes.Main.pntAllOrders

end PakPrimes.PartitionsIntoPrimes
