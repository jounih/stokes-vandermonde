module

public import PNTIntegration.Final
public import PNTIntegration.PrimePartitions
public import PakPrimes.PakNthPrimeUnconditional

/-! # Unconditional Differential Transcendence of the `n`-th Prime Series (`∑ p_n x^n`)

Composes `PakPrimes.PakNthPrimeUnconditional.pak_2_5a_of_pnt` with
`PakPrimes.Main.pntAllOrders` (proved from `MediumPNT` in `PrimeNumberTheoremAnd`),
yielding zero-hypothesis differential transcendence over `ℂ(x)` for the `n`-th prime
ordinary generating function `PakPrimes.NthPrime.series = ∑_{n ≥ 1} p_n x^n`.

Together with `PakPrimes.Main.primeCounting_and_indicator_independent` (giving `∑ π(n) x^n`
and `∑_{p prime} x^p`) and `PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent`
(giving `∏_{p prime} (1 - x^p)⁻¹`), this settles Pak's Conjecture 2.5 (both `∑ p_n x^n` and
`∑ π(n) x^n`) plus two prime generating-function corollaries unconditionally in Lean 4 against
strictly `[propext, Classical.choice, Quot.sound]`.
(Pak's Conjecture 2.6, for the cubic theta series `∑ x^{n^3}`, is formalized separately in
the companion repository `pak-cubic-theta`, DOI `10.5281/zenodo.24492865`.)
-/

public section
namespace PakPrimes.NthPrime

open PowerSeries PakPrimes.PrimeNome PakPrimes.Main
open scoped PowerSeries.WithPiTopology

/-- **Unconditional Resolution of Pak's Conjecture 2.5 (`∑ p_n x^n`)**:
The ordinary generating function of the `n`-th prime numbers
`PakPrimes.NthPrime.series = ∑_{n ≥ 1} p_n x^n = 2x + 3x^2 + 5x^3 + 7x^4 + 11x^5 + ⋯`
is unconditionally differentially transcendental over `ℂ(x)` (zero external hypotheses). -/
theorem pak_2_5a :
    AlgebraicIndependent ℂ (seriesCoordinates series) :=
  PakPrimes.PakNthPrimeUnconditional.pak_2_5a_of_pnt PakPrimes.Main.pntAllOrders

/-- **Pak's Conjecture 2.5 (both series) and Prime Generating-Function Corollaries**:
1. `∑_{p prime} x^p` (prime indicator series),
2. `∑_{n ≥ 0} π(n) x^n` (prime-counting series — Pak Conjecture 2.5),
3. `∑_{n ≥ 1} p_n x^n` (`n`-th prime series — Pak Conjecture 2.5), and
4. `∏_{p prime} (1 - x^p)⁻¹` (partitions into primes, OEIS A000607)
are each unconditionally differentially transcendental over `ℂ(x)`. -/
theorem pak_conjecture_2_5_and_prime_corollaries :
    AlgebraicIndependent ℂ indicatorCoordinates ∧
    AlgebraicIndependent ℂ piCoordinates ∧
    AlgebraicIndependent ℂ (seriesCoordinates series) ∧
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)) :=
  ⟨primeCounting_and_indicator_independent.1,
   primeCounting_and_indicator_independent.2,
   pak_2_5a,
   PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent⟩

end PakPrimes.NthPrime
