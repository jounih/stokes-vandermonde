module

public import PNTIntegration.Final
public import PNTIntegration.PrimePartitions
public import PakPrimes.PakNthPrimeUnconditional

/-! # Unconditional Differential Transcendence of the `n`-th Prime Series (`∑ p_n x^n`)

Composes `PakPrimes.PakNthPrimeUnconditional.pak_2_5a_of_pnt` with
`PakPrimes.Main.pntAllOrders` (proved from `MediumPNT` in `PrimeNumberTheoremAnd`),
yielding zero-hypothesis differential transcendence over `ℂ(x)` for the `n`-th prime
ordinary generating function `PakPrimes.NthPrime.series = ∑_{n ≥ 1} p_n x^n`.

Combined with `PakPrimes.Main.primeCounting_and_indicator_independent` and
`PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent`,
this settles Pak's Conjectures 2.5 (all three prime series) and 2.6 unconditionally
in Lean 4 against strictly `[propext, Classical.choice, Quot.sound]`.
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

/-- **Combined Unconditional Resolution of Pak's Conjectures 2.5 and 2.6**:
1. `∑_{p prime} x^p` (prime indicator series),
2. `∑_{n ≥ 0} π(n) x^n` (prime-counting series),
3. `∑_{n ≥ 1} p_n x^n` (`n`-th prime series), and
4. `∏_{p prime} (1 - x^p)⁻¹` (partitions into primes, OEIS A000607)
are each unconditionally differentially transcendental over `ℂ(x)`. -/
theorem pak_conjectures_2_5_and_2_6_complete :
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
