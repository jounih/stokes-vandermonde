module

public import PNTIntegration.NthPrime

/-!
# Statements Audit Ledger: Pak's Conjecture 2.5 (`∑ p_n x^n`) & Complete Pak 2.5–2.6 Closure

Thin statement ledger re-stating the unconditional (zero-hypothesis) differential transcendence
over `ℂ(x)` of the `n`-th prime ordinary generating function
`∑_{n ≥ 1} p_n x^n = 2x + 3x^2 + 5x^3 + 7x^4 + ⋯` (Pak's Conjecture 2.5), together with
its combination with the prime indicator, prime-counting, and prime-partition series
(completing Pak's Conjectures 2.5 and 2.6).

All declarations are checked by the Lean 4 kernel strictly against
`[propext, Classical.choice, Quot.sound]`, discharging `PNTAllOrders` via `MediumPNT`
from `PrimeNumberTheoremAnd` (`PNT+`).

## Definitions used
- `PakPrimes.NthPrime.series`: `PakPrimes/NthPrimeCriterion.lean:25`
  (`PowerSeries.mk fun | 0 => 0 | k + 1 => (Nat.nth Nat.Prime k : ℂ)`)
- `PakPrimes.PrimeNome.seriesCoordinates`: `PakPrimes/AutonomousTransfer.lean:65`
  (`0 ↦ X`, `k + 1 ↦ derivative^[k] F`)
- `PakPrimes.Main.indicatorCoordinates`, `piCoordinates`: `PakPrimes/MainTheorem.lean`
- `PakPrimes.Main.pntAllOrders`: `PNTIntegration/Final.lean` (from `MediumPNT`)

See `docs/pak-nth-prime.md` for architecture and scope notes.
-/

public section

namespace Statements.PakNthPrime

open scoped PowerSeries.WithPiTopology
open PowerSeries PakPrimes.PrimeNome PakPrimes.Main PakPrimes.NthPrime

/-! ### Textbook-pinning checks on `PakPrimes.NthPrime.series` -/

/-- Constant term is `0` (1-indexed convention `∑_{n ≥ 1} p_n x^n`). -/
example : PowerSeries.coeff 0 PakPrimes.NthPrime.series = 0 :=
  PakPrimes.NthPrime.coeff_zero

/-- For every `n : ℕ`, the `(n + 1)`-st coefficient is literally `Nat.nth Nat.Prime n`
(Mathlib's `n`-th prime, 0-indexed: `p_0 = 2, p_1 = 3, p_2 = 5, …`). -/
example (n : ℕ) : PowerSeries.coeff (n + 1) PakPrimes.NthPrime.series = (Nat.nth Nat.Prime n : ℂ) :=
  PakPrimes.NthPrime.coeff_succ n

/-- Leading coefficients check: `2x + 3x^2 + 5x^3 + …`. -/
example : PowerSeries.coeff 1 PakPrimes.NthPrime.series = 2 := by simp
example : PowerSeries.coeff 2 PakPrimes.NthPrime.series = 3 := by simp
example : PowerSeries.coeff 3 PakPrimes.NthPrime.series = 5 := by
  rw [PakPrimes.NthPrime.coeff_succ]
  exact_mod_cast Nat.nth_prime_two_eq_five

/-! ### Flagship unconditional (zero-hypothesis) theorems -/

/-- **Pak's Conjecture 2.5 (`∑ p_n x^n`), unconditional (zero external hypotheses)**:
The ordinary generating function `∑_{n ≥ 1} p_n x^n` of the sequence of prime numbers
satisfies no nonzero algebraic differential equation over `ℂ(x)`. -/
theorem pak_2_5a :
    AlgebraicIndependent ℂ (seriesCoordinates PakPrimes.NthPrime.series) :=
  PakPrimes.NthPrime.pak_2_5a

/-- **Complete Resolution of Pak's Conjectures 2.5 and 2.6** (all four prime series,
zero external hypotheses):
1. Prime indicator `∑_{p prime} x^p`,
2. Prime-counting OGF `∑_{n ≥ 0} π(n) x^n`,
3. `n`-th prime OGF `∑_{n ≥ 1} p_n x^n`,
4. Partitions into primes `∏_{p prime} (1 - x^p)⁻¹` (OEIS A000607). -/
theorem pak_conjectures_2_5_and_2_6_complete :
    AlgebraicIndependent ℂ indicatorCoordinates ∧
    AlgebraicIndependent ℂ piCoordinates ∧
    AlgebraicIndependent ℂ (seriesCoordinates PakPrimes.NthPrime.series) ∧
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)) :=
  PakPrimes.NthPrime.pak_conjectures_2_5_and_2_6_complete

end Statements.PakNthPrime

end
