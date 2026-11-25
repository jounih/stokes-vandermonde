# Scope Note: Pak's Conjecture 2.5 (`∑ p_n x^n`) & Complete Closure of Pak 2.5–2.6

**Statement spec:** [`Statements/PakNthPrime.lean`](../Statements/PakNthPrime.lean)  
**Unconditional composition:** [`PNTIntegration/NthPrime.lean`](../PNTIntegration/NthPrime.lean)  
**Core proof modules:** [`PakPrimes/PakNthPrimeUnconditional.lean`](../PakPrimes/PakNthPrimeUnconditional.lean), [`PakPrimes/PakNthPrimeClosure.lean`](../PakPrimes/PakNthPrimeClosure.lean), [`PakPrimes/PakNthPrimeStokes.lean`](../PakPrimes/PakNthPrimeStokes.lean), [`PakPrimes/PakNthPrimeEngine.lean`](../PakPrimes/PakNthPrimeEngine.lean), [`PakPrimes/NthPrimeCriterion.lean`](../PakPrimes/NthPrimeCriterion.lean)

## Formalized in Lean 4 (v3.1.0-rc)

- **Zero-hypothesis D-transcendence of `∑_{n ≥ 1} p_n x^n` over `ℂ(x)` (`pak_2_5a`):** Discharges the Prime Number Theorem input `PNTAllOrders` via `PakPrimes.Main.pntAllOrders` (proved from `MediumPNT` in `PrimeNumberTheoremAnd`) and proves that `PakPrimes.NthPrime.series = 2x + 3x^2 + 5x^3 + 7x^4 + 11x^5 + ⋯` (`coeff (n + 1) = Nat.nth Nat.Prime n`) satisfies no nonzero algebraic differential equation over `ℂ(x)`.
- **Complete closure of Pak's Conjectures 2.5 and 2.6 (`pak_conjectures_2_5_and_2_6_complete`):** Combines `∑_{p prime} x^p`, `∑ π(n) x^n`, `∑ p_n x^n`, and `∏_{p prime} (1 - x^p)⁻¹` (OEIS A000607) in one zero-hypothesis theorem checked strictly against `[propext, Classical.choice, Quot.sound]`.

## Proof Architecture

1. **Nome-ray transfer & Abel summation:** Transfers any polynomial ADE for `∑ p_n x^n` to a real autonomous ODE along the nome ray `q = e^{-e^{-u}}` and matches its all-orders asymptotic expansion (from `PNTAllOrders`) with the implicit inverse `w_+` of `Ei(w) + iπ = e^v` convolved with the Gamma kernel.
2. **Entire continuation & sectorial Gevrey-1 bridge (`PakNthPrimeUnconditional.lean`):** Constructs the entire continuation `I_entire` via overlapping horizontal strips, proves uniform Gevrey-1 log-power asymptotics (`HasGev1Exp`) on the rotated closed sector `[-19π/24, 3π/8]` (opening `7π/6 > π`), and feeds this into the Watson uniqueness and balanced-residue Stokes–Vandermonde engine (`PakNthPrimeClosure.lean`, `PakNthPrimeStokes.lean`).
