module

public import PakPrimes
public import PakPrimes.HolderGamma
public import PakPrimes.OstrowskiZeta
public import PakPrimes.DivisorAndMacMahon
public import PakPrimes.MacMahonEulerProduct
public import PakPrimes.PakYeliussizovEGF
public import PakPrimes.PartitionsIntoPrimes
public import PNTIntegration.PrimePartitions

/-!
# Statements Audit Spec: Wave 1–2 Primes, MacMahon, Hölder, and Ostrowski

Self-contained statement ledger for the Wave 1–2 core theorems carried forward from
`v1.0.0`–`v2.0.0`, all depending strictly on `[propext, Classical.choice, Quot.sound]`.
-/

public section

namespace Statements.PrimesAndClassical

open scoped PowerSeries.WithPiTopology
open PowerSeries PakPrimes.PrimeNome PakPrimes.HigherOrderStokes

/-- Unconditional Pak Conjecture 2.5b (`∑_{p prime} q^p` and `∑ π(n) q^n` are D-transcendental
over `ℂ(q)`), using `MediumPNT` from `PrimeNumberTheoremAnd` (`PNT+`). -/
theorem primeCounting_and_indicator_dTrans :
    AlgebraicIndependent ℂ indicatorCoordinates ∧
      AlgebraicIndependent ℂ piCoordinates :=
  PakPrimes.Main.primeCounting_and_indicator_independent

/-- Unconditional D-transcendence over `ℂ(q)` of the literal Euler product for partitions into primes (OEIS A000607). -/
theorem partitionPrimes_eulerProduct_dTrans :
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)) :=
  PakPrimes.PartitionsIntoPrimes.partitionPrimesEulerProduct_algebraicIndependent

/-- Unconditional D-transcendence over `ℂ(q)` of the literal Euler product for partitions into distinct primes (OEIS A000586). -/
theorem distinctPrimes_eulerProduct_dTrans :
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 + (X : PowerSeries ℂ) ^ (p : ℕ)))) :=
  PakPrimes.PartitionsIntoPrimes.distinctPrimesEulerProduct_algebraicIndependent

/-- Unconditional D-transcendence over `ℂ(q)` of MacMahon's plane-partition Euler product `M(q) = ∏ (1 - q^n)^{-n}`. -/
theorem macmahon_eulerProduct_dTrans :
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' i : ℕ, ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (i + 1))) :=
  PakPrimes.DivisorAndMacMahon.macmahonEulerProduct_algebraicIndependent

/-- Hölder's theorem (1887) directly on Mathlib's `Complex.Gamma` over `ℂ(u)`. -/
theorem holder_gamma_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  PakPrimes.HolderGamma.holder_gamma_no_rat_ade P hP

/-- Hilbert (1900) / Ostrowski's theorem (1920) directly on Mathlib's `riemannZeta` over `ℂ(u)`. -/
theorem ostrowski_riemannZeta_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => riemannZeta (x : ℂ)) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  PakPrimes.OstrowskiZeta.ostrowski_riemannZeta_no_rat_ade P hP

end Statements.PrimesAndClassical

end
