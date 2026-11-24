module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.LaurentSeries
public import PNTIntegration.ExplicitADE

public section

/-! # Differential polynomials over the rational function field -/

open scoped nonZeroDivisors RatFunc
namespace PakPrimes.Main

/-- Rational-coefficient polynomial relations in Laurent series reduce to polynomial
coefficient relations in power series by localizing the multivariate polynomial ring. -/
theorem rationalADE_of_polynomialADE {ι : Type} (v : ι → PowerSeries ℂ)
    (h : ∀ p : MvPolynomial ι (Polynomial ℂ), p ≠ 0 → MvPolynomial.aeval v p ≠ 0)
    (P : MvPolynomial ι (RatFunc ℂ)) (hP : P ≠ 0) :
    MvPolynomial.aeval (fun j => (v j : LaurentSeries ℂ)) P ≠ 0 := by
  classical
  let _ := MvPolynomial.algebraMvPolynomial (σ := ι) (R := Polynomial ℂ) (S := RatFunc ℂ)
  let M := (nonZeroDivisors (Polynomial ℂ)).map (MvPolynomial.C (σ := ι))
  obtain ⟨⟨p, d⟩, hd⟩ := IsLocalization.surj M P
  have hp : p ≠ 0 := by
    rintro rfl
    exact hP ((IsLocalization.map_units (MvPolynomial ι (RatFunc ℂ)) d).mul_right_cancel
      (by simpa using hd))
  intro hzero
  have he := congrArg (MvPolynomial.aeval (fun j => (v j : LaurentSeries ℂ))) hd
  rw [map_mul, hzero, zero_mul, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap] at he
  let _ : IsScalarTower (Polynomial ℂ) (PowerSeries ℂ) (LaurentSeries ℂ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hl : MvPolynomial.aeval (fun j => (v j : LaurentSeries ℂ)) p =
      (MvPolynomial.aeval v p : PowerSeries ℂ) :=
    MvPolynomial.aeval_algebraMap_apply _ _ _
  rw [hl] at he
  exact h p hp (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact he.symm))

open PrimeNome

/-- Neither the prime-counting generating series nor the prime-indicator generating
series satisfies a nonzero algebraic differential equation over ℂ(q). -/
theorem primeCounting_and_indicator_no_rationalADE {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (hP : P ≠ 0) :
    MvPolynomial.aeval (fun j : Fin (r + 1) => (seriesJet Pi_series j.val : LaurentSeries ℂ)) P ≠ 0 ∧
    MvPolynomial.aeval (fun j : Fin (r + 1) => (seriesJet I_prime j.val : LaurentSeries ℂ)) P ≠ 0 := by
  constructor
  · exact rationalADE_of_polynomialADE _ (polynomialADE_ne_zero primeCounting_and_indicator_independent.2) P hP
  · exact rationalADE_of_polynomialADE _ (polynomialADE_ne_zero primeCounting_and_indicator_independent.1) P hP

end PakPrimes.Main
