module

public import PNTIntegration.Final
public import Mathlib.Algebra.MvPolynomial.Equiv

public section

/-! # The finite-order algebraic differential equation formulation

A coefficient polynomial in the nome acts through the standard inclusion
`Polynomial ℂ → PowerSeries ℂ`. Variable `j` denotes the ordinary formal derivative
of order `j`; in particular variable zero is the series itself.
-/

namespace PakPrimes.Main

open PrimeNome MvPolynomial

/-- Algebraic independence of the nome and formal jets excludes every nonzero
finite-order differential polynomial with coefficients in `ℂ[q]`. -/
theorem polynomialADE_ne_zero {F : PowerSeries ℂ}
    (hF : AlgebraicIndependent ℂ (seriesCoordinates F)) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0) :
    aeval (fun j : Fin (r + 1) => seriesJet F j.val) P ≠ 0 := by
  let embed : Option (Fin (r + 1)) → ℕ := fun i => i.elim 0 (fun j => j.val + 1)
  have he : Function.Injective embed := by
    intro i k h
    cases i with
    | none =>
      cases k with
      | none => rfl
      | some b => exact (Nat.noConfusion h)
    | some a =>
      cases k with
      | none => exact (Nat.noConfusion h)
      | some b => exact congrArg some (Fin.ext (Nat.succ.inj h))
  let E := optionEquivRight ℂ (Fin (r + 1))
  let jetEval := aeval (fun j : Fin (r + 1) => seriesJet F j.val) (R := Polynomial ℂ)
  have hmaps : (jetEval.restrictScalars ℂ).comp E.toAlgHom =
      aeval (seriesCoordinates F ∘ embed) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp [jetEval, E, embed, Option.elim,
        seriesCoordinates, PowerSeries.algebraMap_apply', Polynomial.coe_X]
    | some j =>
      simp [jetEval, E, embed, Option.elim, seriesCoordinates]
  have hjoint := algebraicIndependent_iff_injective_aeval.mp (hF.comp embed he)
  have hinj : Function.Injective jetEval := by
    intro p q h
    apply E.symm.injective
    apply hjoint
    rw [← hmaps]
    simpa using h
  exact fun hzero => hP (hinj (hzero.trans (map_zero jetEval).symm))

/-- Neither generating series satisfies a polynomial-coefficient algebraic
differential equation of any finite order. -/
theorem primeCounting_and_indicator_no_polynomialADE {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0) :
    aeval (fun j : Fin (r + 1) => seriesJet Pi_series j.val) P ≠ 0 ∧
    aeval (fun j : Fin (r + 1) => seriesJet I_prime j.val) P ≠ 0 :=
  ⟨polynomialADE_ne_zero primeCounting_and_indicator_independent.2 P hP,
   polynomialADE_ne_zero primeCounting_and_indicator_independent.1 P hP⟩

end PakPrimes.Main
