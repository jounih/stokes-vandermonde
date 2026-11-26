module

public import PakPrimes.UnconditionalPrimeDTrans

/-!
# Statements Audit Ledger: Elementary RH-Independent Prime Von Mangoldt Strong D-Transcendence

Thin statement ledger re-stating the completely unconditional, elementary theorems from
`PakPrimes.UnconditionalPrimeDTrans` (zero `RiemannHypothesis`, zero Hardy infinitude, zero
numerical zero tables):

1. **Asymmetric Basepoint `s₀ = 2` (Literal Convergent Von Mangoldt Moments)**:
   `phiLambdaAtTwo w = -ζ'(2 + w) / ζ(2 + w)` equals the literal convergent Dirichlet `L`-series
   `∑_{m ≥ 1} Λ(m) m^{-(2 + w)}` on `Re w > -1` (so its Taylor coefficients at `w = 0` are
   literally `(-1)^n ∑_{m ≥ 2} Λ(m) (log m)^n / m²`, and central reflection does not cancel
   `-ζ'/ζ`). Proves unconditional strong `ℂ({t})` D-transcendence of `ogfOfEGF phiLambdaAtTwo`
   and `formalSeries phiLambdaAtTwo`, plus `ℂ{1/u}` and `ℂ(u)` analytic ADE obstructions for
   `G_Lambda_atTwo_laplace`;
2. **Critical-Line Basepoint `s₀ = 1/2`**:
   Proves the same unconditional strong `ℂ({t})`, `ℂ{1/u}`, and `ℂ(u)` D-transcendence results
   for `phiLambda`, `G_Lambda = formalSeries phiLambda`, and `G_Lambda_laplace` via the elementary
   Euler-accelerated Dirichlet eta nonvanishing certificate on `[0, 1] × [-1/2, 1/2]` and the
   negative-real-axis trivial-zero Stokes ray `θ₀ = π`.

See `docs/geometry-and-unconditional-primes.md` for explicit scope notes.
-/

public section

namespace Statements.UnconditionalPrimes

open PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes PakPrimes.PakYeliussizovEGF
open PakPrimes.FishburnStrongDTrans PakPrimes.HigherOrderStrongDTrans
open PakPrimes.RiemannHypothesisStokes PakPrimes.UnconditionalPrimeDTrans

/-! ### 1. Asymmetric Basepoint `s₀ = 2`: Literal Convergent Von Mangoldt Moments -/

/-- Exact Dirichlet-series identification on `Re w > -1`:
`phiLambdaAtTwo w = LSeries (fun n => (Λ(n) : ℂ)) (2 + w)`. -/
theorem phiLambdaAtTwo_eq_LSeries_vonMangoldt (w : ℂ) (hw : -1 < w.re) :
    phiLambdaAtTwo w = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 + w) :=
  PakPrimes.UnconditionalPrimeDTrans.phiLambdaAtTwo_eq_LSeries_vonMangoldt w hw

/-- Unconditional strong `ℂ({t})` D-transcendence of the literal von Mangoldt moments OGF
at `s₀ = 2`. -/
theorem unconditional_G_Lambda_atTwo_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiLambdaAtTwo) :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_atTwo_ogf_stronglyDTrans

/-- Unconditional strong `ℂ({1/u})` D-transcendence of `formalSeries phiLambdaAtTwo`. -/
theorem unconditional_G_Lambda_atTwo_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiLambdaAtTwo) :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_atTwo_formalSeries_stronglyDTrans

/-- Unconditional `ℂ{1/u}` analytic ADE obstruction for `G_Lambda_atTwo_laplace`. -/
theorem unconditional_G_Lambda_atTwo_laplace_no_conv_ade
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_atTwo_laplace u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) : Q = 0 :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_atTwo_laplace_no_conv_ade Q hQ

/-- Unconditional `ℂ(u)` analytic ADE obstruction for `G_Lambda_atTwo_laplace`. -/
theorem unconditional_G_Lambda_atTwo_laplace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_atTwo_laplace u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_atTwo_laplace_no_rat_ade P hP

/-! ### 2. Critical-Line Basepoint `s₀ = 1/2` (`G_Lambda`) -/

/-- Unconditional strong `ℂ({t})` D-transcendence of `ogfOfEGF phiLambda`. -/
theorem unconditional_G_Lambda_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiLambda) :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_ogf_stronglyDTrans

/-- Unconditional strong `ℂ({1/u})` D-transcendence of `G_Lambda = formalSeries phiLambda`. -/
theorem unconditional_G_Lambda_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiLambda) :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_formalSeries_stronglyDTrans

/-- Unconditional `ℂ{1/u}` analytic ADE obstruction for `G_Lambda_laplace`. -/
theorem unconditional_G_Lambda_laplace_no_conv_ade
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) : Q = 0 :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_laplace_no_conv_ade Q hQ

/-- Unconditional `ℂ(u)` analytic ADE obstruction for `G_Lambda_laplace`. -/
theorem unconditional_G_Lambda_laplace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  PakPrimes.UnconditionalPrimeDTrans.unconditional_G_Lambda_laplace_no_rat_ade P hP

end Statements.UnconditionalPrimes
