module

public import PakPrimes.HigherOrderStrongDTrans
public import PakPrimes.RiemannHypothesisStokes
public import PakPrimes.CogenticAnalyticToolkit

/-!
# Statements Audit Ledger: Universal Strong `ℂ({x})` Lift, Conditional `RH → G_Λ`, & Analytic Certification Toolkit

Thin statement ledger re-stating the headline theorems from:

1. `PakPrimes.HigherOrderStrongDTrans` — **unconditional** universal lift of the rotated-ray,
   arbitrary-pole-order `HigherOrderStokes` engine to **strong differential transcendence over
   `ℂ({x})`** (convergent meromorphic germs at `0`), covering Bernoulli, `tan`, `sec`, `sec^p`,
   Euler–Genocchi powers, trigamma, and Lambert OGFs;
2. `PakPrimes.RiemannHypothesisStokes` + `PakPrimes.HigherOrderStrongDTrans` — **conditional**
   implication proving that `RiemannHypothesis` (together with `InfinitelyManyCriticalLineZeros`)
   implies differential transcendence over `ℂ(x)` and strong differential transcendence over
   `ℂ({x})` of the von Mangoldt Borel-Laplace series `G_Λ`;
3. `PakPrimes.CogenticAnalyticToolkit` — **unconditional** multi-scale Plancherel spectral
   dominance and exact rational Collatz–Wielandt eigenvalue bounds.

See `docs/distinct-density-and-strong-lift.md` for explicit scope notes.
-/

public section

namespace Statements.HigherOrderStrongAndRH

open PakPrimes.HigherOrderStokes PakPrimes.PakYeliussizovEGF PakPrimes.FishburnStrongDTrans
open PakPrimes.HigherOrderStrongDTrans PakPrimes.RiemannHypothesisStokes
open PakPrimes.CogenticAnalyticToolkit

/-- Universal strong `ℂ({x})` lift of the arbitrary-pole-order rotated-ray Stokes engine. -/
theorem ogf_stronglyDTrans_of_higherOrderBorel
    {E : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData E θ₀ ω ord pp) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF E) :=
  PakPrimes.HigherOrderStrongDTrans.ogf_stronglyDTrans_of_higherOrderBorel h

/-- Unconditional strong D-transcendence over `ℂ({x})` of the Bernoulli OGF. -/
theorem bernOGF_stronglyDTrans : StronglyDTransOverMeromorphicGerms bernOGF :=
  PakPrimes.HigherOrderStrongDTrans.bernOGF_stronglyDTrans

/-- Unconditional strong D-transcendence over `ℂ({x})` of the `tan` OGF. -/
theorem tanOGF_stronglyDTrans : StronglyDTransOverMeromorphicGerms (ogfOfEGF Complex.tan) :=
  PakPrimes.HigherOrderStrongDTrans.tanOGF_stronglyDTrans

/-- Unconditional strong D-transcendence over `ℂ({x})` of the `sec^p` OGF for all `p ≥ 1`. -/
theorem secPowOGF_stronglyDTrans (p : ℕ) (hp : 1 ≤ p) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹ ^ p) :=
  PakPrimes.HigherOrderStrongDTrans.secPowOGF_stronglyDTrans p hp

/-- Unconditional strong D-transcendence over `ℂ({x})` of the Euler–Genocchi power OGFs (`p ≥ 1`). -/
theorem eulerGenocchiPowOGF_stronglyDTrans (p : ℕ) (hp : 1 ≤ p) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun ξ => (1 + Complex.exp ξ)⁻¹ ^ p) :=
  PakPrimes.HigherOrderStrongDTrans.eulerGenocchiPowOGF_stronglyDTrans p hp

/-- Unconditional strong D-transcendence over `ℂ({x})` of the trigamma OGF. -/
theorem trigammaOGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF trigammaSeries) :=
  PakPrimes.HigherOrderStrongDTrans.trigammaOGF_stronglyDTrans

/-- Unconditional strong D-transcendence over `ℂ({x})` of the rotated Lambert OGF. -/
theorem lambertOGF_stronglyDTrans (θ₀ : ℝ) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (lambertBorelSeries θ₀)) :=
  PakPrimes.HigherOrderStrongDTrans.lambertOGF_stronglyDTrans θ₀

/-- **Conditional on `RiemannHypothesis`:** D-transcendence over `ℂ(x)` of `G_Λ`. -/
theorem riemannHypothesis_implies_G_Lambda_dTrans
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat G_Lambda P = 0) : P = 0 :=
  PakPrimes.RiemannHypothesisStokes.riemannHypothesis_implies_G_Lambda_dTrans hRH hInf P hP

/-- **Conditional on `RiemannHypothesis`:** strong D-transcendence over `ℂ({x})` of `G_Λ`. -/
theorem riemannHypothesis_implies_G_Lambda_stronglyDTrans
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros) :
    StronglyDTransOverMeromorphicGerms G_Lambda :=
  PakPrimes.HigherOrderStrongDTrans.riemannHypothesis_implies_G_Lambda_stronglyDTrans hRH hInf

/-- Unconditional multi-scale Plancherel spectral-dominance inequalities (`K ≥ 10`). -/
theorem multiscale_filter_spectral_dominance {K : ℕ} (hK : 10 ≤ K) (ξ : ℝ) :
    let x := (avgFilterSymbol K ξ).re
    let y := (avgFilterSymbol K ξ).im
    (0 ≤ x ∧ x ≤ 1) ∧
      y ^ 2 ≤ (5 / (K : ℝ)) * x * (1 - x) ∧
      (1 / 2 : ℝ) * x * (1 - x) ≤ dissipativeSymbol K ξ ∧
      4 * y ^ 2 ≤ (40 / (K : ℝ)) * dissipativeSymbol K ξ :=
  PakPrimes.CogenticAnalyticToolkit.multiscale_filter_spectral_dominance hK ξ

/-- Unconditional exact rational Collatz–Wielandt spectral-radius upper bound. -/
theorem collatz_wielandt_rat_upper_bound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℚ) (lam : ℚ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, (0 : ℚ) < v i)
    (hcert : ∀ i, ∑ j, M i j * (v j : ℝ) ≤ (lam : ℝ) * (v i : ℝ))
    {μ : ℝ} {x : Fin n → ℝ} (hx : x ≠ 0) (heig : M.mulVec x = μ • x) :
    |μ| ≤ (lam : ℝ) :=
  PakPrimes.CogenticAnalyticToolkit.collatz_wielandt_rat_upper_bound M v lam hM hv hcert hx heig

end Statements.HigherOrderStrongAndRH
