module

public import PakPrimes.SpectralPositivity

/-!
# Statements Audit Ledger: Spectral Positivity & Strict Hankel Positive Definiteness (RH-Free / GRH-Free & Hyperbolic)

Thin statement ledger re-stating the unified spectral-positivity and Hankel positive-definiteness
theorems from `PakPrimes.SpectralPositivity`, cleanly separated into three explicit scope tiers:

1. **Unconditional Abstract Analytic & Measure-Theoretic Core (ZERO External Parameters)**:
   - `spectral_lower_from_estimates` and its verified arithmetic instantiations
     `xi_lower_from_estimates` (`h = 15, H = 20, C = 1`),
     `dirichletBeta_lower_from_estimates` (`h = 7, H = 16, C = 10`), and
     `ramanujanDelta_lower_from_estimates` (`h = 10, H = 16, C = 10`), proving that small-`x`
     and large-`x` spectral estimates imply `(99 / 100) * exp (-h * x) ≤ K x` for all `x > 0`;
   - `square_integral_pos`, `hankel_form`, `hankel_posDef_of_positive_weight`, and
     `hankel_det_pos_of_positive_weight`: strict Hankel positive definiteness and positive
     determinants for ANY measurable strictly positive weight `w` on `(0, ∞)` with integrable
     power moments.
2. **Parameterized Zero-RH / Zero-GRH Arithmetic Specializations (`SpectralLowZeroData h H C`)**:
   - **Honesty boundary:** `SpectralLowZeroData h H C` (with `γ₁ : ℝ`, `γ_low : List ℝ` +
     `γ_low_pos` for any additional positive real critical-line low zeros below `H`, `γ_tail : ℕ → ℂ`
     with `Re γ ≥ H` and `|Im γ| < 1 / 2`, and `∑ (4 + (Re γ)²)⁻¹ < C`) and `CramerLowZeroData`
     are **NOT connected in Lean** to the zeros of `completedXi`, `L(s, χ_{-4})`, or `L(s, Δ)`.
     Exact zero enumeration with multiplicity, low-height verification, the Hadamard bound
     `∑ (4 + (Re γ)²)⁻¹ < C`, and the identity matching `spectralMoment` to Taylor coefficients
     of `ξ'/ξ` all remain external. The theorems hold for any data satisfying the fields.
   - **Crucially, ZERO `RiemannHypothesis` or GRH is assumed:** arbitrary off-line zeros inside
     the critical strip (`|Im γ| < 1 / 2`) are permitted! Including `γ_low : List ℝ` makes the
     `(7, 16, 10)` and `(10, 16, 10)` regimes genuinely non-vacuous for Dirichlet $\beta$
     (`γ_low = [10.24..., 12.99...]`) and Ramanujan's $\Delta$ (`γ_low = [13.91...]`), alongside
     Riemann $\xi$ (`(15, 20, 1)`, `γ_low = []`).
3. **Parameterized Subtracted Compact Hyperbolic Spectral Measure (`d = 2, 3`; `SubtractedHyperbolicSpectralData`)**:
   - **Honesty boundary:** `SubtractedHyperbolicSpectralData` is **NOT connected in Lean** to the
     Laplace eigenvalues of a concrete hyperbolic manifold. The positive spectral gap
     `0 < r_min ≤ r j` (after subtracting exceptional/threshold modes), multiplicities, and
     Weyl-law convergence `∑_j r_j^{-4} < ∞` remain external.
   - Proves strict positivity `K_X(x) > 0`, the exact factorial-spectral moment identity
     `ν_k = ∫_0^∞ y^{k+1} K_X(√y) dy = 2 (2k + 3)! ∑_j r_j^{-(2k+4)}`, and strict positive
     definiteness / positive determinants of all shifted Hankel matrices `(ν_{i + j + s})`.

See `docs/completed-xi-and-positivity.md` for full scope transparency and contrast with
Lagarias (1999) / Li's RH positivity criterion.
-/

public section

namespace Statements.SpectralPositivity

open MeasureTheory Polynomial Set
open PakPrimes.SpectralPositivity
open scoped BigOperators Matrix

/-! ### 1. Unconditional Abstract Analytic & Measure-Theoretic Core (ZERO External Parameters) -/

/-- General two-range spectral lower bound: small-`x` (`0 < x ≤ π`) and large-`x` (`π ≤ x`)
estimates plus the gap condition `100 * C * (4 + H²) ≤ exp ((H - h) * π)` imply
`(99 / 100) * exp (-h * x) ≤ K x` for every `x > 0`. -/
theorem spectral_lower_from_estimates (K : ℝ → ℝ) {h H C : ℝ}
    (hC : 0 ≤ C) (hhH : h ≤ H)
    (hgap : 100 * C * (4 + H ^ 2) ≤ Real.exp ((H - h) * Real.pi))
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-h * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-h * x) - C * (4 + H ^ 2) * Real.exp (-H * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-h * x) ≤ K x :=
  PakPrimes.SpectralPositivity.spectral_lower_from_estimates K hC hhH hgap small large hx

/-- Verified arithmetic two-range positivity for the `(15, 20, 1)` regime (Riemann $\xi$). -/
theorem xi_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-15 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-15 * x) - 404 * Real.exp (-20 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-15 * x) ≤ K x :=
  PakPrimes.SpectralPositivity.xi_lower_from_estimates K small large hx

/-- Verified arithmetic two-range positivity for the `(7, 16, 10)` regime (Dirichlet $\beta$). -/
theorem dirichletBeta_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-7 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-7 * x) - 2600 * Real.exp (-16 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-7 * x) ≤ K x :=
  PakPrimes.SpectralPositivity.dirichletBeta_lower_from_estimates K small large hx

/-- Verified arithmetic two-range positivity for the `(10, 16, 10)` regime (Ramanujan's $\Delta$). -/
theorem ramanujanDelta_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-10 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-10 * x) - 2600 * Real.exp (-16 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-10 * x) ≤ K x :=
  PakPrimes.SpectralPositivity.ramanujanDelta_lower_from_estimates K small large hx

/-- Strict positivity of polynomial-square integrals for any atomless nonzero measure on `ℝ`. -/
theorem square_integral_pos (μ : Measure ℝ) [NullSingletonClass μ] [NeZero μ]
    {p : ℝ[X]} (hp : p ≠ 0) (hi : Integrable (fun x => (p.eval x) ^ 2) μ) :
    0 < ∫ x, (p.eval x) ^ 2 ∂μ :=
  PakPrimes.SpectralPositivity.square_integral_pos μ hp hi

/-- Abstract strict positivity of Hankel quadratic forms for any linear moment functional
strictly positive on nonzero polynomial squares. -/
theorem hankel_form (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p * p))
    {n : ℕ} (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < ∑ i, ∑ j, a i * a j * L (X ^ (i.val + j.val)) :=
  PakPrimes.SpectralPositivity.hankel_form L hL a ha

/-- Unified positive-weight Hankel positive-definiteness engine on `(0, ∞)`. -/
theorem hankel_posDef_of_positive_weight {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y)
    (hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume)
    (n : ℕ) :
    (Matrix.of fun i j : Fin n => ∫ y in Ioi (0 : ℝ), y ^ (i.val + j.val) * w y).PosDef :=
  PakPrimes.SpectralPositivity.hankel_posDef_of_positive_weight hw_meas hw_pos hmom n

/-- Unified positive-weight Hankel determinant strict positivity corollary on `(0, ∞)`. -/
theorem hankel_det_pos_of_positive_weight {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y)
    (hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume)
    (n : ℕ) :
    0 < (Matrix.of fun i j : Fin n => ∫ y in Ioi (0 : ℝ), y ^ (i.val + j.val) * w y).det :=
  PakPrimes.SpectralPositivity.hankel_det_pos_of_positive_weight hw_meas hw_pos hmom n

/-! ### 2. Parameterized Zero-RH / Zero-GRH Arithmetic Specializations (`SpectralLowZeroData h H C`)

Every theorem below is parameterized by `SpectralLowZeroData h H C` (with `γ_low : List ℝ` and
`γ_low_pos`), which is NOT connected in Lean to the zeros of `completedXi`, `L(s, χ_{-4})`, or
`L(s, Δ)`; exact zero enumeration, low-height verification, the Hadamard weight bound, and
Taylor-coefficient matching remain external, while arbitrary off-line critical-strip zeros with
`|Im γ| < 1 / 2` are permitted (ZERO RH / GRH assumed). -/

/-- `(15, 20, 1)` regime (Riemann $\xi$, zero RH): strict positivity of `spectralDensity D`. -/
theorem xiDensity_pos (D : SpectralLowZeroData 15 20 1) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  PakPrimes.SpectralPositivity.xiDensity_pos D hx

/-- `(15, 20, 1)` regime (Riemann $\xi$, zero RH): strict positive definiteness of all shifted
Stieltjes Hankel matrices `(μ_{i + j + s})`. -/
theorem xiHankel_posDef (D : SpectralLowZeroData 15 20 1) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  PakPrimes.SpectralPositivity.xiHankel_posDef D s n

/-- `(15, 20, 1)` regime (Riemann $\xi$, zero RH): strict positivity of all shifted Stieltjes
Hankel determinants. -/
theorem xiHankel_det_pos (D : SpectralLowZeroData 15 20 1) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  PakPrimes.SpectralPositivity.xiHankel_det_pos D s n

/-- `(7, 16, 10)` regime (Dirichlet $\beta$, with `γ_low : List ℝ`, zero GRH): strict positivity of
`spectralDensity D`. -/
theorem dirichletBetaDensity_pos (D : SpectralLowZeroData 7 16 10) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  PakPrimes.SpectralPositivity.dirichletBetaDensity_pos D hx

/-- `(7, 16, 10)` regime (Dirichlet $\beta$, zero GRH): strict positive definiteness of all
shifted Stieltjes Hankel matrices. -/
theorem dirichletBetaHankel_posDef (D : SpectralLowZeroData 7 16 10) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  PakPrimes.SpectralPositivity.dirichletBetaHankel_posDef D s n

/-- `(7, 16, 10)` regime (Dirichlet $\beta$, zero GRH): strict positivity of all shifted
Stieltjes Hankel determinants. -/
theorem dirichletBetaHankel_det_pos (D : SpectralLowZeroData 7 16 10) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  PakPrimes.SpectralPositivity.dirichletBetaHankel_det_pos D s n

/-- `(10, 16, 10)` regime (Ramanujan's $\Delta$, with `γ_low : List ℝ`, zero GRH): strict
positivity of `spectralDensity D`. -/
theorem ramanujanDeltaDensity_pos (D : SpectralLowZeroData 10 16 10) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  PakPrimes.SpectralPositivity.ramanujanDeltaDensity_pos D hx

/-- `(10, 16, 10)` regime (Ramanujan's $\Delta$, zero GRH): strict positive definiteness of all
shifted Stieltjes Hankel matrices. -/
theorem ramanujanDeltaHankel_posDef (D : SpectralLowZeroData 10 16 10) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  PakPrimes.SpectralPositivity.ramanujanDeltaHankel_posDef D s n

/-- `(10, 16, 10)` regime (Ramanujan's $\Delta$, zero GRH): strict positivity of all shifted
Stieltjes Hankel determinants. -/
theorem ramanujanDeltaHankel_det_pos (D : SpectralLowZeroData 10 16 10) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  PakPrimes.SpectralPositivity.ramanujanDeltaHankel_det_pos D s n

/-! ### 3. Parameterized Subtracted Compact Hyperbolic Spectral Measure (`d = 2, 3`)

Every theorem below is parameterized by `SubtractedHyperbolicSpectralData`, which is NOT connected
in Lean to a concrete hyperbolic manifold's Laplace eigenvalues (spectral gap, exceptional-mode
subtraction, multiplicities, and Weyl-law convergence `∑_j r_j^{-4} < ∞` remain external). -/

/-- Strict positivity `K_X(x) > 0` of the oscillatory hyperbolic spectral density for every `x > 0`. -/
theorem hyperbolicSpectralDensity_pos (D : SubtractedHyperbolicSpectralData) {x : ℝ} (hx : 0 < x) :
    0 < hyperbolicSpectralDensity D x :=
  PakPrimes.SpectralPositivity.hyperbolicSpectralDensity_pos D hx

/-- Exact factorial-spectral moment identity for the subtracted hyperbolic measure
`dν(y) = y K_X(√y) dy` (`d = 2, 3`): `ν_k = 2 * (2k + 3)! * ∑' j, (D.r j)⁻¹ ^ (2k + 4)`. -/
theorem subtractedHyperbolicMoment_eq_tsum (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    subtractedHyperbolicMoment D k =
      2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4) :=
  PakPrimes.SpectralPositivity.subtractedHyperbolicMoment_eq_tsum D k

/-- Strict positive definiteness of all shifted subtracted hyperbolic Hankel matrices `(ν_{i+j+s})`. -/
theorem subtractedHyperbolicHankel_posDef (D : SubtractedHyperbolicSpectralData) (s n : ℕ) :
    (subtractedHyperbolicHankel D s n).PosDef :=
  PakPrimes.SpectralPositivity.subtractedHyperbolicHankel_posDef D s n

/-- Strict positivity of all shifted subtracted hyperbolic Hankel determinants. -/
theorem subtractedHyperbolicHankel_det_pos (D : SubtractedHyperbolicSpectralData) (s n : ℕ) :
    0 < (subtractedHyperbolicHankel D s n).det :=
  PakPrimes.SpectralPositivity.subtractedHyperbolicHankel_det_pos D s n

end Statements.SpectralPositivity
