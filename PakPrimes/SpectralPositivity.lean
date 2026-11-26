module

public import PakPrimes.BorelStokesVandermonde
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Spectral Positivity & Strict Hankel Positive Definiteness (RH-Free / GRH-Free & Hyperbolic)

This module integrates and generalizes Codex's `PositiveDensity.lean` handoff
(`papers/automorphic_moment_rank/PositiveDensity.lean` and `spectral-positivity.md`)
into the `PakPrimes` Lean 4 library, providing a **single unified positivity & Hankel
positive-definiteness interface** shared across four spectral families with **ZERO**
Riemann Hypothesis or Generalized Riemann Hypothesis assumptions:

## Architecture & Scope Transparency

### 1. Purely Unconditional Analytic & Measure-Theoretic Core (ZERO External Parameters)
Integrating Codex's `PositiveDensity` interface verbatim:
- `spectral_lower_from_estimates`: general two-range lower bound (`0 < x ≤ π` vs `π ≤ x`)
  turning a small-`x` and large-`x` spectral estimate into `(99/100) e^{-h x} ≤ K(x)`.
- Concrete verified arithmetic instantiations:
  - `xi_lower_from_estimates`: Riemann $\xi$ (`h = 15, H = 20, C = 1` $\implies \frac{99}{100} e^{-15 x} \le K_\xi(x)$);
  - `dirichletBeta_lower_from_estimates`: Dirichlet $\beta$ (`h = 7, H = 16, C = 10` $\implies \frac{99}{100} e^{-7 x} \le K_\beta(x)$);
  - `ramanujanDelta_lower_from_estimates`: Ramanujan's $\Delta$ (`h = 10, H = 16, C = 10` $\implies \frac{99}{100} e^{-10 x} \le K_\Delta(x)$).
- `square_integral_pos`: for ANY atomless nonzero measure `μ : Measure ℝ` (`[NullSingletonClass μ] [NeZero μ]`),
  every nonzero real polynomial `p : ℝ[X]` with integrable square satisfies `0 < ∫ x, (p.eval x)^2 ∂μ`.
- `hankel_form`: for ANY real linear moment functional `L : ℝ[X] →ₗ[ℝ] ℝ` positive on nonzero squares,
  every finite Hankel quadratic form is strictly positive.
- `hankel_posDef_of_positive_weight` & `hankel_det_pos_of_positive_weight`:
  bridges `square_integral_pos` + `hankel_form` to ANY measurable strictly positive weight `w : ℝ → ℝ`
  on `(0, ∞)` with all power moments integrable (including `y^s K(√y)` for arithmetic completions and
  `y^(s+1) K_X(√y)` for subtracted hyperbolic spectral measures).

### 2. Parameterized Arithmetic Spectral Instantiations (`SpectralLowZeroData h H C` — ZERO RH / GRH!)
All theorems in Sections 3–4 are **explicitly parameterized** by `SpectralLowZeroData h H C`, which
records ONLY:
- one real low zero `0 < γ₁ ≤ h`,
- an arbitrary finite list `γ_low : List ℝ` of additional positive real critical-line low zeros
  (supporting multiplicities; e.g., `[]` for Riemann $\xi$, `[10.24..., 12.99...]` for Dirichlet
  $\beta$, and `[13.91...]` for Ramanujan's $\Delta$ below `H = 16`),
- exclusion window `Re γ ≥ H` (`H ≥ 1`) for remaining upper-half-plane zeros `ρ = 1/2 + i γ`,
- critical-strip membership `|Im γ| < 1/2` (**NO RH / GRH assumed**: `Im γ` may take arbitrary values
  in `(-1/2, 1/2)`!),
- convergent logarithmic-derivative weight sum `∑ (4 + (Re γ)²)⁻¹ < C` (corresponding to `Λ'(2)/Λ(2) < C`).

**Honesty boundary**: `SpectralLowZeroData` is **NOT** connected in Lean to the zeros of
`completedXi`, $L(s, \chi_{-4})$, or $L(s, \Delta)$. That $\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$
enumerate exactly those zeros with multiplicity, the low-height verification, the Hadamard bound
$\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$, and the identity relating `spectralMoment` to
the Taylor coefficients of $\xi'/\xi$ are all external. The theorems hold for any data satisfying
the fields. From `SpectralLowZeroData`, we prove completely inside Lean:
- small-`x` and large-`x` lower bounds feeding directly into `xi_lower_from_estimates`,
  `dirichletBeta_lower_from_estimates`, and `ramanujanDelta_lower_from_estimates`;
- finiteness and strict positivity of all Stieltjes moments `μ_k = ∫_0^∞ y^k K(√y) dy`;
- strict positive definiteness and strictly positive determinants of all shifted Hankel matrices
  `H_s = (μ_{i+j+s})_{0 ≤ i, j < n}` for the `(15, 20, 1)`, `(7, 16, 10)`, and `(10, 16, 10)`
  parameter regimes.

### 3. Subtracted Hyperbolic Spectral Measure (`SubtractedHyperbolicSpectralData` — $d = 2, 3$)
For a closed connected hyperbolic manifold $X$ of dimension $d = 2$ or $3$, Weyl's law gives
`K_X(x) ~ c_X x^{-d}` as `x → 0⁺`, so `K_X(√y) dy` has infinite mass near `0`, whereas the
subtracted measure `dν(y) = y K_X(√y) dy` has finite moments of ALL orders whenever `∑ r_j^{-4} < ∞`.
Parameterized explicitly by `SubtractedHyperbolicSpectralData` (`0 < r_min ≤ r j` and `∑ r_j^{-4} < ∞`),
we prove:
- exact factorial-spectral moment identity `ν_k = ∫_0^∞ y^{k+1} K_X(√y) dy = 2 (2k + 3)! ∑_j r_j^{-(2k+4)}`;
- strict positive definiteness and strictly positive determinants of all shifted Hankel matrices
  `(ν_{i + j + s})_{0 ≤ i, j < n}` via the exact same `hankel_posDef_of_positive_weight` interface.

**Honesty boundary**: The link to Laplace eigenvalues of an actual hyperbolic manifold (which
exceptional modes are subtracted, multiplicities, and Weyl's law giving $\sum r_j^{-4} < \infty$
in $d = 2, 3$) is outside Lean; positivity of the exponential sum is immediate and the substantive
formalized content is continuity, integrability, the exact factorial-spectral moment identity, and
strict Hankel positive definiteness.
-/

set_option maxHeartbeats 800000

public section
namespace PakPrimes.SpectralPositivity

open MeasureTheory Polynomial Set Filter Real
open PakPrimes.BorelStokesVandermonde
open scoped BigOperators Matrix

noncomputable section

/-! ### 1. Codex's Two-Range Lower-Bound & Abstract Hankel Positivity Interface -/

/-- **General Two-Range Spectral Lower Bound (Codex's 5-Line Argument)**:
If `K : ℝ → ℝ` satisfies `e^{-h x} ≤ K x` on `(0, π]` and
`e^{-h x} - C * (4 + H²) * e^{-H x} ≤ K x` on `[π, ∞)`, and the numerical gap condition
`100 * C * (4 + H²) ≤ exp ((H - h) * π)` holds with `h ≤ H`, then
`(99 / 100) * exp (-h * x) ≤ K x` for EVERY `x > 0`. -/
theorem spectral_lower_from_estimates (K : ℝ → ℝ) {h H C : ℝ}
    (hC : 0 ≤ C) (hhH : h ≤ H)
    (hgap : 100 * C * (4 + H ^ 2) ≤ Real.exp ((H - h) * Real.pi))
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-h * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-h * x) - C * (4 + H ^ 2) * Real.exp (-H * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-h * x) ≤ K x := by
  rcases le_total x Real.pi with hle | hge
  · have := small x hx hle
    linarith [Real.exp_pos (-h * x)]
  · have hg : 100 * C * (4 + H ^ 2) ≤ Real.exp ((H - h) * x) :=
      hgap.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hge (sub_nonneg.mpr hhH)))
    have hm := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-H * x)).le
    rw [← Real.exp_add, show (H - h) * x + -H * x = -h * x by ring] at hm
    have hcoeff_nn : 0 ≤ C * (4 + H ^ 2) := mul_nonneg hC (by positivity)
    linarith [large x hge]

/-- **Riemann $\xi$ Two-Range Positivity (`PositiveDensity.xi_lower_from_estimates`)**:
With `h = 15, H = 20, C = 1`, the two analytic estimates on the centered Cramér sum imply
`(99 / 100) * exp (-15 * x) ≤ K x` for all `x > 0`. -/
theorem xi_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-15 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-15 * x) - 404 * Real.exp (-20 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-15 * x) ≤ K x := by
  refine spectral_lower_from_estimates K (h := 15) (H := 20) (C := 1)
    zero_le_one (by norm_num) ?_ small (fun y hy => by simpa [show (1 : ℝ) * (4 + 20 ^ 2) = 404 by norm_num] using large y hy) hx
  have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h15 : (40400 : ℝ) ≤ Real.exp 15 := calc
    (40400 : ℝ) ≤ (5 / 2 : ℝ) ^ 15 := by norm_num
    _ ≤ (Real.exp 1) ^ 15 := by gcongr
    _ = Real.exp 15 := by rw [← Real.exp_nat_mul]; norm_num
  have hpi : (15 : ℝ) ≤ (20 - 15) * Real.pi := by linarith [Real.pi_gt_three]
  calc 100 * (1 : ℝ) * (4 + 20 ^ 2) = 40400 := by norm_num
    _ ≤ Real.exp 15 := h15
    _ ≤ Real.exp ((20 - 15) * Real.pi) := Real.exp_le_exp.mpr hpi

/-- **Dirichlet $\beta$ Two-Range Positivity (Zero GRH, from `spectral-positivity.md`)**:
With `h = 7, H = 16, C = 10` (`C * (4 + H²) = 2600`), the two analytic estimates imply
`(99 / 100) * exp (-7 * x) ≤ K x` for all `x > 0`. -/
theorem dirichletBeta_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-7 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-7 * x) - 2600 * Real.exp (-16 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-7 * x) ≤ K x := by
  refine spectral_lower_from_estimates K (h := 7) (H := 16) (C := 10)
    (by norm_num) (by norm_num) ?_ small
    (fun y hy => by simpa [show (10 : ℝ) * (4 + 16 ^ 2) = 2600 by norm_num] using large y hy) hx
  have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h18 : (260000 : ℝ) ≤ Real.exp 18 := calc
    (260000 : ℝ) ≤ (5 / 2 : ℝ) ^ 18 := by norm_num
    _ ≤ (Real.exp 1) ^ 18 := by gcongr
    _ = Real.exp 18 := by rw [← Real.exp_nat_mul]; norm_num
  have hpi : (18 : ℝ) ≤ (16 - 7) * Real.pi := by linarith [Real.pi_gt_three]
  calc 100 * (10 : ℝ) * (4 + 16 ^ 2) = 260000 := by norm_num
    _ ≤ Real.exp 18 := h18
    _ ≤ Real.exp ((16 - 7) * Real.pi) := Real.exp_le_exp.mpr hpi

/-- **Ramanujan's $\Delta$ Two-Range Positivity (Zero GRH, from `spectral-positivity.md`)**:
With `h = 10, H = 16, C = 10` (`C * (4 + H²) = 2600`), the two analytic estimates imply
`(99 / 100) * exp (-10 * x) ≤ K x` for all `x > 0`. -/
theorem ramanujanDelta_lower_from_estimates (K : ℝ → ℝ)
    (small : ∀ x, 0 < x → x ≤ Real.pi → Real.exp (-10 * x) ≤ K x)
    (large : ∀ x, Real.pi ≤ x → Real.exp (-10 * x) - 2600 * Real.exp (-16 * x) ≤ K x)
    {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-10 * x) ≤ K x := by
  refine spectral_lower_from_estimates K (h := 10) (H := 16) (C := 10)
    (by norm_num) (by norm_num) ?_ small
    (fun y hy => by simpa [show (10 : ℝ) * (4 + 16 ^ 2) = 2600 by norm_num] using large y hy) hx
  have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h18 : (260000 : ℝ) ≤ Real.exp 18 := calc
    (260000 : ℝ) ≤ (5 / 2 : ℝ) ^ 18 := by norm_num
    _ ≤ (Real.exp 1) ^ 18 := by gcongr
    _ = Real.exp 18 := by rw [← Real.exp_nat_mul]; norm_num
  have hpi : (18 : ℝ) ≤ (16 - 10) * Real.pi := by linarith [Real.pi_gt_three]
  calc 100 * (10 : ℝ) * (4 + 16 ^ 2) = 260000 := by norm_num
    _ ≤ Real.exp 18 := h18
    _ ≤ Real.exp ((16 - 10) * Real.pi) := Real.exp_le_exp.mpr hpi

/-- **Strict Positivity on Polynomial Squares (`PositiveDensity.square_integral_pos`)**:
For any atomless nonzero measure `μ : Measure ℝ`, every nonzero real polynomial `p : ℝ[X]`
with integrable square satisfies `0 < ∫ x, (p.eval x)^2 ∂μ`.
Non-atomicity suffices because a nonzero real polynomial has finitely many roots. -/
theorem square_integral_pos (μ : Measure ℝ) [NullSingletonClass μ] [NeZero μ]
    {p : ℝ[X]} (hp : p ≠ 0) (hi : Integrable (fun x => (p.eval x) ^ 2) μ) :
    0 < ∫ x, (p.eval x) ^ 2 ∂μ := by
  have hn : ∀ᵐ x ∂μ, p.eval x ≠ 0 :=
    (Polynomial.finite_setOfPred_isRoot hp).countable.ae_notMem μ
  have hnon : 0 ≤ᵐ[μ] (fun x => (p.eval x) ^ 2) := .of_forall fun x => sq_nonneg _
  apply lt_of_le_of_ne (integral_nonneg_of_ae hnon)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp he.symm
  obtain ⟨x, hbad, hgood⟩ := (hz.and hn).exists
  exact hgood (by simpa using hbad)

/-- **Abstract Hankel Quadratic Form Positivity (`PositiveDensity.hankel_form`)**:
Finite expansion of the Hankel quadratic form under an arbitrary real linear moment functional
`L : ℝ[X] →ₗ[ℝ] ℝ` that is strictly positive on nonzero polynomial squares. -/
theorem hankel_form (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p * p))
    {n : ℕ} (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < ∑ i, ∑ j, a i * a j * L (X ^ (i.val + j.val)) := by
  classical
  let p : ℝ[X] := ∑ i, a i • X ^ i.val
  have hp : p ≠ 0 := by
    intro h
    apply ha
    funext k
    have hc := congrArg (fun q : ℝ[X] => q.coeff k.val) h
    simpa [p, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using hc
  have hs := hL p hp
  simpa [p, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, mul_assoc, mul_left_comm, mul_comm] using hs

/-! ### 2. Unified Positive-Weight Measure & Hankel Positive Definiteness Bridge -/

/-- Weighted positive measure `w(y) dy` supported on `(0, ∞)` with nonnegative density `w`. -/
@[expose] def posWeightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun y => (Real.toNNReal (w y) : ENNReal))

private lemma posWeightMeasure_nullSingleton (w : ℝ → ℝ) :
    NullSingletonClass (posWeightMeasure w) where
  measure_singleton x := by
    rw [posWeightMeasure, MeasureTheory.withDensity_apply _ (measurableSet_singleton x)]
    have hzero : (volume.restrict (Ioi (0 : ℝ))) {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    exact setLIntegral_measure_zero _ _ hzero

private lemma posWeightMeasure_neZero {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y) :
    NeZero (posWeightMeasure w) where
  out h0 := by
    have huniv : posWeightMeasure w Set.univ = 0 := by rw [h0]; rfl
    rw [posWeightMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at huniv
    have hnn_meas : AEMeasurable (fun y => (Real.toNNReal (w y) : ENNReal))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (ENNReal.continuous_coe.measurable.comp continuous_real_toNNReal.measurable).comp_aemeasurable hw_meas
    have hae_zero : (fun y => (Real.toNNReal (w y) : ENNReal)) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' hnn_meas).mp huniv
    have hvol_ne : (volume.restrict (Ioi (0 : ℝ))) Set.univ ≠ 0 := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioi]
      exact ENNReal.top_ne_zero
    have hne : Filter.NeBot (ae (volume.restrict (Ioi (0 : ℝ)))) :=
      MeasureTheory.ae_neBot.mpr (by intro h; exact hvol_ne (by rw [h]; rfl))
    obtain ⟨y, hy_zero, hy_mem⟩ := (hae_zero.and (ae_restrict_mem measurableSet_Ioi)).exists
    have hpos_y : 0 < w y := hw_pos y hy_mem
    have hto : Real.toNNReal (w y) = 0 := ENNReal.coe_eq_zero.mp hy_zero
    have hle : w y ≤ 0 := Real.toNNReal_eq_zero.mp hto
    linarith

private lemma integrable_posWeightMeasure_iff {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y) (g : ℝ → ℝ) :
    Integrable g (posWeightMeasure w) ↔ IntegrableOn (fun y => w y * g y) (Ioi (0 : ℝ)) volume := by
  have hnn_meas : AEMeasurable (fun y => Real.toNNReal (w y)) (volume.restrict (Ioi (0 : ℝ))) :=
    Measurable.comp_aemeasurable continuous_real_toNNReal.measurable hw_meas
  rw [posWeightMeasure, MeasureTheory.integrable_withDensity_iff_integrable_smul₀ hnn_meas]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal (w y) (hw_pos y hy).le]

private lemma integral_posWeightMeasure {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y) (g : ℝ → ℝ) :
    ∫ y, g y ∂(posWeightMeasure w) = ∫ y in Ioi (0 : ℝ), w y * g y := by
  have hnn_meas : AEMeasurable (fun y => Real.toNNReal (w y)) (volume.restrict (Ioi (0 : ℝ))) :=
    Measurable.comp_aemeasurable continuous_real_toNNReal.measurable hw_meas
  rw [posWeightMeasure, integral_withDensity_eq_integral_smul₀ hnn_meas]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards with y hy
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal (w y) (hw_pos y hy).le]

private lemma integrable_poly_of_pow {μ : Measure ℝ}
    (hpow : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ) (p : ℝ[X]) :
    Integrable (fun y : ℝ => p.eval y) μ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have heq : (fun y => (p + q).eval y) = fun y => p.eval y + q.eval y := by
      funext y; exact Polynomial.eval_add
    rw [heq]; exact hp.add hq
  | monomial k a =>
    have heq : (fun y => (Polynomial.monomial k a).eval y) = fun y => a * y ^ k := by
      funext y; exact Polynomial.eval_monomial
    rw [heq]; exact (hpow k).const_mul a

/-- **Unified Positive-Weight Hankel Positive Definiteness Engine**:
Instantiates Codex's `square_integral_pos` and `hankel_form` for ANY measurable strictly positive
weight `w : ℝ → ℝ` on `(0, ∞)` whose power moments `∫_{0}^{∞} y^k w(y) dy` are all integrable.
Covers all shifted Hankel matrices of Riemann $\xi$, Dirichlet $\beta$, Ramanujan's $\Delta$, and
subtracted compact hyperbolic spectral measures `y K_X(√y) dy` ($d = 2, 3$). -/
theorem hankel_posDef_of_positive_weight {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y)
    (hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume)
    (n : ℕ) :
    (Matrix.of fun i j : Fin n => ∫ y in Ioi (0 : ℝ), y ^ (i.val + j.val) * w y).PosDef := by
  let μ : Measure ℝ := posWeightMeasure w
  have : NullSingletonClass μ := posWeightMeasure_nullSingleton w
  have : NeZero μ := posWeightMeasure_neZero hw_meas hw_pos
  have hpow_int : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ := fun k => by
    rw [integrable_posWeightMeasure_iff hw_meas hw_pos]
    exact (hmom k).congr_fun (fun y _ => mul_comm _ _) measurableSet_Ioi
  have hpoly_int : ∀ p : ℝ[X], Integrable (fun y : ℝ => p.eval y) μ :=
    integrable_poly_of_pow hpow_int
  let L : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun p => ∫ y, p.eval y ∂μ
      map_add' := fun p q => by
        have heq : (fun y => (p + q).eval y) = fun y => p.eval y + q.eval y := by
          funext y; exact Polynomial.eval_add
        rw [heq, MeasureTheory.integral_add (hpoly_int p) (hpoly_int q)]
      map_smul' := fun r p => by
        have heq : (fun y => (r • p).eval y) = fun y => r * p.eval y := by
          funext y; rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
        rw [heq, MeasureTheory.integral_const_mul]; rfl }
  have hL_pos : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p * p) := by
    intro p hp
    have hsq : (fun y : ℝ => (p * p).eval y) = fun y : ℝ => (p.eval y) ^ 2 := by
      funext y; simp [sq]
    change 0 < ∫ y, (p * p).eval y ∂μ
    rw [hsq]
    exact square_integral_pos μ hp (by rw [← hsq]; exact hpoly_int (p * p))
  have hL_pow : ∀ k : ℕ, L (X ^ k) = ∫ y in Ioi (0 : ℝ), y ^ k * w y := fun k => by
    change ∫ y, (X ^ k : ℝ[X]).eval y ∂μ = _
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    rw [integral_posWeightMeasure hw_meas hw_pos]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y _ => mul_comm _ _
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    simp [Matrix.of_apply, add_comm i.val j.val]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    have hform := hankel_form L hL_pos a ha
    refine lt_of_lt_of_eq hform ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hL_pow (i.val + j.val)]; ring

/-- Immediate determinant corollary of `hankel_posDef_of_positive_weight`. -/
theorem hankel_det_pos_of_positive_weight {w : ℝ → ℝ}
    (hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y)
    (hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume)
    (n : ℕ) :
    0 < (Matrix.of fun i j : Fin n => ∫ y in Ioi (0 : ℝ), y ^ (i.val + j.val) * w y).det :=
  (hankel_posDef_of_positive_weight hw_meas hw_pos hmom n).det_pos

/-! ### 3. Parameterized Arithmetic Spectral Data (`SpectralLowZeroData h H C` — ZERO RH / GRH!) -/

private lemma integrableOn_exp_neg_mul_pow_sp (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * t ^ N) (Ioi (0 : ℝ)) volume := by
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (N : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) one_pos ha
  refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, Real.rpow_one, mul_comm]

private lemma realLaplace_monomial_pos_sp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * t ^ m = (m.factorial : ℝ) / a ^ (m + 1) := by
  have hC := Minor.complexLaplace_monomial m (by simpa using ha : (0 : ℝ) < (a : ℂ).re)
  have hcomm := Complex.ofRealCLM.integral_comp_comm (integrableOn_exp_neg_mul_pow_sp m ha)
  have hrew : (fun t : ℝ => Complex.exp (-(a : ℂ) * (t : ℂ)) * (t : ℂ) ^ m) =
      fun t : ℝ => Complex.ofRealCLM (Real.exp (-a * t) * t ^ m) := by
    funext t
    change Complex.exp (-(a : ℂ) * (t : ℂ)) * (t : ℂ) ^ m = ((Real.exp (-a * t) * t ^ m : ℝ) : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_neg]
  rw [hrew, hcomm] at hC
  have hre := congrArg Complex.re hC
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_re] at hre
  rw [hre]
  have hcast : ((m.factorial : ℂ) / (a : ℂ) ^ (m + 1)) =
      (((m.factorial : ℝ) / a ^ (m + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.ofReal_re]

private lemma list_exp_sum_nonneg (l : List ℝ) (x : ℝ) :
    0 ≤ (l.map (fun γ => Real.exp (-γ * x))).sum := by
  refine List.sum_nonneg ?_
  intro y hy
  rcases List.mem_map.mp hy with ⟨γ, _, rfl⟩
  exact (Real.exp_pos _).le

private lemma list_exp_sum_continuous (l : List ℝ) :
    Continuous (fun x : ℝ => (l.map (fun γ => Real.exp (-γ * x))).sum) := by
  induction l with
  | nil => simpa using continuous_const
  | cons γ t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-γ * x)).add ih

private lemma list_exp_sum_pow_integrable (l : List ℝ) (hl : ∀ γ ∈ l, 0 < γ) (N : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ N * (l.map (fun γ => Real.exp (-γ * x))).sum) (Ioi (0 : ℝ)) volume := by
  induction l with
  | nil =>
    simp
  | cons γ t ih =>
    have hγ : 0 < γ := hl γ (by simp)
    have ht : ∀ γ' ∈ t, 0 < γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
    have h1 : IntegrableOn (fun x : ℝ => x ^ N * Real.exp (-γ * x)) (Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_neg_mul_pow_sp N hγ).congr_fun (fun x _ => by ring) measurableSet_Ioi
    have h2 := ih ht
    refine (h1.add h2).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, mul_add]

/-- Minimal RH-free / GRH-free low-ordinate spectral data parameterized by `(h, H, C)`
(intended parameter regimes: `(15, 20, 1)` for Riemann $\xi$ with `γ_low = []`, `(7, 16, 10)`
for Dirichlet $\beta$ with `γ_low = [10.24..., 12.99...]`, and `(10, 16, 10)` for Ramanujan's
$\Delta$ with `γ_low = [13.91...]`).
Nontrivial upper-half-plane zeros are written `ρ = 1/2 + i γ` (`Re γ > 0`, `|Im γ| < 1/2`).
Notice that **no Riemann Hypothesis or GRH is assumed**: `(γ_tail n).im` may be ANY value in
`(-1/2, 1/2)`.

**Honesty boundary**: The structure is NOT connected in Lean to the zeros of `completedXi`,
$L(s, \chi_{-4})$, or $L(s, \Delta)$. That $\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$
enumerate exactly those zeros with multiplicity, the low-height verification, the Hadamard bound
$\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$, and the identity relating `spectralMoment` to
the Taylor coefficients of $\xi'/\xi$ are all external. The theorems hold for any data satisfying
the fields. -/
structure SpectralLowZeroData (h H C : ℝ) where
  /-- First upper-half-plane real zero ordinate `γ₁` (in `(0, h]`). -/
  γ₁ : ℝ
  /-- Strict positivity of the lead ordinate `0 < γ₁`. -/
  γ₁_pos : 0 < γ₁
  /-- Upper bound `γ₁ ≤ h` on the lead real ordinate. -/
  γ₁_le : γ₁ ≤ h
  /-- Additional finite list of critical-line low real zero ordinates `γ_low` (supporting
  multiplicities; e.g., `[]` for Riemann $\xi$, `[10.24..., 12.99...]` for Dirichlet $\beta$,
  `[13.91...]` for Ramanujan's $\Delta$ below `H = 16`). Every entry contributes a positive
  real exponential `e^{-γ x} > 0`. -/
  γ_low : List ℝ
  /-- Strict positivity `0 < γ` for every additional critical-line low ordinate `γ ∈ γ_low`. -/
  γ_low_pos : ∀ γ ∈ γ_low, 0 < γ
  /-- Remaining upper-half-plane zeros `γ_tail n` (counted with multiplicity, paired by
  conjugate symmetry `γ ↔ conj γ` so the real spectral sum equals `∑ Re(e^{-γ x})`). -/
  γ_tail : ℕ → ℂ
  /-- Lower bound `1 ≤ H` on the tail height threshold. -/
  H_ge_one : 1 ≤ H
  /-- Exclusion window: all tail zeros satisfy `H ≤ Re γ`. -/
  tail_re_ge : ∀ n : ℕ, H ≤ (γ_tail n).re
  /-- Critical-strip bound `0 < Re ρ < 1`, i.e., `|Im γ| < 1/2` (**NO RH / GRH assumed**). -/
  tail_im_lt : ∀ n : ℕ, |(γ_tail n).im| < 1 / 2
  /-- Summability of the Hadamard log-derivative comparison weights `1 / (4 + (Re γ)²)`. -/
  tail_summable_weight : Summable (fun n : ℕ => (1 : ℝ) / (4 + (γ_tail n).re ^ 2))
  /-- Upper bound `∑ (4 + (Re γ)²)⁻¹ < C` (corresponding to `Λ'(2)/Λ(2) < C`). -/
  tail_weight_sum_lt : ∑' n : ℕ, (1 : ℝ) / (4 + (γ_tail n).re ^ 2) < C

/-- The real paired Cramér spectral density
`K(x) = e^{-γ₁ x} + ∑_{γ ∈ γ_low} e^{-γ x} + ∑_n e^{-(Re γ_n) x} cos((Im γ_n) x)`
for `x > 0`. -/
@[expose] def spectralDensity {h H C : ℝ} (D : SpectralLowZeroData h H C) (x : ℝ) : ℝ :=
  Real.exp (-D.γ₁ * x) +
    (D.γ_low.map (fun γ => Real.exp (-γ * x))).sum +
    ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)

/-- Centered Stieltjes moments `μ_k = ∫_{0}^{∞} y^k K(√y) dy`. -/
@[expose] def spectralMoment {h H C : ℝ} (D : SpectralLowZeroData h H C) (k : ℕ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y ^ k * spectralDensity D (Real.sqrt y)

/-- Shifted `n × n` Hankel moment matrix `(μ_{i + j + s})_{0 ≤ i, j < n}`. -/
@[expose] def spectralHankel {h H C : ℝ} (D : SpectralLowZeroData h H C) (s n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => spectralMoment D (i.val + j.val + s)

/-- Absolute summability of the tail series in `spectralDensity D x` for every `x > 0`. -/
theorem spectralDensity_tail_summable {h H C : ℝ} (D : SpectralLowZeroData h H C)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)) := by
  have hmaj : Summable (fun n : ℕ => (4 + 2 / x ^ 2) * ((1 : ℝ) / (4 + (D.γ_tail n).re ^ 2))) :=
    D.tail_summable_weight.mul_left (4 + 2 / x ^ 2)
  refine Summable.of_norm_bounded hmaj fun n => ?_
  set v : ℝ := (D.γ_tail n).re
  have hv0 : 0 ≤ v := by linarith [D.H_ge_one, D.tail_re_ge n]
  have h1 : (1 : ℝ) ≤ Real.exp (v * x) := Real.one_le_exp (mul_nonneg hv0 hx.le)
  have h2 : (v * x) ^ 2 / 2 ≤ Real.exp (v * x) := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (v * x) (mul_nonneg hv0 hx.le) 2
  have hv2 : v ^ 2 ≤ (2 / x ^ 2) * Real.exp (v * x) := by
    rw [mul_pow] at h2
    have hx2 : 0 < x ^ 2 := pow_pos hx 2
    calc v ^ 2 = (v ^ 2 * x ^ 2) / x ^ 2 := by field_simp [hx2.ne']
      _ ≤ (2 * Real.exp (v * x)) / x ^ 2 := div_le_div_of_nonneg_right (by linarith) hx2.le
      _ = (2 / x ^ 2) * Real.exp (v * x) := by ring
  have hcomb : 4 + v ^ 2 ≤ (4 + 2 / x ^ 2) * Real.exp (v * x) := by nlinarith
  have hexp_le : Real.exp (-v * x) ≤ (4 + 2 / x ^ 2) * ((1 : ℝ) / (4 + v ^ 2)) := by
    rw [show -v * x = -(v * x) by ring, Real.exp_neg, mul_one_div, le_div_iff₀ (by positivity)]
    have hpos : 0 < Real.exp (v * x) := Real.exp_pos _
    calc (Real.exp (v * x))⁻¹ * (4 + v ^ 2)
        ≤ (Real.exp (v * x))⁻¹ * ((4 + 2 / x ^ 2) * Real.exp (v * x)) :=
          mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hpos.le)
      _ = 4 + 2 / x ^ 2 := by field_simp [hpos.ne']
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-v * x) * |Real.cos ((D.γ_tail n).im * x)|
      ≤ Real.exp (-v * x) * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = Real.exp (-v * x) := mul_one _
    _ ≤ (4 + 2 / x ^ 2) * ((1 : ℝ) / (4 + v ^ 2)) := hexp_le

/-- **Small-`x` Estimate (`0 < x ≤ π`)**: every paired cosine factor has `|Im γ · x| ≤ π/2`,
so every tail term is nonnegative and `exp (-h * x) ≤ spectralDensity D x` (zero RH/GRH). -/
theorem spectralDensity_small_lower {h H C : ℝ} (D : SpectralLowZeroData h H C)
    (x : ℝ) (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    Real.exp (-h * x) ≤ spectralDensity D x := by
  unfold spectralDensity
  have hlead : Real.exp (-h * x) ≤ Real.exp (-D.γ₁ * x) :=
    Real.exp_le_exp.mpr (by nlinarith [D.γ₁_le])
  have hlow_nn : 0 ≤ (D.γ_low.map (fun γ => Real.exp (-γ * x))).sum :=
    list_exp_sum_nonneg D.γ_low x
  have htail_nn : 0 ≤ ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x) := by
    refine tsum_nonneg fun n => mul_nonneg (Real.exp_pos _).le ?_
    have habs : |(D.γ_tail n).im * x| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hx]
      nlinarith [(D.tail_im_lt n).le]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp habs).1], (abs_le.mp habs).2⟩
  linarith

/-- **Large-`x` Estimate (`π ≤ x`)**: since `4 + (H + u)² ≤ (4 + H²)(1 + u + u²/2) ≤ (4 + H²) e^{u x}`
for all `H ≥ 1, u ≥ 0, x ≥ 1`, the entire tail above height `H` is bounded by
`C * (4 + H²) * exp (-H * x)` (zero RH/GRH). -/
theorem spectralDensity_large_lower {h H C : ℝ} (D : SpectralLowZeroData h H C)
    (x : ℝ) (hxpi : Real.pi ≤ x) :
    Real.exp (-h * x) - C * (4 + H ^ 2) * Real.exp (-H * x) ≤ spectralDensity D x := by
  have hx : 0 < x := lt_of_lt_of_le Real.pi_pos hxpi
  have hx1 : 1 ≤ x := by linarith [Real.pi_gt_three]
  have hC_nn : 0 ≤ C := by
    have hnn : 0 ≤ ∑' n : ℕ, (1 : ℝ) / (4 + (D.γ_tail n).re ^ 2) := tsum_nonneg fun _ => by positivity
    linarith [D.tail_weight_sum_lt]
  unfold spectralDensity
  have hlead : Real.exp (-h * x) ≤ Real.exp (-D.γ₁ * x) :=
    Real.exp_le_exp.mpr (by nlinarith [D.γ₁_le])
  have hsum_maj : Summable (fun n : ℕ => ((4 + H ^ 2) * Real.exp (-H * x)) * ((1 : ℝ) / (4 + (D.γ_tail n).re ^ 2))) :=
    D.tail_summable_weight.mul_left _
  have hterm_le : ∀ n : ℕ,
      ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖ ≤
        ((4 + H ^ 2) * Real.exp (-H * x)) * ((1 : ℝ) / (4 + (D.γ_tail n).re ^ 2)) := by
    intro n
    set v : ℝ := (D.γ_tail n).re
    have hvH : H ≤ v := D.tail_re_ge n
    let u : ℝ := v - H
    have hu_nn : 0 ≤ u := by dsimp only [u]; linarith
    have hpoly_exp : 1 + u + u ^ 2 / 2 ≤ Real.exp (u * x) := by
      have h3 := Real.sum_le_exp_of_nonneg hu_nn 3
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h3
      exact h3.trans (Real.exp_le_exp.mpr (by nlinarith))
    -- Key universal inequality: `4 + (H + u)² ≤ (4 + H²)(1 + u + u²/2)` for ALL `H ≥ 0, u ≥ 0`
    have hquad : 4 + v ^ 2 ≤ (4 + H ^ 2) * Real.exp (u * x) := by
      have hv_eq : v = H + u := by dsimp only [u]; ring
      have h2H : 2 * H ≤ 4 + H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
      have hH2 : 1 ≤ (4 + H ^ 2) / 2 := by nlinarith [sq_nonneg H]
      have hstep1 : 4 + (H + u) ^ 2 ≤ (4 + H ^ 2) * (1 + u + u ^ 2 / 2) := by
        nlinarith [sq_nonneg u]
      rw [hv_eq]
      exact hstep1.trans (mul_le_mul_of_nonneg_left hpoly_exp (by positivity))
    have hexp_split : Real.exp (-v * x) * Real.exp (u * x) = Real.exp (-H * x) := by
      rw [← Real.exp_add]; congr 1; dsimp only [u]; ring
    have hexp_le : Real.exp (-v * x) ≤ ((4 + H ^ 2) * Real.exp (-H * x)) * ((1 : ℝ) / (4 + v ^ 2)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      calc Real.exp (-v * x) * (4 + v ^ 2)
          ≤ Real.exp (-v * x) * ((4 + H ^ 2) * Real.exp (u * x)) :=
            mul_le_mul_of_nonneg_left hquad (Real.exp_pos _).le
        _ = (4 + H ^ 2) * (Real.exp (-v * x) * Real.exp (u * x)) := by ring
        _ = (4 + H ^ 2) * Real.exp (-H * x) := by rw [hexp_split]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-v * x) * |Real.cos ((D.γ_tail n).im * x)|
        ≤ Real.exp (-v * x) * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-v * x) := mul_one _
      _ ≤ ((4 + H ^ 2) * Real.exp (-H * x)) * ((1 : ℝ) / (4 + v ^ 2)) := hexp_le
  have hsum_abs : Summable (fun n : ℕ => ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hsum_maj
  have htail_bd : |∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)| ≤
      C * (4 + H ^ 2) * Real.exp (-H * x) := by
    calc |∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)|
        = ‖∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' n : ℕ, ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖ :=
          norm_tsum_le_tsum_norm hsum_abs
      _ ≤ ∑' n : ℕ, ((4 + H ^ 2) * Real.exp (-H * x)) * ((1 : ℝ) / (4 + (D.γ_tail n).re ^ 2)) :=
          hsum_abs.tsum_le_tsum hterm_le hsum_maj
      _ = ((4 + H ^ 2) * Real.exp (-H * x)) * ∑' n : ℕ, (1 : ℝ) / (4 + (D.γ_tail n).re ^ 2) := tsum_mul_left
      _ ≤ ((4 + H ^ 2) * Real.exp (-H * x)) * C :=
          mul_le_mul_of_nonneg_left D.tail_weight_sum_lt.le (by positivity)
      _ = C * (4 + H ^ 2) * Real.exp (-H * x) := by ring
  have hlow_nn : 0 ≤ (D.γ_low.map (fun γ => Real.exp (-γ * x))).sum :=
    list_exp_sum_nonneg D.γ_low x
  linarith [(abs_le.mp htail_bd).1]

/-- Continuity of `spectralDensity D` on `(0, ∞)` via locally uniform Weierstrass M-test. -/
theorem spectralDensity_continuousOn {h H C : ℝ} (D : SpectralLowZeroData h H C) :
    ContinuousOn (spectralDensity D) (Ioi (0 : ℝ)) := by
  intro x₀ hx₀
  have hx₀_pos : 0 < x₀ := hx₀
  let ε : ℝ := x₀ / 2
  have hε_pos : 0 < ε := half_pos hx₀_pos
  have hcont_tail : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x))
      (Ioi ε) := by
    have hbound : ∀ (n : ℕ) (x : ℝ), x ∈ Ioi ε →
        ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖ ≤
          (4 + 2 / ε ^ 2) * ((1 : ℝ) / (4 + (D.γ_tail n).re ^ 2)) := by
      intro n x hx
      have hxgt : ε < x := hx
      set v : ℝ := (D.γ_tail n).re
      have hv0 : 0 ≤ v := by linarith [D.H_ge_one, D.tail_re_ge n]
      have hexp_mono : Real.exp (-v * x) ≤ Real.exp (-v * ε) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h1 : (1 : ℝ) ≤ Real.exp (v * ε) := Real.one_le_exp (by nlinarith)
      have h2 : (v * ε) ^ 2 / 2 ≤ Real.exp (v * ε) := by
        simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (v * ε) (by nlinarith) 2
      have hv2 : v ^ 2 ≤ (2 / ε ^ 2) * Real.exp (v * ε) := by
        rw [mul_pow] at h2
        have hε2 : 0 < ε ^ 2 := pow_pos hε_pos 2
        calc v ^ 2 = (v ^ 2 * ε ^ 2) / ε ^ 2 := by field_simp [hε2.ne']
          _ ≤ (2 * Real.exp (v * ε)) / ε ^ 2 := div_le_div_of_nonneg_right (by linarith) hε2.le
          _ = (2 / ε ^ 2) * Real.exp (v * ε) := by ring
      have hcomb : 4 + v ^ 2 ≤ (4 + 2 / ε ^ 2) * Real.exp (v * ε) := by nlinarith
      have hexp_le : Real.exp (-v * ε) ≤ (4 + 2 / ε ^ 2) * ((1 : ℝ) / (4 + v ^ 2)) := by
        rw [show -v * ε = -(v * ε) by ring, Real.exp_neg, mul_one_div, le_div_iff₀ (by positivity)]
        have hpos : 0 < Real.exp (v * ε) := Real.exp_pos _
        calc (Real.exp (v * ε))⁻¹ * (4 + v ^ 2)
            ≤ (Real.exp (v * ε))⁻¹ * ((4 + 2 / ε ^ 2) * Real.exp (v * ε)) :=
              mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hpos.le)
          _ = 4 + 2 / ε ^ 2 := by field_simp [hpos.ne']
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-v * x) * |Real.cos ((D.γ_tail n).im * x)|
          ≤ Real.exp (-v * x) * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        _ = Real.exp (-v * x) := mul_one _
        _ ≤ Real.exp (-v * ε) := hexp_mono
        _ ≤ (4 + 2 / ε ^ 2) * ((1 : ℝ) / (4 + v ^ 2)) := hexp_le
    have hcont_sub : Continuous (fun p : Ioi ε =>
        ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * p.val) * Real.cos ((D.γ_tail n).im * p.val)) :=
      continuous_tsum (fun n => by fun_prop) (D.tail_summable_weight.mul_left (4 + 2 / ε ^ 2))
        (fun n p => hbound n p.val p.property)
    exact continuousOn_iff_continuous_domRestrict.mpr hcont_sub
  have hx₀_mem : x₀ ∈ Ioi ε := by dsimp only [ε]; change x₀ / 2 < x₀; linarith
  have hcont_at : ContinuousAt (spectralDensity D) x₀ :=
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (-D.γ₁ * x)).continuousAt.add
      (list_exp_sum_continuous D.γ_low).continuousAt).add
      (hcont_tail.continuousAt (isOpen_Ioi.mem_nhds hx₀_mem))
  exact hcont_at.continuousWithinAt

/-- Finiteness of all power moments `y ↦ y^k * spectralDensity D (Real.sqrt y)` on `(0, ∞)`
for ANY `SpectralLowZeroData h H C` (via `y = x²` and Tonelli's theorem). -/
theorem spectralMoment_integrable {h H C : ℝ} (D : SpectralLowZeroData h H C) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ k * spectralDensity D (Real.sqrt y)) (Ioi (0 : ℝ)) volume := by
  have himg : (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext y; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact pow_pos hx 2
    · intro hy; exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have hinj : Set.InjOn (fun x : ℝ => x ^ 2) (Ioi (0 : ℝ)) := fun a ha b hb hab => by
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    nlinarith [sq_nonneg (a - b)]
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x) (Ioi (0 : ℝ)) x :=
    fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  rw [← himg, MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have hrew : (fun x : ℝ => |2 * x| • ((x ^ 2) ^ k * spectralDensity D (Real.sqrt (x ^ 2)))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
      fun x : ℝ => 2 * (x ^ (2 * k + 1) * spectralDensity D x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, abs_of_pos (by linarith), Real.sqrt_sq hx0.le, ← pow_mul, pow_succ]
    ring
  refine Integrable.congr ?_ hrew.symm
  refine MeasureTheory.Integrable.const_mul ?_ 2
  have hcont : ContinuousOn (fun x : ℝ => x ^ (2 * k + 1) * spectralDensity D x) (Ioi (0 : ℝ)) :=
    (continuousOn_pow (2 * k + 1)).mul (spectralDensity_continuousOn D)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * k + 1) * spectralDensity D x)
      (volume.restrict (Ioi (0 : ℝ))) := hcont.aestronglyMeasurable measurableSet_Ioi
  let leadLow : ℝ → ℝ := fun x =>
    Real.exp (-D.γ₁ * x) + (D.γ_low.map (fun γ => Real.exp (-γ * x))).sum
  have hleadLow_nn : ∀ x : ℝ, 0 ≤ leadLow x := fun x =>
    add_nonneg (Real.exp_pos _).le (list_exp_sum_nonneg D.γ_low x)
  have hleadLow_meas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((continuous_pow (2 * k + 1)).mul
        ((by fun_prop : Continuous fun x : ℝ => Real.exp (-D.γ₁ * x)).add
          (list_exp_sum_continuous D.γ_low))).measurable
  have hlead_int : IntegrableOn (fun x : ℝ => x ^ (2 * k + 1) * leadLow x) (Ioi (0 : ℝ)) volume := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (2 * k + 1) * Real.exp (-D.γ₁ * x)) (Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_neg_mul_pow_sp (2 * k + 1) D.γ₁_pos).congr_fun (fun x _ => by ring) measurableSet_Ioi
    have h2 : IntegrableOn (fun x : ℝ => x ^ (2 * k + 1) * (D.γ_low.map (fun γ => Real.exp (-γ * x))).sum)
        (Ioi (0 : ℝ)) volume := list_exp_sum_pow_integrable D.γ_low D.γ_low_pos (2 * k + 1)
    exact (h1.add h2).congr_fun (fun x _ => by dsimp only [leadLow, Pi.add_apply]; ring) measurableSet_Ioi
  let g_tail : ℝ → ENNReal := fun x =>
    ∑' n : ℕ, ENNReal.ofReal (x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x))
  have hlint_tail : ∫⁻ x in Ioi (0 : ℝ), g_tail x < ⊤ := by
    dsimp only [g_tail]
    rw [MeasureTheory.lintegral_tsum fun n => (by fun_prop : Measurable fun x : ℝ =>
        ENNReal.ofReal (x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x))).aemeasurable]
    have hterm_lint : ∀ n : ℕ,
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x)) =
          ENNReal.ofReal (((2 * k + 1).factorial : ℝ) / (D.γ_tail n).re ^ (2 * k + 2)) := by
      intro n
      have hv_pos : 0 < (D.γ_tail n).re := by linarith [D.H_ge_one, D.tail_re_ge n]
      have hint_n : IntegrableOn (fun x : ℝ => x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x))
          (Ioi (0 : ℝ)) volume :=
        (integrableOn_exp_neg_mul_pow_sp (2 * k + 1) hv_pos).congr_fun (fun x _ => by ring) measurableSet_Ioi
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_n
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le)]
      congr 1
      have hcomm : (fun x : ℝ => x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x)) =
          fun x : ℝ => Real.exp (-(D.γ_tail n).re * x) * x ^ (2 * k + 1) := by funext x; ring
      rw [hcomm, realLaplace_monomial_pos_sp (2 * k + 1) hv_pos]
    simp_rw [hterm_lint]
    let C_k : ℝ := 5 * ((2 * k + 1).factorial : ℝ)
    have hsum_R : Summable (fun n : ℕ => ((2 * k + 1).factorial : ℝ) / (D.γ_tail n).re ^ (2 * k + 2)) := by
      refine Summable.of_nonneg_of_le (fun n => by
          have hv1 : 1 ≤ (D.γ_tail n).re := D.H_ge_one.trans (D.tail_re_ge n); positivity)
        (fun n => ?_) (D.tail_summable_weight.mul_left C_k)
      set v : ℝ := (D.γ_tail n).re
      have hv1 : 1 ≤ v := D.H_ge_one.trans (D.tail_re_ge n)
      have hv2k : (1 : ℝ) ≤ v ^ (2 * k) := one_le_pow₀ hv1
      have hpow_ge : v ^ 2 ≤ v ^ (2 * k + 2) := by
        rw [pow_add]; exact le_mul_of_one_le_left (by positivity) hv2k
      have h4v : 4 + v ^ 2 ≤ 5 * v ^ 2 := by nlinarith
      calc ((2 * k + 1).factorial : ℝ) / v ^ (2 * k + 2)
          ≤ ((2 * k + 1).factorial : ℝ) / v ^ 2 :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hpow_ge
        _ ≤ C_k * ((1 : ℝ) / (4 + v ^ 2)) := by
            dsimp only [C_k]
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [Nat.cast_nonneg (α := ℝ) (2 * k + 1).factorial]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
        have hv1 : 1 ≤ (D.γ_tail n).re := D.H_ge_one.trans (D.tail_re_ge n); positivity) hsum_R]
    exact ENNReal.ofReal_lt_top
  refine ⟨hmeas, ?_⟩
  have hpt_enorm : ∀ x ∈ Ioi (0 : ℝ),
      ‖x ^ (2 * k + 1) * spectralDensity D x‖ₑ ≤
        ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x) + g_tail x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxp : 0 ≤ x ^ (2 * k + 1) := pow_nonneg hx0.le _
    rw [Real.eNorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hxp]
    have hsum_n : Summable (fun n : ℕ => Real.exp (-(D.γ_tail n).re * x)) := by
      have hmaj := D.tail_summable_weight.mul_left (4 + 2 / x ^ 2)
      refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_) hmaj
      set v : ℝ := (D.γ_tail n).re
      have hv0 : 0 ≤ v := by linarith [D.H_ge_one, D.tail_re_ge n]
      have h1 : (1 : ℝ) ≤ Real.exp (v * x) := Real.one_le_exp (mul_nonneg hv0 hx0.le)
      have h2 : (v * x) ^ 2 / 2 ≤ Real.exp (v * x) := by
        simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (v * x) (mul_nonneg hv0 hx0.le) 2
      have hv2 : v ^ 2 ≤ (2 / x ^ 2) * Real.exp (v * x) := by
        rw [mul_pow] at h2
        have hx2 : 0 < x ^ 2 := pow_pos hx0 2
        calc v ^ 2 = (v ^ 2 * x ^ 2) / x ^ 2 := by field_simp [hx2.ne']
          _ ≤ (2 * Real.exp (v * x)) / x ^ 2 := div_le_div_of_nonneg_right (by linarith) hx2.le
          _ = (2 / x ^ 2) * Real.exp (v * x) := by ring
      have hcomb : 4 + v ^ 2 ≤ (4 + 2 / x ^ 2) * Real.exp (v * x) := by nlinarith
      rw [show -v * x = -(v * x) by ring, Real.exp_neg, mul_one_div, le_div_iff₀ (by positivity)]
      have hpos : 0 < Real.exp (v * x) := Real.exp_pos _
      calc (Real.exp (v * x))⁻¹ * (4 + v ^ 2)
          ≤ (Real.exp (v * x))⁻¹ * ((4 + 2 / x ^ 2) * Real.exp (v * x)) :=
            mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hpos.le)
        _ = 4 + 2 / x ^ 2 := by field_simp [hpos.ne']
    have hK_le : |spectralDensity D x| ≤ leadLow x + ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) := by
      have hsd : spectralDensity D x = leadLow x +
          ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x) := rfl
      rw [hsd]
      have habs_s : Summable (fun n : ℕ => ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun n => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) hsum_n
      calc |leadLow x + ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)|
          ≤ |leadLow x| + |∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)| :=
            abs_add_le _ _
        _ ≤ leadLow x + ∑' n : ℕ, ‖Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)‖ := by
            rw [abs_of_nonneg (hleadLow_nn x), ← Real.norm_eq_abs]
            exact add_le_add le_rfl (norm_tsum_le_tsum_norm habs_s)
        _ ≤ leadLow x + ∑' n : ℕ, Real.exp (-(D.γ_tail n).re * x) := by
            exact add_le_add le_rfl (habs_s.tsum_le_tsum (fun n => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) hsum_n)
    have hmul_le : x ^ (2 * k + 1) * |spectralDensity D x| ≤
        x ^ (2 * k + 1) * leadLow x + ∑' n : ℕ, x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x) := by
      rw [tsum_mul_left, ← mul_add]
      exact mul_le_mul_of_nonneg_left hK_le hxp
    calc ENNReal.ofReal (x ^ (2 * k + 1) * |spectralDensity D x|)
        ≤ ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x +
            ∑' n : ℕ, x ^ (2 * k + 1) * Real.exp (-(D.γ_tail n).re * x)) :=
          ENNReal.ofReal_le_ofReal hmul_le
      _ = ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x) + g_tail x := by
          rw [ENNReal.ofReal_add (mul_nonneg hxp (hleadLow_nn x)) (tsum_nonneg fun _ => by positivity),
            ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum_n.mul_left _)]
  have hlint_le : ∫⁻ x in Ioi (0 : ℝ), ‖x ^ (2 * k + 1) * spectralDensity D x‖ₑ ≤
      (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x)) +
        ∫⁻ x in Ioi (0 : ℝ), g_tail x := by
    rw [← MeasureTheory.lintegral_add_left hleadLow_meas]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpt_enorm x hx
  have hlead_lt : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * k + 1) * leadLow x) < ⊤ := by
    have hfin := hlead_int.2
    refine lt_of_le_of_lt ?_ hfin
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le _) (hleadLow_nn x))]
  exact lt_of_le_of_lt hlint_le (ENNReal.add_lt_top.mpr ⟨hlead_lt, hlint_tail⟩)

/-- **Master Hankel Positive Definiteness for Any Positive `SpectralLowZeroData`**:
Whenever `spectralDensity D` is strictly positive on `(0, ∞)`, ALL shifted Hankel moment matrices
`spectralHankel D s n` are strictly positive definite (via Codex's `square_integral_pos` + `hankel_form`). -/
theorem spectralHankel_posDef_of_pos {h H C : ℝ} (D : SpectralLowZeroData h H C)
    (hpos : ∀ x > 0, 0 < spectralDensity D x) (s n : ℕ) :
    (spectralHankel D s n).PosDef := by
  let w : ℝ → ℝ := fun y => y ^ s * spectralDensity D (Real.sqrt y)
  have hw_cont : ContinuousOn w (Ioi (0 : ℝ)) :=
    (continuousOn_pow s).mul ((spectralDensity_continuousOn D).comp Real.continuous_sqrt.continuousOn
      fun y hy => Real.sqrt_pos.mpr hy)
  have hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))) :=
    (hw_cont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y := fun y hy =>
    mul_pos (pow_pos hy s) (hpos _ (Real.sqrt_pos.mpr hy))
  have hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume := fun k => by
    refine (spectralMoment_integrable D (k + s)).congr_fun (fun y _ => ?_) measurableSet_Ioi
    dsimp only [w]; rw [pow_add]; ring
  have hpd := hankel_posDef_of_positive_weight hw_meas hw_pos hmom n
  convert hpd using 1
  ext i j
  simp only [spectralHankel, Matrix.of_apply, spectralMoment]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  dsimp only [w]; rw [pow_add]; ring

/-- Immediate moment strict positivity corollary (the `1 × 1` Hankel matrix at shift `k`). -/
theorem spectralMoment_pos_of_pos {h H C : ℝ} (D : SpectralLowZeroData h H C)
    (hpos : ∀ x > 0, 0 < spectralDensity D x) (k : ℕ) :
    0 < spectralMoment D k := by
  have h1 := (spectralHankel_posDef_of_pos D hpos k 1).diag_pos (i := (0 : Fin 1))
  simpa [spectralHankel] using h1

/-! ### 4. Concrete RH-Free / GRH-Free Parameter Regimes (`(15, 20, 1)`, `(7, 16, 10)`, `(10, 16, 10)`)

**Honesty boundary**: Every theorem below is parameterized by `SpectralLowZeroData h H C`, which is
NOT connected in Lean to the zeros of `completedXi`, $L(s, \chi_{-4})$, or $L(s, \Delta)$. That
$\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$ enumerate exactly those zeros with
multiplicity (with `γ_low = []` for $\xi$, `[10.24..., 12.99...]` for $\beta$, `[13.91...]` for
$\Delta$), the low-height verification, the Hadamard bound $\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$,
and the identity relating `spectralMoment` to the Taylor coefficients of $\xi'/\xi$ are all external.
The theorems hold for any data satisfying the fields. -/

/-- **Riemann-$\xi$ Parameter Regime `(15, 20, 1)` (RH-Free)**:
`(99 / 100) * exp (-15 * x) ≤ spectralDensity D x` for all `x > 0` and any
`D : SpectralLowZeroData 15 20 1` (intended for $\xi$ with `γ_low = []`).
The structure is NOT connected in Lean to the zeros of `completedXi`, $L(s, \chi_{-4})$, or
$L(s, \Delta)$; see `SpectralLowZeroData`. -/
theorem xiDensity_ge_lower_bound (D : SpectralLowZeroData 15 20 1) {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-15 * x) ≤ spectralDensity D x :=
  xi_lower_from_estimates (spectralDensity D)
    (spectralDensity_small_lower D)
    (fun y hy => by simpa [show (1 : ℝ) * (4 + 20 ^ 2) = 404 by norm_num] using spectralDensity_large_lower D y hy) hx

/-- Strict positivity `0 < spectralDensity D x` for any `D : SpectralLowZeroData 15 20 1`
(unlinked in Lean to `completedXi`; see `SpectralLowZeroData`). -/
theorem xiDensity_pos (D : SpectralLowZeroData 15 20 1) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  lt_of_lt_of_le (by positivity) (xiDensity_ge_lower_bound D hx)

/-- Strict positivity `0 < spectralMoment D k` for any `D : SpectralLowZeroData 15 20 1`
(unlinked in Lean to `completedXi` or Taylor coefficients of $\xi'/\xi$; see `SpectralLowZeroData`). -/
theorem xiMoment_pos (D : SpectralLowZeroData 15 20 1) (k : ℕ) :
    0 < spectralMoment D k :=
  spectralMoment_pos_of_pos D (fun _ hx => xiDensity_pos D hx) k

/-- Strict positive definiteness of `(spectralHankel D s n)` for any `D : SpectralLowZeroData 15 20 1`
(unlinked in Lean to `completedXi`; see `SpectralLowZeroData`). -/
theorem xiHankel_posDef (D : SpectralLowZeroData 15 20 1) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  spectralHankel_posDef_of_pos D (fun _ hx => xiDensity_pos D hx) s n

/-- Strict positivity of `(spectralHankel D s n).det` for any `D : SpectralLowZeroData 15 20 1`
(unlinked in Lean to `completedXi`; see `SpectralLowZeroData`). -/
theorem xiHankel_det_pos (D : SpectralLowZeroData 15 20 1) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  (xiHankel_posDef D s n).det_pos

/-- **Dirichlet-$\beta$ Parameter Regime `(7, 16, 10)` (GRH-Free)**:
`(99 / 100) * exp (-7 * x) ≤ spectralDensity D x` for all `x > 0` and any
`D : SpectralLowZeroData 7 16 10` (intended for Dirichlet $\beta$ with `γ_low = [10.24..., 12.99...]`).
The structure is NOT connected in Lean to the zeros of `completedXi`, $L(s, \chi_{-4})$, or
$L(s, \Delta)$; see `SpectralLowZeroData`. -/
theorem dirichletBetaDensity_ge_lower_bound (D : SpectralLowZeroData 7 16 10) {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-7 * x) ≤ spectralDensity D x :=
  dirichletBeta_lower_from_estimates (spectralDensity D)
    (spectralDensity_small_lower D)
    (fun y hy => by simpa [show (10 : ℝ) * (4 + 16 ^ 2) = 2600 by norm_num] using spectralDensity_large_lower D y hy) hx

/-- Strict positivity `0 < spectralDensity D x` for any `D : SpectralLowZeroData 7 16 10`
(unlinked in Lean to $L(s, \chi_{-4})$; see `SpectralLowZeroData`). -/
theorem dirichletBetaDensity_pos (D : SpectralLowZeroData 7 16 10) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  lt_of_lt_of_le (by positivity) (dirichletBetaDensity_ge_lower_bound D hx)

/-- Strict positivity `0 < spectralMoment D k` for any `D : SpectralLowZeroData 7 16 10`
(unlinked in Lean to $L(s, \chi_{-4})$; see `SpectralLowZeroData`). -/
theorem dirichletBetaMoment_pos (D : SpectralLowZeroData 7 16 10) (k : ℕ) :
    0 < spectralMoment D k :=
  spectralMoment_pos_of_pos D (fun _ hx => dirichletBetaDensity_pos D hx) k

/-- Strict positive definiteness of `(spectralHankel D s n)` for any `D : SpectralLowZeroData 7 16 10`
(unlinked in Lean to $L(s, \chi_{-4})$; see `SpectralLowZeroData`). -/
theorem dirichletBetaHankel_posDef (D : SpectralLowZeroData 7 16 10) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  spectralHankel_posDef_of_pos D (fun _ hx => dirichletBetaDensity_pos D hx) s n

/-- Strict positivity of `(spectralHankel D s n).det` for any `D : SpectralLowZeroData 7 16 10`
(unlinked in Lean to $L(s, \chi_{-4})$; see `SpectralLowZeroData`). -/
theorem dirichletBetaHankel_det_pos (D : SpectralLowZeroData 7 16 10) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  (dirichletBetaHankel_posDef D s n).det_pos

/-- **Ramanujan-$\Delta$ Parameter Regime `(10, 16, 10)` (GRH-Free)**:
`(99 / 100) * exp (-10 * x) ≤ spectralDensity D x` for all `x > 0` and any
`D : SpectralLowZeroData 10 16 10` (intended for Ramanujan's $\Delta$ with `γ_low = [13.91...]`).
The structure is NOT connected in Lean to the zeros of `completedXi`, $L(s, \chi_{-4})$, or
$L(s, \Delta)$; see `SpectralLowZeroData`. -/
theorem ramanujanDeltaDensity_ge_lower_bound (D : SpectralLowZeroData 10 16 10) {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-10 * x) ≤ spectralDensity D x :=
  ramanujanDelta_lower_from_estimates (spectralDensity D)
    (spectralDensity_small_lower D)
    (fun y hy => by simpa [show (10 : ℝ) * (4 + 16 ^ 2) = 2600 by norm_num] using spectralDensity_large_lower D y hy) hx

/-- Strict positivity `0 < spectralDensity D x` for any `D : SpectralLowZeroData 10 16 10`
(unlinked in Lean to $L(s, \Delta)$; see `SpectralLowZeroData`). -/
theorem ramanujanDeltaDensity_pos (D : SpectralLowZeroData 10 16 10) {x : ℝ} (hx : 0 < x) :
    0 < spectralDensity D x :=
  lt_of_lt_of_le (by positivity) (ramanujanDeltaDensity_ge_lower_bound D hx)

/-- Strict positivity `0 < spectralMoment D k` for any `D : SpectralLowZeroData 10 16 10`
(unlinked in Lean to $L(s, \Delta)$; see `SpectralLowZeroData`). -/
theorem ramanujanDeltaMoment_pos (D : SpectralLowZeroData 10 16 10) (k : ℕ) :
    0 < spectralMoment D k :=
  spectralMoment_pos_of_pos D (fun _ hx => ramanujanDeltaDensity_pos D hx) k

/-- Strict positive definiteness of `(spectralHankel D s n)` for any `D : SpectralLowZeroData 10 16 10`
(unlinked in Lean to $L(s, \Delta)$; see `SpectralLowZeroData`). -/
theorem ramanujanDeltaHankel_posDef (D : SpectralLowZeroData 10 16 10) (s n : ℕ) :
    (spectralHankel D s n).PosDef :=
  spectralHankel_posDef_of_pos D (fun _ hx => ramanujanDeltaDensity_pos D hx) s n

/-- Strict positivity of `(spectralHankel D s n).det` for any `D : SpectralLowZeroData 10 16 10`
(unlinked in Lean to $L(s, \Delta)$; see `SpectralLowZeroData`). -/
theorem ramanujanDeltaHankel_det_pos (D : SpectralLowZeroData 10 16 10) (s n : ℕ) :
    0 < (spectralHankel D s n).det :=
  (ramanujanDeltaHankel_posDef D s n).det_pos

/-! ### 5. Subtracted Compact Hyperbolic Spectral Measure `dν(y) = y K_X(√y) dy` ($d = 2, 3$)

Following `spectral-positivity.md`, for a closed connected hyperbolic manifold $X$ of dimension
$d = 2$ or $3$, retaining the oscillatory Laplace eigenvalues `λ_j > ((d-1)/2)²` with spectral
parameters `r_j = √(λ_j - a²) > 0` gives `K_X(x) = ∑_j e^{-r_j x} > 0`. By Weyl's law,
`∑_j r_j^{-4} < ∞` (whereas `∑_j r_j^{-2} = ∞`), so the subtracted measure `dν(y) = y K_X(√y) dy`
has finite moments `ν_k = 2 (2k + 3)! ∑_j r_j^{-(2k+4)}` and strictly positive-definite shifted
Hankel matrices via the exact same `hankel_posDef_of_positive_weight` engine.

**Honesty boundary**: The link to Laplace eigenvalues of an actual hyperbolic manifold (which
exceptional modes are subtracted, multiplicities, and Weyl's law giving $\sum r_j^{-4} < \infty$
in $d = 2, 3$) is outside Lean; positivity of the exponential sum is immediate and the substantive
formalized content is continuity, integrability, the exact factorial-spectral moment identity, and
strict Hankel positive definiteness.
-/

/-- Parameterized oscillatory spectral data for a compact hyperbolic manifold $X$ in dimension
$d = 2$ or $3$ (with exceptional/threshold modes `λ ≤ a²` already subtracted).

**Honesty boundary**: The link to Laplace eigenvalues of an actual hyperbolic manifold (which
exceptional modes are subtracted, multiplicities, and Weyl's law giving $\sum r_j^{-4} < \infty$
in $d = 2, 3$) is outside Lean; positivity of the exponential sum is immediate and the substantive
formalized content is continuity, integrability, the exact factorial-spectral moment identity, and
strict Hankel positive definiteness. -/
structure SubtractedHyperbolicSpectralData where
  /-- Oscillatory spectral parameters `r_j = √(λ_j - a²) > 0` (counted with multiplicity). -/
  r : ℕ → ℝ
  /-- Positive spectral gap `r_min > 0` above the threshold `a²`. -/
  r_min : ℝ
  r_min_pos : 0 < r_min
  /-- Uniform lower bound `r_min ≤ r j` for all retained modes. -/
  r_ge : ∀ j : ℕ, r_min ≤ r j
  /-- Weyl-law convergence `∑_j r_j^{-4} < ∞` (valid in dimensions `d = 2` and `d = 3`). -/
  summable_inv_pow_four : Summable (fun j : ℕ => (r j)⁻¹ ^ 4)

/-- The oscillatory hyperbolic spectral density `K_X(x) = ∑_j e^{-r_j x}` for `x > 0`. -/
@[expose] def hyperbolicSpectralDensity (D : SubtractedHyperbolicSpectralData) (x : ℝ) : ℝ :=
  ∑' j : ℕ, Real.exp (-D.r j * x)

/-- Moments of the subtracted hyperbolic measure `dν(y) = y K_X(√y) dy`:
`ν_k = ∫_{0}^{∞} y^{k+1} K_X(√y) dy`. -/
@[expose] def subtractedHyperbolicMoment (D : SubtractedHyperbolicSpectralData) (k : ℕ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y ^ (k + 1) * hyperbolicSpectralDensity D (Real.sqrt y)

/-- Shifted `n × n` Hankel matrix `(ν_{i + j + s})_{0 ≤ i, j < n}` of the subtracted hyperbolic
measure `dν(y) = y K_X(√y) dy`. -/
@[expose] def subtractedHyperbolicHankel (D : SubtractedHyperbolicSpectralData) (s n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => subtractedHyperbolicMoment D (i.val + j.val + s)

private lemma exp_neg_mul_le_24_div_pow_four {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    Real.exp (-r * x) ≤ (24 / x ^ 4) * r⁻¹ ^ 4 := by
  have h4 := Real.pow_div_factorial_le_exp (r * x) (mul_nonneg hr.le hx.le) 4
  have hfac4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac4, mul_pow] at h4
  have hpos_e : 0 < Real.exp (r * x) := Real.exp_pos _
  have h4' : r ^ 4 * x ^ 4 ≤ 24 * Real.exp (r * x) := by linarith
  have hr4 : 0 < r ^ 4 := pow_pos hr 4
  have hx4 : 0 < x ^ 4 := pow_pos hx 4
  rw [show -r * x = -(r * x) by ring, Real.exp_neg, inv_pow]
  calc (Real.exp (r * x))⁻¹
      = (r ^ 4 * x ^ 4) / (r ^ 4 * x ^ 4 * Real.exp (r * x)) := by
        field_simp [hr4.ne', hx4.ne', hpos_e.ne']
    _ ≤ (24 * Real.exp (r * x)) / (r ^ 4 * x ^ 4 * Real.exp (r * x)) :=
        div_le_div_of_nonneg_right h4' (by positivity)
    _ = (24 / x ^ 4) * (r ^ 4)⁻¹ := by
        field_simp [hr4.ne', hx4.ne', hpos_e.ne']

private lemma hyperbolic_exp_summable (D : SubtractedHyperbolicSpectralData) {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => Real.exp (-D.r j * x)) := by
  have hmaj : Summable (fun j : ℕ => (24 / x ^ 4) * (D.r j)⁻¹ ^ 4) :=
    D.summable_inv_pow_four.mul_left (24 / x ^ 4)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun j => ?_) hmaj
  exact exp_neg_mul_le_24_div_pow_four (lt_of_lt_of_le D.r_min_pos (D.r_ge j)) hx

/-- Strict positivity `K_X(x) > 0` for every `x > 0`. -/
theorem hyperbolicSpectralDensity_pos (D : SubtractedHyperbolicSpectralData) {x : ℝ} (hx : 0 < x) :
    0 < hyperbolicSpectralDensity D x := by
  unfold hyperbolicSpectralDensity
  have hle : Real.exp (-D.r 0 * x) ≤ ∑' j : ℕ, Real.exp (-D.r j * x) :=
    (hyperbolic_exp_summable D hx).le_tsum 0 fun _ _ => (Real.exp_pos _).le
  exact lt_of_lt_of_le (Real.exp_pos _) hle

/-- Continuity of `hyperbolicSpectralDensity D` on `(0, ∞)`. -/
theorem hyperbolicSpectralDensity_continuousOn (D : SubtractedHyperbolicSpectralData) :
    ContinuousOn (hyperbolicSpectralDensity D) (Ioi (0 : ℝ)) := by
  intro x₀ hx₀
  have hx₀_pos : 0 < x₀ := hx₀
  let ε : ℝ := x₀ / 2
  have hε_pos : 0 < ε := half_pos hx₀_pos
  have hcont_sub : Continuous (fun p : Ioi ε => ∑' j : ℕ, Real.exp (-D.r j * p.val)) := by
    refine continuous_tsum (fun j => by fun_prop)
      (D.summable_inv_pow_four.mul_left (24 / ε ^ 4)) fun j p => ?_
    have hp : ε < p.val := p.property
    have hr_pos : 0 < D.r j := lt_of_lt_of_le D.r_min_pos (D.r_ge j)
    have hmono : Real.exp (-D.r j * p.val) ≤ Real.exp (-D.r j * ε) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hmono.trans (exp_neg_mul_le_24_div_pow_four hr_pos hε_pos)
  have hcont_on : ContinuousOn (hyperbolicSpectralDensity D) (Ioi ε) :=
    continuousOn_iff_continuous_domRestrict.mpr hcont_sub
  have hx₀_mem : x₀ ∈ Ioi ε := by dsimp only [ε]; change x₀ / 2 < x₀; linarith
  exact (hcont_on.continuousAt (isOpen_Ioi.mem_nhds hx₀_mem)).continuousWithinAt

private lemma hyperbolic_inv_pow_summable (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    Summable (fun j : ℕ => (D.r j)⁻¹ ^ (2 * k + 4)) := by
  have hmaj : Summable (fun j : ℕ => ((D.r_min)⁻¹ ^ (2 * k)) * (D.r j)⁻¹ ^ 4) :=
    D.summable_inv_pow_four.mul_left _
  refine Summable.of_nonneg_of_le (fun j => by have := lt_of_lt_of_le D.r_min_pos (D.r_ge j); positivity)
    (fun j => ?_) hmaj
  have hr_pos : 0 < D.r j := lt_of_lt_of_le D.r_min_pos (D.r_ge j)
  have hinv_le : (D.r j)⁻¹ ≤ (D.r_min)⁻¹ := inv_anti₀ D.r_min_pos (D.r_ge j)
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hr_pos.le) hinv_le _) (by positivity)

/-- **Finiteness & Exact Spectral Moment Formula for the Subtracted Hyperbolic Measure**
(`spectral-positivity.md`, line 45):
For every `k : ℕ`, `y ↦ y^{k+1} K_X(√y)` is integrable on `(0, ∞)` and
`subtractedHyperbolicMoment D k = 2 * (2k + 3)! * ∑' j, (D.r j)⁻¹ ^ (2k + 4)`. -/
theorem subtractedHyperbolicMoment_integrable_and_eq (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (k + 1) * hyperbolicSpectralDensity D (Real.sqrt y)) (Ioi (0 : ℝ)) volume ∧
      subtractedHyperbolicMoment D k =
        2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4) := by
  have himg : (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext y; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact pow_pos hx 2
    · intro hy; exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have hinj : Set.InjOn (fun x : ℝ => x ^ 2) (Ioi (0 : ℝ)) := fun a ha b hb hab => by
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    nlinarith [sq_nonneg (a - b)]
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x) (Ioi (0 : ℝ)) x :=
    fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hrew : (fun x : ℝ => |2 * x| • ((x ^ 2) ^ (k + 1) * hyperbolicSpectralDensity D (Real.sqrt (x ^ 2)))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
      fun x : ℝ => 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, abs_of_pos (by linarith), Real.sqrt_sq hx0.le, ← pow_mul]
    have hpow : x ^ (2 * (k + 1)) * x = x ^ (2 * k + 3) := by
      rw [← pow_succ]; ring
    calc 2 * x * (x ^ (2 * (k + 1)) * hyperbolicSpectralDensity D x)
        = 2 * ((x ^ (2 * (k + 1)) * x) * hyperbolicSpectralDensity D x) := by ring
      _ = 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) := by rw [hpow]
  -- Compute exact `lintegral` via Tonelli's theorem (`lintegral_tsum`)
  have hlint_eq : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) =
      ENNReal.ofReal (2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4)) := by
    have hpt : ∀ x ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) =
          ∑' j : ℕ, ENNReal.ofReal (2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3))) := by
      intro x hx
      have hx0 : 0 < x := hx
      unfold hyperbolicSpectralDensity
      have hmul : 2 * (x ^ (2 * k + 3) * ∑' j : ℕ, Real.exp (-D.r j * x)) =
          ∑' j : ℕ, 2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3)) := by
        rw [← tsum_mul_left, ← tsum_mul_left]
        refine tsum_congr fun j => by ring
      rw [hmul, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        (((hyperbolic_exp_summable D hx0).mul_right _).mul_left _)]
    have hcongr : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) =
        ∫⁻ x in Ioi (0 : ℝ), ∑' j : ℕ, ENNReal.ofReal (2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3))) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpt x hx
    rw [hcongr, MeasureTheory.lintegral_tsum fun j => (by fun_prop : Measurable fun x : ℝ =>
        ENNReal.ofReal (2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3)))).aemeasurable]
    have hterm : ∀ j : ℕ,
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3))) =
          ENNReal.ofReal (2 * ((2 * k + 3).factorial : ℝ) * (D.r j)⁻¹ ^ (2 * k + 4)) := by
      intro j
      have hr_pos : 0 < D.r j := lt_of_lt_of_le D.r_min_pos (D.r_ge j)
      have hint_j : IntegrableOn (fun x : ℝ => 2 * (Real.exp (-D.r j * x) * x ^ (2 * k + 3)))
          (Ioi (0 : ℝ)) volume :=
        (integrableOn_exp_neg_mul_pow_sp (2 * k + 3) hr_pos).const_mul 2
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_j
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (pow_nonneg hx.le _))),
        MeasureTheory.integral_const_mul, realLaplace_monomial_pos_sp (2 * k + 3) hr_pos]
      congr 1; rw [inv_pow, div_eq_mul_inv]; ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by have := lt_of_lt_of_le D.r_min_pos (D.r_ge j); positivity)
      ((hyperbolic_inv_pow_summable D k).mul_left _), tsum_mul_left]
  -- Deduce integrability and exact integral value simultaneously!
  have hcont_x : ContinuousOn (fun x : ℝ => 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) (Ioi (0 : ℝ)) :=
    continuousOn_const.mul ((continuousOn_pow (2 * k + 3)).mul (hyperbolicSpectralDensity_continuousOn D))
  have hint_x : IntegrableOn (fun x : ℝ => 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) (Ioi (0 : ℝ)) volume := by
    refine ⟨hcont_x.aestronglyMeasurable measurableSet_Ioi, ?_⟩
    have hle : ∫⁻ x in Ioi (0 : ℝ), ‖2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)‖ₑ =
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg zero_le_two
        (mul_nonneg (pow_nonneg hx.le _) (hyperbolicSpectralDensity_pos D hx).le))]
    change ∫⁻ x in Ioi (0 : ℝ), ‖2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x)‖ₑ < ⊤
    rw [hle, hlint_eq]
    exact ENNReal.ofReal_lt_top
  have hint_y : IntegrableOn (fun y : ℝ => y ^ (k + 1) * hyperbolicSpectralDensity D (Real.sqrt y)) (Ioi (0 : ℝ)) volume := by
    rw [← himg, MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact hint_x.congr hrew.symm
  have hval_x : ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) =
      2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4) := by
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ => 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg zero_le_two (mul_nonneg (pow_nonneg hx.le _) (hyperbolicSpectralDensity_pos D hx).le)
    have hof := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_x hnn_ae
    rw [hlint_eq] at hof
    have hR_nn : 0 ≤ 2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4) :=
      mul_nonneg (by positivity) (tsum_nonneg fun j => by have := lt_of_lt_of_le D.r_min_pos (D.r_ge j); positivity)
    have hL_nn : 0 ≤ ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) :=
      MeasureTheory.integral_nonneg_of_ae hnn_ae
    exact (ENNReal.ofReal_eq_ofReal_iff hL_nn hR_nn).mp hof
  have hval_y : subtractedHyperbolicMoment D k =
      ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * k + 3) * hyperbolicSpectralDensity D x) := by
    unfold subtractedHyperbolicMoment
    conv_lhs => rw [← himg]
    rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact MeasureTheory.integral_congr_ae hrew
  exact ⟨hint_y, hval_y.trans hval_x⟩

theorem subtractedHyperbolicMoment_integrable (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (k + 1) * hyperbolicSpectralDensity D (Real.sqrt y)) (Ioi (0 : ℝ)) volume :=
  (subtractedHyperbolicMoment_integrable_and_eq D k).1

theorem subtractedHyperbolicMoment_eq_tsum (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    subtractedHyperbolicMoment D k =
      2 * ((2 * k + 3).factorial : ℝ) * ∑' j : ℕ, (D.r j)⁻¹ ^ (2 * k + 4) :=
  (subtractedHyperbolicMoment_integrable_and_eq D k).2

/-- **Strict Positive Definiteness of All Shifted Subtracted Hyperbolic Hankel Matrices ($d = 2, 3$)**,
via Codex's unified `hankel_posDef_of_positive_weight` interface applied to `w(y) = y^{s+1} K_X(√y)`. -/
theorem subtractedHyperbolicHankel_posDef (D : SubtractedHyperbolicSpectralData) (s n : ℕ) :
    (subtractedHyperbolicHankel D s n).PosDef := by
  let w : ℝ → ℝ := fun y => y ^ (s + 1) * hyperbolicSpectralDensity D (Real.sqrt y)
  have hw_cont : ContinuousOn w (Ioi (0 : ℝ)) :=
    (continuousOn_pow (s + 1)).mul ((hyperbolicSpectralDensity_continuousOn D).comp
      Real.continuous_sqrt.continuousOn fun y hy => Real.sqrt_pos.mpr hy)
  have hw_meas : AEMeasurable w (volume.restrict (Ioi (0 : ℝ))) :=
    (hw_cont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hw_pos : ∀ y ∈ Ioi (0 : ℝ), 0 < w y := fun y hy =>
    mul_pos (pow_pos hy (s + 1)) (hyperbolicSpectralDensity_pos D (Real.sqrt_pos.mpr hy))
  have hmom : ∀ k : ℕ, IntegrableOn (fun y : ℝ => y ^ k * w y) (Ioi (0 : ℝ)) volume := fun k => by
    refine (subtractedHyperbolicMoment_integrable D (k + s)).congr_fun (fun y _ => ?_) measurableSet_Ioi
    dsimp only [w]
    rw [show k + s + 1 = k + (s + 1) by omega, pow_add]; ring
  have hpd := hankel_posDef_of_positive_weight hw_meas hw_pos hmom n
  convert hpd using 1
  ext i j
  simp only [subtractedHyperbolicHankel, Matrix.of_apply, subtractedHyperbolicMoment]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  dsimp only [w]
  rw [show i.val + j.val + s + 1 = (i.val + j.val) + (s + 1) by omega, pow_add]; ring

theorem subtractedHyperbolicMoment_pos (D : SubtractedHyperbolicSpectralData) (k : ℕ) :
    0 < subtractedHyperbolicMoment D k := by
  have h1 := (subtractedHyperbolicHankel_posDef D k 1).diag_pos (i := (0 : Fin 1))
  simpa [subtractedHyperbolicHankel] using h1

theorem subtractedHyperbolicHankel_det_pos (D : SubtractedHyperbolicSpectralData) (s n : ℕ) :
    0 < (subtractedHyperbolicHankel D s n).det :=
  (subtractedHyperbolicHankel_posDef D s n).det_pos

end
end PakPrimes.SpectralPositivity
