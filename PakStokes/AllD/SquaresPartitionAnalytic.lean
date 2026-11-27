module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Unconditional Analytic Wave Decomposition for Partitions into Squares (`d = 2`)

Proves 100% unconditionally from Mathlib — using ONLY elementary cotangent partial
fractions (`cot_series_rep`), real Fourier inversion (`Continuous.fourier_fourierInv_eq`),
differentiation of the Fourier transform (`Real.iteratedDeriv_fourier`), and Poisson
summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`), with ZERO contour
integrals and ZERO Mellin transforms — the exact all-orders identity on `X > 0`:
```
2 X⁻³ ∑'_{n : ℕ+} n² / (exp(n² / X²) - 1)
  = sqPartConst - X⁻¹
    - ∑'_{k : ℕ+} ∑'_{m : ℕ+} √m * (sqRay0 * exp(-sqRay0 * k * √m * X)
                                  + sqRay1 * exp(-sqRay1 * k * √m * X))
```
where `sqRay0 = 2 π^(3/2) (1 + I)` and `sqRay1 = 2 π^(3/2) (1 - I)`. -/
public section
namespace CubicTheta.AllD
open Complex Filter Set MeasureTheory
open scoped Topology FourierTransform
noncomputable section

/-- The `d = 2` square-partition leading constant `∫_{-∞}^{∞} u² / (exp(u²) - 1) du`
(equal to `(√π / 2) ζ(3/2)`). -/
def sqPartConst : ℂ :=
  ∫ u : ℝ, if u = 0 then (1 : ℂ) else (((u ^ 2 / (Real.exp (u ^ 2) - 1) : ℝ) : ℂ))

/-- The two `d = 2` Stokes rays `A_{2, 0} = 2 π^(3/2) (1 + I)` and `A_{2, 1} = 2 π^(3/2) (1 - I)`. -/
def sqRay0 : ℂ := ((2 * Real.pi ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (1 + I)
def sqRay1 : ℂ := ((2 * Real.pi ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (1 - I)

/-! ### 1. Elementary Complex Exponential Integrals and Lorentzian Fourier Transforms -/

private lemma integrable_fourier_mul {g : ℝ → ℂ} (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * g x) := by
  have hc : Continuous (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I)) := by fun_prop
  refine hg.norm.mono' (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

private lemma fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ c * g x) ξ = c * 𝓕 g ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

private lemma fourier_add_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have h : (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * (f x + g x)) =
      fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * f x +
        Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * g x := by funext x; ring
  rw [h, integral_add (integrable_fourier_mul hf ξ) (integrable_fourier_mul hg ξ)]

private lemma fourier_sub_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have h : (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * (f x - g x)) =
      fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * f x -
        Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * g x := by funext x; ring
  rw [h, integral_sub (integrable_fourier_mul hf ξ) (integrable_fourier_mul hg ξ)]

private lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ ↦ Real.exp (-c * |y|)) := by
  have h1 : IntegrableOn (fun y : ℝ ↦ Real.exp (-c * y)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have hpos : IntegrableOn (fun y : ℝ ↦ Real.exp (-c * |y|)) (Ioi 0) :=
    h1.congr_fun (fun y hy ↦ by rw [abs_of_pos hy]) measurableSet_Ioi
  have hneg : IntegrableOn (fun y : ℝ ↦ Real.exp (-c * |y|)) (Iic 0) := by
    have hici : IntegrableOn (fun y : ℝ ↦ Real.exp (-c * |y|)) (Ici 0) :=
      Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
    simpa [abs_neg] using hici.comp_neg
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

private lemma integral_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    (∫ y in Ioi (0 : ℝ), Complex.exp (-z * (y : ℂ))) = z⁻¹ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hint : IntegrableOn (fun y : ℝ ↦ Complex.exp (-z * (y : ℂ))) (Ioi 0) := by
    have hr : IntegrableOn (fun y : ℝ ↦ Real.exp (-z.re * y)) (Ioi 0) := by
      simpa using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) 0
    refine hr.mono' ?_ ?_
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
  have hd : ∀ y ∈ Ici (0 : ℝ),
      HasDerivAt (fun x : ℝ ↦ -z⁻¹ * Complex.exp (-z * (x : ℂ)))
        (Complex.exp (-z * (y : ℂ))) y := by
    intro y _
    have h1 : HasDerivAt (fun x : ℝ ↦ -z * (x : ℂ)) (-z) y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-z)
    have h2 := h1.cexp.const_mul (-z⁻¹)
    convert h2 using 1
    field_simp [hz0]
  have hlim : Tendsto (fun y : ℝ ↦ -z⁻¹ * Complex.exp (-z * (y : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hreal : Tendsto (fun y : ℝ ↦ ‖-z⁻¹‖ * Real.exp (-z.re * y)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ ↦ -z.re * y) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hz) tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul ‖-z⁻¹‖
    refine hreal.congr fun y ↦ ?_
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  simpa using hftc

private lemma integral_mul_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    (∫ y in Ioi (0 : ℝ), (y : ℂ) * Complex.exp (-z * (y : ℂ))) = (z ^ 2)⁻¹ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hint : IntegrableOn (fun y : ℝ ↦ (y : ℂ) * Complex.exp (-z * (y : ℂ))) (Ioi 0) := by
    have hhalf : 0 < z.re / 2 := half_pos hz
    have hr : IntegrableOn (fun y : ℝ ↦ (2 / z.re) * Real.exp (-(z.re / 2) * y)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hhalf) 0).const_mul (2 / z.re)
    refine hr.mono' ?_ ?_
    · exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      change 0 < y at hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      have hlin : z.re / 2 * y ≤ Real.exp (z.re / 2 * y) := by
        linarith [Real.add_one_le_exp (z.re / 2 * y)]
      have hy_le : y ≤ (2 / z.re) * Real.exp (z.re / 2 * y) := by
        have h1 : (2 / z.re) * (z.re / 2 * y) = y := by field_simp [hz.ne']
        calc y = (2 / z.re) * (z.re / 2 * y) := h1.symm
          _ ≤ (2 / z.re) * Real.exp (z.re / 2 * y) :=
              mul_le_mul_of_nonneg_left hlin (by positivity)
      calc y * Real.exp (-z.re * y)
          ≤ ((2 / z.re) * Real.exp (z.re / 2 * y)) * Real.exp (-z.re * y) :=
            mul_le_mul_of_nonneg_right hy_le (Real.exp_pos _).le
        _ = (2 / z.re) * (Real.exp (z.re / 2 * y) * Real.exp (-z.re * y)) := by ring
        _ = (2 / z.re) * Real.exp (-(z.re / 2) * y) := by
            rw [← Real.exp_add]; congr 2; ring
  let F (x : ℝ) : ℂ := -((x : ℂ) * z⁻¹ + (z ^ 2)⁻¹) * Complex.exp (-z * (x : ℂ))
  have hd : ∀ y ∈ Ici (0 : ℝ),
      HasDerivAt F ((y : ℂ) * Complex.exp (-z * (y : ℂ))) y := by
    intro y _
    have h1 : HasDerivAt (fun x : ℝ ↦ -((x : ℂ) * z⁻¹ + (z ^ 2)⁻¹)) (-z⁻¹) y := by
      have ha : HasDerivAt (fun x : ℝ ↦ (x : ℂ) * z⁻¹) z⁻¹ y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const z⁻¹
      exact (ha.add_const (z ^ 2)⁻¹).neg
    have h2 : HasDerivAt (fun x : ℝ ↦ Complex.exp (-z * (x : ℂ)))
        (-z * Complex.exp (-z * (y : ℂ))) y := by
      have ha : HasDerivAt (fun x : ℝ ↦ -z * (x : ℂ)) (-z) y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-z)
      simpa [mul_comm] using ha.cexp
    convert h1.mul h2 using 1
    field_simp [hz0]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hhalf : 0 < z.re / 2 := half_pos hz
    have hdom : Tendsto (fun y : ℝ ↦ ((2 / z.re) * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖) *
        Real.exp (-(z.re / 2) * y)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ ↦ -(z.re / 2) * y) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hhalf) tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul _
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [F, norm_mul, norm_neg, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have htri : ‖(y : ℂ) * z⁻¹ + (z ^ 2)⁻¹‖ ≤ y * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖ := by
      have := norm_add_le ((y : ℂ) * z⁻¹) (z ^ 2)⁻¹
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy] using this
    have hlin : z.re / 2 * y ≤ Real.exp (z.re / 2 * y) := by
      linarith [Real.add_one_le_exp (z.re / 2 * y)]
    have hy_le : y ≤ (2 / z.re) * Real.exp (z.re / 2 * y) := by
      have h1 : (2 / z.re) * (z.re / 2 * y) = y := by field_simp [hz.ne']
      calc y = (2 / z.re) * (z.re / 2 * y) := h1.symm
        _ ≤ (2 / z.re) * Real.exp (z.re / 2 * y) :=
            mul_le_mul_of_nonneg_left hlin (by positivity)
    have h1le : (1 : ℝ) ≤ Real.exp (z.re / 2 * y) := Real.one_le_exp (by positivity)
    have hcomb : y * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖ ≤
        ((2 / z.re) * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖) * Real.exp (z.re / 2 * y) := by
      have h1 : y * ‖z⁻¹‖ ≤ (2 / z.re) * ‖z⁻¹‖ * Real.exp (z.re / 2 * y) := by
        calc y * ‖z⁻¹‖ ≤ ((2 / z.re) * Real.exp (z.re / 2 * y)) * ‖z⁻¹‖ :=
              mul_le_mul_of_nonneg_right hy_le (norm_nonneg _)
          _ = (2 / z.re) * ‖z⁻¹‖ * Real.exp (z.re / 2 * y) := by ring
      have h2 : ‖(z ^ 2)⁻¹‖ ≤ ‖(z ^ 2)⁻¹‖ * Real.exp (z.re / 2 * y) :=
        le_mul_of_one_le_right (norm_nonneg _) h1le
      linarith
    calc ‖(y : ℂ) * z⁻¹ + (z ^ 2)⁻¹‖ * Real.exp (-z.re * y)
        ≤ (((2 / z.re) * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖) * Real.exp (z.re / 2 * y)) *
            Real.exp (-z.re * y) :=
          mul_le_mul_of_nonneg_right (htri.trans hcomb) (Real.exp_pos _).le
      _ = ((2 / z.re) * ‖z⁻¹‖ + ‖(z ^ 2)⁻¹‖) * Real.exp (-(z.re / 2) * y) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  simpa [F] using hftc

private lemma integral_split_real_even {g : ℝ → ℂ} (hg : Integrable g) :
    (∫ y : ℝ, g y) = (∫ y in Ioi (0 : ℝ), g (-y)) + (∫ y in Ioi (0 : ℝ), g y) := by
  have hsplit := (integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hg).symm
  rw [compl_Iic] at hsplit
  rw [hsplit]
  congr 1
  have hneg : (∫ y in Iic (0 : ℝ), g y) = ∫ y in Ioi (0 : ℝ), g (-y) := by
    have h := integral_comp_neg_Iic (c := (0 : ℝ)) (fun y ↦ g (-y))
    simpa only [neg_neg, neg_zero] using h
  exact hneg

private lemma lorentz_sq_add_ne_zero {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    (x : ℂ) ^ 2 + a ^ 2 ≠ 0 := by
  have hfac : (x : ℂ) ^ 2 + a ^ 2 = (a - (x : ℂ) * I) * (a + (x : ℂ) * I) := by
    ring_nf; simp [Complex.I_sq]
  rw [hfac]
  apply mul_ne_zero
  · intro h; have hre := congrArg Complex.re h; simp at hre; linarith
  · intro h; have hre := congrArg Complex.re h; simp at hre; linarith

private lemma integrable_inv_sq_add {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹) := by
  have hcont : Continuous (fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹) :=
    ((Complex.continuous_ofReal.pow 2).add continuous_const).inv₀ (lorentz_sq_add_ne_zero ha)
  let R : ℝ := max (2 * ‖a‖) 2
  have hR : 2 ≤ R := le_max_right _ _
  have hcomp : IsCompact (Icc (-R) R) := isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  let C : ℝ := max (|M| * (R ^ 2 + 1)) 2
  have hbase : Integrable (fun x : ℝ ↦ C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine hbase.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : |x| ≤ R
  · have hmem : x ∈ Icc (-R) R := abs_le.mp hx
    have h1 : ‖((x : ℂ) ^ 2 + a ^ 2)⁻¹‖ ≤ |M| := (hM x hmem).trans (le_abs_self M)
    have hden : 1 + x ^ 2 ≤ R ^ 2 + 1 := by
      have : x ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg x) hx 2
      linarith
    have hpos : 0 < 1 + x ^ 2 := by positivity
    have h2 : ‖((x : ℂ) ^ 2 + a ^ 2)⁻¹‖ * (1 + x ^ 2) ≤ C := by
      calc ‖((x : ℂ) ^ 2 + a ^ 2)⁻¹‖ * (1 + x ^ 2)
          ≤ |M| * (R ^ 2 + 1) := mul_le_mul h1 hden hpos.le (abs_nonneg M)
        _ ≤ C := le_max_left _ _
    exact (le_mul_inv_iff₀ hpos).mpr h2
  · push Not at hx
    have hx2_gt : 2 < |x| := lt_of_le_of_lt hR hx
    have hxa : 2 * ‖a‖ < |x| := lt_of_le_of_lt (le_max_left _ _) hx
    have hnorm : (1 + x ^ 2) / 2 ≤ ‖(x : ℂ) ^ 2 + a ^ 2‖ := by
      have htri : ‖(x : ℂ) ^ 2‖ - ‖a ^ 2‖ ≤ ‖(x : ℂ) ^ 2 + a ^ 2‖ := by
        have := norm_sub_norm_le ((x : ℂ) ^ 2) (-a ^ 2)
        simpa [sub_neg_eq_add, norm_neg] using this
      have hsq : ‖(x : ℂ) ^ 2‖ = x ^ 2 := by simp [sq_abs]
      have ha2 : ‖a ^ 2‖ ≤ x ^ 2 / 4 := by
        rw [norm_pow]
        have : 4 * ‖a‖ ^ 2 ≤ x ^ 2 := by
          have h1 : (2 * ‖a‖) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by positivity) hxa.le 2
          rw [sq_abs] at h1
          linarith
        linarith
      have hx2 : 4 ≤ x ^ 2 := by
        have h1 : (2 : ℝ) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) hx2_gt.le 2
        rw [sq_abs] at h1
        linarith
      rw [hsq] at htri
      linarith
    have hpos_l : 0 < (1 + x ^ 2) / 2 := by positivity
    rw [norm_inv]
    calc ‖(x : ℂ) ^ 2 + a ^ 2‖⁻¹
        ≤ ((1 + x ^ 2) / 2)⁻¹ := inv_anti₀ hpos_l hnorm
      _ = 2 * (1 + x ^ 2)⁻¹ := by field_simp
      _ ≤ C * (1 + x ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma integrable_inv_sq_add_one_sq :
    Integrable (fun x : ℝ ↦ ((((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ : ℂ)) := by
  have h1 : Integrable (fun x : ℝ ↦ (((x : ℂ) ^ 2 + 1)⁻¹ : ℂ)) := by
    simpa using integrable_inv_sq_add (a := 1) (by simp)
  refine h1.norm.mono' ?_ (Eventually.of_forall fun x ↦ ?_)
  · have hne : ∀ y : ℝ, ((y : ℂ) ^ 2 + 1) ^ 2 ≠ 0 := fun y ↦
      pow_ne_zero 2 (by simpa using lorentz_sq_add_ne_zero (a := 1) (by simp) y)
    exact ((((Complex.continuous_ofReal.pow 2).add continuous_const).pow 2).inv₀ hne).aestronglyMeasurable
  · rw [norm_inv, norm_pow, norm_inv]
    have hge1 : (1 : ℝ) ≤ ‖(x : ℂ) ^ 2 + 1‖ := by
      have heq : (x : ℂ) ^ 2 + 1 = ((x ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      nlinarith [sq_nonneg x]
    exact inv_anti₀ (by linarith) (by nlinarith)

/-- **Elementary Fourier Transform of the Complex Lorentzian `1 / (x² + a²)` (`Re a > 0`)**:
proved from real exponential integration and Fourier inversion, ZERO contour integrals! -/
private theorem fourier_lorentzian {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (((x : ℂ) ^ 2 + a ^ 2)⁻¹ : ℂ)) ξ =
      ((Real.pi : ℂ) / a) * Complex.exp (-2 * (Real.pi : ℂ) * a * ((|ξ| : ℝ) : ℂ)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let E : ℝ → ℂ := fun y ↦ Complex.exp (-2 * (Real.pi : ℂ) * a * ((|y| : ℝ) : ℂ))
  have hE_cont : Continuous E :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_abs))
  have hE_int : Integrable E := by
    have hpos : 0 < 2 * Real.pi * a.re := by positivity
    refine (integrable_exp_neg_abs hpos).mono' hE_cont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    have hre : (-2 * (Real.pi : ℂ) * a * ((|y| : ℝ) : ℂ)).re = -(2 * Real.pi * a.re) * |y| := by
      simp [Complex.mul_re]
    rw [show ‖E y‖ = Real.exp (-2 * (Real.pi : ℂ) * a * ((|y| : ℝ) : ℂ)).re from Complex.norm_exp _, hre]
  have hFE : ∀ x : ℝ, 𝓕 E x = (a / (Real.pi : ℂ)) * ((x : ℂ) ^ 2 + a ^ 2)⁻¹ := by
    intro x
    rw [Real.fourier_real_eq_integral_exp_smul]
    let g (y : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * y * x) * I) * E y
    have hg_int : Integrable g := integrable_fourier_mul hE_int x
    change (∫ y : ℝ, g y) = _
    rw [integral_split_real_even hg_int]
    have h1 : (∫ y in Ioi (0 : ℝ), g (-y)) = (2 * (Real.pi : ℂ) * (a - (x : ℂ) * I))⁻¹ := by
      have heq : EqOn (fun y : ℝ ↦ g (-y))
          (fun y : ℝ ↦ Complex.exp (-(2 * (Real.pi : ℂ) * (a - (x : ℂ) * I)) * (y : ℂ))) (Ioi 0) := by
        intro y hy
        change 0 < y at hy
        simp only [g, E, abs_neg, abs_of_pos hy, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [setIntegral_congr_fun measurableSet_Ioi heq]
      apply integral_cexp_neg_mul_Ioi
      have : (2 * (Real.pi : ℂ) * (a - (x : ℂ) * I)).re = 2 * Real.pi * a.re := by
        simp [Complex.mul_re]
      rw [this]; positivity
    have h2 : (∫ y in Ioi (0 : ℝ), g y) = (2 * (Real.pi : ℂ) * (a + (x : ℂ) * I))⁻¹ := by
      have heq : EqOn g
          (fun y : ℝ ↦ Complex.exp (-(2 * (Real.pi : ℂ) * (a + (x : ℂ) * I)) * (y : ℂ))) (Ioi 0) := by
        intro y hy
        change 0 < y at hy
        simp only [g, E, abs_of_pos hy, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [setIntegral_congr_fun measurableSet_Ioi heq]
      apply integral_cexp_neg_mul_Ioi
      have : (2 * (Real.pi : ℂ) * (a + (x : ℂ) * I)).re = 2 * Real.pi * a.re := by
        simp [Complex.mul_re]
      rw [this]; positivity
    rw [h1, h2]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hne1 : a - (x : ℂ) * I ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    have hne2 : a + (x : ℂ) * I ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    have hne3 : (x : ℂ) ^ 2 + a ^ 2 ≠ 0 := lorentz_sq_add_ne_zero ha x
    field_simp [hpi, hne1, hne2, hne3]
    ring_nf; simp [Complex.I_sq]
  have hFE_int : Integrable (𝓕 E) := by
    rw [show 𝓕 E = fun x : ℝ ↦ (a / (Real.pi : ℂ)) * ((x : ℂ) ^ 2 + a ^ 2)⁻¹ from funext hFE]
    exact (integrable_inv_sq_add ha).const_mul _
  have hFE_even : 𝓕⁻ E = 𝓕 E := by
    ext x
    rw [Real.fourierInv_eq_fourier_neg, hFE (-x), hFE x]
    simp
  have hinv := congrFun (hE_cont.fourier_fourierInv_eq hE_int hFE_int) ξ
  rw [hFE_even, show 𝓕 E = fun x : ℝ ↦ (a / (Real.pi : ℂ)) * ((x : ℂ) ^ 2 + a ^ 2)⁻¹ from funext hFE,
      fourier_const_mul] at hinv
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc 𝓕 (fun x : ℝ ↦ (((x : ℂ) ^ 2 + a ^ 2)⁻¹ : ℂ)) ξ
      = ((Real.pi : ℂ) / a) * ((a / (Real.pi : ℂ)) * 𝓕 (fun x : ℝ ↦ (((x : ℂ) ^ 2 + a ^ 2)⁻¹ : ℂ)) ξ) := by
          field_simp [hpi, ha0]
    _ = ((Real.pi : ℂ) / a) * E ξ := by rw [hinv]

/-- **Elementary Fourier Transform of `1 / (x² + 1)²`**: proved from
`integral_mul_cexp_neg_mul_Ioi` and Fourier inversion! -/
private theorem fourier_lorentzian_sq (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ ((((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ : ℂ)) ξ =
      ((Real.pi : ℂ) / 2) * (1 + 2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * ((|ξ| : ℝ) : ℂ)) := by
  let E : ℝ → ℂ := fun y ↦ (1 + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))
  have hE_cont : Continuous E := by unfold E; fun_prop
  have hE_int : Integrable E := by
    refine ((integrable_exp_neg_abs Real.pi_pos).const_mul (3 : ℝ)).mono'
      hE_cont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    have hre : (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)).re = -(2 * Real.pi) * |y| := by
      simp [Complex.mul_re]
    rw [show ‖E y‖ = ‖(1 : ℂ) + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)‖ *
        Real.exp (-(2 * Real.pi) * |y|) by
      simp only [E, norm_mul, Complex.norm_exp, hre]]
    have htri : ‖(1 : ℂ) + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)‖ ≤ 1 + 2 * (Real.pi * |y|) := by
      have h1 := norm_add_le (1 : ℂ) (2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_abs, mul_assoc] using h1
    have hlin : Real.pi * |y| ≤ Real.exp (Real.pi * |y|) := by
      linarith [Real.add_one_le_exp (Real.pi * |y|)]
    have h1le : (1 : ℝ) ≤ Real.exp (Real.pi * |y|) := Real.one_le_exp (by positivity)
    have hcomb : 1 + 2 * (Real.pi * |y|) ≤ 3 * Real.exp (Real.pi * |y|) := by linarith
    calc ‖(1 : ℂ) + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)‖ * Real.exp (-(2 * Real.pi) * |y|)
        ≤ (3 * Real.exp (Real.pi * |y|)) * Real.exp (-(2 * Real.pi) * |y|) :=
          mul_le_mul_of_nonneg_right (htri.trans hcomb) (Real.exp_pos _).le
      _ = 3 * Real.exp (-Real.pi * |y|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hFE : ∀ x : ℝ, 𝓕 E x = (2 / (Real.pi : ℂ)) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ := by
    intro x
    rw [Real.fourier_real_eq_integral_exp_smul]
    let g (y : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * y * x) * I) * E y
    have hg_int : Integrable g := integrable_fourier_mul hE_int x
    change (∫ y : ℝ, g y) = _
    rw [integral_split_real_even hg_int]
    have hbranch (s : ℝ) :
        (∫ y in Ioi (0 : ℝ), (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * (1 + (s : ℂ) * I)) * (y : ℂ))) =
        (2 * (Real.pi : ℂ))⁻¹ * ((1 + (s : ℂ) * I)⁻¹ + ((1 + (s : ℂ) * I) ^ 2)⁻¹) := by
      let z : ℂ := 2 * (Real.pi : ℂ) * (1 + (s : ℂ) * I)
      have hz : 0 < z.re := by
        have : z.re = 2 * Real.pi := by simp [z, Complex.mul_re]
        rw [this]; positivity
      have hi1 : IntegrableOn (fun y : ℝ ↦ Complex.exp (-z * (y : ℂ))) (Ioi 0) := by
        have hr : IntegrableOn (fun y : ℝ ↦ Real.exp (-z.re * y)) (Ioi 0) := by
          simpa using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) 0
        refine hr.mono' (by fun_prop) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
        rw [Complex.norm_exp]; simp [Complex.mul_re]
      have hi2 : IntegrableOn (fun y : ℝ ↦ (2 * (Real.pi : ℂ)) * ((y : ℂ) * Complex.exp (-z * (y : ℂ))))
          (Ioi 0) := by
        have hhalf : 0 < z.re / 2 := half_pos hz
        have hr : IntegrableOn (fun y : ℝ ↦ (2 / z.re) * Real.exp (-(z.re / 2) * y)) (Ioi 0) :=
          (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hhalf) 0).const_mul (2 / z.re)
        apply Integrable.const_mul
        refine hr.mono' (by fun_prop) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        change 0 < y at hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        have hlin : z.re / 2 * y ≤ Real.exp (z.re / 2 * y) := by
          linarith [Real.add_one_le_exp (z.re / 2 * y)]
        have hy_le : y ≤ (2 / z.re) * Real.exp (z.re / 2 * y) := by
          have h1 : (2 / z.re) * (z.re / 2 * y) = y := by field_simp [hz.ne']
          calc y = (2 / z.re) * (z.re / 2 * y) := h1.symm
            _ ≤ (2 / z.re) * Real.exp (z.re / 2 * y) :=
                mul_le_mul_of_nonneg_left hlin (by positivity)
        calc y * Real.exp (-z.re * y)
            ≤ ((2 / z.re) * Real.exp (z.re / 2 * y)) * Real.exp (-z.re * y) :=
              mul_le_mul_of_nonneg_right hy_le (Real.exp_pos _).le
          _ = (2 / z.re) * Real.exp (-(z.re / 2) * y) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      have hrewrite : EqOn (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.exp (-z * (y : ℂ)))
          (fun y : ℝ ↦ Complex.exp (-z * (y : ℂ)) +
            (2 * (Real.pi : ℂ)) * ((y : ℂ) * Complex.exp (-z * (y : ℂ)))) (Ioi 0) := fun _ _ ↦ by ring
      rw [setIntegral_congr_fun measurableSet_Ioi hrewrite, integral_add hi1 hi2,
          integral_const_mul, integral_cexp_neg_mul_Ioi hz, integral_mul_cexp_neg_mul_Ioi hz]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h1s : 1 + (s : ℂ) * I ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this
      dsimp only [z]
      field_simp [hpi, h1s]
    have h1 : (∫ y in Ioi (0 : ℝ), g (-y)) =
        (2 * (Real.pi : ℂ))⁻¹ * ((1 + ((-x : ℝ) : ℂ) * I)⁻¹ + ((1 + ((-x : ℝ) : ℂ) * I) ^ 2)⁻¹) := by
      rw [← hbranch (-x)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy; change 0 < y at hy
      simp only [g, E, abs_neg, abs_of_pos hy]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    have h2 : (∫ y in Ioi (0 : ℝ), g y) =
        (2 * (Real.pi : ℂ))⁻¹ * ((1 + (x : ℂ) * I)⁻¹ + ((1 + (x : ℂ) * I) ^ 2)⁻¹) := by
      rw [← hbranch x]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy; change 0 < y at hy
      simp only [g, E, abs_of_pos hy]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [h1, h2]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hne1 : 1 - (x : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hne2 : 1 + (x : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hne3 : (x : ℂ) ^ 2 + 1 ≠ 0 := by
      simpa using lorentz_sq_add_ne_zero (a := 1) (by simp) x
    push_cast
    rw [show (1 : ℂ) + -(x : ℂ) * I = 1 - (x : ℂ) * I by ring]
    field_simp [hpi, hne1, hne2, hne3]
    ring_nf; simp [Complex.I_sq]
  have hFE_int : Integrable (𝓕 E) := by
    rw [show 𝓕 E = fun x : ℝ ↦ (2 / (Real.pi : ℂ)) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ from funext hFE]
    exact integrable_inv_sq_add_one_sq.const_mul _
  have hFE_even : 𝓕⁻ E = 𝓕 E := by
    ext x
    rw [Real.fourierInv_eq_fourier_neg, hFE (-x), hFE x]
    simp
  have hinv := congrFun (hE_cont.fourier_fourierInv_eq hE_int hFE_int) ξ
  rw [hFE_even, show 𝓕 E = fun x : ℝ ↦ (2 / (Real.pi : ℂ)) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ from funext hFE,
      fourier_const_mul] at hinv
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc 𝓕 (fun x : ℝ ↦ ((((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ : ℂ)) ξ
      = ((Real.pi : ℂ) / 2) *
          ((2 / (Real.pi : ℂ)) * 𝓕 (fun x : ℝ ↦ ((((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ : ℂ)) ξ) := by
          field_simp [hpi]
    _ = ((Real.pi : ℂ) / 2) * E ξ := by rw [hinv]
    _ = _ := by dsimp [E]; ring

/-! ### 2. Cotangent Partial Fraction Identity for `f_t(x) = x² / (exp(t x²) - 1)` -/

private def sqFunc (t : ℝ) (x : ℝ) : ℂ :=
  if x = 0 then ((t⁻¹ : ℝ) : ℂ) else (((x ^ 2 / (Real.exp (t * x ^ 2) - 1) : ℝ) : ℂ))

private def sqRemTerm (t : ℝ) (m : ℕ+) (x : ℝ) : ℂ :=
  (((2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) : ℝ) : ℂ))

private def sqRem (t : ℝ) (x : ℝ) : ℂ := ∑' m : ℕ+, sqRemTerm t m x

private lemma sqFunc_continuous {t : ℝ} (ht : 0 < t) : Continuous (sqFunc t) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [continuousAt_iff_punctured_nhds, sqFunc, ite_eq_left rfl]
    have hderiv : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    have hslope : Tendsto (fun u : ℝ ↦ (Real.exp u - 1) / u) (𝓝[≠] 0) (𝓝 1) := by
      have h := hderiv.tendsto_slope_zero
      simpa [div_eq_inv_mul] using h
    have hinv : Tendsto (fun u : ℝ ↦ u / (Real.exp u - 1)) (𝓝[≠] 0) (𝓝 1) := by
      simpa [one_div] using (hslope.inv₀ one_ne_zero).congr (fun u ↦ inv_div _ _)
    have hmap : Tendsto (fun y : ℝ ↦ t * y ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun y : ℝ ↦ t * y ^ 2) 0 := by fun_prop
        have h0 : Tendsto (fun y : ℝ ↦ t * y ^ 2) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact mul_ne_zero ht.ne' (pow_ne_zero 2 hy)
    have hcomp : Tendsto (fun y : ℝ ↦ t⁻¹ * ((t * y ^ 2) / (Real.exp (t * y ^ 2) - 1)))
        (𝓝[≠] 0) (𝓝 (t⁻¹ * 1)) := (hinv.comp hmap).const_mul t⁻¹
    rw [mul_one] at hcomp
    have hcompC := Complex.continuous_ofReal.continuousAt.tendsto.comp hcomp
    refine hcompC.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := hy
    simp only [Function.comp_apply, sqFunc, hy0, ↓reduceIte]
    congr 1; field_simp [ht.ne']
  · have hden : Real.exp (t * x ^ 2) - 1 ≠ 0 := by
      have hpos : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx)
      linarith [Real.one_lt_exp_iff.mpr hpos]
    have hc : ContinuousAt (fun y : ℝ ↦ (((y ^ 2 / (Real.exp (t * y ^ 2) - 1) : ℝ) : ℂ))) x :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_id.pow 2).div (((continuousAt_const.mul (continuousAt_id.pow 2)).rexp).sub
          continuousAt_const) hden)
    refine hc.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp [sqFunc, hy]

private lemma sqFunc_norm_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖sqFunc t x‖ ≤ if x = 0 then t⁻¹ else 2 / (t ^ 2 * x ^ 2) := by
  by_cases hx : x = 0
  · subst hx
    simp only [sqFunc, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht,
      le_refl]
  · simp only [sqFunc, hx, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    have hu : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx)
    have hexp : t ^ 2 * x ^ 4 / 2 ≤ Real.exp (t * x ^ 2) - 1 := by
      have h := Real.sum_le_exp_of_nonneg hu.le 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h
      have hsq : (t * x ^ 2) ^ 2 = t ^ 2 * x ^ 4 := by ring
      rw [hsq] at h
      linarith
    have hpos_d : 0 < Real.exp (t * x ^ 2) - 1 := by linarith [Real.one_lt_exp_iff.mpr hu]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg x) hpos_d.le)]
    calc x ^ 2 / (Real.exp (t * x ^ 2) - 1)
        ≤ x ^ 2 / (t ^ 2 * x ^ 4 / 2) :=
          div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) hexp
      _ = 2 / (t ^ 2 * x ^ 2) := by field_simp [ht.ne', hx]

private lemma sqFunc_integrable {t : ℝ} (ht : 0 < t) : Integrable (sqFunc t) := by
  let C : ℝ := max (2 * t⁻¹) (4 / t ^ 2)
  have hbase : Integrable (fun x : ℝ ↦ C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine hbase.mono' (sqFunc_continuous ht).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  by_cases hx1 : x ^ 2 ≤ 1
  · by_cases hx0 : x = 0
    · subst hx0
      have h1 := sqFunc_norm_le ht 0
      simp only [↓reduceIte] at h1
      calc ‖sqFunc t 0‖ ≤ t⁻¹ := h1
        _ ≤ 2 * t⁻¹ := by linarith [inv_pos.mpr ht]
        _ ≤ C := le_max_left _ _
        _ = C * (1 + 0 ^ 2)⁻¹ := by simp
    · have hu : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx0)
      have hexp : t * x ^ 2 ≤ Real.exp (t * x ^ 2) - 1 := by
        linarith [Real.add_one_le_exp (t * x ^ 2)]
      have hnorm : ‖sqFunc t x‖ ≤ t⁻¹ := by
        simp only [sqFunc, hx0, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (div_nonneg (sq_nonneg x) (by linarith))]
        calc x ^ 2 / (Real.exp (t * x ^ 2) - 1)
            ≤ x ^ 2 / (t * x ^ 2) := div_le_div_of_nonneg_left (sq_nonneg x) hu hexp
          _ = t⁻¹ := by field_simp [ht.ne', hx0]
      have h1 : t⁻¹ ≤ 2 * t⁻¹ * (1 + x ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ (by positivity)]
        nlinarith [inv_pos.mpr ht]
      exact hnorm.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · push Not at hx1
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
    have hnorm := sqFunc_norm_le ht x
    simp only [hx0, ↓reduceIte] at hnorm
    have h1 : 2 / (t ^ 2 * x ^ 2) ≤ (4 / t ^ 2) * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      have hpos : 0 < t ^ 2 * x ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      have : (4 / t ^ 2) * (t ^ 2 * x ^ 2) = 4 * x ^ 2 := by field_simp [ht.ne']
      linarith
    exact hnorm.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

private lemma sqFunc_isBigO {t : ℝ} (ht : 0 < t) :
    (sqFunc t) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / t ^ 2, Filter.hasBasis_cocompact.eventually_iff.mpr
    ⟨Metric.closedBall (0 : ℝ) 1, isCompact_closedBall 0 1, fun x hx ↦ ?_⟩⟩
  have hgt : 1 < |x| := by
    have hnot : ¬ dist x 0 ≤ 1 := fun h ↦ hx (Metric.mem_closedBall.mpr h)
    rw [Real.dist_eq, sub_zero] at hnot
    linarith
  have hx0 : x ≠ 0 := by rintro rfl; simp at hgt; linarith
  have hnorm := sqFunc_norm_le ht x
  simp only [hx0, ↓reduceIte] at hnorm
  have hrpow : ‖|x| ^ (-(2 : ℝ))‖ = (x ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
        Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, sq_abs]
  rw [hrpow]
  calc ‖sqFunc t x‖ ≤ 2 / (t ^ 2 * x ^ 2) := hnorm
    _ = (2 / t ^ 2) * (x ^ 2)⁻¹ := by ring

/-- Exact cotangent partial-fraction identity: `x⁴ r_t(x) = f_t(x) - 1/t + x²/2` for ALL `x ∈ ℝ`! -/
private theorem sqRem_identity {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ((x : ℂ) ^ 4) * sqRem t x = sqFunc t x - ((t⁻¹ : ℝ) : ℂ) + ((x : ℂ) ^ 2) / 2 := by
  by_cases hx : x = 0
  · subst hx; simp [sqFunc]
  · have hu : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx)
    let z : ℂ := I * (((t * x ^ 2 / (2 * Real.pi) : ℝ) : ℂ))
    have hz_mem : z ∈ integerComplement := by
      rintro ⟨k, hk⟩
      have him := congrArg Complex.im hk
      simp only [z, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, one_mul, zero_add, Complex.intCast_im] at him
      have hpos : 0 < t * x ^ 2 / (2 * Real.pi) := by positivity
      linarith
    have hcot := cot_series_rep hz_mem
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : I ≠ 0 := Complex.I_ne_zero
    have hlhs : (I / (2 * (Real.pi : ℂ))) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)) =
        (1 / 2 : ℂ) + (((Real.exp (t * x ^ 2) - 1)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cot_pi_eq_exp_ratio]
      have harg : 2 * (Real.pi : ℂ) * I * z = -((t * x ^ 2 : ℝ) : ℂ) := by
        dsimp only [z]; push_cast
        have h1 : 2 * (Real.pi : ℂ) * I * (I * ((t : ℂ) * (x : ℂ) ^ 2 / (2 * (Real.pi : ℂ)))) =
            (I * I) * ((t : ℂ) * (x : ℂ) ^ 2) := by
          field_simp [hpi]
        rw [h1, Complex.I_mul_I]; ring
      rw [harg]
      have hrecip : Complex.exp (-((t * x ^ 2 : ℝ) : ℂ)) =
          (((Real.exp (t * x ^ 2) : ℝ) : ℂ))⁻¹ := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Complex.ofReal_inv]
      rw [hrecip]
      have hepos : 0 < Real.exp (t * x ^ 2) := Real.exp_pos _
      have hegt1 : 1 < Real.exp (t * x ^ 2) := Real.one_lt_exp_iff.mpr hu
      let E : ℂ := ((Real.exp (t * x ^ 2) : ℝ) : ℂ)
      have hE0 : E ≠ 0 := Complex.ofReal_ne_zero.mpr hepos.ne'
      have hE1 : E - 1 ≠ 0 := by
        intro h; have hre := congrArg Complex.re h
        simp only [E, Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hre
        linarith
      have hden : (1 : ℂ) - E⁻¹ ≠ 0 := by
        intro h
        have h1 : (1 - E⁻¹) * E = 0 := by rw [h, zero_mul]
        rw [sub_mul, one_mul, inv_mul_cancel₀ hE0] at h1
        exact hE1 h1
      rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
      change (I / (2 * (Real.pi : ℂ))) * ((Real.pi : ℂ) * ((E⁻¹ + 1) / (I * (1 - E⁻¹)))) =
        (1 / 2 : ℂ) + (E - 1)⁻¹
      field_simp [hpi, hI, hE0, hE1, hden]
      ring
    have hterm (m : ℕ+) :
        (I / (2 * (Real.pi : ℂ))) * (1 / (z - (m.val : ℂ)) + 1 / (z + (m.val : ℂ))) =
          ((x : ℂ) ^ 2) * sqRemTerm t m x := by
      have hz_ne1 : z - (m.val : ℂ) ≠ 0 := by
        intro h; have him := congrArg Complex.im h
        simp only [z, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add,
          Complex.natCast_im, sub_zero, Complex.zero_im] at him
        have : 0 < t * x ^ 2 / (2 * Real.pi) := by positivity
        linarith
      have hz_ne2 : z + (m.val : ℂ) ≠ 0 := by
        intro h; have him := congrArg Complex.im h
        simp only [z, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add,
          Complex.natCast_im, add_zero, Complex.zero_im] at him
        have : 0 < t * x ^ 2 / (2 * Real.pi) := by positivity
        linarith
      have hden : ((t : ℂ) ^ 2 * (x : ℂ) ^ 4 + 4 * (Real.pi : ℂ) ^ 2 * (m.val : ℂ) ^ 2) ≠ 0 := by
        have hpos : (0 : ℝ) < t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2 := by positivity
        exact_mod_cast hpos.ne'
      have hz_eq : z = I * (t : ℂ) * (x : ℂ) ^ 2 / (2 * (Real.pi : ℂ)) := by
        dsimp only [z]; push_cast; ring
      simp only [sqRemTerm]; push_cast
      have hsum : 1 / (z - (m.val : ℂ)) + 1 / (z + (m.val : ℂ)) =
          2 * z / (z ^ 2 - (m.val : ℂ) ^ 2) := by
        have hprod : z ^ 2 - (m.val : ℂ) ^ 2 = (z - (m.val : ℂ)) * (z + (m.val : ℂ)) := by ring
        rw [hprod]
        field_simp [hz_ne1, hz_ne2]
        ring
      rw [hsum, hz_eq]
      have hz2 : (I * (t : ℂ) * (x : ℂ) ^ 2 / (2 * (Real.pi : ℂ))) ^ 2 - (m.val : ℂ) ^ 2 =
          -((t : ℂ) ^ 2 * (x : ℂ) ^ 4 + 4 * (Real.pi : ℂ) ^ 2 * (m.val : ℂ) ^ 2) /
            (4 * (Real.pi : ℂ) ^ 2) := by
        field_simp [hpi]
        ring_nf; simp [Complex.I_sq]
      rw [hz2]
      field_simp [hpi, hden]
      ring_nf; simp [Complex.I_sq]
    have hmul := congrArg ((I / (2 * (Real.pi : ℂ))) * ·) hcot
    rw [hlhs, mul_add, ← tsum_mul_left] at hmul
    simp_rw [hterm] at hmul
    rw [tsum_mul_left] at hmul
    have hfirst : (I / (2 * (Real.pi : ℂ))) * (1 / z) = ((t : ℂ) * (x : ℂ) ^ 2)⁻¹ := by
      dsimp only [z]; push_cast
      field_simp [hpi, hI, Complex.ofReal_ne_zero.mpr ht.ne', Complex.ofReal_ne_zero.mpr hx]
    rw [hfirst] at hmul
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hsq : ((x : ℂ) ^ 2) * ((1 / 2 : ℂ) + (((Real.exp (t * x ^ 2) - 1)⁻¹ : ℝ) : ℂ)) =
        ((x : ℂ) ^ 2) * (((t : ℂ) * (x : ℂ) ^ 2)⁻¹ + ((x : ℂ) ^ 2) * sqRem t x) := by
      unfold sqRem; rw [hmul]
    simp only [sqFunc, hx, ↓reduceIte]
    have hsub_eq : ((x : ℂ) ^ 2) * (((t : ℂ) * (x : ℂ) ^ 2)⁻¹) = ((t : ℂ)⁻¹) := by
      field_simp [hxC, htC]
    have hterm_eq : ((x : ℂ) ^ 2) * (((Real.exp (t * x ^ 2) - 1)⁻¹ : ℝ) : ℂ) =
        (((x ^ 2 / (Real.exp (t * x ^ 2) - 1) : ℝ) : ℂ)) := by
      push_cast; rw [div_eq_mul_inv]
    rw [mul_add, mul_add, hsub_eq, hterm_eq] at hsq
    rw [Complex.ofReal_inv]
    linear_combination -hsq

/-! ### 3. Fubini Fourier Transform of `sqRem t` and 4th-Derivative Computation of `𝓕 (sqFunc t)` -/

private def sqAlpha (t : ℝ) (m : ℕ+) : ℝ := Real.sqrt (Real.pi * (m.val : ℝ) / t)

private lemma sqAlpha_pos {t : ℝ} (ht : 0 < t) (m : ℕ+) : 0 < sqAlpha t m := by
  have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  exact Real.sqrt_pos.mpr (by positivity)

private def sqA1 (t : ℝ) (m : ℕ+) : ℂ := ((sqAlpha t m : ℝ) : ℂ) * (1 - I)
private def sqA2 (t : ℝ) (m : ℕ+) : ℂ := ((sqAlpha t m : ℝ) : ℂ) * (1 + I)

private lemma sqA1_re {t : ℝ} (m : ℕ+) : (sqA1 t m).re = sqAlpha t m := by
  simp [sqA1, Complex.mul_re]

private lemma sqA2_re {t : ℝ} (m : ℕ+) : (sqA2 t m).re = sqAlpha t m := by
  simp [sqA2, Complex.mul_re]

private lemma sqA1_ne_zero {t : ℝ} (ht : 0 < t) (m : ℕ+) : sqA1 t m ≠ 0 := by
  intro h; have hre := congrArg Complex.re h
  rw [sqA1_re, Complex.zero_re] at hre
  linarith [sqAlpha_pos ht m]

private lemma sqA2_ne_zero {t : ℝ} (ht : 0 < t) (m : ℕ+) : sqA2 t m ≠ 0 := by
  intro h; have hre := congrArg Complex.re h
  rw [sqA2_re, Complex.zero_re] at hre
  linarith [sqAlpha_pos ht m]

private lemma sqRemTerm_split {t : ℝ} (ht : 0 < t) (m : ℕ+) (x : ℝ) :
    sqRemTerm t m x =
      (1 / (2 * (Real.pi : ℂ) * I * (m.val : ℂ))) *
        (((x : ℂ) ^ 2 + (sqA1 t m) ^ 2)⁻¹ - ((x : ℂ) ^ 2 + (sqA2 t m) ^ 2)⁻¹) := by
  have hm_pos : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hsq : (sqAlpha t m) ^ 2 = Real.pi * (m.val : ℝ) / t := Real.sq_sqrt (by positivity)
  have ha1_sq : (sqA1 t m) ^ 2 = -((2 * Real.pi * (m.val : ℝ) / t : ℝ) : ℂ) * I := by
    calc (sqA1 t m) ^ 2
        = (((sqAlpha t m) ^ 2 : ℝ) : ℂ) * (1 - I) ^ 2 := by simp [sqA1, mul_pow]
      _ = ((Real.pi * (m.val : ℝ) / t : ℝ) : ℂ) * (-2 * I) := by
            rw [hsq]; ring_nf; simp [Complex.I_sq]; ring
      _ = _ := by push_cast; ring
  have ha2_sq : (sqA2 t m) ^ 2 = ((2 * Real.pi * (m.val : ℝ) / t : ℝ) : ℂ) * I := by
    calc (sqA2 t m) ^ 2
        = (((sqAlpha t m) ^ 2 : ℝ) : ℂ) * (1 + I) ^ 2 := by simp [sqA2, mul_pow]
      _ = ((Real.pi * (m.val : ℝ) / t : ℝ) : ℂ) * (2 * I) := by
            rw [hsq]; ring_nf; simp [Complex.I_sq]
      _ = _ := by push_cast; ring
  have h1ne : (x : ℂ) ^ 2 + (sqA1 t m) ^ 2 ≠ 0 :=
    lorentz_sq_add_ne_zero (by rw [sqA1_re]; exact sqAlpha_pos ht m) x
  have h2ne : (x : ℂ) ^ 2 + (sqA2 t m) ^ 2 ≠ 0 :=
    lorentz_sq_add_ne_zero (by rw [sqA2_re]; exact sqAlpha_pos ht m) x
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hm : (m.val : ℂ) ≠ 0 := by exact_mod_cast m.property.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hden : ((t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have h1' : (t : ℂ) * (x : ℂ) ^ 2 - 2 * (Real.pi : ℂ) * (m.val : ℂ) * I ≠ 0 := by
    intro h; have him := congrArg Complex.im h
    simp at him; rw [← Complex.ofReal_pow, Complex.ofReal_im] at him
    have hpos : 0 < 2 * Real.pi * (m.val : ℝ) := by positivity
    linarith
  have h2' : (t : ℂ) * (x : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (m.val : ℂ) * I ≠ 0 := by
    intro h; have him := congrArg Complex.im h
    simp at him; rw [← Complex.ofReal_pow, Complex.ofReal_im] at him
    have hpos : 0 < 2 * Real.pi * (m.val : ℝ) := by positivity
    linarith
  have heq1 : ((x : ℂ) ^ 2 + -(2 * (Real.pi : ℂ) * (m.val : ℂ) / (t : ℂ)) * I) =
      ((t : ℂ) * (x : ℂ) ^ 2 - 2 * (Real.pi : ℂ) * (m.val : ℂ) * I) / (t : ℂ) := by
    field_simp [htC]; ring
  have heq2 : ((x : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (m.val : ℂ) / (t : ℂ) * I) =
      ((t : ℂ) * (x : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (m.val : ℂ) * I) / (t : ℂ) := by
    field_simp [htC]
  rw [ha1_sq, ha2_sq]
  simp only [sqRemTerm]
  push_cast at hden ⊢
  rw [heq1, heq2]
  field_simp [hpi, Complex.I_ne_zero, hm, htC, h1', h2', hden]
  ring_nf; simp

private lemma fourier_sqRemTerm {t : ℝ} (ht : 0 < t) (m : ℕ+) (ξ : ℝ) :
    𝓕 (sqRemTerm t m) ξ =
      (1 / (2 * I * (m.val : ℂ))) *
        (Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * ((|ξ| : ℝ) : ℂ)) / sqA1 t m -
         Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * ((|ξ| : ℝ) : ℂ)) / sqA2 t m) := by
  have hfun : sqRemTerm t m = fun x : ℝ ↦
      (1 / (2 * (Real.pi : ℂ) * I * (m.val : ℂ))) *
        (((x : ℂ) ^ 2 + (sqA1 t m) ^ 2)⁻¹ - ((x : ℂ) ^ 2 + (sqA2 t m) ^ 2)⁻¹) :=
    funext (sqRemTerm_split ht m)
  rw [hfun, fourier_const_mul,
      fourier_sub_eq
        (integrable_inv_sq_add (by rw [sqA1_re]; exact sqAlpha_pos ht m))
        (integrable_inv_sq_add (by rw [sqA2_re]; exact sqAlpha_pos ht m))]
  rw [fourier_lorentzian (by rw [sqA1_re]; exact sqAlpha_pos ht m) ξ,
      fourier_lorentzian (by rw [sqA2_re]; exact sqAlpha_pos ht m) ξ]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hm : (m.val : ℂ) ≠ 0 := by exact_mod_cast m.property.ne'
  field_simp [hpi, Complex.I_ne_zero, hm, sqA1_ne_zero ht m, sqA2_ne_zero ht m]

private lemma sqRemTerm_integrable {t : ℝ} (ht : 0 < t) (m : ℕ+) :
    Integrable (sqRemTerm t m) := by
  have hfun : sqRemTerm t m = fun x : ℝ ↦
      (1 / (2 * (Real.pi : ℂ) * I * (m.val : ℂ))) *
        (((x : ℂ) ^ 2 + (sqA1 t m) ^ 2)⁻¹ - ((x : ℂ) ^ 2 + (sqA2 t m) ^ 2)⁻¹) :=
    funext (sqRemTerm_split ht m)
  rw [hfun]
  exact ((integrable_inv_sq_add (by rw [sqA1_re]; exact sqAlpha_pos ht m)).sub
    (integrable_inv_sq_add (by rw [sqA2_re]; exact sqAlpha_pos ht m))).const_mul _

private lemma sqRemTerm_integral_norm {t : ℝ} (ht : 0 < t) (m : ℕ+) :
    (∫ x : ℝ, ‖sqRemTerm t m x‖) = (Real.sqrt t / (2 * Real.sqrt Real.pi)) *
      ((m.val : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hm_pos : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hpt : ∀ x : ℝ, ‖sqRemTerm t m x‖ =
      2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) := fun x ↦ by
    have hpos : (0 : ℝ) < 2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) := by positivity
    simp only [sqRemTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hval := fourier_sqRemTerm ht m 0
  simp only [Real.fourier_real_eq_integral_exp_smul, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, abs_zero] at hval
  have hre : (∫ x : ℝ, ‖sqRemTerm t m x‖) = (∫ x : ℝ, sqRemTerm t m x).re := by
    have hfun : (fun x : ℝ ↦ sqRemTerm t m x) = fun x : ℝ ↦ ((‖sqRemTerm t m x‖ : ℝ) : ℂ) := by
      funext x; rw [hpt x]; rfl
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [hre, hval]
  have hsimp : (1 / (2 * I * (m.val : ℂ))) * (1 / sqA1 t m - 1 / sqA2 t m) =
      (((1 / (2 * (m.val : ℝ) * sqAlpha t m) : ℝ) : ℂ)) := by
    have hm : (m.val : ℂ) ≠ 0 := by exact_mod_cast m.property.ne'
    have hα : (sqAlpha t m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sqAlpha_pos ht m).ne'
    have h1m : (1 : ℂ) - I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
    have h1p : (1 : ℂ) + I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
    simp only [sqA1, sqA2]; push_cast
    field_simp [Complex.I_ne_zero, hm, hα, h1m, h1p]
    ring_nf; rw [show I ^ 3 = I ^ 2 * I by ring, Complex.I_sq]; ring
  rw [hsimp, Complex.ofReal_re]
  have hα_eq : sqAlpha t m = Real.sqrt Real.pi * Real.sqrt (m.val : ℝ) / Real.sqrt t := by
    unfold sqAlpha
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
  have hrpow : (m.val : ℝ) ^ (-(3 / 2 : ℝ)) = ((m.val : ℝ) * Real.sqrt (m.val : ℝ))⁻¹ := by
    rw [Real.rpow_neg hm_pos.le, Real.sqrt_eq_rpow,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm_pos, Real.rpow_one]
  rw [hα_eq, hrpow]
  have hsqrt_t : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsqrt_pi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsqrt_m : Real.sqrt (m.val : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm_pos).ne'
  field_simp [hsqrt_t, hsqrt_pi, hsqrt_m, hm_pos.ne']

private lemma sqRem_summable_int_norm {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ+ ↦ ∫ x : ℝ, ‖sqRemTerm t m x‖) := by
  simp_rw [sqRemTerm_integral_norm ht]
  have hp : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hp' : Summable (fun m : ℕ+ ↦ (m.val : ℝ) ^ (-(3 / 2 : ℝ))) := by
    refine (hp.subtype (fun n ↦ 0 < n)).congr fun m ↦ ?_
    change ((m.val : ℝ) ^ (3 / 2 : ℝ))⁻¹ = _
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    rfl
  exact hp'.mul_left _

private lemma sqRem_continuous {t : ℝ} (ht : 0 < t) : Continuous (sqRem t) := by
  have hu : Summable (fun m : ℕ+ ↦ 2 * t / (4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2)) := by
    have h2 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by simp
    have h2' : Summable (fun m : ℕ+ ↦ ((m.val : ℝ) ^ 2)⁻¹) := h2.subtype (fun n ↦ 0 < n)
    refine (h2'.mul_left (2 * t / (4 * Real.pi ^ 2))).congr fun m ↦ ?_
    ring
  refine continuous_tsum (fun m ↦ ?_) hu (fun m x ↦ ?_)
  · unfold sqRemTerm
    have hden : ∀ x : ℝ, t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2 ≠ 0 :=
      fun x ↦ (by positivity : (0 : ℝ) < _).ne'
    exact Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) hden)
  · have hpos : (0 : ℝ) < 2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) := by positivity
    simp only [sqRemTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [sq_nonneg (t * x ^ 2)])

private lemma sqRem_integrable {t : ℝ} (ht : 0 < t) : Integrable (sqRem t) := by
  refine ⟨(sqRem_continuous ht).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hsum_int := sqRem_summable_int_norm ht
  have hle_pt : ∀ x : ℝ, ‖sqRem t x‖ₑ ≤ ∑' m : ℕ+, ‖sqRemTerm t m x‖ₑ := fun x ↦ by
    have hsum_x : Summable (fun m : ℕ+ ↦ ‖sqRemTerm t m x‖) := by
      have h2 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by simp
      refine ((h2.subtype (fun n ↦ 0 < n)).mul_left (2 * t / (4 * Real.pi ^ 2))).of_nonneg_of_le
        (fun _ ↦ norm_nonneg _) fun m ↦ ?_
      have hpos : (0 : ℝ) < 2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) := by positivity
      simp only [sqRemTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc 2 * t / (t ^ 2 * x ^ 4 + 4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2)
          ≤ 2 * t / (4 * Real.pi ^ 2 * (m.val : ℝ) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg (t * x ^ 2)])
        _ = 2 * t / (4 * Real.pi ^ 2) * ((m.val : ℝ) ^ 2)⁻¹ := by ring
    have hnorm := norm_tsum_le_tsum_norm hsum_x
    calc ‖sqRem t x‖ₑ = ENNReal.ofReal ‖sqRem t x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' m : ℕ+, ‖sqRemTerm t m x‖) := ENNReal.ofReal_le_ofReal hnorm
      _ = ∑' m : ℕ+, ENNReal.ofReal ‖sqRemTerm t m x‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) hsum_x
      _ = ∑' m : ℕ+, ‖sqRemTerm t m x‖ₑ := by simp_rw [ofReal_norm]
  calc ∫⁻ x : ℝ, ‖sqRem t x‖ₑ
      ≤ ∫⁻ x : ℝ, ∑' m : ℕ+, ‖sqRemTerm t m x‖ₑ := lintegral_mono hle_pt
    _ = ∑' m : ℕ+, ∫⁻ x : ℝ, ‖sqRemTerm t m x‖ₑ :=
        lintegral_tsum (fun m ↦ (sqRemTerm_integrable ht m).aestronglyMeasurable.eNorm)
    _ = ∑' m : ℕ+, ENNReal.ofReal (∫ x : ℝ, ‖sqRemTerm t m x‖) := by
        congr 1; funext m; exact (ofReal_integral_norm_eq_lintegral_eNorm (sqRemTerm_integrable ht m)).symm
    _ = ENNReal.ofReal (∑' m : ℕ+, ∫ x : ℝ, ‖sqRemTerm t m x‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m ↦ integral_nonneg fun _ ↦ norm_nonneg _) hsum_int).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Fubini Fourier transform of `sqRem t` for ALL `ξ ∈ ℝ`! -/
private theorem fourier_sqRem {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (sqRem t) ξ =
      ∑' m : ℕ+, (1 / (2 * I * (m.val : ℂ))) *
        (Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * ((|ξ| : ℝ) : ℂ)) / sqA1 t m -
         Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * ((|ξ| : ℝ) : ℂ)) / sqA2 t m) := by
  simp_rw [← fourier_sqRemTerm ht]
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, sqRem]
  have hpt : ∀ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * (∑' m : ℕ+, sqRemTerm t m x) =
      ∑' m : ℕ+, Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * sqRemTerm t m x := fun x ↦ by
    rw [tsum_mul_left]
  simp_rw [hpt]
  have hF_int (m : ℕ+) : Integrable
      (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * sqRemTerm t m x) :=
    integrable_fourier_mul (sqRemTerm_integrable ht m) ξ
  have hF_sum : Summable (fun m : ℕ+ ↦ ∫ x : ℝ,
      ‖Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * sqRemTerm t m x‖) := by
    refine (sqRem_summable_int_norm ht).congr fun m ↦ ?_
    congr 1; funext x; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm

private lemma summable_pow_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun m : ℕ+ ↦ (m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by
  let M : ℕ := 2 * (k + 2)
  have hbound (m : ℕ+) :
      (m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ)) ≤
        ((M.factorial : ℝ) / c ^ M) * ((m.val : ℝ) ^ 2)⁻¹ := by
    have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
    have hu : 0 ≤ c * Real.sqrt (m.val : ℝ) := by positivity
    have hexp : (c * Real.sqrt (m.val : ℝ)) ^ M / (M.factorial : ℝ) ≤
        Real.exp (c * Real.sqrt (m.val : ℝ)) := Real.pow_div_factorial_le_exp _ hu M
    have hpow : (c * Real.sqrt (m.val : ℝ)) ^ M = c ^ M * (m.val : ℝ) ^ (k + 2) := by
      rw [mul_pow]
      congr 1
      change Real.sqrt (m.val : ℝ) ^ (2 * (k + 2)) = _
      rw [pow_mul, Real.sq_sqrt hm.le]
    rw [hpow] at hexp
    have hpos_l : 0 < c ^ M * (m.val : ℝ) ^ (k + 2) / (M.factorial : ℝ) := by positivity
    have hinv : Real.exp (-c * Real.sqrt (m.val : ℝ)) ≤
        (M.factorial : ℝ) / (c ^ M * (m.val : ℝ) ^ (k + 2)) := by
      rw [neg_mul, Real.exp_neg]
      calc (Real.exp (c * Real.sqrt (m.val : ℝ)))⁻¹
          ≤ (c ^ M * (m.val : ℝ) ^ (k + 2) / (M.factorial : ℝ))⁻¹ := inv_anti₀ hpos_l hexp
        _ = (M.factorial : ℝ) / (c ^ M * (m.val : ℝ) ^ (k + 2)) := inv_div _ _
    calc (m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))
        ≤ (m.val : ℝ) ^ k * ((M.factorial : ℝ) / (c ^ M * (m.val : ℝ) ^ (k + 2))) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ((M.factorial : ℝ) / c ^ M) * ((m.val : ℝ) ^ 2)⁻¹ := by
          rw [pow_add]; field_simp [hm.ne', hc.ne']
  have hdom : Summable (fun m : ℕ+ ↦ ((M.factorial : ℝ) / c ^ M) * ((m.val : ℝ) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by simp
    exact (h2.subtype (fun n ↦ 0 < n)).mul_left _
  exact Summable.of_nonneg_of_le (fun _ ↦ by positivity) hbound hdom

/-- Term-by-term 4th derivative of `𝓕 (sqRem t)` on `ξ > 0`! -/
private theorem iteratedDeriv_four_fourier_sqRem {t : ℝ} (ht : 0 < t) {ξ : ℝ} (hξ : 0 < ξ) :
    iteratedDeriv 4 (𝓕 (sqRem t)) ξ =
      ((2 * Real.pi : ℂ) ^ 4) *
        ∑' m : ℕ+, (1 / (2 * I * (m.val : ℂ))) *
          ((sqA1 t m) ^ 3 * Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (ξ : ℂ)) -
           (sqA2 t m) ^ 3 * Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (ξ : ℂ))) := by
  let term (k : ℕ) (m : ℕ+) (y : ℝ) : ℂ :=
    (1 / (2 * I * (m.val : ℂ))) *
      ((-2 * (Real.pi : ℂ) * sqA1 t m) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (y : ℂ)) / sqA1 t m -
       (-2 * (Real.pi : ℂ) * sqA2 t m) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (y : ℂ)) / sqA2 t m)
  have hnorm_a1 (m : ℕ+) : ‖sqA1 t m‖ = sqAlpha t m * Real.sqrt 2 := by
    rw [sqA1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqAlpha_pos ht m)]
    congr 1; rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hnorm_a2 (m : ℕ+) : ‖sqA2 t m‖ = sqAlpha t m * Real.sqrt 2 := by
    rw [sqA2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqAlpha_pos ht m)]
    congr 1; rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hα_split (m : ℕ+) : sqAlpha t m = Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) := by
    unfold sqAlpha
    rw [show Real.pi * (m.val : ℝ) / t = (Real.pi / t) * (m.val : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
  have hterm_bound (k : ℕ) (a : ℝ) (ha : 0 < a) (m : ℕ+) (y : ℝ) (hy : a ≤ y) :
      ‖term k m y‖ ≤
        ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k *
          (Real.sqrt (t / Real.pi) / Real.sqrt 2)) *
        ((m.val : ℝ) ^ k * Real.exp (-(2 * Real.pi * Real.sqrt (Real.pi / t) * a) * Real.sqrt (m.val : ℝ))) := by
    let c : ℝ := 2 * Real.pi * Real.sqrt (Real.pi / t) * a
    let C : ℝ := (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k *
      (Real.sqrt (t / Real.pi) / Real.sqrt 2)
    have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.property
    have hm_sqrt : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
    have hre_bound : Real.exp (-2 * Real.pi * sqAlpha t m * y) ≤
        Real.exp (-c * Real.sqrt (m.val : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hα_split m]; dsimp [c]
      have hpos : 0 ≤ 2 * Real.pi * Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) := by positivity
      nlinarith
    have hpiece (A : ℂ) (hre : A.re = sqAlpha t m) (hnA : ‖A‖ = sqAlpha t m * Real.sqrt 2) :
        ‖(-2 * (Real.pi : ℂ) * A) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * A * (y : ℂ)) / A‖ ≤
          C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by
      rw [norm_div, norm_mul, norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_exp, hnA]
      have hre_exp : (-2 * (Real.pi : ℂ) * A * (y : ℂ)).re = -2 * Real.pi * sqAlpha t m * y := by
        simp [Complex.mul_re, hre]
      rw [hre_exp]
      have hinv_le : (sqAlpha t m * Real.sqrt 2)⁻¹ ≤ Real.sqrt (t / Real.pi) / Real.sqrt 2 := by
        rw [hα_split m, mul_assoc, mul_inv, div_eq_mul_inv]
        have h1 : (Real.sqrt (Real.pi / t))⁻¹ = Real.sqrt (t / Real.pi) := by
          rw [Real.sqrt_div ht.le, Real.sqrt_div Real.pi_pos.le, inv_div]
        rw [show (Real.sqrt (Real.pi * t⁻¹))⁻¹ = Real.sqrt (t / Real.pi) by
          rw [← div_eq_mul_inv, h1]]
        have h2 : (Real.sqrt (m.val : ℝ) * Real.sqrt 2)⁻¹ ≤ (Real.sqrt 2)⁻¹ := by
          apply inv_anti₀ (Real.sqrt_pos.mpr zero_lt_two)
          nlinarith [Real.sqrt_pos.mpr zero_lt_two]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have hpow_le : (2 * Real.pi * (sqAlpha t m * Real.sqrt 2)) ^ k ≤
          (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k * (m.val : ℝ) ^ k := by
        rw [hα_split m, show 2 * Real.pi * (Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) *
            Real.sqrt 2) = (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) *
            Real.sqrt (m.val : ℝ) by ring, mul_pow]
        gcongr
        have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
      have hα_pos : 0 < sqAlpha t m := sqAlpha_pos ht m
      rw [div_eq_mul_inv]
      calc (2 * Real.pi * (sqAlpha t m * Real.sqrt 2)) ^ k *
            Real.exp (-2 * Real.pi * sqAlpha t m * y) * (sqAlpha t m * Real.sqrt 2)⁻¹
          ≤ ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k * (m.val : ℝ) ^ k) *
            Real.exp (-c * Real.sqrt (m.val : ℝ)) * (Real.sqrt (t / Real.pi) / Real.sqrt 2) := by
            gcongr
        _ = C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by
            dsimp [C]; ring
    have hpref : ‖(1 : ℂ) / (2 * I * (m.val : ℂ))‖ ≤ 1 / 2 := by
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
          Complex.norm_natCast]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp only [term]
    rw [norm_mul]
    have hsub := (norm_sub_le _ _).trans (add_le_add
      (hpiece (sqA1 t m) (sqA1_re m) (hnorm_a1 m))
      (hpiece (sqA2 t m) (sqA2_re m) (hnorm_a2 m)))
    calc ‖(1 : ℂ) / (2 * I * (m.val : ℂ))‖ * _
        ≤ (1 / 2) * (C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) +
            C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ)))) :=
          mul_le_mul hpref hsub (norm_nonneg _) (by positivity)
      _ = C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by ring
  have hdiff_step (k : ℕ) (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ ↦ ∑' m : ℕ+, term k m y) (∑' m : ℕ+, term (k + 1) m x) x := by
    let a : ℝ := x / 2
    let b : ℝ := x + 1
    have ha : 0 < a := half_pos hx
    have hmem : x ∈ Ioo a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
    have hd_each (m : ℕ+) (y : ℝ) : HasDerivAt (term k m) (term (k + 1) m y) y := by
      have h1 : HasDerivAt (fun z : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (z : ℂ)))
          ((-2 * (Real.pi : ℂ) * sqA1 t m) *
            Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ (-2 * (Real.pi : ℂ) * sqA1 t m) * (z : ℂ))
            (-2 * (Real.pi : ℂ) * sqA1 t m) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-2 * (Real.pi : ℂ) * sqA1 t m)
        simpa [mul_comm] using hlin.cexp
      have h2 : HasDerivAt (fun z : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (z : ℂ)))
          ((-2 * (Real.pi : ℂ) * sqA2 t m) *
            Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ (-2 * (Real.pi : ℂ) * sqA2 t m) * (z : ℂ))
            (-2 * (Real.pi : ℂ) * sqA2 t m) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-2 * (Real.pi : ℂ) * sqA2 t m)
        simpa [mul_comm] using hlin.cexp
      have hcomb := (((h1.const_mul ((-2 * (Real.pi : ℂ) * sqA1 t m) ^ k)).div_const (sqA1 t m)).sub
        ((h2.const_mul ((-2 * (Real.pi : ℂ) * sqA2 t m) ^ k)).div_const (sqA2 t m))).const_mul
        (1 / (2 * I * (m.val : ℂ)))
      convert hcomb using 1
      dsimp only [term]
      rw [pow_succ, pow_succ]; ring
    have hc : 0 < 2 * Real.pi * Real.sqrt (Real.pi / t) * a := by positivity
    have hu_sum := (summable_pow_mul_exp_neg_sqrt hc (k + 1)).mul_left
      ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ (k + 1) *
        (Real.sqrt (t / Real.pi) / Real.sqrt 2))
    have hsum_k : Summable (fun m : ℕ+ ↦ term k m x) :=
      Summable.of_norm_bounded ((summable_pow_mul_exp_neg_sqrt hc k).mul_left _)
        (fun m ↦ hterm_bound k a ha m x (by dsimp [a]; linarith))
    exact hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_Ioo isPreconnected_Ioo
      (fun m y _ ↦ hd_each m y) (fun m y hy ↦ hterm_bound (k + 1) a ha m y hy.1.le)
      hmem hsum_k hmem
  have hiter : ∀ k : ℕ, ∀ x > 0, iteratedDeriv k (𝓕 (sqRem t)) x = ∑' m : ℕ+, term k m x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [iteratedDeriv_zero, fourier_sqRem ht x]
      apply tsum_congr; intro m
      simp [term, abs_of_pos hx]
    | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hnear : iteratedDeriv k (𝓕 (sqRem t)) =ᶠ[𝓝 x] fun y ↦ ∑' m : ℕ+, term k m y :=
        (lt_mem_nhds hx).mono fun y hy ↦ ih y hy
      rw [hnear.deriv_eq, (hdiff_step k x hx).deriv]
  rw [hiter 4 ξ hξ, ← tsum_mul_left]
  apply tsum_congr; intro m
  dsimp only [term]
  field_simp [sqA1_ne_zero ht m, sqA2_ne_zero ht m]

private lemma iteratedDeriv_four_exp_neg_two_pi {ξ : ℝ} (hξ : 0 < ξ) :
    iteratedDeriv 4 (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) ξ =
      ((2 * Real.pi : ℂ) ^ 4) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)) := by
  have heq : (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
      fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
    (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
  rw [heq.iteratedDeriv_eq 4]
  have hgen (k : ℕ) (x : ℝ) :
      iteratedDeriv k (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) x =
        (-2 * (Real.pi : ℂ)) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ)) := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun y : ℝ ↦
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) =
        fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) from
        funext ih]
      have hd : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))
          ((-2 * (Real.pi : ℂ)) ^ (k + 1) * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ))) x := by
        have h1 : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) * (y : ℂ)) (-2 * (Real.pi : ℂ)) x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-2 * (Real.pi : ℂ))
        convert (h1.cexp).const_mul ((-2 * (Real.pi : ℂ)) ^ k) using 1
        rw [pow_succ]; ring
      exact hd.deriv
  rw [hgen 4 ξ]
  ring

private lemma iteratedDeriv_four_mul_exp_neg_two_pi {ξ : ℝ} (hξ : 0 < ξ) :
    iteratedDeriv 4 (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) ξ =
      ((2 * Real.pi : ℂ) ^ 4) * (2 * (Real.pi : ℂ) * (ξ : ℂ) - 3) *
        Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)) := by
  have heq : (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
      fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
    (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
  rw [heq.iteratedDeriv_eq 4]
  have hgen (k : ℕ) (x : ℝ) :
      iteratedDeriv k (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) x =
        (-2 * (Real.pi : ℂ)) ^ k * (1 - (k : ℂ) + 2 * (Real.pi : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ)) := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) =
        fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k * (1 - (k : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) from funext ih]
      have h1 : HasDerivAt (fun y : ℝ ↦ 1 - (k : ℂ) + (2 * (Real.pi : ℂ)) * (y : ℂ))
          (2 * (Real.pi : ℂ)) x := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (2 * (Real.pi : ℂ))).const_add (1 - (k : ℂ))
      have h2 : HasDerivAt (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))
          ((-2 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ))) x := by
        have hlin : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) * (y : ℂ)) (-2 * (Real.pi : ℂ)) x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-2 * (Real.pi : ℂ))
        simpa [mul_comm] using hlin.cexp
      have hd : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k *
          (1 - (k : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))
          ((-2 * (Real.pi : ℂ)) ^ k *
            (2 * (Real.pi : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ)) +
              (1 - (k : ℂ) + 2 * (Real.pi : ℂ) * (x : ℂ)) *
                ((-2 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ))))) x := by
        have hmul := (h1.mul h2).const_mul ((-2 * (Real.pi : ℂ)) ^ k)
        refine hmul.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
        change (-2 * (Real.pi : ℂ)) ^ k * (1 - (k : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) =
          (-2 * (Real.pi : ℂ)) ^ k * ((1 - (k : ℂ) + (2 * (Real.pi : ℂ)) * (y : ℂ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))
        ring
      rw [hd.deriv, pow_succ, Nat.cast_add, Nat.cast_one]
      ring
  rw [hgen 4 ξ]
  norm_num; ring

/-- **Exact Explicit Fourier Transform of `sqFunc t` on `ξ > 0`** (ZERO contour integrals!). -/
private theorem fourier_sqFunc_pos {t : ℝ} (ht : 0 < t) {ξ : ℝ} (hξ : 0 < ξ) :
    𝓕 (sqFunc t) ξ =
      ∑' m : ℕ+, (1 / (2 * I * (m.val : ℂ))) *
        ((sqA1 t m) ^ 3 * Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (ξ : ℂ)) -
         (sqA2 t m) ^ 3 * Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (ξ : ℂ))) := by
  let c1 : ℂ := 1 / 2
  let c2 : ℂ := 1 / 2 - ((t⁻¹ : ℝ) : ℂ)
  let Q (x : ℝ) : ℂ := c1 * ((x : ℂ) ^ 2 + 1)⁻¹ + c2 * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹
  let ψ (x : ℝ) : ℂ := sqRem t x - Q x
  have h1_int : Integrable (fun x : ℝ ↦ (((x : ℂ) ^ 2 + 1)⁻¹ : ℂ)) := by
    simpa using integrable_inv_sq_add (a := 1) (by simp)
  have h2_int : Integrable (fun x : ℝ ↦ ((((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ : ℂ)) :=
    integrable_inv_sq_add_one_sq
  have hQ_int : Integrable Q := (h1_int.const_mul c1).add (h2_int.const_mul c2)
  have hψ_int : Integrable ψ := (sqRem_integrable ht).sub hQ_int
  have hψ_x4 : ∀ x : ℝ, ((x : ℂ) ^ 4) * ψ x =
      sqFunc t x + (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((x : ℂ) ^ 2 + 1)⁻¹ +
        (((t⁻¹ : ℝ) : ℂ) - 1 / 2) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ := by
    intro x
    dsimp only [ψ, Q, c1, c2]
    rw [mul_sub, sqRem_identity ht x]
    have hne : (x : ℂ) ^ 2 + 1 ≠ 0 := by simpa using lorentz_sq_add_ne_zero (a := 1) (by simp) x
    field_simp [hne]; ring
  have hψ4_int : Integrable (fun x : ℝ ↦ (x ^ 4 : ℝ) • ψ x) := by
    have hfun : (fun x : ℝ ↦ (x ^ 4 : ℝ) • ψ x) = fun x : ℝ ↦
        sqFunc t x + (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((x : ℂ) ^ 2 + 1)⁻¹ +
          (((t⁻¹ : ℝ) : ℂ) - 1 / 2) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹ := by
      funext x; rw [Complex.real_smul, Complex.ofReal_pow, hψ_x4 x]
    rw [hfun]
    exact ((sqFunc_integrable ht).add (h1_int.const_mul _)).add (h2_int.const_mul _)
  have hψ_moments : ∀ n : ℕ, (n : ℕ∞) ≤ 4 → Integrable (fun x : ℝ ↦ x ^ n • ψ x) := by
    intro n hn
    have hn4 : n ≤ 4 := by exact_mod_cast hn
    refine (hψ_int.norm.add hψ4_int.norm).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact ((continuous_pow n).aestronglyMeasurable.smul hψ_int.aestronglyMeasurable)
    · simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs, abs_pow]
      have hpow : |x| ^ n ≤ 1 + |x| ^ 4 := by
        by_cases hx1 : |x| ≤ 1
        · have : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
          linarith [pow_nonneg (abs_nonneg x) 4]
        · push Not at hx1
          linarith [pow_le_pow_right₀ hx1.le hn4]
      calc |x| ^ n * ‖ψ x‖ ≤ (1 + |x| ^ 4) * ‖ψ x‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = ‖ψ x‖ + |x| ^ 4 * ‖ψ x‖ := by ring
  have hFψ_d4 := congrFun (Real.iteratedDeriv_fourier hψ_moments le_rfl) ξ
  have hFψ_val : 𝓕 (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 4 • ψ x) ξ =
      ((2 * Real.pi : ℂ) ^ 4) *
        (𝓕 (sqFunc t) ξ +
          (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((Real.pi : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) +
          (((t⁻¹ : ℝ) : ℂ) - 1 / 2) * (((Real.pi : ℂ) / 2) * (1 + 2 * (Real.pi : ℂ) * (ξ : ℂ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)))) := by
    have hfun : (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 4 • ψ x) =
        fun x : ℝ ↦ ((2 * Real.pi : ℂ) ^ 4) *
          ((sqFunc t x + (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((x : ℂ) ^ 2 + 1)⁻¹) +
            (((t⁻¹ : ℝ) : ℂ) - 1 / 2) * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹) := by
      funext x
      rw [smul_eq_mul, ← hψ_x4 x]
      have hI4 : (I : ℂ) ^ 4 = 1 := by simp [pow_succ, Complex.I_mul_I]
      calc (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 4 * ψ x
          = ((2 * (Real.pi : ℂ)) ^ 4 * I ^ 4) * ((x : ℂ) ^ 4 * ψ x) := by ring
        _ = _ := by rw [hI4, mul_one]
    rw [hfun, fourier_const_mul]
    have h12_int : Integrable (fun x : ℝ ↦
        sqFunc t x + (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((x : ℂ) ^ 2 + 1)⁻¹) :=
      (sqFunc_integrable ht).add (h1_int.const_mul _)
    rw [fourier_add_eq h12_int (h2_int.const_mul _),
        fourier_add_eq (sqFunc_integrable ht) (h1_int.const_mul _),
        fourier_const_mul, fourier_const_mul]
    have hL1 := fourier_lorentzian (a := 1) (by simp) ξ
    have hL2 := fourier_lorentzian_sq ξ
    simp only [one_pow, div_one, mul_one, abs_of_pos hξ] at hL1 hL2
    rw [hL1, hL2]
  have hFQ : ∀ y : ℝ, 𝓕 Q y =
      (c1 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) +
      (c2 * ((Real.pi : ℂ) / 2)) * ((1 + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) := by
    intro y
    change 𝓕 (fun x : ℝ ↦ c1 * ((x : ℂ) ^ 2 + 1)⁻¹ + c2 * (((x : ℂ) ^ 2 + 1) ^ 2)⁻¹) y = _
    rw [fourier_add_eq (h1_int.const_mul c1) (h2_int.const_mul c2),
        fourier_const_mul, fourier_const_mul]
    have hL1 := fourier_lorentzian (a := 1) (by simp) y
    have hL2 := fourier_lorentzian_sq y
    simp only [one_pow, div_one, mul_one] at hL1 hL2
    rw [hL1, hL2]; ring
  have hco : ContDiff ℝ 4 (fun y : ℝ ↦ (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hexp_cd : ContDiff ℝ 4 (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) :=
    (contDiff_const.mul hco).cexp
  have hc1 : ContDiff ℝ 4 (fun y : ℝ ↦ (c1 * (Real.pi : ℂ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) := contDiff_const.mul hexp_cd
  have hc2 : ContDiff ℝ 4 (fun y : ℝ ↦ (c2 * ((Real.pi : ℂ) / 2)) *
      ((1 + 2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))) :=
    contDiff_const.mul ((contDiff_const.add (contDiff_const.mul hco)).mul hexp_cd)
  have hFQ_d4 : iteratedDeriv 4 (𝓕 Q) ξ =
      ((2 * Real.pi : ℂ) ^ 4) *
        ((c1 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)) +
         (c2 * ((Real.pi : ℂ) / 2)) * (2 * (Real.pi : ℂ) * (ξ : ℂ) - 3) *
           Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) := by
    have hfun : 𝓕 Q =ᶠ[𝓝 ξ] fun y : ℝ ↦
        (c1 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) +
        (c2 * ((Real.pi : ℂ) / 2)) * ((1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by rw [hFQ y, abs_of_pos hy]
    rw [hfun.iteratedDeriv_eq 4,
        iteratedDeriv_fun_add hc1.contDiffAt hc2.contDiffAt,
        iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    have he1 : (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
        fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
    have he2 : (fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
        fun y : ℝ ↦ (1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
    rw [← he1.iteratedDeriv_eq 4, ← he2.iteratedDeriv_eq 4,
        iteratedDeriv_four_exp_neg_two_pi hξ, iteratedDeriv_four_mul_exp_neg_two_pi hξ]
    ring
  have hsplit_F : 𝓕 (sqRem t) = fun y ↦ 𝓕 ψ y + 𝓕 Q y := by
    ext y
    have hsq : sqRem t = fun x ↦ ψ x + Q x := by funext x; dsimp [ψ]; ring
    rw [hsq, fourier_add_eq hψ_int hQ_int]
  have hψ_cd : ContDiffAt ℝ 4 (𝓕 ψ) ξ := by
    have hA : ∀ n : ℕ, (n : ℕ∞) ≤ 4 → Integrable (fun v : ℝ ↦ ‖v‖ ^ n * ‖ψ v‖) := by
      intro n hn
      convert (hψ_moments n hn).norm with x
      simp
    exact (Real.contDiff_fourier hA).contDiffAt
  have hQ_cd : ContDiffAt ℝ 4 (𝓕 Q) ξ := by
    have hfun : 𝓕 Q =ᶠ[𝓝 ξ] fun y : ℝ ↦
        (c1 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) +
        (c2 * ((Real.pi : ℂ) / 2)) * ((1 + 2 * (Real.pi : ℂ) * (y : ℂ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by rw [hFQ y, abs_of_pos hy]
    exact (hc1.add hc2).contDiffAt.congr_of_eventuallyEq hfun
  have hsum_d4 : iteratedDeriv 4 (𝓕 (sqRem t)) ξ =
      iteratedDeriv 4 (𝓕 ψ) ξ + iteratedDeriv 4 (𝓕 Q) ξ := by
    rw [hsplit_F]
    exact iteratedDeriv_fun_add hψ_cd hQ_cd
  rw [iteratedDeriv_four_fourier_sqRem ht hξ, hFψ_d4, hFψ_val, hFQ_d4] at hsum_d4
  have hcancel :
      ((2 * Real.pi : ℂ) ^ 4) *
        (𝓕 (sqFunc t) ξ +
          (1 / 2 - 2 * ((t⁻¹ : ℝ) : ℂ)) * ((Real.pi : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) +
          (((t⁻¹ : ℝ) : ℂ) - 1 / 2) * (((Real.pi : ℂ) / 2) * (1 + 2 * (Real.pi : ℂ) * (ξ : ℂ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)))) +
      ((2 * Real.pi : ℂ) ^ 4) *
        ((c1 * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)) +
         (c2 * ((Real.pi : ℂ) / 2)) * (2 * (Real.pi : ℂ) * (ξ : ℂ) - 3) *
           Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) =
      ((2 * Real.pi : ℂ) ^ 4) * 𝓕 (sqFunc t) ξ := by
    dsimp only [c1, c2]; ring
  rw [hcancel] at hsum_d4
  have h2pi4 : (2 * (Real.pi : ℂ)) ^ 4 ≠ 0 :=
    pow_ne_zero 4 (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_left_cancel₀ h2pi4 hsum_d4.symm

/-! ### 4. Poisson Summation & Final Unconditional `d = 2` Analytic Identity -/

private lemma fourier_sqFunc_at_X {X : ℝ} (hX : 0 < X) {ξ : ℝ} (hξ : 0 < ξ) :
    ((2 : ℂ) * ((X : ℂ)⁻¹) ^ 3) * 𝓕 (sqFunc (X ^ 2)⁻¹) ξ =
      -∑' m : ℕ+, ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
        (sqRay0 * Complex.exp (-sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) +
         sqRay1 * Complex.exp (-sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))) := by
  have ht : 0 < (X ^ 2)⁻¹ := by positivity
  rw [fourier_sqFunc_pos ht hξ, ← tsum_neg, ← tsum_mul_left]
  apply tsum_congr; intro m
  have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hα : sqAlpha (X ^ 2)⁻¹ m = Real.sqrt Real.pi * Real.sqrt (m.val : ℝ) * X := by
    unfold sqAlpha
    rw [div_inv_eq_mul, Real.sqrt_mul (by positivity), Real.sqrt_mul Real.pi_pos.le,
        Real.sqrt_sq hX.le]
  have hpi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add Real.pi_pos, Real.rpow_one]
  have hexp1 : -2 * (Real.pi : ℂ) * sqA1 (X ^ 2)⁻¹ m * (ξ : ℂ) =
      -sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) := by
    simp only [sqA1, sqRay1, hα, hpi32]; push_cast; ring
  have hexp2 : -2 * (Real.pi : ℂ) * sqA2 (X ^ 2)⁻¹ m * (ξ : ℂ) =
      -sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) := by
    simp only [sqA2, sqRay0, hα, hpi32]; push_cast; ring
  rw [hexp1, hexp2]
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hm0 : (m.val : ℂ) ≠ 0 := by exact_mod_cast m.property.ne'
  have hsq_m : ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) ^ 2 = (m.val : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hm.le, Complex.ofReal_natCast]
  have hsq_pi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hA1_cube : (sqA1 (X ^ 2)⁻¹ m) ^ 3 =
      ((Real.pi : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) * (m.val : ℂ) *
        ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ) ^ 3) * (-2 - 2 * I) := by
    rw [sqA1, hα, mul_pow]
    have h1 : (((Real.sqrt Real.pi * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) ^ 3 =
        (Real.pi : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) * (m.val : ℂ) *
          ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ) ^ 3 := by
      push_cast
      calc (((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ)) ^ 3
          = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) *
            (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) ^ 2 * ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)) * (X : ℂ) ^ 3 := by ring
        _ = _ := by rw [hsq_pi, hsq_m]; ring
    have h2 : ((1 : ℂ) - I) ^ 3 = -2 - 2 * I := by
      ring_nf; rw [show I ^ 3 = I ^ 2 * I by ring, Complex.I_sq]; ring
    rw [h1, h2]
  have hA2_cube : (sqA2 (X ^ 2)⁻¹ m) ^ 3 =
      ((Real.pi : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) * (m.val : ℂ) *
        ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ) ^ 3) * (-2 + 2 * I) := by
    rw [sqA2, hα, mul_pow]
    have h1 : (((Real.sqrt Real.pi * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) ^ 3 =
        (Real.pi : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) * (m.val : ℂ) *
          ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ) ^ 3 := by
      push_cast
      calc (((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) * (X : ℂ)) ^ 3
          = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) *
            (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) ^ 2 * ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)) * (X : ℂ) ^ 3 := by ring
        _ = _ := by rw [hsq_pi, hsq_m]; ring
    have h2 : ((1 : ℂ) + I) ^ 3 = -2 + 2 * I := by
      ring_nf; rw [show I ^ 3 = I ^ 2 * I by ring, Complex.I_sq]; ring
    rw [h1, h2]
  rw [hA1_cube, hA2_cube]
  simp only [sqRay0, sqRay1, hpi32]
  push_cast
  field_simp [hX0, hm0, Complex.I_ne_zero]
  ring_nf; simp [Complex.I_sq]; ring

private lemma fourier_sqFunc_zero_at_X {X : ℝ} (hX : 0 < X) :
    ((X : ℂ)⁻¹) ^ 3 * 𝓕 (sqFunc (X ^ 2)⁻¹) 0 = sqPartConst := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left (g := fun x : ℝ ↦ sqFunc (X ^ 2)⁻¹ x) X
  simp only [Complex.real_smul, abs_inv, abs_of_pos hX] at hsub
  have heq : (fun u : ℝ ↦ sqFunc (X ^ 2)⁻¹ (X * u)) =
      fun u : ℝ ↦ ((X ^ 2 : ℝ) : ℂ) *
        (if u = 0 then (1 : ℂ) else (((u ^ 2 / (Real.exp (u ^ 2) - 1) : ℝ) : ℂ))) := by
    funext u
    by_cases hu : u = 0
    · subst hu
      simp only [mul_zero, sqFunc, ↓reduceIte, mul_one]
      push_cast; simp
    · have hXu : X * u ≠ 0 := mul_ne_zero hX.ne' hu
      simp only [sqFunc, hXu, hu, ↓reduceIte]
      have harg : (X ^ 2)⁻¹ * (X * u) ^ 2 = u ^ 2 := by field_simp [hX.ne']
      rw [harg]; push_cast; ring
  have h1 : ∫ x : ℝ, sqFunc (X ^ 2)⁻¹ x =
      ((X : ℂ) ^ 3) * sqPartConst := by
    have h2 : ∫ u : ℝ, sqFunc (X ^ 2)⁻¹ (X * u) = ((X : ℂ) ^ 2) * sqPartConst := by
      rw [heq, integral_const_mul, Complex.ofReal_pow]; rfl
    rw [h2] at hsub
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    calc ∫ x : ℝ, sqFunc (X ^ 2)⁻¹ x
        = (X : ℂ) * (((X : ℂ)⁻¹) * ∫ x : ℝ, sqFunc (X ^ 2)⁻¹ x) := by field_simp [hX0]
      _ = (X : ℂ) * ((X : ℂ) ^ 2 * sqPartConst) := by rw [← Complex.ofReal_inv, ← hsub]
      _ = (X : ℂ) ^ 3 * sqPartConst := by ring
  rw [h1]
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  field_simp [hX0]

private lemma fourier_sqFunc_even (t : ℝ) (ξ : ℝ) : 𝓕 (sqFunc t) (-ξ) = 𝓕 (sqFunc t) ξ := by
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun x : ℝ ↦ sqFunc t (-x)) = sqFunc t := by
    funext x
    by_cases hx : x = 0
    · subst hx; simp [sqFunc]
    · simp [sqFunc, hx, neg_ne_zero.mpr hx]
  rw [hfun]

private lemma summable_sqWave_inner {X : ℝ} (hX : 0 < X) (ξ : ℝ) (hξ : 0 < ξ) :
    Summable (fun m : ℕ+ ↦ ‖((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
      (sqRay0 * Complex.exp (-sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) +
       sqRay1 * Complex.exp (-sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))))‖) := by
  let c : ℝ := 2 * Real.pi ^ (3 / 2 : ℝ) * ξ * X
  have hc : 0 < c := by positivity
  let C : ℝ := ‖sqRay0‖ + ‖sqRay1‖
  have hdom := (summable_pow_mul_exp_neg_sqrt hc 1).mul_left C
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hdom
  have hm : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.property
  have hre0 : (-sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))).re =
      -c * Real.sqrt (m.val : ℝ) := by
    simp [sqRay0, c, Complex.mul_re]; ring
  have hre1 : (-sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))).re =
      -c * Real.sqrt (m.val : ℝ) := by
    simp [sqRay1, c, Complex.mul_re]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have htri : ‖sqRay0 * Complex.exp (-sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) +
      sqRay1 * Complex.exp (-sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))‖ ≤
      C * Real.exp (-c * Real.sqrt (m.val : ℝ)) := by
    calc _ ≤ ‖sqRay0 * Complex.exp _‖ + ‖sqRay1 * Complex.exp _‖ := norm_add_le _ _
      _ = ‖sqRay0‖ * Real.exp (-c * Real.sqrt (m.val : ℝ)) +
          ‖sqRay1‖ * Real.exp (-c * Real.sqrt (m.val : ℝ)) := by
            rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, hre0, hre1]
      _ = C * Real.exp (-c * Real.sqrt (m.val : ℝ)) := by dsimp [C]; ring
  have hsqrt_le : Real.sqrt (m.val : ℝ) ≤ (m.val : ℝ) := by
    have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
  calc Real.sqrt (m.val : ℝ) * _
      ≤ (m.val : ℝ) * (C * Real.exp (-c * Real.sqrt (m.val : ℝ))) :=
        mul_le_mul hsqrt_le htri (norm_nonneg _) (by positivity)
    _ = C * ((m.val : ℝ) ^ 1 * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by ring

private lemma summable_fourier_sqFunc_int {X : ℝ} (hX : 0 < X) :
    Summable (fun k : ℤ ↦ 𝓕 (sqFunc (X ^ 2)⁻¹) (k : ℝ)) := by
  have hpos_sum : Summable (fun k : ℕ+ ↦ ‖𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)‖) := by
    let c₀ : ℝ := Real.pi ^ (3 / 2 : ℝ) * X
    have hc₀ : 0 < c₀ := by positivity
    let S₀ : ℝ := ∑' m : ℕ+, (m.val : ℝ) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))
    have hS₀_sum : Summable (fun m : ℕ+ ↦ (m.val : ℝ) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))) := by
      simpa using summable_pow_mul_exp_neg_sqrt hc₀ 1
    let C : ℝ := (X ^ 3 / 2) * (‖sqRay0‖ + ‖sqRay1‖) * S₀
    have hdom : Summable (fun k : ℕ+ ↦ C * Real.exp (-c₀ * (k.val : ℝ))) := by
      have h1 : Summable (fun n : ℕ ↦ Real.exp (-c₀ * (n : ℝ))) := by
        simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hc₀
      exact (h1.subtype (fun n ↦ 0 < n)).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdom
    have hk : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast k.property
    have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.property
    have hval := fourier_sqFunc_at_X hX hk
    have hnorm_eq : ‖𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)‖ =
        (X ^ 3 / 2) * ‖∑' m : ℕ+, ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
          (sqRay0 * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           sqRay1 * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))‖ := by
      have h1 := congrArg norm hval
      rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hX, norm_neg] at h1
      calc ‖𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)‖
          = (X ^ 3 / 2) * (2 * (X⁻¹) ^ 3 * ‖𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)‖) := by
              field_simp [hX.ne']
        _ = _ := by rw [h1]
    rw [hnorm_eq]
    have hle_m (m : ℕ+) :
        ‖((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
          (sqRay0 * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           sqRay1 * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))‖ ≤
        ((‖sqRay0‖ + ‖sqRay1‖) * Real.exp (-c₀ * (k.val : ℝ))) *
          ((m.val : ℝ) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))) := by
      have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.property
      have hm_sqrt : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
      have hre0 : (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
          -(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ)) := by
        simp [sqRay0, c₀, Complex.mul_re]; ring
      have hre1 : (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
          -(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ)) := by
        simp [sqRay1, c₀, Complex.mul_re]; ring
      have hexp_split : Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) ≤
          Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hm_sqrt hc₀.le,
                   mul_le_mul_of_nonneg_left hk1 hc₀.le]
      have hsqrt_le : Real.sqrt (m.val : ℝ) ≤ (m.val : ℝ) := by
        have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have htri : ‖sqRay0 * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
          sqRay1 * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))‖ ≤
          (‖sqRay0‖ + ‖sqRay1‖) * Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) := by
        calc _ ≤ ‖sqRay0 * Complex.exp _‖ + ‖sqRay1 * Complex.exp _‖ := norm_add_le _ _
          _ = (‖sqRay0‖ + ‖sqRay1‖) * Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) := by
              rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, hre0, hre1]; ring
      calc Real.sqrt (m.val : ℝ) * _
          ≤ (m.val : ℝ) * ((‖sqRay0‖ + ‖sqRay1‖) *
              (Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ)))) :=
            mul_le_mul hsqrt_le (htri.trans (mul_le_mul_of_nonneg_left hexp_split (by positivity)))
              (norm_nonneg _) (by positivity)
        _ = ((‖sqRay0‖ + ‖sqRay1‖) * Real.exp (-c₀ * (k.val : ℝ))) *
              ((m.val : ℝ) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))) := by ring
    have htsum_le := (norm_tsum_le_tsum_norm (summable_sqWave_inner hX (k.val : ℝ) hk)).trans
      ((summable_sqWave_inner hX (k.val : ℝ) hk).tsum_le_tsum hle_m (hS₀_sum.mul_left _))
    rw [tsum_mul_left] at htsum_le
    calc (X ^ 3 / 2) * _
        ≤ (X ^ 3 / 2) * (((‖sqRay0‖ + ‖sqRay1‖) * Real.exp (-c₀ * (k.val : ℝ))) * S₀) :=
          mul_le_mul_of_nonneg_left htsum_le (by positivity)
      _ = C * Real.exp (-c₀ * (k.val : ℝ)) := by dsimp [C]; ring
  have hnat : Summable (fun n : ℕ ↦ 𝓕 (sqFunc (X ^ 2)⁻¹) (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    have h := hpos_sum.of_norm
    exact (Equiv.pnatEquivNat.symm.summable_iff.mpr h).congr fun n ↦ by
      simp [Equiv.pnatEquivNat]
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, ?_⟩
  refine hnat.congr fun n ↦ ?_
  rw [Int.cast_neg, Int.cast_natCast, fourier_sqFunc_even]

private lemma tsum_int_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x)
    (hsum : Summable (fun k : ℤ ↦ f (k : ℝ))) :
    (∑' k : ℤ, f (k : ℝ)) = f 0 + 2 * ∑' k : ℕ+, f (k.val : ℝ) := by
  have hnat : Summable (fun n : ℕ ↦ f (n : ℝ)) :=
    hsum.comp_injective Int.ofNat_injective
  have hneg : Summable (fun n : ℕ ↦ f ((-(n + 1 : ℕ) : ℤ) : ℝ)) := by
    have h1 := (summable_nat_add_iff 1).mpr hnat
    refine h1.congr fun n ↦ ?_
    have harg : ((-(n + 1 : ℕ) : ℤ) : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [harg, heven]
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have h0_split : (∑' n : ℕ, f ((n : ℤ) : ℝ)) = f 0 + ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ) := by
    have h1 := hnat.tsum_eq_zero_add
    simpa [Nat.cast_zero] using h1
  have hneg_eq' : (∑' n : ℕ, f (((-(↑n + 1) : ℤ) : ℝ))) = ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ) :=
    tsum_congr fun n ↦ by
      have harg : ((-(↑n + 1) : ℤ) : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [harg, heven]
  rw [h0_split, hneg_eq', tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f (n : ℝ))]
  ring

/-- **100% Unconditional Analytic Identity for Partitions into Squares (`d = 2`)**:
For EVERY `X > 0`:
`2 X⁻³ ∑'_{n : ℕ+} n² / (exp(n² / X²) - 1) =
   sqPartConst - X⁻¹
   - ∑'_{k : ℕ+} ∑'_{m : ℕ+} √m * (sqRay0 * exp(-sqRay0 * k * √m * X)
                                 + sqRay1 * exp(-sqRay1 * k * √m * X))`. -/
theorem squares_partition_analytic_identity {X : ℝ} (hX : 0 < X) :
    ((2 : ℂ) * ((X : ℂ)⁻¹) ^ 3) *
      (∑' n : ℕ+, (((n.val : ℝ) ^ 2 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ)) =
    sqPartConst - ((X : ℂ)⁻¹) -
      ∑' k : ℕ+, ∑' m : ℕ+,
        ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
          (sqRay0 * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           sqRay1 * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) := by
  have ht : 0 < (X ^ 2)⁻¹ := by positivity
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (sqFunc_continuous ht) one_lt_two (sqFunc_isBigO ht) (summable_fourier_sqFunc_int hX) 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hpois
  have hsq_even : ∀ x : ℝ, sqFunc (X ^ 2)⁻¹ (-x) = sqFunc (X ^ 2)⁻¹ x := fun x ↦ by
    by_cases hx : x = 0
    · subst hx; simp [sqFunc]
    · simp [sqFunc, hx, neg_ne_zero.mpr hx]
  have hsq_sum_int : Summable (fun n : ℤ ↦ sqFunc (X ^ 2)⁻¹ (n : ℝ)) := by
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((sqFunc_isBigO ht).comp_tendsto Int.tendsto_coe_cofinite)
  rw [tsum_int_even hsq_even hsq_sum_int,
      tsum_int_even (fourier_sqFunc_even (X ^ 2)⁻¹) (summable_fourier_sqFunc_int hX)] at hpois
  have h0 : sqFunc (X ^ 2)⁻¹ 0 = ((X : ℂ) ^ 2) := by
    simp [sqFunc]
  have hlhs_eq : (∑' n : ℕ+, sqFunc (X ^ 2)⁻¹ (n.val : ℝ)) =
      ∑' n : ℕ+, (((n.val : ℝ) ^ 2 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ) := by
    apply tsum_congr; intro n
    have hn0 : (n.val : ℝ) ≠ 0 := by exact_mod_cast n.property.ne'
    simp only [sqFunc, hn0, ↓reduceIte, inv_mul_eq_div]
  rw [h0, hlhs_eq] at hpois
  have hmul := congrArg (((X : ℂ)⁻¹) ^ 3 * ·) hpois
  rw [mul_add, mul_add, fourier_sqFunc_zero_at_X hX] at hmul
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hterm0 : ((X : ℂ)⁻¹) ^ 3 * (X : ℂ) ^ 2 = ((X : ℂ)⁻¹) := by field_simp [hX0]
  rw [hterm0] at hmul
  have hrhs_waves : ((X : ℂ)⁻¹) ^ 3 * (2 * ∑' k : ℕ+, 𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)) =
      -∑' k : ℕ+, ∑' m : ℕ+,
        ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) *
          (sqRay0 * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           sqRay1 * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) := by
    rw [show ((X : ℂ)⁻¹) ^ 3 * (2 * ∑' k : ℕ+, 𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ)) =
        ((2 : ℂ) * ((X : ℂ)⁻¹) ^ 3) * ∑' k : ℕ+, 𝓕 (sqFunc (X ^ 2)⁻¹) (k.val : ℝ) by ring,
        ← tsum_mul_left, ← tsum_neg]
    apply tsum_congr; intro k
    have hk : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast k.property
    exact fourier_sqFunc_at_X hX hk
  rw [hrhs_waves] at hmul
  linear_combination hmul

end
end CubicTheta.AllD
