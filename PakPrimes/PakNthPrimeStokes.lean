module

public import PakPrimes.PakNthPrimeEngine
public import PakPrimes.PrimePencilEone
public import PakPrimes.PrimePencilHalfPlane
public import PakPrimes.NthPrimeCriterion
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic

/-! # Pak Conjecture 2.5a (`∑ p_n q^n`) — Exact Stokes Relation, Holomorphicity of `R(t)`, and Engine Bridge

This module formalizes Pillar 1 of the proof of Pak's ICM 2018 Conjecture 2.5a and wires the
literal exponential-integral Stokes perturbation and lateral contour integrals `I_±(u)` directly
into `PakPrimes.PakNthPrimeEngine.pak_nth_prime_engine_eq_zero` and
`PakPrimes.NthPrime.series`:

1. **Exact bounds on `E1(x) = ∫_{u > x} e^{-u}/u du`**: positivity, exponential tail decay
   `E1 x ≤ exp (-x) / x`, antitonicity, logarithmic origin growth `E1 x ≤ -log x + E1 1` on `(0, 1]`,
   and global integrability of `x ↦ exp (-x + σ * E1 x)` on `(0, ∞)` for every `σ < 1`.
2. **Holomorphicity & analyticity of `R_integral(t) = t ∫_0^∞ exp(-x + t E1(x)) dx`**:
   complex differentiability (`DifferentiableOn ℂ`) and analyticity (`AnalyticOnNhd ℂ`) on the
   full open half-plane `{t : ℂ | t.re < 1}` via dominated differentiation under the integral sign.
3. **Exact Maclaurin / moment series of `R_integral`** on `‖t‖ < 1`:
   `R_integral t = ∑' l : ℕ, (pencilMoment l / l!) * t^(l + 1)` with strictly positive
   coefficients and explicit geometric growth bounds.
4. **Exact Stokes perturbation `η(t) = -(exp(2πi t) - 1) R_integral(t)`**:
   explicit Cauchy-product coefficients `etaCoeff m`, convergence on `‖t‖ < 1`, geometric bound
   `‖etaCoeff m‖ ≤ C * 2^m`, explicit `etaCoeff 2 = -2πi ≠ 0` and `etaCoeff 3 ≠ 0`, and
   unconditional proof of `{m : ℕ | 2 ≤ m ∧ etaCoeff m ≠ 0}.Infinite`.
5. **Exact complex `Ei(w)`, positive-axis `T_integral`, literal valley contour integrals `I_±(u)`**,
   integration by parts, contour invariance, exact contour collapse `I_±(u) = R(e^{-u}) + e^{∓ iπ e^{-u}} T(e^{-u})`,
   `ContDiff ℝ ⊤` smoothness on `ℝ`, and the exact Stokes identity
   `I_-(u) = exp(2πi e^{-u}) I_+(u) - (exp(2πi e^{-u}) - 1) R(e^{-u})`.
6. **Direct wiring into `PakNthPrimeEngine.pak_nth_prime_engine_eq_zero`** and autonomous transfer
   from `PakPrimes.NthPrime.series`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.PakNthPrimeStokes

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology BigOperators

noncomputable section

/-! ### 1. Exact Origin & Tail Bounds on `E1` and Integrability on `{Re t < 1}` -/

/-- `PakNthPrimeEngine.E1` coincides definitionally with `PrimePencil.Eone`. -/
lemma E1_eq_Eone : PakNthPrimeEngine.E1 = PrimePencil.Eone := rfl

lemma E1_pos {x : ℝ} (hx : 0 < x) : 0 < PakNthPrimeEngine.E1 x :=
  PrimePencil.eone_pos hx

lemma E1_measurable : Measurable PakNthPrimeEngine.E1 :=
  PrimePencil.eone_measurable

lemma E1_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt PakNthPrimeEngine.E1 (-Real.exp (-x) / x) x :=
  PrimePencil.eone_hasDerivAt hx

lemma E1_le_exp_div {x : ℝ} (hx : 0 < x) :
    PakNthPrimeEngine.E1 x ≤ Real.exp (-x) / x :=
  PrimePencil.eone_exp_bound hx

lemma E1_one_le : PakNthPrimeEngine.E1 1 ≤ Real.exp (-1) := by
  simpa using E1_le_exp_div zero_lt_one

lemma E1_antitoneOn : AntitoneOn PakNthPrimeEngine.E1 (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hhint := PakNthPrimeEngine.integrableOn_exp_neg_div_Ioi hx
  have hsplit : (∫ u in Set.Ioc x y, Real.exp (-u) / u) +
      ∫ u in Set.Ioi y, Real.exp (-u) / u =
      ∫ u in Set.Ioi x, Real.exp (-u) / u := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hhint.mono_set Set.Ioc_subset_Ioi_self)
      (hhint.mono_set (Set.Ioi_subset_Ioi hxy)), Set.Ioc_union_Ioi_eq_Ioi hxy]
  have hnonneg : 0 ≤ ∫ u in Set.Ioc x y, Real.exp (-u) / u := by
    refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
    have hu_pos : 0 < u := lt_trans hx hu.1
    positivity
  change ∫ u in Set.Ioi y, Real.exp (-u) / u ≤ ∫ u in Set.Ioi x, Real.exp (-u) / u
  linarith

/-- Exact logarithmic growth bound at the origin: for `0 < x ≤ 1`,
`E1 x ≤ -log x + E1 1`. -/
theorem E1_le_neg_log_add_E1_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    PakNthPrimeEngine.E1 x ≤ -Real.log x + PakNthPrimeEngine.E1 1 := by
  have hhint := PakNthPrimeEngine.integrableOn_exp_neg_div_Ioi hx
  have hsplit : PakNthPrimeEngine.E1 x =
      (∫ u in Set.Ioc x 1, Real.exp (-u) / u) + PakNthPrimeEngine.E1 1 := by
    dsimp only [PakNthPrimeEngine.E1]
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hhint.mono_set Set.Ioc_subset_Ioi_self)
      (hhint.mono_set (Set.Ioi_subset_Ioi hx1)), Set.Ioc_union_Ioi_eq_Ioi hx1]
  have hinv_int : IntegrableOn (fun u : ℝ => u⁻¹) (Set.Ioc x 1) := by
    have hcont : ContinuousOn (fun u : ℝ => u⁻¹) (Set.Icc x 1) :=
      continuousOn_inv₀.mono fun u hu => (lt_of_lt_of_le hx hu.1).ne'
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmono : (∫ u in Set.Ioc x 1, Real.exp (-u) / u) ≤ ∫ u in Set.Ioc x 1, u⁻¹ := by
    refine setIntegral_mono_on (hhint.mono_set Set.Ioc_subset_Ioi_self) hinv_int
      measurableSet_Ioc fun u hu => ?_
    have hu_pos : 0 < u := lt_trans hx hu.1
    rw [div_eq_mul_inv]
    calc Real.exp (-u) * u⁻¹ ≤ 1 * u⁻¹ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) (inv_nonneg.mpr hu_pos.le)
      _ = u⁻¹ := one_mul _
  have hlog : (∫ u in Set.Ioc x 1, u⁻¹) = -Real.log x := by
    rw [← intervalIntegral.integral_of_le hx1, integral_inv_of_pos hx zero_lt_one,
      one_div, Real.log_inv]
  linarith

theorem E1_le_neg_log_add_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    PakNthPrimeEngine.E1 x ≤ -Real.log x + 1 := by
  have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith [E1_le_neg_log_add_E1_one hx hx1, E1_one_le]

/-- Global integrability of `x ↦ exp (-x + σ * E1 x)` on `(0, ∞)` for every real `σ < 1`. -/
theorem integrableOn_exp_neg_add_mul_E1 {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (fun x : ℝ => Real.exp (-x + σ * PakNthPrimeEngine.E1 x)) (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-x + σ * PakNthPrimeEngine.E1 x)) (volume.restrict (Set.Ioi 0)) :=
    (measurable_id.neg.add (measurable_const.mul E1_measurable)).exp.aestronglyMeasurable
  by_cases hσ0 : σ ≤ 0
  · have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
        (fun x _ => by simp) measurableSet_Ioi
    refine hexp.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith [E1_pos hx])
  · push Not at hσ0
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
    constructor
    · have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioc 0 1) := by
        have hi : IntervalIntegrable (fun x : ℝ => x ^ (-σ)) volume 0 1 :=
          intervalIntegral.intervalIntegrable_rpow' (by linarith)
        exact hi.1
      have hdom : IntegrableOn (fun x : ℝ => Real.exp (σ * PakNthPrimeEngine.E1 1) * x ^ (-σ))
          (Set.Ioc 0 1) :=
        hrpow_int.const_mul _
      refine hdom.mono'
        ((measurable_id.neg.add (measurable_const.mul E1_measurable)).exp.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      have hE := E1_le_neg_log_add_E1_one hx.1 hx.2
      have harg : -x + σ * PakNthPrimeEngine.E1 x ≤
          σ * PakNthPrimeEngine.E1 1 + (-σ) * Real.log x := by
        nlinarith [hx.1]
      calc Real.exp (-x + σ * PakNthPrimeEngine.E1 x)
          ≤ Real.exp (σ * PakNthPrimeEngine.E1 1 + (-σ) * Real.log x) := Real.exp_le_exp.mpr harg
        _ = Real.exp (σ * PakNthPrimeEngine.E1 1) * Real.exp ((-σ) * Real.log x) := Real.exp_add _ _
        _ = Real.exp (σ * PakNthPrimeEngine.E1 1) * x ^ (-σ) := by
            rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]
    · have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 1) :=
        (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 1).congr_fun
          (fun x _ => by simp) measurableSet_Ioi
      have hdom : IntegrableOn (fun x : ℝ => Real.exp (σ * PakNthPrimeEngine.E1 1) * Real.exp (-x))
          (Set.Ioi 1) :=
        hexp.const_mul _
      refine hdom.mono'
        ((measurable_id.neg.add (measurable_const.mul E1_measurable)).exp.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hE : PakNthPrimeEngine.E1 x ≤ PakNthPrimeEngine.E1 1 :=
        E1_antitoneOn (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr hx_pos) (le_of_lt hx)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)

lemma norm_cexp_neg_add_mul_E1 (t : ℂ) (x : ℝ) :
    ‖Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ))‖ =
      Real.exp (-x + t.re * PakNthPrimeEngine.E1 x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem integrableOn_cexp_neg_add_mul_E1 {t : ℂ} (ht : t.re < 1) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)))
      (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)))
      (volume.restrict (Set.Ioi 0)) := by
    have h1 : Measurable (fun x : ℝ => -(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)) :=
      (Complex.continuous_ofReal.measurable.neg).add
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp E1_measurable))
    exact (Complex.continuous_exp.measurable.comp h1).aestronglyMeasurable
  refine (integrableOn_exp_neg_add_mul_E1 ht).mono' hmeas ?_
  filter_upwards with x
  rw [norm_cexp_neg_add_mul_E1]

/-! ### 2. Holomorphicity & Analyticity of `R_integral` on `{t : ℂ | t.re < 1}` -/

/-- The inner Laplace-exponential integral `∫_{x > 0} exp (-x + t * E1 x) dx`. -/
@[expose] def R_inner (t : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ))

lemma R_integral_eq_mul_R_inner (t : ℂ) :
    PakNthPrimeEngine.R_integral t = t * R_inner t := rfl

/-- Dominated differentiation under the integral sign for `R_inner` on `{t : ℂ | t.re < 1}`. -/
theorem hasDerivAt_R_inner {t₀ : ℂ} (ht₀ : t₀.re < 1) :
    HasDerivAt R_inner
      (∫ x in Set.Ioi (0 : ℝ),
        (PakNthPrimeEngine.E1 x : ℂ) * Complex.exp (-(x : ℂ) + t₀ * (PakNthPrimeEngine.E1 x : ℂ)))
      t₀ := by
  let r : ℝ := (1 - t₀.re) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  let σ : ℝ := max (t₀.re + r) 0
  have hσ_nn : 0 ≤ σ := le_max_right _ _
  have hσ_lt : σ < 1 := max_lt (by dsimp [r]; linarith) zero_lt_one
  let σ' : ℝ := (σ + 1) / 2
  have hσ'_lt : σ' < 1 := by dsimp [σ']; linarith
  let δ : ℝ := σ' - σ
  have hδ : 0 < δ := by dsimp [δ, σ']; linarith
  let bound : ℝ → ℝ := fun x => δ⁻¹ * Real.exp (-x + σ' * PakNthPrimeEngine.E1 x)
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_exp_neg_add_mul_E1 hσ'_lt).const_mul δ⁻¹
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable
        (fun x : ℝ => Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
    refine Eventually.of_forall fun t => ?_
    have h1 : Measurable (fun x : ℝ => -(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)) :=
      (Complex.continuous_ofReal.measurable.neg).add
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp E1_measurable))
    exact (Complex.continuous_exp.measurable.comp h1).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => (PakNthPrimeEngine.E1 x : ℂ) *
        Complex.exp (-(x : ℂ) + t₀ * (PakNthPrimeEngine.E1 x : ℂ)))
      (volume.restrict (Set.Ioi 0)) := by
    have h1 : Measurable (fun x : ℝ => -(x : ℂ) + t₀ * (PakNthPrimeEngine.E1 x : ℂ)) :=
      (Complex.continuous_ofReal.measurable.neg).add
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp E1_measurable))
    exact ((Complex.continuous_ofReal.measurable.comp E1_measurable).mul
      (Complex.continuous_exp.measurable.comp h1)).aestronglyMeasurable
  have hbound_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ∀ t ∈ Metric.ball t₀ r,
      ‖(PakNthPrimeEngine.E1 x : ℂ) *
        Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ))‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have hEx : 0 < PakNthPrimeEngine.E1 x := E1_pos hx
    have htre : t.re ≤ σ := by
      have hdist : ‖t - t₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have hre_le : t.re - t₀.re ≤ ‖t - t₀‖ := by
        simpa [Complex.sub_re] using Complex.re_le_norm (t - t₀)
      exact le_trans (by linarith) (le_max_left _ _)
    have hlin : δ * PakNthPrimeEngine.E1 x ≤ Real.exp (δ * PakNthPrimeEngine.E1 x) :=
      le_trans (by linarith) (Real.add_one_le_exp (δ * PakNthPrimeEngine.E1 x))
    have hEx_le : PakNthPrimeEngine.E1 x ≤ δ⁻¹ * Real.exp (δ * PakNthPrimeEngine.E1 x) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm]
      exact hlin
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hEx.le, norm_cexp_neg_add_mul_E1]
    dsimp only [bound]
    calc PakNthPrimeEngine.E1 x * Real.exp (-x + t.re * PakNthPrimeEngine.E1 x)
        ≤ (δ⁻¹ * Real.exp (δ * PakNthPrimeEngine.E1 x)) *
            Real.exp (-x + σ * PakNthPrimeEngine.E1 x) := by
          exact mul_le_mul hEx_le (Real.exp_le_exp.mpr (by nlinarith))
            (Real.exp_pos _).le (by positivity)
      _ = δ⁻¹ * (Real.exp (δ * PakNthPrimeEngine.E1 x) * Real.exp (-x + σ * PakNthPrimeEngine.E1 x)) := by
          ring
      _ = δ⁻¹ * Real.exp (-x + σ' * PakNthPrimeEngine.E1 x) := by
          rw [← Real.exp_add]; congr 2; dsimp [δ]; ring
  have hdiff_ae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ t ∈ Metric.ball t₀ r,
      HasDerivAt (fun z : ℂ => Complex.exp (-(x : ℂ) + z * (PakNthPrimeEngine.E1 x : ℂ)))
        ((PakNthPrimeEngine.E1 x : ℂ) *
          Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ))) t := by
    filter_upwards with x t _
    have h1 : HasDerivAt (fun z : ℂ => -(x : ℂ) + z * (PakNthPrimeEngine.E1 x : ℂ))
        (PakNthPrimeEngine.E1 x : ℂ) t := by
      have hmul : HasDerivAt (fun z : ℂ => z * (PakNthPrimeEngine.E1 x : ℂ))
          (PakNthPrimeEngine.E1 x : ℂ) t := by
        simpa using (hasDerivAt_id t).mul_const (PakNthPrimeEngine.E1 x : ℂ)
      exact hmul.const_add (-(x : ℂ))
    convert h1.cexp using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hr)
    hF_meas (integrableOn_cexp_neg_add_mul_E1 ht₀) hF'_meas hbound_ae hbound_int hdiff_ae).2

theorem differentiableOn_R_inner :
    DifferentiableOn ℂ R_inner {t : ℂ | t.re < 1} :=
  fun _ ht => (hasDerivAt_R_inner ht).differentiableAt.differentiableWithinAt

/-- **Exact Holomorphicity of `R_integral`**: `R_integral(t) = t ∫_0^∞ exp(-x + t E1(x)) dx`
is complex-differentiable on the open half-plane `{t : ℂ | t.re < 1}`. -/
theorem R_holomorphic_on_halfplane :
    DifferentiableOn ℂ PakNthPrimeEngine.R_integral {t : ℂ | t.re < 1} := by
  intro t ht
  exact ((hasDerivAt_id t).mul (hasDerivAt_R_inner ht)).differentiableAt.differentiableWithinAt

lemma isOpen_halfplane_re_lt_one : IsOpen {t : ℂ | t.re < 1} :=
  isOpen_lt Complex.continuous_re continuous_const

lemma isPreconnected_halfplane_re_lt_one : IsPreconnected {t : ℂ | t.re < 1} := by
  have hconv : Convex ℝ {t : ℂ | t.re < 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    by_cases ha0 : a = 0
    · subst ha0; nlinarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith
  exact hconv.isPreconnected

/-- Full complex analyticity of `R_integral` on `{t : ℂ | t.re < 1}`. -/
theorem R_analyticOnNhd_halfplane :
    AnalyticOnNhd ℂ PakNthPrimeEngine.R_integral {t : ℂ | t.re < 1} :=
  R_holomorphic_on_halfplane.analyticOnNhd isOpen_halfplane_re_lt_one

/-- Unconditional continuity of `R_integral` at `-1` (discharging the continuity hypothesis
of `PakNthPrimeEngine.infinitely_many_cm_ne_zero`). -/
theorem R_integral_continuousAt_neg_one :
    ContinuousAt PakNthPrimeEngine.R_integral (-1) :=
  (R_holomorphic_on_halfplane.differentiableAt
    (isOpen_halfplane_re_lt_one.mem_nhds (by simp : (-1 : ℂ).re < 1))).continuousAt

/-! ### 3. Exact Power-Series / Moment Representation of `R_integral` on `‖t‖ < 1` -/

/-- Exact Taylor coefficients of `R_inner`: `r_l = (1/l!) ∫_0^∞ e^{-x} E1(x)^l dx`. -/
@[expose] def R_momentCoeff (l : ℕ) : ℝ :=
  PrimePencil.pencilMoment l / (l.factorial : ℝ)

theorem R_momentCoeff_pos (l : ℕ) : 0 < R_momentCoeff l :=
  div_pos (PrimePencil.pencilMoment_pos l) (by positivity)

theorem R_momentCoeff_zero : R_momentCoeff 0 = 1 := by
  have h0 : PrimePencil.pencilMoment 0 = 1 := by
    simp [PrimePencil.pencilMoment, integral_exp_Iic_zero]
  simp [R_momentCoeff, h0]

/-- Exact Maclaurin expansion of `R_inner` on the open unit disk `‖t‖ < 1`. -/
theorem hasSum_R_inner {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun l : ℕ => (R_momentCoeff l : ℂ) * t ^ l) (R_inner t) := by
  let F : ℕ → ℝ → ℂ := fun N x =>
    ∑ l ∈ Finset.range N, Complex.exp (-(x : ℂ)) * ((t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))
  have hF_meas : ∀ N, AEStronglyMeasurable (F N) (volume.restrict (Set.Ioi 0)) := by
    intro N
    have hm : Measurable (F N) := by
      refine Finset.measurable_sum _ fun l _ => ?_
      have hE : Measurable (fun x : ℝ => (PakNthPrimeEngine.E1 x : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp E1_measurable
      exact (Complex.continuous_exp.measurable.comp Complex.continuous_ofReal.measurable.neg).mul
        (((measurable_const.mul hE).pow_const l).div_const _)
    exact hm.aestronglyMeasurable
  have hbound_int : Integrable (fun x : ℝ => Real.exp (-x + ‖t‖ * PakNthPrimeEngine.E1 x))
      (volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_neg_add_mul_E1 ht
  have hF_bound : ∀ N, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖F N x‖ ≤ Real.exp (-x + ‖t‖ * PakNthPrimeEngine.E1 x) := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hEx : 0 ≤ PakNthPrimeEngine.E1 x := (E1_pos hx).le
    have htsum : HasSum (fun l : ℕ => (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ))
        (Real.exp (‖t‖ * PakNthPrimeEngine.E1 x)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖t‖ * PakNthPrimeEngine.E1 x))
    calc ‖F N x‖
        ≤ ∑ l ∈ Finset.range N,
            ‖Complex.exp (-(x : ℂ)) *
              ((t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))‖ := norm_sum_le _ _
      _ = Real.exp (-x) * ∑ l ∈ Finset.range N,
            (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [norm_mul, Complex.norm_exp, norm_div, norm_pow, norm_mul,
            Complex.norm_real, Real.norm_of_nonneg hEx, Complex.norm_natCast]
          simp
      _ ≤ Real.exp (-x) * Real.exp (‖t‖ * PakNthPrimeEngine.E1 x) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact sum_le_hasSum (Finset.range N) (fun l _ => by positivity) htsum
      _ = Real.exp (-x + ‖t‖ * PakNthPrimeEngine.E1 x) := by rw [← Real.exp_add]
  have hF_lim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun N => F N x) atTop
        (𝓝 (Complex.exp (-(x : ℂ) + t * (PakNthPrimeEngine.E1 x : ℂ)))) := by
    filter_upwards with x
    have hhs := NormedSpace.expSeries_div_hasSum_exp (t * (PakNthPrimeEngine.E1 x : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at hhs
    have hmul : Tendsto (fun N => Complex.exp (-(x : ℂ)) *
        ∑ l ∈ Finset.range N, (t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))
        atTop (𝓝 (Complex.exp (-(x : ℂ)) * Complex.exp (t * (PakNthPrimeEngine.E1 x : ℂ)))) :=
      hhs.tendsto_sum_nat.const_mul _
    rw [← Complex.exp_add] at hmul
    refine hmul.congr fun N => ?_
    simp [F, Finset.mul_sum]
  have hint_lim : Tendsto (fun N => ∫ x in Set.Ioi (0 : ℝ), F N x) atTop (𝓝 (R_inner t)) :=
    tendsto_integral_of_dominated_convergence _ hF_meas hbound_int hF_bound hF_lim
  have hterm_int : ∀ l : ℕ,
      IntegrableOn (fun x : ℝ => Complex.exp (-(x : ℂ)) *
        ((t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))) (Set.Ioi 0) := by
    intro l
    have heq : (fun x : ℝ => Complex.exp (-(x : ℂ)) *
          ((t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))) =
        fun x : ℝ => (t ^ l / (l.factorial : ℂ)) *
          (((Real.exp (-x) * PrimePencil.Eone x ^ l : ℝ) : ℂ)) := by
      ext x
      rw [mul_pow, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, E1_eq_Eone]
      push_cast
      ring
    rw [heq]
    exact ((Complex.ofRealCLM.integrable_comp (PrimePencil.pencilMoment_integrable l)).const_mul _)
  have hint_eq : ∀ N : ℕ,
      (∫ x in Set.Ioi (0 : ℝ), F N x) = ∑ l ∈ Finset.range N, (R_momentCoeff l : ℂ) * t ^ l := by
    intro N
    dsimp only [F]
    rw [integral_finsetSum _ fun l _ => hterm_int l]
    refine Finset.sum_congr rfl fun l _ => ?_
    have heq : (fun x : ℝ => Complex.exp (-(x : ℂ)) *
          ((t * (PakNthPrimeEngine.E1 x : ℂ)) ^ l / (l.factorial : ℂ))) =
        fun x : ℝ => (t ^ l / (l.factorial : ℂ)) *
          (((Real.exp (-x) * PrimePencil.Eone x ^ l : ℝ) : ℂ)) := by
      ext x
      rw [mul_pow, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, E1_eq_Eone]
      push_cast
      ring
    have hint_ofReal :
        (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) * PrimePencil.Eone x ^ l : ℝ) : ℂ)) =
        (((∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * PrimePencil.Eone x ^ l) : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm (PrimePencil.pencilMoment_integrable l)
    rw [heq, integral_const_mul, hint_ofReal]
    dsimp only [R_momentCoeff, PrimePencil.pencilMoment]
    push_cast
    ring
  have hsum_norm : Summable (fun l : ℕ => ‖(R_momentCoeff l : ℂ) * t ^ l‖) := by
    refine summable_of_sum_range_le (c := ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + ‖t‖ * PakNthPrimeEngine.E1 x))
      (fun l => norm_nonneg _) (fun N => ?_)
    have hnorm_eq : ∀ l : ℕ, ‖(R_momentCoeff l : ℂ) * t ^ l‖ =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ) := by
      intro l
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (R_momentCoeff_pos l).le, norm_pow]
      dsimp only [R_momentCoeff, PrimePencil.pencilMoment]
      have heq : (fun x : ℝ => Real.exp (-x) * (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ)) =
          fun x : ℝ => (‖t‖ ^ l / (l.factorial : ℝ)) * (Real.exp (-x) * PrimePencil.Eone x ^ l) := by
        ext x; rw [mul_pow, E1_eq_Eone]; ring
      rw [heq, integral_const_mul]
      ring
    simp_rw [hnorm_eq]
    have hsub_int : ∀ l : ℕ, IntegrableOn
        (fun x : ℝ => Real.exp (-x) * (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ))
        (Set.Ioi 0) := by
      intro l
      have heq : (fun x : ℝ => Real.exp (-x) * (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ)) =
          fun x : ℝ => (‖t‖ ^ l / (l.factorial : ℝ)) * (Real.exp (-x) * PrimePencil.Eone x ^ l) := by
        ext x; rw [mul_pow, E1_eq_Eone]; ring
      rw [heq]
      exact (PrimePencil.pencilMoment_integrable l).const_mul _
    rw [← integral_finsetSum _ fun l _ => hsub_int l]
    refine setIntegral_mono_on
      (integrable_finsetSum _ fun l _ => hsub_int l)
      (integrableOn_exp_neg_add_mul_E1 ht) measurableSet_Ioi fun x hx => ?_
    have hEx : 0 ≤ PakNthPrimeEngine.E1 x := (E1_pos hx).le
    have htsum : HasSum (fun l : ℕ => (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ))
        (Real.exp (‖t‖ * PakNthPrimeEngine.E1 x)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖t‖ * PakNthPrimeEngine.E1 x))
    calc (∑ l ∈ Finset.range N, Real.exp (-x) * (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ))
        = Real.exp (-x) * ∑ l ∈ Finset.range N, (‖t‖ * PakNthPrimeEngine.E1 x) ^ l / (l.factorial : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
      _ ≤ Real.exp (-x) * Real.exp (‖t‖ * PakNthPrimeEngine.E1 x) :=
          mul_le_mul_of_nonneg_left (sum_le_hasSum (Finset.range N) (fun l _ => by positivity) htsum)
            (Real.exp_pos _).le
      _ = Real.exp (-x + ‖t‖ * PakNthPrimeEngine.E1 x) := by rw [← Real.exp_add]
  have htend : Tendsto (fun N => ∑ l ∈ Finset.range N, (R_momentCoeff l : ℂ) * t ^ l)
      atTop (𝓝 (R_inner t)) := by
    simpa only [hint_eq] using hint_lim
  have hsum : Summable (fun l : ℕ => (R_momentCoeff l : ℂ) * t ^ l) := hsum_norm.of_norm
  have heq : (∑' l : ℕ, (R_momentCoeff l : ℂ) * t ^ l) = R_inner t :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat htend
  exact heq ▸ hsum.hasSum

theorem summable_norm_R_momentCoeff {t : ℂ} (ht : ‖t‖ < 1) :
    Summable (fun l : ℕ => ‖(R_momentCoeff l : ℂ) * t ^ l‖) := by
  have hpos := hasSum_R_inner (t := (‖t‖ : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg (norm_nonneg t)] using ht)
  have hsum_real : Summable (fun l : ℕ => R_momentCoeff l * ‖t‖ ^ l) := by
    have hre := (Complex.reCLM.hasSum hpos).summable
    refine hre.congr fun l => ?_
    simp [Complex.reCLM_apply, ← Complex.ofReal_pow]
  refine hsum_real.congr fun l => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (R_momentCoeff_pos l).le, norm_pow]

/-- Exact power-series / moment representation of `R_integral` on `‖t‖ < 1`:
`R_integral t = ∑' l : ℕ, ((pencilMoment l / l!) : ℂ) * t^(l + 1)`. -/
theorem R_integral_eq_tsum {t : ℂ} (ht : ‖t‖ < 1) :
    PakNthPrimeEngine.R_integral t =
      ∑' l : ℕ, (R_momentCoeff l : ℂ) * t ^ (l + 1) := by
  have h := (hasSum_R_inner ht).mul_left t
  rw [R_integral_eq_mul_R_inner, ← h.tsum_eq]
  congr 1
  ext l
  rw [pow_succ]
  ring

/-- Explicit geometric growth bound on `R_momentCoeff l` for any radius `0 < s < 1`. -/
theorem R_momentCoeff_le_geom {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (l : ℕ) :
    R_momentCoeff l ≤
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x)) * (s⁻¹) ^ l := by
  have ht : ‖(s : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hs0] using hs1
  have hsum := hasSum_R_inner ht
  have hre : HasSum (fun k : ℕ => R_momentCoeff k * s ^ k)
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x)) := by
    have h1 := Complex.reCLM.hasSum hsum
    have hR : (R_inner (s : ℂ)).re =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x) := by
      dsimp only [R_inner]
      have hfun : (fun x : ℝ => Complex.exp (-(x : ℂ) + (s : ℂ) * (PakNthPrimeEngine.E1 x : ℂ))) =
          fun x : ℝ => ((Real.exp (-x + s * PakNthPrimeEngine.E1 x) : ℝ) : ℂ) := by
        ext x
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [hfun]
      have hint_ofReal : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x + s * PakNthPrimeEngine.E1 x) : ℝ) : ℂ)) =
          (((∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x)) : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm (integrableOn_exp_neg_add_mul_E1 hs1)
      rw [hint_ofReal]
      simp
    change HasSum (fun k : ℕ => ((R_momentCoeff k : ℂ) * (s : ℂ) ^ k).re) (R_inner (s : ℂ)).re at h1
    rw [hR] at h1
    refine h1.congr_fun fun k => ?_
    simp [← Complex.ofReal_pow]
  have hle : R_momentCoeff l * s ^ l ≤
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x) := by
    have h1 := sum_le_hasSum ({l} : Finset ℕ)
      (fun k _ => mul_nonneg (R_momentCoeff_pos k).le (pow_nonneg hs0.le k)) hre
    simpa using h1
  calc R_momentCoeff l = (R_momentCoeff l * s ^ l) * (s⁻¹) ^ l := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0.ne', one_pow, mul_one]
    _ ≤ (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + s * PakNthPrimeEngine.E1 x)) * (s⁻¹) ^ l :=
        mul_le_mul_of_nonneg_right hle (by positivity)

/-! ### 4. Exact Power-Series Expansion & Unconditional Infinite Support of `η(t)` -/

/-- The literal Stokes perturbation function `η(t) = -(exp (2πi t) - 1) * R_integral t`. -/
@[expose] def eta_integral (t : ℂ) : ℂ :=
  -(Complex.exp (2 * Real.pi * I * t) - 1) * PakNthPrimeEngine.R_integral t

/-- Explicit Maclaurin coefficients of `η(t)` (`c_m = 0` for `m < 2`). -/
@[expose] def etaCoeff (m : ℕ) : ℂ :=
  if m < 2 then 0
  else ∑ l ∈ Finset.range (m - 1),
    (-((2 * Real.pi * I) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℂ))) *
      (R_momentCoeff l : ℂ)

theorem eta_holomorphic_on_halfplane :
    DifferentiableOn ℂ eta_integral {t : ℂ | t.re < 1} := by
  have hexp : Differentiable ℂ (fun t : ℂ => -(Complex.exp (2 * Real.pi * I * t) - 1)) :=
    ((Complex.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id)).sub
      (differentiable_const 1)).neg
  exact hexp.differentiableOn.mul R_holomorphic_on_halfplane

theorem eta_analyticOnNhd_halfplane :
    AnalyticOnNhd ℂ eta_integral {t : ℂ | t.re < 1} :=
  eta_holomorphic_on_halfplane.analyticOnNhd isOpen_halfplane_re_lt_one

/-- Exact trigonometric factorization `η(t) = -2i exp(iπ t) * (sin(π t) * R_integral t)`
matching `PakPrimes.PrimePencil.massApproximant_factored_affine_bound`. -/
theorem eta_integral_eq_sin_mul (t : ℂ) :
    eta_integral t =
      -2 * I * Complex.exp (I * (Real.pi : ℂ) * t) *
        (Complex.sin ((Real.pi : ℂ) * t) * PakNthPrimeEngine.R_integral t) := by
  dsimp only [eta_integral]
  rw [Complex.sin]
  have h1 : Complex.exp (I * (Real.pi : ℂ) * t) * Complex.exp (-(Real.pi : ℂ) * t * I) = 1 := by
    rw [← Complex.exp_add]
    have : I * (Real.pi : ℂ) * t + -(Real.pi : ℂ) * t * I = 0 := by ring
    rw [this, Complex.exp_zero]
  have h2 : Complex.exp (I * (Real.pi : ℂ) * t) * Complex.exp ((Real.pi : ℂ) * t * I) =
      Complex.exp (2 * (Real.pi : ℂ) * I * t) := by
    rw [← Complex.exp_add]
    congr 1; ring
  have hI2 : (2 * I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hfac : -(Complex.exp (2 * (Real.pi : ℂ) * I * t) - 1) =
      -2 * I * Complex.exp (I * (Real.pi : ℂ) * t) *
        ((Complex.exp (-(Real.pi : ℂ) * t * I) - Complex.exp ((Real.pi : ℂ) * t * I)) * I / 2) := by
    have hI : I * I = -1 := Complex.I_mul_I
    calc -(Complex.exp (2 * (Real.pi : ℂ) * I * t) - 1)
        = 1 - Complex.exp (2 * (Real.pi : ℂ) * I * t) := by ring
      _ = Complex.exp (I * (Real.pi : ℂ) * t) * Complex.exp (-(Real.pi : ℂ) * t * I) -
            Complex.exp (I * (Real.pi : ℂ) * t) * Complex.exp ((Real.pi : ℂ) * t * I) := by
          rw [h1, h2]
      _ = Complex.exp (I * (Real.pi : ℂ) * t) *
            (Complex.exp (-(Real.pi : ℂ) * t * I) - Complex.exp ((Real.pi : ℂ) * t * I)) := by ring
      _ = -2 * I * Complex.exp (I * (Real.pi : ℂ) * t) *
            ((Complex.exp (-(Real.pi : ℂ) * t * I) - Complex.exp ((Real.pi : ℂ) * t * I)) * I / 2) := by
          have h12 : (-2 * I) * I / 2 = (1 : ℂ) := by
            calc (-2 * I) * I / 2 = -(I * I) := by ring
              _ = 1 := by rw [hI]; ring
          calc Complex.exp (I * (Real.pi : ℂ) * t) *
                (Complex.exp (-(Real.pi : ℂ) * t * I) - Complex.exp ((Real.pi : ℂ) * t * I))
              = ((-2 * I) * I / 2) * (Complex.exp (I * (Real.pi : ℂ) * t) *
                  (Complex.exp (-(Real.pi : ℂ) * t * I) - Complex.exp ((Real.pi : ℂ) * t * I))) := by
                rw [h12, one_mul]
            _ = _ := by ring
  rw [hfac]
  simp only [neg_mul]
  ring

/-- Exact Maclaurin expansion of `η(t)` on `‖t‖ < 1`:
`η(t) = ∑' m : ℕ, etaCoeff (m + 2) * t ^ (m + 2)`. -/
theorem hasSum_eta_integral {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun m : ℕ => etaCoeff (m + 2) * t ^ (m + 2)) (eta_integral t) := by
  let a : ℕ → ℂ := fun j =>
    -((2 * Real.pi * I) ^ (j + 1) / (((j + 1).factorial : ℕ) : ℂ)) * t ^ j
  let b : ℕ → ℂ := fun l => (R_momentCoeff l : ℂ) * t ^ l
  have ha_norm : Summable (fun j : ℕ => ‖a j‖) := by
    have hexp_sum : Summable (fun j : ℕ => ‖(2 * Real.pi * I * t) ^ j / (j.factorial : ℂ)‖) := by
      have h := (NormedSpace.expSeries_div_hasSum_exp ‖2 * (Real.pi : ℂ) * I * t‖).summable
      refine h.congr fun j => ?_
      rw [norm_div, norm_pow, Complex.norm_natCast]
    have hshift : Summable (fun j : ℕ => ‖(2 * Real.pi * I * t) ^ (j + 1) / (((j + 1).factorial : ℕ) : ℂ)‖) :=
      hexp_sum.comp_injective Nat.succ_injective
    by_cases ht0 : t = 0
    · subst ht0
      refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
      have hj0 : j ≠ 0 := by simpa using hj
      simp [a, zero_pow hj0]
    · have hnorm_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
      refine (hshift.mul_left ‖t‖⁻¹).congr fun j => ?_
      dsimp only [a]
      rw [norm_mul, norm_neg, norm_div, norm_pow, norm_pow, Complex.norm_natCast,
        norm_div, norm_pow, norm_mul, mul_pow, pow_succ, pow_succ, Complex.norm_natCast]
      have hne : ‖t‖ ≠ 0 := hnorm_pos.ne'
      have hmul : ‖2 * (Real.pi : ℂ) * I‖ ^ j * ‖2 * (Real.pi : ℂ) * I‖ * (‖t‖ ^ j * ‖t‖) /
            (((j + 1).factorial : ℕ) : ℝ) =
          ‖t‖ * (‖2 * (Real.pi : ℂ) * I‖ ^ j * ‖2 * (Real.pi : ℂ) * I‖ /
            (((j + 1).factorial : ℕ) : ℝ) * ‖t‖ ^ j) := by ring
      rw [hmul, inv_mul_cancel_left₀ hne]
  have hb_norm : Summable (fun l : ℕ => ‖b l‖) := summable_norm_R_momentCoeff ht
  have ha_sum : (∑' j : ℕ, a j) * t = -(Complex.exp (2 * Real.pi * I * t) - 1) := by
    have hhs := NormedSpace.expSeries_div_hasSum_exp (2 * (Real.pi : ℂ) * I * t)
    rw [← Complex.exp_eq_exp_ℂ] at hhs
    have hsplit := hhs.summable.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
    rw [hhs.tsum_eq] at hsplit
    have hsub : Complex.exp (2 * Real.pi * I * t) - 1 =
        ∑' j : ℕ, (2 * Real.pi * I * t) ^ (j + 1) / (((j + 1).factorial : ℕ) : ℂ) := by
      linear_combination -hsplit
    rw [hsub, ← tsum_neg, ← tsum_mul_right]
    congr 1; ext j
    dsimp only [a]
    rw [mul_pow, pow_succ]
    ring
  have hb_sum : ∑' l : ℕ, b l = R_inner t := (hasSum_R_inner ht).tsum_eq
  have hcauchy := hasSum_sum_range_mul_of_summable_norm ha_norm hb_norm
  have hmul := hcauchy.mul_right (t ^ 2)
  have hval : ((∑' j, a j) * ∑' l, b l) * t ^ 2 = eta_integral t := by
    dsimp only [eta_integral, R_integral_eq_mul_R_inner]
    rw [← hb_sum, ← ha_sum]
    ring
  rw [hval] at hmul
  refine hmul.congr_fun fun m => ?_
  dsimp only [etaCoeff, a, b]
  have hm2 : ¬ (m + 2 < 2) := by omega
  simp only [hm2, ↓reduceIte, show m + 2 - 1 = m + 1 by omega]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_range_reflect
    (fun k => -((2 * Real.pi * I) ^ (k + 1) / (((k + 1).factorial : ℕ) : ℂ)) * t ^ k *
      ((R_momentCoeff (m - k) : ℂ) * t ^ (m - k)) * t ^ 2) (m + 1)]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlm : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have h1 : m + 1 - 1 - l = m - l := by omega
  have h2 : m - (m - l) = l := by omega
  have h3 : m - l + 1 = m + 1 - l := by omega
  rw [h1, h2, h3]
  have hpow : t ^ (m - l) * t ^ l * t ^ 2 = t ^ (m + 2) := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel hlm]
  calc -((2 * (Real.pi : ℂ) * I) ^ (m + 1 - l) / (((m + 1 - l).factorial : ℕ) : ℂ)) *
        (R_momentCoeff l : ℂ) * t ^ (m + 2)
      = -((2 * (Real.pi : ℂ) * I) ^ (m + 1 - l) / (((m + 1 - l).factorial : ℕ) : ℂ)) *
        (R_momentCoeff l : ℂ) * (t ^ (m - l) * t ^ l * t ^ 2) := by rw [hpow]
    _ = -((2 * (Real.pi : ℂ) * I) ^ (m + 1 - l) / (((m + 1 - l).factorial : ℕ) : ℂ)) *
        t ^ (m - l) * ((R_momentCoeff l : ℂ) * t ^ l) * t ^ 2 := by ring

theorem eta_integral_eq_tsum {t : ℂ} (ht : ‖t‖ < 1) :
    eta_integral t = ∑' m : ℕ, etaCoeff (m + 2) * t ^ (m + 2) :=
  (hasSum_eta_integral ht).tsum_eq.symm

/-- Explicit geometric bound on `etaCoeff m`: `‖etaCoeff m‖ ≤ Cc * 2^m` for all `m ≥ 2`. -/
theorem etaCoeff_geom_bound :
    ∃ Cc > 0, ∀ m : ℕ, 2 ≤ m → ‖etaCoeff m‖ ≤ Cc * (2 : ℝ) ^ m := by
  let M_half : ℝ := ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + (1 / 2 : ℝ) * PakNthPrimeEngine.E1 x)
  have hM_pos : 0 < M_half := by
    dsimp only [M_half]
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun x => (Real.exp_pos _).le)
      (integrableOn_exp_neg_add_mul_E1 (by norm_num))]
    have hsupp : Function.support (fun x : ℝ => Real.exp (-x + (1 / 2 : ℝ) * PakNthPrimeEngine.E1 x)) = Set.univ := by
      ext x; simp [(Real.exp_pos _).ne']
    rw [hsupp, Set.univ_inter]
    simp
  refine ⟨M_half * Real.exp (2 * Real.pi), by positivity, fun m hm => ?_⟩
  dsimp only [etaCoeff]
  have hnot : ¬ (m < 2) := by omega
  simp only [hnot, ↓reduceIte]
  have h2pi_sum : HasSum (fun j : ℕ => (2 * Real.pi) ^ j / (j.factorial : ℝ))
      (Real.exp (2 * Real.pi)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (2 * Real.pi))
  calc ‖∑ l ∈ Finset.range (m - 1),
          (-((2 * Real.pi * I) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℂ))) *
            (R_momentCoeff l : ℂ)‖
      ≤ ∑ l ∈ Finset.range (m - 1),
          ‖(-((2 * Real.pi * I) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℂ))) *
            (R_momentCoeff l : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Finset.range (m - 1),
          ((2 * Real.pi) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℝ)) *
            (M_half * (2 : ℝ) ^ m) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hlm : l < m - 1 := Finset.mem_range.mp hl
        rw [norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_natCast,
          Complex.norm_real, Real.norm_of_nonneg (R_momentCoeff_pos l).le]
        have h2pi : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
          rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
            Complex.norm_I, mul_one]
        rw [h2pi]
        have hr := R_momentCoeff_le_geom (s := 1 / 2) (by norm_num) (by norm_num) l
        have hinv : ((1 / 2 : ℝ)⁻¹) = 2 := by norm_num
        rw [hinv] at hr
        have h2pow : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        have hr' : R_momentCoeff l ≤ M_half * (2 : ℝ) ^ m :=
          hr.trans (mul_le_mul_of_nonneg_left h2pow hM_pos.le)
        exact mul_le_mul_of_nonneg_left hr' (by positivity)
    _ = (∑ l ∈ Finset.range (m - 1),
          (2 * Real.pi) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℝ)) *
          (M_half * (2 : ℝ) ^ m) := by rw [← Finset.sum_mul]
    _ ≤ Real.exp (2 * Real.pi) * (M_half * (2 : ℝ) ^ m) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hbij : (∑ l ∈ Finset.range (m - 1),
            (2 * Real.pi) ^ (m - 1 - l) / (((m - 1 - l).factorial : ℕ) : ℝ)) =
            ∑ j ∈ Finset.Icc 1 (m - 1), (2 * Real.pi) ^ j / (j.factorial : ℝ) := by
          refine Finset.sum_bij (fun l _ => m - 1 - l) ?_ ?_ ?_ ?_
          · intro l hl
            simp only [Finset.mem_range] at hl
            simp only [Finset.mem_Icc]; omega
          · intro l₁ hl₁ l₂ hl₂ h
            simp only [Finset.mem_range] at hl₁ hl₂; omega
          · intro j hj
            simp only [Finset.mem_Icc] at hj
            exact ⟨m - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
          · intro l _; rfl
        rw [hbij]
        exact sum_le_hasSum (Finset.Icc 1 (m - 1)) (fun j _ => by positivity) h2pi_sum
    _ = (M_half * Real.exp (2 * Real.pi)) * (2 : ℝ) ^ m := by ring

/-- Explicit leading coefficient: `c_2 = -2πi ≠ 0`. -/
theorem etaCoeff_two : etaCoeff 2 = -(2 * (Real.pi : ℂ) * I) := by
  simp [etaCoeff, R_momentCoeff_zero]

theorem etaCoeff_two_ne_zero : etaCoeff 2 ≠ 0 := by
  rw [etaCoeff_two]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Explicit third coefficient: `c_3 = 2π² - 2πi M_1 ≠ 0` (since `Re(c_3) = 2π² > 0`). -/
theorem etaCoeff_three :
    etaCoeff 3 = 2 * (Real.pi : ℂ) ^ 2 - 2 * (Real.pi : ℂ) * I * (R_momentCoeff 1 : ℂ) := by
  simp only [etaCoeff, show ¬ (3 < 2) by norm_num, ↓reduceIte, show 3 - 1 = 2 by norm_num,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, R_momentCoeff_zero,
    show 2 - 1 = 1 by norm_num, Nat.factorial_two, Nat.factorial_one, Nat.cast_ofNat, Nat.cast_one,
    Complex.ofReal_one, div_one, pow_one, mul_one]
  have hI2 : (2 * (Real.pi : ℂ) * I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
    calc (2 * (Real.pi : ℂ) * I) ^ 2 = 4 * (Real.pi : ℂ) ^ 2 * (I * I) := by ring
      _ = -(4 * (Real.pi : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
  rw [hI2]
  ring

theorem etaCoeff_three_ne_zero : etaCoeff 3 ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  rw [etaCoeff_three] at hre
  simp [Complex.sub_re, Complex.mul_re, sq] at hre

/-- **Unconditional Infinite Support of `etaCoeff`**: Directly from `R_holomorphic_on_halfplane`
and `R_integral_neg_ne_zero` (with zero extra assumptions on `R`), infinitely many Taylor
coefficients `c_m` (`m ≥ 2`) of `η(t) = -(exp(2πi t) - 1) R_integral(t)` are nonzero! -/
theorem etaCoeff_infinite_support :
    {m : ℕ | 2 ≤ m ∧ etaCoeff m ≠ 0}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  let S : Finset ℕ := hfin.toFinset
  let Q : Polynomial ℂ := ∑ m ∈ S, Polynomial.C (etaCoeff m) * Polynomial.X ^ m
  have hball : ∀ t ∈ Metric.ball (0 : ℂ) 1, eta_integral t = Q.eval t := by
    intro t ht
    have hnorm : ‖t‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ht
    rw [eta_integral_eq_tsum hnorm]
    have hsupp : Function.support (fun m : ℕ => etaCoeff (m + 2) * t ^ (m + 2)) ⊆
        (S.image (fun m => m - 2) : Set ℕ) := by
      intro m hm
      have hcm : etaCoeff (m + 2) ≠ 0 := left_ne_zero_of_mul hm
      have hmem : m + 2 ∈ S := hfin.mem_toFinset.mpr ⟨by omega, hcm⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m + 2, hmem, by omega⟩)
    rw [tsum_eq_sum (s := S.image (fun m => m - 2)) (fun m hm => by
      by_contra hne; exact hm (hsupp hne))]
    change _ = Polynomial.evalRingHom t (∑ m ∈ S, Polynomial.C (etaCoeff m) * Polynomial.X ^ m)
    rw [map_sum]
    refine Finset.sum_bij (fun m _ => m + 2) ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      have hk2 : 2 ≤ k := (hfin.mem_toFinset.mp hk).1
      rwa [Nat.sub_add_cancel hk2]
    · intro m₁ _ m₂ _ h; omega
    · intro k hk
      have hk2 : 2 ≤ k := (hfin.mem_toFinset.mp hk).1
      exact ⟨k - 2, Finset.mem_image.mpr ⟨k, hk, rfl⟩, Nat.sub_add_cancel hk2⟩
    · intro m _
      change etaCoeff (m + 2) * t ^ (m + 2) =
        Polynomial.eval t (Polynomial.C (etaCoeff (m + 2)) * Polynomial.X ^ (m + 2))
      simp
  have hev : eta_integral =ᶠ[𝓝 (0 : ℂ)] fun t => Q.eval t :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one) hball
  have hQ_an : AnalyticOnNhd ℂ (fun t => Q.eval t) {t : ℂ | t.re < 1} :=
    Q.differentiable.differentiableOn.analyticOnNhd isOpen_halfplane_re_lt_one
  have heq_hp : Set.EqOn eta_integral (fun t => Q.eval t) {t : ℂ | t.re < 1} :=
    eta_analyticOnNhd_halfplane.eqOn_of_preconnected_of_eventuallyEq hQ_an
      isPreconnected_halfplane_re_lt_one (by simp : (0 : ℂ) ∈ {t : ℂ | t.re < 1}) hev
  have hroots : ∀ k : ℕ, Q.IsRoot (-((k + 1 : ℕ) : ℂ)) := by
    intro k
    have hmem : (-((k + 1 : ℕ) : ℂ)) ∈ {t : ℂ | t.re < 1} := by
      simp only [Set.mem_ofPred_eq, Complex.neg_re, Complex.natCast_re]; linarith
    have heq_k : eta_integral (-((k + 1 : ℕ) : ℂ)) = Q.eval (-((k + 1 : ℕ) : ℂ)) := heq_hp hmem
    change Q.eval (-((k + 1 : ℕ) : ℂ)) = 0
    rw [← heq_k]
    dsimp only [eta_integral]
    have hexp : Complex.exp (2 * Real.pi * I * -((k + 1 : ℕ) : ℂ)) = 1 := by
      have h1 : 2 * Real.pi * I * -((k + 1 : ℕ) : ℂ) =
          ((-(k + 1 : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
        push_cast; ring
      rw [h1]
      exact Complex.exp_int_mul_two_pi_mul_I (-(k + 1 : ℤ))
    rw [hexp, sub_self, neg_zero, zero_mul]
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hinf_roots : {z : ℂ | Q.IsRoot z}.Infinite :=
      Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -((k + 1 : ℕ) : ℂ))
        (fun a b h => by
          have h1 : ((a + 1 : ℕ) : ℂ) = ((b + 1 : ℕ) : ℂ) := neg_inj.mp h
          have h2 : a + 1 = b + 1 := by exact_mod_cast h1
          omega)
        hroots
    have hfin_roots : {z : ℂ | Q.IsRoot z}.Finite :=
      (Q.roots.toFinset.finite_toSet).subset fun z hz => by
        simpa [Polynomial.mem_roots hQne] using hz
    exact hinf_roots hfin_roots
  have hhalf : (-((1 / 2 : ℝ) : ℂ)) ∈ {t : ℂ | t.re < 1} := by
    simp only [Set.mem_ofPred_eq, Complex.neg_re, Complex.ofReal_re]; norm_num
  have h0 : eta_integral (-((1 / 2 : ℝ) : ℂ)) = 0 := by
    simpa [hQ0] using heq_hp hhalf
  dsimp only [eta_integral] at h0
  have hexp_half : Complex.exp (2 * Real.pi * I * -((1 / 2 : ℝ) : ℂ)) = -1 := by
    have harg : 2 * (Real.pi : ℂ) * I * -((1 / 2 : ℝ) : ℂ) = -((Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hexp_half] at h0
  have hne : -((-1 : ℂ) - 1) ≠ 0 := by norm_num
  have hR0 : PakNthPrimeEngine.R_integral (-((1 / 2 : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hne
  exact PakNthPrimeEngine.R_integral_neg_ne_zero (1 / 2) (by norm_num) hR0

/-! ### 5. Complex Exponential Integral `Ei(w)`, Branch-Cut Identities, and `T_integral` -/

/-- Entire modified exponential integral
`Ein(w) = ∑_{k=0}^∞ (-1)^k w^{k+1} / ((k+1) * (k+1)!)`. -/
@[expose] def Ein_complex (w : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ) ^ k * w ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ)

/-- Real modified exponential integral `Ein(x)` on `ℝ`. -/
@[expose] def Ein_real (x : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ)

/-- Euler-Mascheroni constant characterized via `E1(1) + γ = Ein(1)`. -/
@[expose] def gammaE1 : ℝ := Ein_real 1 - PakNthPrimeEngine.E1 1

/-- Principal branch of `Ei(w)` on `ℂ \ (-∞, 0]`: `Ei(w) = γ + log w - Ein(-w)`. -/
@[expose] def Ei_complex (w : ℂ) : ℂ :=
  (gammaE1 : ℂ) + Complex.log w - Ein_complex (-w)

/-- Real exponential integral `Ei(x) = γ + log x - Ein(-x)` on `(0, ∞)`. -/
@[expose] def Ei_real (x : ℝ) : ℝ :=
  gammaE1 + Real.log x - Ein_real (-x)

/-- Complex `E1(z)` via horizontal ray shift: `E1_complex z = ∫_{r > 0} exp(-(z + r)) / (z + r) dr`. -/
@[expose] def E1_complex (z : ℂ) : ℂ :=
  ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))

/-- Positive-axis real-Ei integral `T(t) = t * ∫_{x > 0} exp(x - t * Ei(x)) dx`. -/
@[expose] def T_integral (t : ℂ) : ℂ :=
  t * ∫ x in Set.Ioi (0 : ℝ), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))

lemma summable_norm_Ein_term (w : ℂ) :
    Summable (fun k : ℕ => ‖(-1 : ℂ) ^ k * w ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ)‖) := by
  have hexp : Summable (fun k : ℕ => ‖w‖ ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ‖w‖).summable.comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hexp
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_natCast]
  have hle : (((k + 1).factorial : ℕ) : ℝ) ≤ (((k + 1) * (k + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg w) _) (by positivity) hle

lemma norm_Ein_complex_le (w : ℂ) : ‖Ein_complex w‖ ≤ Real.exp ‖w‖ := by
  have hexp_hs : HasSum (fun k : ℕ => ‖w‖ ^ k / (k.factorial : ℝ)) (Real.exp ‖w‖) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ‖w‖
  have hshift_sum : Summable (fun k : ℕ => ‖w‖ ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ)) :=
    hexp_hs.summable.comp_injective Nat.succ_injective
  have hshift_le : (∑' k : ℕ, ‖w‖ ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ)) ≤ Real.exp ‖w‖ := by
    have hsplit := hexp_hs.summable.sum_add_tsum_nat_add 1
    rw [hexp_hs.tsum_eq] at hsplit
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
    linarith
  calc ‖Ein_complex w‖
      ≤ ∑' k : ℕ, ‖(-1 : ℂ) ^ k * w ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_Ein_term w)
    _ ≤ ∑' k : ℕ, ‖w‖ ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ) := by
        refine (summable_norm_Ein_term w).tsum_le_tsum (fun k => ?_) hshift_sum
        rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
          Complex.norm_natCast]
        have hle : (((k + 1).factorial : ℕ) : ℝ) ≤ (((k + 1) * (k + 1).factorial : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
        exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg w) _) (by positivity) hle
    _ ≤ Real.exp ‖w‖ := hshift_le

lemma summable_Ein_real_term (x : ℝ) :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k * x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ)) := by
  have h := (summable_norm_Ein_term (x : ℂ)).of_norm
  have hre := (Complex.reCLM.hasSum h.hasSum).summable
  refine hre.congr fun k => ?_
  have heq : ((-1 : ℂ) ^ k * (x : ℂ) ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ)) =
      ((((-1 : ℝ) ^ k * x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ) : ℝ) : ℂ)) := by
    push_cast; rfl
  change Complex.reCLM _ = _
  rw [heq]
  simp only [Complex.reCLM_apply, Complex.ofReal_re]

lemma Ein_complex_ofReal (x : ℝ) : Ein_complex (x : ℂ) = (Ein_real x : ℂ) := by
  have hs := Complex.ofRealCLM.hasSum (summable_Ein_real_term x).hasSum
  have hts : (∑' k : ℕ, (((-1 : ℝ) ^ k * x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ) : ℝ) : ℂ)) =
      (Ein_real x : ℂ) := hs.tsum_eq
  rw [← hts]
  dsimp only [Ein_complex]
  congr 1; ext k
  push_cast; rfl

lemma hasDerivAt_Ein_complex_sum (w : ℂ) :
    HasDerivAt Ein_complex
      (∑' k : ℕ, (-1 : ℂ) ^ k * w ^ k / (((k + 1).factorial : ℕ) : ℂ)) w := by
  let R : ℝ := ‖w‖ + 1
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have hu : Summable (fun k : ℕ => R ^ k / (k.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp R).summable
  have hconv : Summable (fun k : ℕ => (-1 : ℂ) ^ k * w ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ)) :=
    (summable_norm_Ein_term w).of_norm
  refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball w 1)
    (g := fun k (z : ℂ) => (-1 : ℂ) ^ k * z ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℂ))
    (g' := fun k (z : ℂ) => (-1 : ℂ) ^ k * z ^ k / (((k + 1).factorial : ℕ) : ℂ))
    hu Metric.isOpen_ball (convex_ball w 1).isPreconnected
    (fun k z _ => ?_) (fun k z hz => ?_) (Metric.mem_ball_self zero_lt_one) hconv
    (Metric.mem_ball_self zero_lt_one)
  · have hpow : HasDerivAt (fun y : ℂ => y ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * z ^ k) z :=
      hasDerivAt_pow (k + 1) z
    have h1 := (hpow.const_mul ((-1 : ℂ) ^ k)).div_const (((k + 1) * (k + 1).factorial : ℕ) : ℂ)
    convert h1 using 1
    have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    field_simp [hne]
  · have hzR : ‖z‖ ≤ R := by
      have hd : ‖z - w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have htri : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by simpa using norm_add_le (z - w) w
      dsimp [R]; linarith
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
      Complex.norm_natCast]
    have hfact : (k.factorial : ℝ) ≤ (((k + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    calc ‖z‖ ^ k / (((k + 1).factorial : ℕ) : ℝ)
        ≤ R ^ k / (((k + 1).factorial : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzR k) (by positivity)
      _ ≤ R ^ k / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_left (pow_nonneg hR_nn k) (by positivity) hfact

lemma hasDerivAt_Ein_complex {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt Ein_complex ((1 - Complex.exp (-w)) / w) w := by
  have hd := hasDerivAt_Ein_complex_sum w
  have heq : (∑' k : ℕ, (-1 : ℂ) ^ k * w ^ k / (((k + 1).factorial : ℕ) : ℂ)) =
      (1 - Complex.exp (-w)) / w := by
    have hhs := NormedSpace.expSeries_div_hasSum_exp (-w)
    rw [← Complex.exp_eq_exp_ℂ] at hhs
    have hsplit := hhs.summable.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
    rw [hhs.tsum_eq] at hsplit
    have hmul : w * ∑' k : ℕ, (-1 : ℂ) ^ k * w ^ k / (((k + 1).factorial : ℕ) : ℂ) =
        1 - Complex.exp (-w) := by
      rw [← tsum_mul_left]
      have hterm : (fun k : ℕ => w * ((-1 : ℂ) ^ k * w ^ k / (((k + 1).factorial : ℕ) : ℂ))) =
          fun k : ℕ => -((-w) ^ (k + 1) / (((k + 1).factorial : ℕ) : ℂ)) := by
        ext k
        rw [neg_eq_neg_one_mul w, mul_pow, pow_succ (-1 : ℂ), pow_succ w]
        ring
      rw [hterm, tsum_neg]
      linear_combination -hsplit
    rw [eq_div_iff hw, mul_comm]
    exact hmul
  rwa [heq] at hd

lemma differentiable_Ein_complex : Differentiable ℂ Ein_complex :=
  fun w => (hasDerivAt_Ein_complex_sum w).differentiableAt

lemma continuous_Ein_complex : Continuous Ein_complex :=
  differentiable_Ein_complex.continuous

lemma hasDerivAt_Ein_real {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Ein_real ((1 - Real.exp (-x)) / x) x := by
  have hc := (hasDerivAt_Ein_complex (w := (x : ℂ)) (Complex.ofReal_ne_zero.mpr hx)).comp x
    (hasDerivAt_id x).ofReal_comp
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hc
  have hfun : (⇑Complex.reCLM ∘ Ein_complex ∘ Complex.ofReal) = Ein_real :=
    funext fun t => by simp [Ein_complex_ofReal]
  rw [hfun] at hre
  convert hre using 1
  simp only [Complex.reCLM_apply, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_re]

/-- Exact derivative of the principal branch `Ei_complex` on `ℂ \ (-∞, 0]`: `Ei'(w) = exp(w) / w`. -/
theorem hasDerivAt_Ei_complex {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt Ei_complex (Complex.exp w / w) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hw
  have hein : HasDerivAt (fun z : ℂ => Ein_complex (-z))
      (((1 - Complex.exp (-(-w))) / (-w)) * (-1)) w :=
    (hasDerivAt_Ein_complex (neg_ne_zero.mpr hw0)).comp w (hasDerivAt_id w).neg
  have htot := (hlog.const_add (gammaE1 : ℂ)).fun_sub hein
  have hder : w⁻¹ - (1 - Complex.exp (-(-w))) / (-w) * (-1) = Complex.exp w / w := by
    rw [neg_neg]
    field_simp [hw0]
    ring
  rw [hder] at htot
  exact htot

/-- Fundamental relation `E1(x) + log(x) - Ein(x) = -gammaE1` for all `x > 0`. -/
theorem E1_add_log_sub_Ein_real {x : ℝ} (hx : 0 < x) :
    PakNthPrimeEngine.E1 x + Real.log x - Ein_real x = -gammaE1 := by
  let g : ℝ → ℝ := fun u =>
    PakNthPrimeEngine.E1 (Real.exp u) + Real.log (Real.exp u) - Ein_real (Real.exp u)
  have hg : ∀ u : ℝ, HasDerivAt g 0 u := by
    intro u
    have he : 0 < Real.exp u := Real.exp_pos u
    have hE := (E1_hasDerivAt he).comp u (Real.hasDerivAt_exp u)
    have hL := (Real.hasDerivAt_log he.ne').comp u (Real.hasDerivAt_exp u)
    have hEin := (hasDerivAt_Ein_real he.ne').comp u (Real.hasDerivAt_exp u)
    have htot := (hE.fun_add hL).fun_sub hEin
    have h0 : -Real.exp (-Real.exp u) / Real.exp u * Real.exp u +
        (Real.exp u)⁻¹ * Real.exp u -
        (1 - Real.exp (-Real.exp u)) / Real.exp u * Real.exp u = 0 := by
      rw [div_mul_cancel₀ _ he.ne', inv_mul_cancel₀ he.ne', div_mul_cancel₀ _ he.ne']
      ring
    rwa [h0] at htot
  have hconst : g (Real.log x) = g 0 :=
    is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv)
      (Real.log x) 0
  have hg0 : g 0 = -gammaE1 := by
    dsimp only [g, gammaE1]
    simp [Real.exp_zero, Real.log_one]
  rw [hg0] at hconst
  simpa only [g, Real.exp_log hx] using hconst

lemma Ei_complex_ofReal_pos {x : ℝ} (hx : 0 < x) :
    Ei_complex (x : ℂ) = (Ei_real x : ℂ) := by
  dsimp only [Ei_complex, Ei_real]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_neg, Ein_complex_ofReal]
  push_cast
  rfl

/-- Elementary exponential lower bound `-Ein(-x) ≥ (exp(x) - 1 - x) / x` for `x > 0`. -/
theorem neg_Ein_real_neg_ge {x : ℝ} (hx : 0 < x) :
    (Real.exp x - 1 - x) / x ≤ -Ein_real (-x) := by
  have hterm_eq : ∀ k : ℕ,
      -((-1 : ℝ) ^ k * (-x) ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ)) =
      x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ) := by
    intro k
    rw [neg_eq_neg_one_mul x, mul_pow, pow_succ (-1 : ℝ)]
    have h1 : (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (-1 : ℝ)) = -1 := by
      have : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
      linarith
    calc -((-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (-1 : ℝ) * x ^ (k + 1)) /
            (((k + 1) * (k + 1).factorial : ℕ) : ℝ))
        = -(((-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (-1 : ℝ))) * x ^ (k + 1) /
            (((k + 1) * (k + 1).factorial : ℕ) : ℝ)) := by ring
      _ = x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ) := by rw [h1]; ring
  have hneg : -Ein_real (-x) =
      ∑' k : ℕ, x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ) := by
    dsimp only [Ein_real]
    rw [← tsum_neg]
    congr 1; ext k; exact hterm_eq k
  have hsum_rhs : Summable (fun k : ℕ => x ^ (k + 1) / (((k + 1) * (k + 1).factorial : ℕ) : ℝ)) :=
    (summable_Ein_real_term (-x)).neg.congr hterm_eq
  have hexp_hs : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have hshift2 : Summable (fun k : ℕ => x ^ (k + 2) / (((k + 2).factorial : ℕ) : ℝ)) :=
    hexp_hs.summable.comp_injective (fun a b h => by omega)
  have hshift2_eq : (∑' k : ℕ, x ^ (k + 2) / (((k + 2).factorial : ℕ) : ℝ)) = Real.exp x - 1 - x := by
    have hsplit := hexp_hs.summable.sum_add_tsum_nat_add 2
    rw [hexp_hs.tsum_eq] at hsplit
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one] at hsplit
    linarith
  have hsum_lhs : Summable (fun k : ℕ => x ^ (k + 1) / (((k + 2).factorial : ℕ) : ℝ)) := by
    refine (hshift2.mul_left x⁻¹).congr fun k => ?_
    rw [pow_succ, inv_mul_eq_div, div_right_comm, mul_div_cancel_right₀ _ hx.ne']
  have hlhs_eq : (∑' k : ℕ, x ^ (k + 1) / (((k + 2).factorial : ℕ) : ℝ)) = (Real.exp x - 1 - x) / x := by
    rw [eq_div_iff hx.ne', ← tsum_mul_right, ← hshift2_eq]
    congr 1; ext k
    rw [pow_succ]; ring
  rw [hneg, ← hlhs_eq]
  refine hsum_lhs.tsum_le_tsum (fun k => ?_) hsum_rhs
  have hle : (((k + 1) * (k + 1).factorial : ℕ) : ℝ) ≤ (((k + 2).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ (k + 1))
  exact div_le_div_of_nonneg_left (pow_nonneg hx.le _) (by positivity) hle

theorem Ei_real_ge {x : ℝ} (hx : 0 < x) :
    gammaE1 + Real.log x + (Real.exp x - 1 - x) / x ≤ Ei_real x := by
  dsimp only [Ei_real]
  linarith [neg_Ein_real_neg_ge hx]

theorem Ei_real_ge_log {x : ℝ} (hx : 0 < x) :
    gammaE1 + Real.log x ≤ Ei_real x := by
  have h1 : 0 ≤ (Real.exp x - 1 - x) / x := by
    refine div_nonneg ?_ hx.le
    linarith [Real.add_one_le_exp x]
  linarith [Ei_real_ge hx]

/-- Super-exponential tail comparison: for `a > 0` and `x ≥ 1`,
`x - a * (exp x / x) ≤ -x + 6 / a`. -/
lemma tail_exp_div_dominates {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    x - a * (Real.exp x / x) ≤ -x + 6 / a := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h3 : x ^ 3 / (6 : ℝ) ≤ Real.exp x := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp x hx_pos.le 3
  have hexp_ge : x ^ 2 / 6 ≤ Real.exp x / x := by
    rw [le_div_iff₀ hx_pos]
    calc x ^ 2 / 6 * x = x ^ 3 / 6 := by ring
      _ ≤ Real.exp x := h3
  have hsq : 0 ≤ (a / 6) * (x - 6 / a) ^ 2 := by positivity
  have hexpand : (a / 6) * (x - 6 / a) ^ 2 = a * (x ^ 2 / 6) - 2 * x + 6 / a := by
    field_simp [ha.ne']
    ring
  nlinarith

/-- Global integrability of the positive-axis `T_integral` integrand for `0 < Re t < 1`. -/
theorem integrableOn_T_integrand {t : ℂ} (ht0 : 0 < t.re) (ht1 : t.re < 1) :
    IntegrableOn (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) (Set.Ioi 0) := by
  have hEi_cont : ContinuousOn Ei_real (Set.Ioi 0) := by
    have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
      Real.continuousOn_log.mono fun x hx => ne_of_gt hx
    have hein : ContinuousOn (fun x : ℝ => Ein_real (-x)) (Set.Ioi 0) := by
      have hc : Continuous Ein_real := by
        have h : Ein_real = fun x : ℝ => (Ein_complex (x : ℂ)).re := by
          ext x; simp [Ein_complex_ofReal]
        rw [h]
        exact Complex.continuous_re.comp (continuous_Ein_complex.comp Complex.continuous_ofReal)
      exact (hc.comp continuous_neg).continuousOn
    exact (continuousOn_const.add hlog).sub hein
  have hmeas_fun : ContinuousOn (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) (Set.Ioi 0) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.continuousOn).sub
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hEi_cont)))
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hrpow : IntegrableOn (fun x : ℝ => x ^ (-t.re)) (Set.Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
    refine (hrpow.const_mul (Real.exp (1 - t.re * gammaE1))).mono'
      ((hmeas_fun.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Complex.norm_exp]
    have hre : ((x : ℂ) - t * (Ei_real x : ℂ)).re = x - t.re * Ei_real x := by
      simp [Complex.mul_re]
    rw [hre]
    have hge := Ei_real_ge_log hx.1
    have harg : x - t.re * Ei_real x ≤ (1 - t.re * gammaE1) + (-t.re) * Real.log x := by
      nlinarith [hx.2]
    calc Real.exp (x - t.re * Ei_real x)
        ≤ Real.exp ((1 - t.re * gammaE1) + (-t.re) * Real.log x) := Real.exp_le_exp.mpr harg
      _ = Real.exp (1 - t.re * gammaE1) * Real.exp ((-t.re) * Real.log x) := Real.exp_add _ _
      _ = Real.exp (1 - t.re * gammaE1) * x ^ (-t.re) := by
          rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]
  · have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 1) :=
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 1).congr_fun
        (fun x _ => by simp) measurableSet_Ioi
    let C : ℝ := Real.exp (-t.re * (gammaE1 - 2) + 6 / t.re)
    refine (hexp.const_mul C).mono'
      ((hmeas_fun.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hEi_big : gammaE1 - 2 + Real.exp x / x ≤ Ei_real x := by
      have hge := Ei_real_ge hx_pos
      have hdiv : (Real.exp x - 1 - x) / x = Real.exp x / x - 1 / x - 1 := by
        field_simp [hx_pos.ne']
      have h1x : 1 / x ≤ 1 := by rw [div_le_one hx_pos]; exact le_of_lt hx
      linarith
    rw [Complex.norm_exp]
    have hre : ((x : ℂ) - t * (Ei_real x : ℂ)).re = x - t.re * Ei_real x := by
      simp [Complex.mul_re]
    rw [hre]
    have htail := tail_exp_div_dominates ht0 (le_of_lt hx)
    have harg : x - t.re * Ei_real x ≤ (-t.re * (gammaE1 - 2) + 6 / t.re) + (-x) := by
      nlinarith
    calc Real.exp (x - t.re * Ei_real x)
        ≤ Real.exp ((-t.re * (gammaE1 - 2) + 6 / t.re) + (-x)) := Real.exp_le_exp.mpr harg
      _ = C * Real.exp (-x) := Real.exp_add _ _

/-! ### 5b. Properties of `E1_complex` and Exact Branch-Cut Identities -/

lemma integrableOn_Ioi_comp_add_left {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x : ℝ}
    (hf : IntegrableOn f (Set.Ioi x)) :
    IntegrableOn (fun r : ℝ => f (x + r)) (Set.Ioi (0 : ℝ)) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf ⊢
  have h := hf.comp_add_left x
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp [Set.indicator, Set.mem_Ioi]

lemma setIntegral_Ioi_comp_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (x : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), f (x + r)) = ∫ u in Set.Ioi x, f u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
    (fun u : ℝ => (Set.Ioi x).indicator f u) x
  rw [← h]
  congr 1; ext r
  simp [Set.indicator, Set.mem_Ioi]

lemma setIntegral_Iic_zero_eq_Ioi_zero_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ s in Set.Iic (0 : ℝ), f s) = ∫ x in Set.Ioi (0 : ℝ), f (-x) := by
  rw [← setIntegral_congr_set Iio_ae_eq_Iic, ← integral_indicator measurableSet_Iio,
    ← integral_indicator measurableSet_Ioi]
  have h := MeasureTheory.integral_neg_eq_self (μ := volume)
    (fun s : ℝ => (Set.Iio (0 : ℝ)).indicator f s)
  rw [← h]
  congr 1; ext x
  simp [Set.indicator, Set.mem_Iio, Set.mem_Ioi]

lemma norm_add_ofReal_ge_re (z : ℂ) (r : ℝ) :
    z.re + r ≤ ‖z + (r : ℂ)‖ := by
  have h1 : (z + (r : ℂ)).re = z.re + r := by simp
  rw [← h1]
  exact Complex.re_le_norm _

lemma norm_add_ofReal_ge_abs_im (z : ℂ) (r : ℝ) :
    |z.im| ≤ ‖z + (r : ℂ)‖ := by
  have h1 : (z + (r : ℂ)).im = z.im := by simp
  rw [← h1]
  exact Complex.abs_im_le_norm _

lemma integrableOn_E1_complex_integrand_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun r : ℝ => Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))) (Set.Ioi 0) := by
    refine (Complex.continuous_exp.comp
      (continuous_const.add Complex.continuous_ofReal).neg).continuousOn.div
      (continuous_const.add Complex.continuous_ofReal).continuousOn fun r hr => ?_
    intro h0
    have hre := congr_arg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [Set.mem_Ioi.mp hr]
  have hdom : IntegrableOn (fun r : ℝ => (Real.exp (-z.re) / z.re) * Real.exp (-r)) (Set.Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
      (fun r _ => by simp) measurableSet_Ioi).const_mul _
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_div, Complex.norm_exp]
  have hre : (-(z + (r : ℂ))).re = -z.re + (-r) := by simp; ring
  rw [hre, Real.exp_add]
  have hge : z.re ≤ ‖z + (r : ℂ)‖ := le_trans (by linarith [Set.mem_Ioi.mp hr])
    (norm_add_ofReal_ge_re z r)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hz hge

lemma integrableOn_E1_complex_integrand_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun r : ℝ => Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))) (Set.Ioi 0) := by
    refine (Complex.continuous_exp.comp
      (continuous_const.add Complex.continuous_ofReal).neg).continuousOn.div
      (continuous_const.add Complex.continuous_ofReal).continuousOn fun r _ => ?_
    intro h0
    have him := congr_arg Complex.im h0
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him
    exact hz him
  have hdom : IntegrableOn (fun r : ℝ => (Real.exp (-z.re) / |z.im|) * Real.exp (-r)) (Set.Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
      (fun r _ => by simp) measurableSet_Ioi).const_mul _
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r _
  rw [norm_div, Complex.norm_exp]
  have hre : (-(z + (r : ℂ))).re = -z.re + (-r) := by simp; ring
  rw [hre, Real.exp_add, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hz) (norm_add_ofReal_ge_abs_im z r)

lemma E1_complex_ofReal_pos {x : ℝ} (hx : 0 < x) :
    E1_complex (x : ℂ) = (PakNthPrimeEngine.E1 x : ℂ) := by
  dsimp only [E1_complex, PakNthPrimeEngine.E1]
  have hfun : (fun r : ℝ => Complex.exp (-((x : ℂ) + (r : ℂ))) / ((x : ℂ) + (r : ℂ))) =
      fun r : ℝ => (((Real.exp (-(x + r)) / (x + r) : ℝ) : ℂ)) := by
    ext r
    rw [← Complex.ofReal_add, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_div]
  have hint_shift : IntegrableOn (fun r : ℝ => Real.exp (-(x + r)) / (x + r)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_Ioi_comp_add_left (PakNthPrimeEngine.integrableOn_exp_neg_div_Ioi hx)
  have hint_eq : (∫ r in Set.Ioi (0 : ℝ), Real.exp (-(x + r)) / (x + r)) =
      ∫ u in Set.Ioi x, Real.exp (-u) / u :=
    setIntegral_Ioi_comp_add_left (fun u : ℝ => Real.exp (-u) / u) x
  have hint_ofReal : (∫ r in Set.Ioi (0 : ℝ), (((Real.exp (-(x + r)) / (x + r) : ℝ) : ℂ))) =
      (((∫ r in Set.Ioi (0 : ℝ), Real.exp (-(x + r)) / (x + r)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hint_shift
  rw [hfun, hint_ofReal, hint_eq]

/-- Uniform domination on the right half-plane: `‖E1_complex z‖ ≤ E1 (z.re)` for all `z.re > 0`! -/
theorem norm_E1_complex_le_E1 {z : ℂ} (hz : 0 < z.re) :
    ‖E1_complex z‖ ≤ PakNthPrimeEngine.E1 z.re := by
  dsimp only [E1_complex, PakNthPrimeEngine.E1]
  have hint_shift : IntegrableOn (fun r : ℝ => Real.exp (-(z.re + r)) / (z.re + r)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_Ioi_comp_add_left (PakNthPrimeEngine.integrableOn_exp_neg_div_Ioi hz)
  have hint_eq : (∫ r in Set.Ioi (0 : ℝ), Real.exp (-(z.re + r)) / (z.re + r)) =
      ∫ u in Set.Ioi z.re, Real.exp (-u) / u :=
    setIntegral_Ioi_comp_add_left (fun u : ℝ => Real.exp (-u) / u) z.re
  rw [← hint_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on (integrableOn_E1_complex_integrand_of_re_pos hz).norm
    hint_shift measurableSet_Ioi fun r hr => ?_
  rw [norm_div, Complex.norm_exp]
  have hre : (-(z + (r : ℂ))).re = -(z.re + r) := by simp
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith [Set.mem_Ioi.mp hr])
    (norm_add_ofReal_ge_re z r)

/-- Uniform bound away from the real axis: `‖E1_complex z‖ ≤ exp (-z.re) / |z.im|`. -/
theorem norm_E1_complex_le_exp_div_im {z : ℂ} (hz : z.im ≠ 0) :
    ‖E1_complex z‖ ≤ Real.exp (-z.re) / |z.im| := by
  dsimp only [E1_complex]
  have hexp1 : (∫ r in Set.Ioi (0 : ℝ), Real.exp (-r)) = 1 := by
    simpa using integral_exp_neg_Ioi (0 : ℝ)
  have hdom : IntegrableOn (fun r : ℝ => (Real.exp (-z.re) / |z.im|) * Real.exp (-r)) (Set.Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
      (fun r _ => by simp) measurableSet_Ioi).const_mul _
  calc ‖∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))‖
      ≤ ∫ r in Set.Ioi (0 : ℝ), ‖Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), (Real.exp (-z.re) / |z.im|) * Real.exp (-r) := by
        refine setIntegral_mono_on (integrableOn_E1_complex_integrand_of_im_ne_zero hz).norm
          hdom measurableSet_Ioi fun r _ => ?_
        rw [norm_div, Complex.norm_exp]
        have hre : (-(z + (r : ℂ))).re = -z.re + (-r) := by simp; ring
        rw [hre, Real.exp_add, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hz) (norm_add_ofReal_ge_abs_im z r)
    _ = Real.exp (-z.re) / |z.im| := by rw [integral_const_mul, hexp1, mul_one]

/-- Complex derivative of `E1_complex` off the real axis: `E1'(z) = -exp(-z) / z`. -/
theorem hasDerivAt_E1_complex {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) :
    HasDerivAt E1_complex (-Complex.exp (-z₀) / z₀) z₀ := by
  let d : ℝ := |z₀.im| / 2
  have hd : 0 < d := half_pos (abs_pos.mpr hz₀)
  let F : ℂ → ℝ → ℂ := fun z r => Complex.exp (-(z + (r : ℂ))) / (z + (r : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z r =>
    -Complex.exp (-(z + (r : ℂ))) * (z + (r : ℂ) + 1) / (z + (r : ℂ)) ^ 2
  let bound : ℝ → ℝ := fun r => (Real.exp (-z₀.re + d) * (1 / d + 1 / d ^ 2)) * Real.exp (-r)
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
      (fun r _ => by simp) measurableSet_Ioi).const_mul _
  have hne_ball : ∀ z ∈ Metric.ball z₀ d, ∀ r : ℝ, d ≤ ‖z + (r : ℂ)‖ := by
    intro z hz r
    have hdist : ‖z - z₀‖ < d := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have him_diff : |z.im - z₀.im| < d :=
      lt_of_le_of_lt (by simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)) hdist
    have him_ge : d ≤ |z.im| := by
      have htri : |z₀.im| - |z.im| ≤ |z.im - z₀.im| := by
        rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub z₀.im z.im
      dsimp [d] at htri him_diff ⊢
      linarith
    exact him_ge.trans (norm_add_ofReal_ge_abs_im z r)
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hd] with z hz
    have hcont : ContinuousOn (F z) (Set.Ioi (0 : ℝ)) := by
      refine (Complex.continuous_exp.comp
        (continuous_const.add Complex.continuous_ofReal).neg).continuousOn.div
        (continuous_const.add Complex.continuous_ofReal).continuousOn fun r _ => ?_
      exact norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball z hz r))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hcont : ContinuousOn (F' z₀) (Set.Ioi (0 : ℝ)) := by
      have hnum : ContinuousOn (fun r : ℝ => -Complex.exp (-(z₀ + (r : ℂ))) * (z₀ + (r : ℂ) + 1)) (Set.Ioi 0) :=
        ((Complex.continuous_exp.comp (continuous_const.add Complex.continuous_ofReal).neg).neg.mul
          ((continuous_const.add Complex.continuous_ofReal).add continuous_const)).continuousOn
      refine hnum.div ((continuous_const.add Complex.continuous_ofReal).pow 2).continuousOn fun r _ => ?_
      exact pow_ne_zero 2 (norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball z₀ (Metric.mem_ball_self hd) r)))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound_ae : ∀ᵐ (r : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ d,
      ‖F' z r‖ ≤ bound r := by
    filter_upwards with r z hz
    have hzr : d ≤ ‖z + (r : ℂ)‖ := hne_ball z hz r
    have hzr_ne : z + (r : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd hzr)
    have hre_le : -z.re ≤ -z₀.re + d := by
      have hdist : ‖z - z₀‖ < d := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hle : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
      linarith [abs_le.mp (hle.trans hdist.le)]
    have hsplit : F' z r = -Complex.exp (-(z + (r : ℂ))) * (1 / (z + (r : ℂ)) + 1 / (z + (r : ℂ)) ^ 2) := by
      dsimp only [F']
      field_simp [hzr_ne]
    rw [hsplit, norm_mul, norm_neg, Complex.norm_exp]
    have hre : (-(z + (r : ℂ))).re = -z.re + (-r) := by simp; ring
    rw [hre, Real.exp_add]
    have hnorm_sum : ‖1 / (z + (r : ℂ)) + 1 / (z + (r : ℂ)) ^ 2‖ ≤ 1 / d + 1 / d ^ 2 := by
      calc ‖1 / (z + (r : ℂ)) + 1 / (z + (r : ℂ)) ^ 2‖
          ≤ ‖1 / (z + (r : ℂ))‖ + ‖1 / (z + (r : ℂ)) ^ 2‖ := norm_add_le _ _
        _ = 1 / ‖z + (r : ℂ)‖ + 1 / ‖z + (r : ℂ)‖ ^ 2 := by simp [norm_pow]
        _ ≤ 1 / d + 1 / d ^ 2 := add_le_add
            (div_le_div_of_nonneg_left zero_le_one hd hzr)
            (div_le_div_of_nonneg_left zero_le_one (pow_pos hd 2) (pow_le_pow_left₀ hd.le hzr 2))
    dsimp only [bound]
    calc Real.exp (-z.re) * Real.exp (-r) * ‖1 / (z + (r : ℂ)) + 1 / (z + (r : ℂ)) ^ 2‖
        ≤ (Real.exp (-z₀.re + d) * Real.exp (-r)) * (1 / d + 1 / d ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre_le) (Real.exp_pos _).le)
            hnorm_sum (norm_nonneg _) (by positivity)
      _ = Real.exp (-z₀.re + d) * (1 / d + 1 / d ^ 2) * Real.exp (-r) := by ring
  have hdiff_ae : ∀ᵐ (r : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ d,
      HasDerivAt (F · r) (F' z r) z := by
    filter_upwards with r z hz
    have hzr_ne : z + (r : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball z hz r))
    have hadd : HasDerivAt (fun w : ℂ => w + (r : ℂ)) 1 z := by
      simpa using (hasDerivAt_id z).add_const (r : ℂ)
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-(w + (r : ℂ)))) (-Complex.exp (-(z + (r : ℂ)))) z := by
      simpa using hadd.neg.cexp
    convert hexp.div hadd hzr_ne using 1
    dsimp only [F']
    ring
  have ⟨hF'_int, hderiv_int⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ hd)
      hF_meas (integrableOn_E1_complex_integrand_of_im_ne_zero hz₀) hF'_meas hbound_ae hbound_int hdiff_ae
  have hftc : (∫ r in Set.Ioi (0 : ℝ), F' z₀ r) = -Complex.exp (-z₀) / z₀ := by
    have hr_deriv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt (F z₀) (F' z₀ r) r := by
      intro r _
      have hzr_ne : z₀ + (r : ℂ) ≠ 0 :=
        norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball z₀ (Metric.mem_ball_self hd) r))
      have hadd : HasDerivAt (fun u : ℝ => z₀ + (u : ℂ)) 1 r := by
        simpa using (hasDerivAt_id r).ofReal_comp.const_add z₀
      have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(z₀ + (u : ℂ)))) (-Complex.exp (-(z₀ + (r : ℂ)))) r := by
        simpa using hadd.neg.cexp
      convert hexp.div hadd hzr_ne using 1
      dsimp only [F']
      ring
    have htend : Tendsto (F z₀) atTop (𝓝 (0 : ℂ)) := by
      refine squeeze_zero_norm (a := fun r : ℝ => (Real.exp (-z₀.re) / |z₀.im|) * Real.exp (-r))
        (fun r => ?_) ?_
      · dsimp only [F]
        rw [norm_div, Complex.norm_exp]
        have hre : (-(z₀ + (r : ℂ))).re = -z₀.re + (-r) := by simp; ring
        rw [hre, Real.exp_add, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hz₀) (norm_add_ofReal_ge_abs_im z₀ r)
      · have h0 : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
        simpa using h0.const_mul (Real.exp (-z₀.re) / |z₀.im|)
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hr_deriv hF'_int htend
    rw [hval]
    dsimp only [F]
    simp [neg_div]
  rwa [hftc] at hderiv_int

/-- Pointwise limit `E1_complex (x + I * ε) → E1 x` (and `E1_complex (x - I * ε) → E1 x`) as `ε → 0`. -/
theorem tendsto_E1_complex_ofReal_add_I_mul {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => E1_complex ((x : ℂ) + I * (ε : ℂ))) (𝓝 (0 : ℝ))
      (𝓝 (PakNthPrimeEngine.E1 x : ℂ)) := by
  rw [← E1_complex_ofReal_pos hx]
  dsimp only [E1_complex]
  let bound : ℝ → ℝ := fun r => Real.exp (-(x + r)) / (x + r)
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_Ioi_comp_add_left (PakNthPrimeEngine.integrableOn_exp_neg_div_Ioi hx)
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
  · refine Eventually.of_forall fun ε => ?_
    have hre : ((x : ℂ) + I * (ε : ℂ)).re = x := by simp
    exact (integrableOn_E1_complex_integrand_of_re_pos (by rw [hre]; exact hx)).aestronglyMeasurable
  · refine Eventually.of_forall fun ε => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_div, Complex.norm_exp]
    have hre : (-((x : ℂ) + I * (ε : ℂ) + (r : ℂ))).re = -(x + r) := by simp
    have hge : x + r ≤ ‖(x : ℂ) + I * (ε : ℂ) + (r : ℂ)‖ := by
      have hre2 : ((x : ℂ) + I * (ε : ℂ)).re = x := by simp
      simpa [hre2] using norm_add_ofReal_ge_re ((x : ℂ) + I * (ε : ℂ)) r
    rw [hre]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith [Set.mem_Ioi.mp hr]) hge
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hne : (x : ℂ) + (r : ℂ) ≠ 0 := by
      intro h0
      have hre := congr_arg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith [Set.mem_Ioi.mp hr]
    have hlin : Tendsto (fun ε : ℝ => (x : ℂ) + I * (ε : ℂ) + (r : ℂ)) (𝓝 (0 : ℝ))
        (𝓝 ((x : ℂ) + (r : ℂ))) := by
      have hc : Continuous (fun ε : ℝ => (x : ℂ) + I * (ε : ℂ) + (r : ℂ)) :=
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).add continuous_const
      simpa using hc.tendsto (0 : ℝ)
    exact (Complex.continuous_exp.continuousAt.tendsto.comp hlin.neg).div hlin hne

/-- Branch-cut limit of `Complex.log (-1 - I * ε)` as `ε → 0⁺`: equals `-I * π`. -/
lemma tendsto_log_neg_one_sub_I_mul :
    Tendsto (fun ε : ℝ => Complex.log (-1 - I * (ε : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (-I * (Real.pi : ℂ))) := by
  have hnorm : Tendsto (fun ε : ℝ => Real.log ‖-1 - I * (ε : ℂ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont_norm : ContinuousAt (fun ε : ℝ => ‖(-1 : ℂ) - I * (ε : ℂ)‖) 0 :=
      (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).norm.continuousAt
    have hc : ContinuousAt (fun ε : ℝ => Real.log ‖(-1 : ℂ) - I * (ε : ℂ)‖) 0 :=
      ContinuousAt.comp (Real.continuousAt_log (by simp)) hcont_norm
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have harg : Tendsto (fun ε : ℝ => Complex.arg (-1 - I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (-Real.pi)) := by
    have hev : (fun ε : ℝ => Complex.arg (-1 - I * (ε : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ => Real.arcsin (ε / ‖-1 - I * (ε : ℂ)‖) - Real.pi := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      unfold Complex.arg
      have hre : ¬ (0 ≤ (-1 - I * (ε : ℂ)).re) := by simp
      have him : ¬ (0 ≤ (-1 - I * (ε : ℂ)).im) := by simp; linarith
      split_ifs
      simp
    refine Tendsto.congr' hev.symm ?_
    have hdiv : Tendsto (fun ε : ℝ => ε / ‖-1 - I * (ε : ℂ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ => ε / ‖-1 - I * (ε : ℂ)‖) 0 :=
        continuousAt_id.div
          ((continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).norm.continuousAt)
          (by simp)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have harc := (Real.continuous_arcsin.tendsto 0).comp hdiv
    simpa [Real.arcsin_zero] using harc.sub_const Real.pi
  have htot := (Complex.continuous_ofReal.tendsto 0 |>.comp hnorm).add
    ((Complex.continuous_ofReal.tendsto (-Real.pi) |>.comp harg).mul_const I)
  refine htot.congr (fun ε => ?_) |>.trans ?_
  · simp [Complex.log]
  · simp; ring_nf

/-- Branch-cut limit of `Complex.log (-1 + I * ε)` as `ε → 0⁺`: equals `+I * π`. -/
lemma tendsto_log_neg_one_add_I_mul :
    Tendsto (fun ε : ℝ => Complex.log (-1 + I * (ε : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (I * (Real.pi : ℂ))) := by
  have hnorm : Tendsto (fun ε : ℝ => Real.log ‖-1 + I * (ε : ℂ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont_norm : ContinuousAt (fun ε : ℝ => ‖(-1 : ℂ) + I * (ε : ℂ)‖) 0 :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).norm.continuousAt
    have hc : ContinuousAt (fun ε : ℝ => Real.log ‖(-1 : ℂ) + I * (ε : ℂ)‖) 0 :=
      ContinuousAt.comp (Real.continuousAt_log (by simp)) hcont_norm
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have harg : Tendsto (fun ε : ℝ => Complex.arg (-1 + I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
    have hev : (fun ε : ℝ => Complex.arg (-1 + I * (ε : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ => Real.arcsin ((-ε) / ‖-1 + I * (ε : ℂ)‖) + Real.pi := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      unfold Complex.arg
      have hre : ¬ (0 ≤ (-1 + I * (ε : ℂ)).re) := by simp
      have him : 0 ≤ (-1 + I * (ε : ℂ)).im := by simp; linarith
      split_ifs
      simp
    refine Tendsto.congr' hev.symm ?_
    have hdiv : Tendsto (fun ε : ℝ => (-ε) / ‖-1 + I * (ε : ℂ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ => (-ε) / ‖-1 + I * (ε : ℂ)‖) 0 :=
        continuousAt_id.neg.div
          ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).norm.continuousAt)
          (by simp)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have harc := (Real.continuous_arcsin.tendsto 0).comp hdiv
    simpa [Real.arcsin_zero] using harc.add_const Real.pi
  have htot := (Complex.continuous_ofReal.tendsto 0 |>.comp hnorm).add
    ((Complex.continuous_ofReal.tendsto Real.pi |>.comp harg).mul_const I)
  refine htot.congr (fun ε => ?_) |>.trans ?_
  · simp [Complex.log]
  · simp; ring_nf

/-- **Exact Lower Half-Plane Branch-Cut Identity**:
For every `w : ℂ` with `w.im < 0`, `Ei_complex w = -E1_complex (-w) - I * π`. -/
theorem Ei_complex_eq_neg_E1_sub_I_pi {w : ℂ} (hw : w.im < 0) :
    Ei_complex w = -E1_complex (-w) - I * (Real.pi : ℂ) := by
  let h : ℂ → ℂ := fun z => Ei_complex z + E1_complex (-z)
  have hh_deriv : ∀ z : ℂ, z.im < 0 → HasDerivAt h 0 z := by
    intro z hz
    have hslit : z ∈ Complex.slitPlane := Or.inr (ne_of_lt hz)
    have hEi := hasDerivAt_Ei_complex hslit
    have hE1 : HasDerivAt (fun y : ℂ => E1_complex (-y)) (-Complex.exp (-(-z)) / (-z) * (-1)) z :=
      (hasDerivAt_E1_complex (z₀ := -z) (by simp; linarith)).comp z (hasDerivAt_id z).neg
    have htot := hEi.fun_add hE1
    have h0 : Complex.exp z / z + -Complex.exp (-(-z)) / (-z) * (-1) = 0 := by
      rw [neg_neg]
      have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hslit
      field_simp [hz0]
      ring
    rwa [h0] at htot
  have hconst : ∀ z₁ z₂ : ℂ, z₁.im < 0 → z₂.im < 0 → h z₁ = h z₂ := by
    intro z₁ z₂ h₁ h₂
    have hx : ∀ (x₁ x₂ y : ℝ), 0 < y → h ((x₁ : ℂ) - I * (y : ℂ)) = h ((x₂ : ℂ) - I * (y : ℂ)) := by
      intro x₁ x₂ y hy
      have hd_all : ∀ x : ℝ, HasDerivAt (fun t : ℝ => h ((t : ℂ) - I * (y : ℂ))) 0 x := by
        intro x
        have hd := (hh_deriv ((x : ℂ) - I * (y : ℂ)) (by simp; linarith)).comp x
          ((hasDerivAt_id x).ofReal_comp.sub_const (I * (y : ℂ)))
        simpa [Function.comp_def] using hd
      exact is_const_of_deriv_eq_zero (fun x => (hd_all x).differentiableAt)
        (fun x => (hd_all x).deriv) x₁ x₂
    have hy : ∀ (x : ℝ) (u₁ u₂ : ℝ),
        h ((x : ℂ) - I * (Real.exp u₁ : ℂ)) = h ((x : ℂ) - I * (Real.exp u₂ : ℂ)) := by
      intro x u₁ u₂
      have hd_all : ∀ u : ℝ, HasDerivAt (fun t : ℝ => h ((x : ℂ) - I * (Real.exp t : ℂ))) 0 u := by
        intro u
        have him : ((x : ℂ) - I * (Real.exp u : ℂ)).im < 0 := by
          rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
          linarith [Real.exp_pos u]
        have hd := (hh_deriv ((x : ℂ) - I * (Real.exp u : ℂ)) him).comp u
          (((Real.hasDerivAt_exp u).ofReal_comp.const_mul I).const_sub (x : ℂ))
        simpa [Function.comp_def] using hd
      exact is_const_of_deriv_eq_zero (fun u => (hd_all u).differentiableAt)
        (fun u => (hd_all u).deriv) u₁ u₂
    have hz1 : z₁ = (z₁.re : ℂ) - I * (Real.exp (Real.log (-z₁.im)) : ℂ) := by
      rw [Real.exp_log (by linarith)]
      apply Complex.ext <;> simp
    have hz2 : z₂ = (z₂.re : ℂ) - I * (Real.exp (Real.log (-z₂.im)) : ℂ) := by
      rw [Real.exp_log (by linarith)]
      apply Complex.ext <;> simp
    rw [hz1, hz2]
    exact (hx z₁.re z₂.re (Real.exp (Real.log (-z₁.im))) (Real.exp_pos _)).trans
      (hy z₂.re (Real.log (-z₁.im)) (Real.log (-z₂.im)))
  have hlim : Tendsto (fun ε : ℝ => h (-1 - I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (-I * (Real.pi : ℂ))) := by
    have hE1_lim : Tendsto (fun ε : ℝ => E1_complex (-(-1 - I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
        (𝓝 (PakNthPrimeEngine.E1 1 : ℂ)) := by
      have h1 : Tendsto (fun ε : ℝ => E1_complex ((1 : ℂ) + I * (ε : ℂ))) (𝓝[>] (0 : ℝ))
          (𝓝 (PakNthPrimeEngine.E1 1 : ℂ)) :=
        (tendsto_E1_complex_ofReal_add_I_mul zero_lt_one).mono_left nhdsWithin_le_nhds
      refine h1.congr fun ε => ?_
      congr 1; ring
    have hEin_lim : Tendsto (fun ε : ℝ => Ein_complex (-(-1 - I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
        (𝓝 (Ein_real 1 : ℂ)) := by
      have hc : Continuous (fun ε : ℝ => Ein_complex (-(-1 - I * (ε : ℂ)))) :=
        continuous_Ein_complex.comp
          (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).neg
      have h1 : Tendsto (fun ε : ℝ => Ein_complex (-(-1 - I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
          (𝓝 (Ein_complex (-(-1 - I * ((0 : ℝ) : ℂ))))) :=
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      have h0 : Ein_complex (-(-1 - I * ((0 : ℝ) : ℂ))) = (Ein_real 1 : ℂ) := by
        simpa using Ein_complex_ofReal 1
      rwa [h0] at h1
    have hEi_lim : Tendsto (fun ε : ℝ => Ei_complex (-1 - I * (ε : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 ((gammaE1 : ℂ) + (-I * (Real.pi : ℂ)) - (Ein_real 1 : ℂ))) :=
      (tendsto_const_nhds.add tendsto_log_neg_one_sub_I_mul).sub hEin_lim
    have hsum := hEi_lim.add hE1_lim
    have hsimp : ((gammaE1 : ℂ) + -I * (Real.pi : ℂ) - (Ein_real 1 : ℂ)) +
        (PakNthPrimeEngine.E1 1 : ℂ) = -I * (Real.pi : ℂ) := by
      dsimp only [gammaE1]
      push_cast
      ring
    rwa [hsimp] at hsum
  have hconst_lim : Tendsto (fun ε : ℝ => h (-1 - I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (h w)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hconst w (-1 - I * (ε : ℂ)) hw (by simp; linarith)
  have hhw : h w = -I * (Real.pi : ℂ) := tendsto_nhds_unique hconst_lim hlim
  dsimp only [h] at hhw
  linear_combination hhw

/-- **Exact Upper Half-Plane Branch-Cut Identity**:
For every `w : ℂ` with `0 < w.im`, `Ei_complex w = -E1_complex (-w) + I * π`. -/
theorem Ei_complex_eq_neg_E1_add_I_pi {w : ℂ} (hw : 0 < w.im) :
    Ei_complex w = -E1_complex (-w) + I * (Real.pi : ℂ) := by
  let h : ℂ → ℂ := fun z => Ei_complex z + E1_complex (-z)
  have hh_deriv : ∀ z : ℂ, 0 < z.im → HasDerivAt h 0 z := by
    intro z hz
    have hslit : z ∈ Complex.slitPlane := Or.inr (ne_of_gt hz)
    have hEi := hasDerivAt_Ei_complex hslit
    have hE1 : HasDerivAt (fun y : ℂ => E1_complex (-y)) (-Complex.exp (-(-z)) / (-z) * (-1)) z :=
      (hasDerivAt_E1_complex (z₀ := -z) (by simp; linarith)).comp z (hasDerivAt_id z).neg
    have htot := hEi.fun_add hE1
    have h0 : Complex.exp z / z + -Complex.exp (-(-z)) / (-z) * (-1) = 0 := by
      rw [neg_neg]
      have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hslit
      field_simp [hz0]
      ring
    rwa [h0] at htot
  have hconst : ∀ z₁ z₂ : ℂ, 0 < z₁.im → 0 < z₂.im → h z₁ = h z₂ := by
    intro z₁ z₂ h₁ h₂
    have hx : ∀ (x₁ x₂ y : ℝ), 0 < y → h ((x₁ : ℂ) + I * (y : ℂ)) = h ((x₂ : ℂ) + I * (y : ℂ)) := by
      intro x₁ x₂ y hy
      have hd_all : ∀ x : ℝ, HasDerivAt (fun t : ℝ => h ((t : ℂ) + I * (y : ℂ))) 0 x := by
        intro x
        have hd := (hh_deriv ((x : ℂ) + I * (y : ℂ)) (by simp; linarith)).comp x
          ((hasDerivAt_id x).ofReal_comp.add_const (I * (y : ℂ)))
        simpa [Function.comp_def] using hd
      exact is_const_of_deriv_eq_zero (fun x => (hd_all x).differentiableAt)
        (fun x => (hd_all x).deriv) x₁ x₂
    have hy : ∀ (x : ℝ) (u₁ u₂ : ℝ),
        h ((x : ℂ) + I * (Real.exp u₁ : ℂ)) = h ((x : ℂ) + I * (Real.exp u₂ : ℂ)) := by
      intro x u₁ u₂
      have hd_all : ∀ u : ℝ, HasDerivAt (fun t : ℝ => h ((x : ℂ) + I * (Real.exp t : ℂ))) 0 u := by
        intro u
        have him : 0 < ((x : ℂ) + I * (Real.exp u : ℂ)).im := by
          rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
          linarith [Real.exp_pos u]
        have hd := (hh_deriv ((x : ℂ) + I * (Real.exp u : ℂ)) him).comp u
          (((Real.hasDerivAt_exp u).ofReal_comp.const_mul I).const_add (x : ℂ))
        simpa [Function.comp_def] using hd
      exact is_const_of_deriv_eq_zero (fun u => (hd_all u).differentiableAt)
        (fun u => (hd_all u).deriv) u₁ u₂
    have hz1 : z₁ = (z₁.re : ℂ) + I * (Real.exp (Real.log z₁.im) : ℂ) := by
      rw [Real.exp_log h₁]
      apply Complex.ext <;> simp
    have hz2 : z₂ = (z₂.re : ℂ) + I * (Real.exp (Real.log z₂.im) : ℂ) := by
      rw [Real.exp_log h₂]
      apply Complex.ext <;> simp
    rw [hz1, hz2]
    exact (hx z₁.re z₂.re (Real.exp (Real.log z₁.im)) (Real.exp_pos _)).trans
      (hy z₂.re (Real.log z₁.im) (Real.log z₂.im))
  have hlim : Tendsto (fun ε : ℝ => h (-1 + I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (I * (Real.pi : ℂ))) := by
    have hE1_lim : Tendsto (fun ε : ℝ => E1_complex (-(-1 + I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
        (𝓝 (PakNthPrimeEngine.E1 1 : ℂ)) := by
      have hneg0 : Tendsto (fun ε : ℝ => -ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using continuous_neg.tendsto (0 : ℝ)
      have h1 : Tendsto (fun ε : ℝ => E1_complex ((1 : ℂ) + I * ((-ε : ℝ) : ℂ))) (𝓝[>] (0 : ℝ))
          (𝓝 (PakNthPrimeEngine.E1 1 : ℂ)) :=
        ((tendsto_E1_complex_ofReal_add_I_mul zero_lt_one).comp hneg0).mono_left nhdsWithin_le_nhds
      refine h1.congr fun ε => ?_
      congr 1; push_cast; ring
    have hEin_lim : Tendsto (fun ε : ℝ => Ein_complex (-(-1 + I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
        (𝓝 (Ein_real 1 : ℂ)) := by
      have hc : Continuous (fun ε : ℝ => Ein_complex (-(-1 + I * (ε : ℂ)))) :=
        continuous_Ein_complex.comp
          (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).neg
      have h1 : Tendsto (fun ε : ℝ => Ein_complex (-(-1 + I * (ε : ℂ)))) (𝓝[>] (0 : ℝ))
          (𝓝 (Ein_complex (-(-1 + I * ((0 : ℝ) : ℂ))))) :=
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      have h0 : Ein_complex (-(-1 + I * ((0 : ℝ) : ℂ))) = (Ein_real 1 : ℂ) := by
        simpa using Ein_complex_ofReal 1
      rwa [h0] at h1
    have hEi_lim : Tendsto (fun ε : ℝ => Ei_complex (-1 + I * (ε : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 ((gammaE1 : ℂ) + (I * (Real.pi : ℂ)) - (Ein_real 1 : ℂ))) :=
      (tendsto_const_nhds.add tendsto_log_neg_one_add_I_mul).sub hEin_lim
    have hsum := hEi_lim.add hE1_lim
    have hsimp : ((gammaE1 : ℂ) + I * (Real.pi : ℂ) - (Ein_real 1 : ℂ)) +
        (PakNthPrimeEngine.E1 1 : ℂ) = I * (Real.pi : ℂ) := by
      dsimp only [gammaE1]
      push_cast
      ring
    rwa [hsimp] at hsum
  have hconst_lim : Tendsto (fun ε : ℝ => h (-1 + I * (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (h w)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hconst w (-1 + I * (ε : ℂ)) hw (by simp; linarith)
  have hhw : h w = I * (Real.pi : ℂ) := tendsto_nhds_unique hconst_lim hlim
  dsimp only [h] at hhw
  linear_combination hhw

/-! ### 5c. Literal Valley Contour Integrals `I_±(u)`, IBP, Contour Collapse, Smoothness, and Exact Stokes Relation -/

/-- Shifted horizontal line point `s + σ i ε` (`σ = -1` for lower valley `C_+`, `σ = +1` for upper valley `C_-`). -/
@[expose] def valleyPoint (σ s ε : ℝ) : ℂ :=
  (s : ℂ) + (σ : ℂ) * I * (ε : ℂ)

/-- Post-IBP valley contour integral:
`J_valley σ t ε = exp (σ π i t) * t * ∫_{-∞}^{+∞} exp ((s + σ i ε) - t Ei(s + σ i ε)) ds`. -/
@[expose] def J_valley (σ : ℝ) (t : ℂ) (ε : ℝ) : ℂ :=
  Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * t) * t *
    ∫ s : ℝ, Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))

/-- Literal `li^{-1}` complex-valley contour integral (with `1/w` kernel before IBP):
`I_contour σ u ε = exp (σ π i e^{-u}) * e^{-2u} * ∫_{-∞}^{+∞} exp (2(s + σ i ε) - e^{-u} Ei(s + σ i ε)) / (s + σ i ε) ds`. -/
@[expose] def I_contour (σ : ℝ) (u ε : ℝ) : ℂ :=
  let t : ℂ := (Real.exp (-u) : ℂ)
  Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * t) * t ^ 2 *
    ∫ s : ℝ, Complex.exp (2 * valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε)) /
      valleyPoint σ s ε

/-- Literal lateral integral `I_+(u)` defined on all of `ℝ` via the lower valley contour `Im w = -1/4`. -/
@[expose] def I_plus (u : ℝ) : ℂ := I_contour (-1) u (1 / 4)

/-- Literal lateral integral `I_-(u)` defined on all of `ℝ` via the upper valley contour `Im w = +1/4`. -/
@[expose] def I_minus (u : ℝ) : ℂ := I_contour 1 u (1 / 4)

lemma valleyPoint_re (σ s ε : ℝ) : (valleyPoint σ s ε).re = s := by
  simp [valleyPoint]

lemma valleyPoint_im (σ s ε : ℝ) : (valleyPoint σ s ε).im = σ * ε := by
  simp [valleyPoint]

lemma valleyPoint_mem_slitPlane {σ s ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 < ε) :
    valleyPoint σ s ε ∈ Complex.slitPlane := by
  right
  rw [valleyPoint_im]
  rcases hσ with rfl | rfl <;> linarith

lemma valleyPoint_ne_zero {σ s ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 < ε) :
    valleyPoint σ s ε ≠ 0 :=
  Complex.slitPlane_ne_zero (valleyPoint_mem_slitPlane hσ hε)

lemma abs_le_norm_valleyPoint (σ s ε : ℝ) : |s| ≤ ‖valleyPoint σ s ε‖ := by
  simpa [valleyPoint_re] using Complex.abs_re_le_norm (valleyPoint σ s ε)

lemma eps_le_norm_valleyPoint {σ s ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 ≤ ε) :
    ε ≤ ‖valleyPoint σ s ε‖ := by
  have h1 := Complex.abs_im_le_norm (valleyPoint σ s ε)
  rw [valleyPoint_im] at h1
  rcases hσ with rfl | rfl
  · simpa [abs_of_nonneg hε] using h1
  · simpa [abs_of_nonneg hε] using h1

lemma norm_valleyPoint_le {σ s ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 ≤ ε) :
    ‖valleyPoint σ s ε‖ ≤ |s| + ε := by
  dsimp only [valleyPoint]
  calc ‖(s : ℂ) + (σ : ℂ) * I * (ε : ℂ)‖
      ≤ ‖(s : ℂ)‖ + ‖(σ : ℂ) * I * (ε : ℂ)‖ := norm_add_le _ _
    _ = |s| + |σ| * ε := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
    _ = |s| + ε := by rcases hσ with rfl | rfl <;> norm_num

lemma Ei_complex_valleyPoint_branch {σ s ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 < ε) :
    Ei_complex (valleyPoint σ s ε) =
      -E1_complex (-(valleyPoint σ s ε)) + (σ : ℂ) * I * (Real.pi : ℂ) := by
  rcases hσ with rfl | rfl
  · have him : (valleyPoint (-1) s ε).im < 0 := by rw [valleyPoint_im]; linarith
    rw [Ei_complex_eq_neg_E1_sub_I_pi him]; push_cast; ring
  · have him : 0 < (valleyPoint 1 s ε).im := by rw [valleyPoint_im]; linarith
    rw [Ei_complex_eq_neg_E1_add_I_pi him]; push_cast; ring

lemma continuous_Ei_complex_valleyPoint {σ ε : ℝ} (hσ : σ = -1 ∨ σ = 1) (hε : 0 < ε) :
    Continuous (fun s : ℝ => Ei_complex (valleyPoint σ s ε)) := by
  refine continuous_iff_continuousAt.mpr fun s => ?_
  have hd := (hasDerivAt_Ei_complex (valleyPoint_mem_slitPlane hσ hε)).comp s
    ((hasDerivAt_id s).ofReal_comp.add_const ((σ : ℂ) * I * (ε : ℂ)))
  exact hd.continuousAt

/-- Exact vertical-shift perturbation bound on `x > 0`, `0 ≤ ε`:
`‖Ei_complex (x + σ i ε) - Ei_real x‖ ≤ ε * (exp x / x)`. -/
theorem norm_Ei_complex_valleyPoint_sub_Ei_real {σ x ε : ℝ}
    (hσ : σ = -1 ∨ σ = 1) (hx : 0 < x) (hε : 0 ≤ ε) :
    ‖Ei_complex (valleyPoint σ x ε) - (Ei_real x : ℂ)‖ ≤ ε * (Real.exp x / x) := by
  have h0 : Ei_complex (valleyPoint σ x 0) = (Ei_real x : ℂ) := by
    simpa [valleyPoint] using Ei_complex_ofReal_pos hx
  rw [← h0]
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) ε,
      HasDerivAt (fun r : ℝ => Ei_complex (valleyPoint σ x r))
        (Complex.exp (valleyPoint σ x τ) / valleyPoint σ x τ * ((σ : ℂ) * I)) τ := by
    intro τ _
    have hslit : valleyPoint σ x τ ∈ Complex.slitPlane := Or.inl (by rw [valleyPoint_re]; exact hx)
    have hlin : HasDerivAt (fun r : ℝ => valleyPoint σ x r) ((σ : ℂ) * I) τ := by
      dsimp only [valleyPoint]
      simpa using ((hasDerivAt_id τ).ofReal_comp.const_mul ((σ : ℂ) * I)).const_add (x : ℂ)
    exact (hasDerivAt_Ei_complex hslit).comp τ hlin
  have hcont : ContinuousOn
      (fun τ : ℝ => Complex.exp (valleyPoint σ x τ) / valleyPoint σ x τ * ((σ : ℂ) * I))
      (Set.uIcc (0 : ℝ) ε) := by
    have hlin : Continuous (fun τ : ℝ => valleyPoint σ x τ) :=
      continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
    refine ((Complex.continuous_exp.comp hlin).continuousOn.div hlin.continuousOn ?_).mul continuousOn_const
    intro τ _
    exact Complex.slitPlane_ne_zero (Or.inl (by rw [valleyPoint_re]; exact hx))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hftc]
  have hbound : ∀ τ ∈ Set.uIoc (0 : ℝ) ε,
      ‖Complex.exp (valleyPoint σ x τ) / valleyPoint σ x τ * ((σ : ℂ) * I)‖ ≤ Real.exp x / x := by
    intro τ _
    rw [norm_mul, norm_div, Complex.norm_exp, valleyPoint_re, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [hσ1, mul_one]
    have hge : x ≤ ‖valleyPoint σ x τ‖ := by
      simpa [abs_of_pos hx] using abs_le_norm_valleyPoint σ x τ
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx hge
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [sub_zero, abs_of_nonneg hε, mul_comm] using hle

/-- Real-part lower bound on `0 < x ≤ 1`, `0 ≤ ε ≤ 1/2`:
`gammaE1 - exp 2 + log x ≤ (Ei_complex (x + σ i ε)).re`. -/
lemma re_Ei_complex_valleyPoint_ge_small {σ x ε : ℝ}
    (hσ : σ = -1 ∨ σ = 1) (hx0 : 0 < x) (hx1 : x ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    gammaE1 - Real.exp 2 + Real.log x ≤ (Ei_complex (valleyPoint σ x ε)).re := by
  dsimp only [Ei_complex]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.log_re]
  have hnorm_ge : x ≤ ‖valleyPoint σ x ε‖ := by
    simpa [abs_of_pos hx0] using abs_le_norm_valleyPoint σ x ε
  have hlog : Real.log x ≤ Real.log ‖valleyPoint σ x ε‖ := Real.log_le_log hx0 hnorm_ge
  have hnorm_le : ‖-valleyPoint σ x ε‖ ≤ 2 := by
    rw [norm_neg]
    have h1 := norm_valleyPoint_le (s := x) hσ hε0
    rw [abs_of_pos hx0] at h1
    linarith
  have hein : (Ein_complex (-valleyPoint σ x ε)).re ≤ Real.exp 2 :=
    (Complex.re_le_norm _).trans ((norm_Ein_complex_le _).trans (Real.exp_le_exp.mpr hnorm_le))
  linarith

/-- Uniform norm bound on `Ei_complex (x + σ i ε)` for `0 ≤ x ≤ 1` and fixed `0 < ε ≤ 1/2`. -/
lemma norm_Ei_complex_valleyPoint_le_small {σ x ε : ℝ}
    (hσ : σ = -1 ∨ σ = 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ‖Ei_complex (valleyPoint σ x ε)‖ ≤
      |gammaE1| + |Real.log ε| + Real.log 2 + Real.pi + Real.exp 2 := by
  dsimp only [Ei_complex]
  have hge : ε ≤ ‖valleyPoint σ x ε‖ := eps_le_norm_valleyPoint hσ hε0.le
  have hle : ‖valleyPoint σ x ε‖ ≤ 2 := by
    have h1 := norm_valleyPoint_le (s := x) hσ hε0.le
    rw [abs_of_nonneg hx0] at h1
    linarith
  have hlog_re : |Real.log ‖valleyPoint σ x ε‖| ≤ |Real.log ε| + Real.log 2 := by
    have h1 : Real.log ε ≤ Real.log ‖valleyPoint σ x ε‖ := Real.log_le_log hε0 hge
    have h2 : Real.log ‖valleyPoint σ x ε‖ ≤ Real.log 2 :=
      Real.log_le_log (lt_of_lt_of_le hε0 hge) hle
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log ε)], by linarith [abs_nonneg (Real.log ε)]⟩
  have hlog_norm : ‖Complex.log (valleyPoint σ x ε)‖ ≤ |Real.log ε| + Real.log 2 + Real.pi := by
    rw [Complex.log]
    calc ‖(Real.log ‖valleyPoint σ x ε‖ : ℂ) + (Complex.arg (valleyPoint σ x ε) : ℂ) * I‖
        ≤ ‖(Real.log ‖valleyPoint σ x ε‖ : ℂ)‖ + ‖(Complex.arg (valleyPoint σ x ε) : ℂ) * I‖ :=
          norm_add_le _ _
      _ = |Real.log ‖valleyPoint σ x ε‖| + |Complex.arg (valleyPoint σ x ε)| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_I, mul_one]
      _ ≤ (|Real.log ε| + Real.log 2) + Real.pi :=
          add_le_add hlog_re (Complex.abs_arg_le_pi _)
  have hein : ‖Ein_complex (-valleyPoint σ x ε)‖ ≤ Real.exp 2 :=
    (norm_Ein_complex_le _).trans (Real.exp_le_exp.mpr (by simpa [norm_neg] using hle))
  calc ‖(gammaE1 : ℂ) + Complex.log (valleyPoint σ x ε) - Ein_complex (-valleyPoint σ x ε)‖
      ≤ ‖(gammaE1 : ℂ) + Complex.log (valleyPoint σ x ε)‖ + ‖Ein_complex (-valleyPoint σ x ε)‖ :=
        norm_sub_le _ _
    _ ≤ ‖(gammaE1 : ℂ)‖ + ‖Complex.log (valleyPoint σ x ε)‖ + ‖Ein_complex (-valleyPoint σ x ε)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ |gammaE1| + (|Real.log ε| + Real.log 2 + Real.pi) + Real.exp 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
    _ = |gammaE1| + |Real.log ε| + Real.log 2 + Real.pi + Real.exp 2 := by ring

/-- Tail absorption lemma: for `a > 0` and `x ≥ 1`,
`Real.exp x * Real.exp (x - a * (Real.exp x / x)) ≤ (16 / a ^ 2 * Real.exp (12 / a)) * Real.exp (-x)`. -/
lemma exp_mul_tail_absorb {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    Real.exp x * Real.exp (x - a * (Real.exp x / x)) ≤
      (16 / a ^ 2 * Real.exp (12 / a)) * Real.exp (-x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  set y : ℝ := Real.exp x / x
  have hy : 0 < y := div_pos (Real.exp_pos x) hx_pos
  have hsq_exp : x ^ 2 / 2 ≤ Real.exp x := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp x hx_pos.le 2
  have hx_le_2y : x ≤ 2 * y := by
    dsimp only [y]
    rw [mul_div_assoc', le_div_iff₀ hx_pos]
    nlinarith
  have hexp_le_2y2 : Real.exp x ≤ 2 * y ^ 2 := by
    have hxy : Real.exp x = x * y := by dsimp only [y]; field_simp [hx_pos.ne']
    rw [hxy, sq]
    nlinarith
  have hy2_exp : y ^ 2 * Real.exp (-(a / 2) * y) ≤ 8 / a ^ 2 := by
    have h2 : ((a / 2) * y) ^ 2 / 2 ≤ Real.exp ((a / 2) * y) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp ((a / 2) * y) (by positivity) 2
    have hrew : Real.exp (-(a / 2) * y) = (Real.exp ((a / 2) * y))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hrew, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    have hmul : y ^ 2 = (8 / a ^ 2) * (((a / 2) * y) ^ 2 / 2) := by field_simp [ha.ne']; ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have htail := tail_exp_div_dominates (a := a / 2) (by positivity) hx
  have h12 : 6 / (a / 2) = 12 / a := by field_simp [ha.ne']; ring
  rw [h12] at htail
  have hsplit : x - a * y = -(a / 2) * y + (x - (a / 2) * y) := by ring
  rw [hsplit, Real.exp_add]
  calc Real.exp x * (Real.exp (-(a / 2) * y) * Real.exp (x - (a / 2) * y))
      ≤ (2 * y ^ 2) * (Real.exp (-(a / 2) * y) * Real.exp (-x + 12 / a)) := by
        refine mul_le_mul hexp_le_2y2 ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) (Real.exp_pos _).le
    _ = 2 * (y ^ 2 * Real.exp (-(a / 2) * y)) * (Real.exp (12 / a) * Real.exp (-x)) := by
        rw [Real.exp_add]; ring
    _ ≤ 2 * (8 / a ^ 2) * (Real.exp (12 / a) * Real.exp (-x)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hy2_exp (by norm_num)
    _ = (16 / a ^ 2 * Real.exp (12 / a)) * Real.exp (-x) := by ring

/-- Upper bound `‖Ei_complex (x + σ i ε)‖ ≤ (|gammaE1| + 3) * exp x` for `x ≥ 1`, `0 ≤ ε ≤ 1/2`. -/
lemma norm_Ei_complex_valleyPoint_le_large {σ x ε : ℝ}
    (hσ : σ = -1 ∨ σ = 1) (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    ‖Ei_complex (valleyPoint σ x ε)‖ ≤ (|gammaE1| + 3) * Real.exp x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpert := norm_Ei_complex_valleyPoint_sub_Ei_real hσ hx_pos hε0
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog_le : Real.log x ≤ Real.exp x :=
    (Real.log_le_sub_one_of_pos hx_pos).trans (by linarith [Real.add_one_le_exp x])
  have hein_le : |Ein_real (-x)| ≤ Real.exp x := by
    have h1 : |Ein_real (-x)| = ‖Ein_complex ((-x : ℝ) : ℂ)‖ := by
      rw [Ein_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    have hn : ‖((-x : ℝ) : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hx_pos]
    have h2 := norm_Ein_complex_le ((-x : ℝ) : ℂ)
    rwa [hn] at h2
  have hEi_real : |Ei_real x| ≤ (|gammaE1| + 2) * Real.exp x := by
    dsimp only [Ei_real]
    have h1 : 1 ≤ Real.exp x := Real.one_le_exp hx_pos.le
    calc |gammaE1 + Real.log x - Ein_real (-x)|
        ≤ |gammaE1 + Real.log x| + |Ein_real (-x)| := abs_sub _ _
      _ ≤ |gammaE1| + |Real.log x| + |Ein_real (-x)| := add_le_add (abs_add_le _ _) le_rfl
      _ = |gammaE1| + Real.log x + |Ein_real (-x)| := by rw [abs_of_nonneg hlog]
      _ ≤ |gammaE1| * Real.exp x + Real.exp x + Real.exp x := by nlinarith [abs_nonneg gammaE1]
      _ = (|gammaE1| + 2) * Real.exp x := by ring
  have hdiv : ε * (Real.exp x / x) ≤ Real.exp x := by
    have h1 : Real.exp x / x ≤ Real.exp x := div_le_self (Real.exp_pos _).le hx
    nlinarith [Real.exp_pos x]
  have htri : ‖Ei_complex (valleyPoint σ x ε)‖ ≤
      ‖Ei_complex (valleyPoint σ x ε) - (Ei_real x : ℂ)‖ + ‖(Ei_real x : ℂ)‖ := by
    simpa using norm_add_le (Ei_complex (valleyPoint σ x ε) - (Ei_real x : ℂ)) (Ei_real x : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at htri
  linarith

/-- Lower bound on `Re (t * Ei_complex (x + σ i ε))` for `x ≥ 1`, `0 ≤ ε ≤ 1/2`, and `t` with
`0 < t.re` and `ε * |t.im| ≤ (1 / 2 - ε / 2) * t.re` (satisfied for all real `t > 0` with `ε ≤ 1/2`,
and for all complex `t` with `|t.im| ≤ t.re` at `ε = 1/4`!). -/
lemma re_mul_Ei_complex_valleyPoint_ge_large {σ x ε : ℝ} {t : ℂ}
    (hσ : σ = -1 ∨ σ = 1) (hx : 1 ≤ x) (hε0 : 0 ≤ ε)
    (ht0 : 0 < t.re) (hsec : ε * |t.im| ≤ (1 - ε) * t.re - (t.re / 4)) :
    t.re * (gammaE1 - 2) + (t.re / 4) * (Real.exp x / x) ≤
      (t * Ei_complex (valleyPoint σ x ε)).re := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpert := norm_Ei_complex_valleyPoint_sub_Ei_real hσ hx_pos hε0
  have hre_diff : |(Ei_complex (valleyPoint σ x ε)).re - Ei_real x| ≤ ε * (Real.exp x / x) := by
    have h1 := Complex.abs_re_le_norm (Ei_complex (valleyPoint σ x ε) - (Ei_real x : ℂ))
    simpa using h1.trans hpert
  have him_diff : |(Ei_complex (valleyPoint σ x ε)).im| ≤ ε * (Real.exp x / x) := by
    have h1 := Complex.abs_im_le_norm (Ei_complex (valleyPoint σ x ε) - (Ei_real x : ℂ))
    simpa using h1.trans hpert
  have hEi_big : gammaE1 - 2 + Real.exp x / x ≤ Ei_real x := by
    have hge := Ei_real_ge hx_pos
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
    have hdiv : (Real.exp x - 1 - x) / x = Real.exp x / x - 1 / x - 1 := by
      field_simp [hx_pos.ne']
    have h1x : 1 / x ≤ 1 := by rw [div_le_one hx_pos]; exact hx
    linarith
  have hre_ge : gammaE1 - 2 + (1 - ε) * (Real.exp x / x) ≤ (Ei_complex (valleyPoint σ x ε)).re := by
    linarith [(abs_le.mp hre_diff).1]
  have him_prod : -(t.im * (Ei_complex (valleyPoint σ x ε)).im) ≥ -(|t.im| * (ε * (Real.exp x / x))) := by
    have h1 : |t.im * (Ei_complex (valleyPoint σ x ε)).im| ≤ |t.im| * (ε * (Real.exp x / x)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left him_diff (abs_nonneg _)
    linarith [(abs_le.mp h1).2]
  rw [Complex.mul_re]
  have hy_nn : 0 ≤ Real.exp x / x := by positivity
  nlinarith

/-- Uniform dominating bound for `‖exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖`
and its `s`/`t`-derivatives on `ℝ` when `t` lies in a compact subset of the sector
`{0 < Re t, ε * |Im t| ≤ (1 - ε) * Re t - Re t / 4}` and `ε ∈ [ε₀, ε₁] ⊆ (0, 1/2]`. -/
lemma valley_integrand_dom {σ : ℝ} (hσ : σ = -1 ∨ σ = 1)
    {c₀ M ε₀ ε₁ : ℝ} (hc₀ : 0 < c₀) (hε₀ : 0 < ε₀) (hε₁ : ε₁ ≤ 1 / 2) :
    ∃ C > 0, ∀ (t : ℂ) (ε s : ℝ), c₀ ≤ t.re → ‖t‖ ≤ M → ε₀ ≤ ε → ε ≤ ε₁ →
      ε * |t.im| ≤ (1 - ε) * t.re - t.re / 4 →
      ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤ C * Real.exp (-|s|) ∧
      ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε)) *
          (1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε)‖ ≤ C * Real.exp (-|s|) ∧
      ‖Ei_complex (valleyPoint σ s ε) *
          Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤ C * Real.exp (-|s|) := by
  let M' : ℝ := max M c₀
  have hM'_pos : 0 < M' := lt_of_lt_of_le hc₀ (le_max_right _ _)
  let K_neg : ℝ := Real.exp (M' * (1 / ε₀ + Real.pi))
  let K_mid_Ei : ℝ := |gammaE1| + |Real.log ε₀| + Real.log 2 + Real.pi + Real.exp 2
  let K_mid : ℝ := Real.exp (1 + M' * K_mid_Ei) * Real.exp 1
  let K_pos_base : ℝ := Real.exp (M' * |gammaE1 - 2|)
  let K_pos0 : ℝ := K_pos_base * Real.exp (24 / c₀)
  let K_pos1 : ℝ := K_pos_base * (16 / (c₀ / 4) ^ 2 * Real.exp (12 / (c₀ / 4)))
  let C : ℝ :=
    (K_neg + K_mid + K_pos0 + K_pos1) *
      (1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3)) + 1
  have hK_neg_pos : 0 < K_neg := Real.exp_pos _
  have hK_mid_Ei_nn : 0 ≤ K_mid_Ei := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [K_mid_Ei]; positivity
  have hK_mid_pos : 0 < K_mid := by dsimp only [K_mid]; positivity
  have hK_pos0_pos : 0 < K_pos0 := by dsimp only [K_pos0, K_pos_base]; positivity
  have hK_pos1_pos : 0 < K_pos1 := by dsimp only [K_pos1, K_pos_base]; positivity
  have hC_pos : 0 < C := by
    have h1 : 0 ≤ K_neg + K_mid + K_pos0 + K_pos1 := by positivity
    have h2 : 0 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
      have : 0 ≤ Real.pi := Real.pi_pos.le
      positivity
    dsimp only [C]
    nlinarith
  refine ⟨C, hC_pos, fun t ε s htre htnorm hε_lo hε_hi hsec_ε => ?_⟩
  have hε_pos : 0 < ε := lt_of_lt_of_le hε₀ hε_lo
  have ht_pos : 0 < t.re := lt_of_lt_of_le hc₀ htre
  have htnorm' : ‖t‖ ≤ M' := htnorm.trans (le_max_left _ _)
  have hε_half : ε ≤ 1 / 2 := hε_hi.trans hε₁
  by_cases hs0 : s ≤ 0
  · have habs : |s| = -s := abs_of_nonpos hs0
    have hbranch := Ei_complex_valleyPoint_branch (s := s) hσ hε_pos
    have hE1_b : ‖E1_complex (-valleyPoint σ s ε)‖ ≤ 1 / ε₀ := by
      have him_ne : (-valleyPoint σ s ε).im ≠ 0 := by
        rw [Complex.neg_im, valleyPoint_im]
        rcases hσ with rfl | rfl <;> linarith
      have hb := norm_E1_complex_le_exp_div_im him_ne
      have hre : -(-valleyPoint σ s ε).re = s := by simp [valleyPoint_re]
      have him_abs : |(-valleyPoint σ s ε).im| = ε := by
        rw [Complex.neg_im, valleyPoint_im, abs_neg]
        rcases hσ with rfl | rfl <;> simp [abs_of_pos hε_pos]
      rw [hre, him_abs] at hb
      calc ‖E1_complex (-valleyPoint σ s ε)‖ ≤ Real.exp s / ε := hb
        _ ≤ 1 / ε := div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr hs0) hε_pos.le
        _ ≤ 1 / ε₀ := div_le_div_of_nonneg_left zero_le_one hε₀ hε_lo
    have hEi_b : ‖Ei_complex (valleyPoint σ s ε)‖ ≤ 1 / ε₀ + Real.pi := by
      rw [hbranch]
      calc ‖-E1_complex (-valleyPoint σ s ε) + (σ : ℂ) * I * (Real.pi : ℂ)‖
          ≤ ‖-E1_complex (-valleyPoint σ s ε)‖ + ‖(σ : ℂ) * I * (Real.pi : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / ε₀ + Real.pi := by
            rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
              mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
            have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
            rw [hσ1, one_mul]
            linarith
    have hbase : ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤
        K_neg * Real.exp (-|s|) := by
      rw [Complex.norm_exp, Complex.sub_re, valleyPoint_re, habs, neg_neg]
      have hre_le : -(t * Ei_complex (valleyPoint σ s ε)).re ≤ M' * (1 / ε₀ + Real.pi) := by
        have h1 : -(t * Ei_complex (valleyPoint σ s ε)).re ≤ ‖t * Ei_complex (valleyPoint σ s ε)‖ :=
          (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        rw [norm_mul] at h1
        exact h1.trans (mul_le_mul htnorm' hEi_b (norm_nonneg _) hM'_pos.le)
      calc Real.exp (s - (t * Ei_complex (valleyPoint σ s ε)).re)
          ≤ Real.exp (M' * (1 / ε₀ + Real.pi) + s) := Real.exp_le_exp.mpr (by linarith)
        _ = K_neg * Real.exp s := Real.exp_add _ _
    have hfac : ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ ≤
        1 + M' * (Real.exp 1 / ε₀) := by
      calc ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖
          ≤ ‖(1 : ℂ)‖ + ‖t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ := norm_sub_le _ _
        _ = 1 + ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ := by
            rw [norm_one, norm_div, norm_mul, Complex.norm_exp, valleyPoint_re]
        _ ≤ 1 + M' * (Real.exp 1 / ε₀) := by
            have h1 : ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ ≤ M' * (Real.exp 1 / ε₀) := by
              rw [mul_div_assoc]
              refine mul_le_mul htnorm' ?_ (by positivity) hM'_pos.le
              have he : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
              have hv : ε₀ ≤ ‖valleyPoint σ s ε‖ := hε_lo.trans (eps_le_norm_valleyPoint hσ hε_pos.le)
              exact div_le_div₀ (Real.exp_pos 1).le he hε₀ hv
            linarith
    have hS1 : K_neg ≤ K_neg + K_mid + K_pos0 + K_pos1 := by linarith
    have hpi_nn : 0 ≤ Real.pi := Real.pi_pos.le
    have hR1 : 1 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
      have : 0 ≤ M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
      linarith
    have hR2 : 1 + M' * (Real.exp 1 / ε₀) ≤
        1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
      have : 0 ≤ M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
      linarith
    have hR3 : 1 / ε₀ + Real.pi ≤
        1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
      have : 0 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + K_mid_Ei + (|gammaE1| + 3) := by positivity
      linarith
    have hK_le : K_neg ≤ C := by
      have hm := mul_le_mul hS1 hR1 zero_le_one (by positivity)
      dsimp only [C]; linarith
    have hK_fac : K_neg * (1 + M' * (Real.exp 1 / ε₀)) ≤ C := by
      have hm := mul_le_mul hS1 hR2 (by positivity) (by positivity)
      dsimp only [C]; linarith
    have hK_Ei : (1 / ε₀ + Real.pi) * K_neg ≤ C := by
      have hm := mul_le_mul hS1 hR3 (by positivity) (by positivity)
      dsimp only [C]; linarith
    refine ⟨hbase.trans (mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le), ?_, ?_⟩
    · rw [norm_mul]
      calc _ ≤ (K_neg * Real.exp (-|s|)) * (1 + M' * (Real.exp 1 / ε₀)) :=
            mul_le_mul hbase hfac (norm_nonneg _) (by positivity)
        _ = (K_neg * (1 + M' * (Real.exp 1 / ε₀))) * Real.exp (-|s|) := by ring
        _ ≤ C * Real.exp (-|s|) := mul_le_mul_of_nonneg_right hK_fac (Real.exp_pos _).le
    · rw [norm_mul]
      calc _ ≤ (1 / ε₀ + Real.pi) * (K_neg * Real.exp (-|s|)) :=
            mul_le_mul hEi_b hbase (norm_nonneg _) (by positivity)
        _ = ((1 / ε₀ + Real.pi) * K_neg) * Real.exp (-|s|) := by ring
        _ ≤ C * Real.exp (-|s|) := mul_le_mul_of_nonneg_right hK_Ei (Real.exp_pos _).le
  · push Not at hs0
    by_cases hs1 : s ≤ 1
    · have habs : |s| = s := abs_of_pos hs0
      have hEi_b : ‖Ei_complex (valleyPoint σ s ε)‖ ≤ K_mid_Ei := by
        have h1 := norm_Ei_complex_valleyPoint_le_small hσ hs0.le hs1 hε_pos hε_half
        have hlog_le : |Real.log ε| ≤ |Real.log ε₀| := by
          have hε1' : ε ≤ 1 := by linarith
          have hε0' : ε₀ ≤ 1 := by linarith
          rw [abs_of_nonpos (Real.log_nonpos hε_pos.le hε1'),
            abs_of_nonpos (Real.log_nonpos hε₀.le hε0')]
          linarith [Real.log_le_log hε₀ hε_lo]
        dsimp only [K_mid_Ei]
        linarith
      have hbase : ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤
          K_mid * Real.exp (-|s|) := by
        rw [Complex.norm_exp, Complex.sub_re, valleyPoint_re, habs]
        have hre_le : -(t * Ei_complex (valleyPoint σ s ε)).re ≤ M' * K_mid_Ei := by
          have h1 : -(t * Ei_complex (valleyPoint σ s ε)).re ≤ ‖t * Ei_complex (valleyPoint σ s ε)‖ :=
            (neg_le_abs _).trans (Complex.abs_re_le_norm _)
          rw [norm_mul] at h1
          exact h1.trans (mul_le_mul htnorm' hEi_b (norm_nonneg _) hM'_pos.le)
        calc Real.exp (s - (t * Ei_complex (valleyPoint σ s ε)).re)
            ≤ Real.exp (1 + M' * K_mid_Ei) := Real.exp_le_exp.mpr (by linarith)
          _ ≤ Real.exp (1 + M' * K_mid_Ei) * Real.exp (1 - s) := by
              exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (by linarith))
          _ = K_mid * Real.exp (-s) := by
              have h1s : Real.exp (1 - s) = Real.exp 1 * Real.exp (-s) := by
                rw [sub_eq_add_neg, Real.exp_add]
              rw [h1s]; dsimp only [K_mid]; ring
      have hfac : ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ ≤
          1 + M' * (Real.exp 1 / ε₀) := by
        calc ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖
            ≤ ‖(1 : ℂ)‖ + ‖t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ := norm_sub_le _ _
          _ = 1 + ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ := by
              rw [norm_one, norm_div, norm_mul, Complex.norm_exp, valleyPoint_re]
          _ ≤ 1 + M' * (Real.exp 1 / ε₀) := by
              have h1 : ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ ≤ M' * (Real.exp 1 / ε₀) := by
                rw [mul_div_assoc]
                refine mul_le_mul htnorm' ?_ (by positivity) hM'_pos.le
                have he : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr hs1
                have hv : ε₀ ≤ ‖valleyPoint σ s ε‖ := hε_lo.trans (eps_le_norm_valleyPoint hσ hε_pos.le)
                exact div_le_div₀ (Real.exp_pos 1).le he hε₀ hv
              linarith
      have hS1 : K_mid ≤ K_neg + K_mid + K_pos0 + K_pos1 := by linarith
      have hpi_nn : 0 ≤ Real.pi := Real.pi_pos.le
      have hR1 : 1 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
        linarith
      have hR2 : 1 + M' * (Real.exp 1 / ε₀) ≤
          1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
        linarith
      have hR3 : K_mid_Ei ≤
          1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + (|gammaE1| + 3) := by positivity
        linarith
      have hK_le : K_mid ≤ C := by
        have hm := mul_le_mul hS1 hR1 zero_le_one (by positivity)
        dsimp only [C]; linarith
      have hK_fac : K_mid * (1 + M' * (Real.exp 1 / ε₀)) ≤ C := by
        have hm := mul_le_mul hS1 hR2 (by positivity) (by positivity)
        dsimp only [C]; linarith
      have hK_Ei : K_mid_Ei * K_mid ≤ C := by
        have hm := mul_le_mul hS1 hR3 hK_mid_Ei_nn (by positivity)
        dsimp only [C]; linarith
      refine ⟨hbase.trans (mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le), ?_, ?_⟩
      · rw [norm_mul]
        calc _ ≤ (K_mid * Real.exp (-|s|)) * (1 + M' * (Real.exp 1 / ε₀)) :=
              mul_le_mul hbase hfac (norm_nonneg _) (by positivity)
          _ = (K_mid * (1 + M' * (Real.exp 1 / ε₀))) * Real.exp (-|s|) := by ring
          _ ≤ C * Real.exp (-|s|) := mul_le_mul_of_nonneg_right hK_fac (Real.exp_pos _).le
      · rw [norm_mul]
        calc _ ≤ K_mid_Ei * (K_mid * Real.exp (-|s|)) :=
              mul_le_mul hEi_b hbase (norm_nonneg _) hK_mid_Ei_nn
          _ = (K_mid_Ei * K_mid) * Real.exp (-|s|) := by ring
          _ ≤ C * Real.exp (-|s|) := mul_le_mul_of_nonneg_right hK_Ei (Real.exp_pos _).le
    · push Not at hs1
      have hs1' : 1 ≤ s := le_of_lt hs1
      have habs : |s| = s := abs_of_pos hs0
      have hre_ge := re_mul_Ei_complex_valleyPoint_ge_large hσ hs1' hε_pos.le ht_pos hsec_ε
      have htre_le_M : t.re ≤ M' := (Complex.re_le_norm t).trans htnorm'
      have hbase_raw : ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤
          K_pos_base * Real.exp (s - (c₀ / 4) * (Real.exp s / s)) := by
        rw [Complex.norm_exp, Complex.sub_re, valleyPoint_re]
        have h1 : -(t.re * (gammaE1 - 2)) ≤ M' * |gammaE1 - 2| := by
          calc -(t.re * (gammaE1 - 2)) = t.re * -(gammaE1 - 2) := by ring
            _ ≤ t.re * |gammaE1 - 2| := mul_le_mul_of_nonneg_left (neg_le_abs _) ht_pos.le
            _ ≤ M' * |gammaE1 - 2| := mul_le_mul_of_nonneg_right htre_le_M (abs_nonneg _)
        have hy_nn : 0 ≤ Real.exp s / s := by positivity
        have harg : s - (t * Ei_complex (valleyPoint σ s ε)).re ≤
            M' * |gammaE1 - 2| + (s - (c₀ / 4) * (Real.exp s / s)) := by
          nlinarith
        calc Real.exp (s - (t * Ei_complex (valleyPoint σ s ε)).re)
            ≤ Real.exp (M' * |gammaE1 - 2| + (s - (c₀ / 4) * (Real.exp s / s))) :=
              Real.exp_le_exp.mpr harg
          _ = K_pos_base * Real.exp (s - (c₀ / 4) * (Real.exp s / s)) := Real.exp_add _ _
      have hbase : ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤
          K_pos0 * Real.exp (-|s|) := by
        rw [habs]
        have htail := tail_exp_div_dominates (a := c₀ / 4) (by positivity) hs1'
        have h24 : 6 / (c₀ / 4) = 24 / c₀ := by field_simp [hc₀.ne']; ring
        rw [h24] at htail
        calc ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖
            ≤ K_pos_base * Real.exp (s - (c₀ / 4) * (Real.exp s / s)) := hbase_raw
          _ ≤ K_pos_base * Real.exp (-s + 24 / c₀) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) (Real.exp_pos _).le
          _ = K_pos0 * Real.exp (-s) := by dsimp only [K_pos0]; rw [Real.exp_add]; ring
      have hexp_base : Real.exp s * ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ ≤
          K_pos1 * Real.exp (-|s|) := by
        rw [habs]
        calc Real.exp s * ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖
            ≤ Real.exp s * (K_pos_base * Real.exp (s - (c₀ / 4) * (Real.exp s / s))) :=
              mul_le_mul_of_nonneg_left hbase_raw (Real.exp_pos _).le
          _ = K_pos_base * (Real.exp s * Real.exp (s - (c₀ / 4) * (Real.exp s / s))) := by ring
          _ ≤ K_pos_base * ((16 / (c₀ / 4) ^ 2 * Real.exp (12 / (c₀ / 4))) * Real.exp (-s)) :=
              mul_le_mul_of_nonneg_left (exp_mul_tail_absorb (by positivity) hs1') (Real.exp_pos _).le
          _ = K_pos1 * Real.exp (-s) := by dsimp only [K_pos1]; ring
      have hpi_nn : 0 ≤ Real.pi := Real.pi_pos.le
      have hR1 : 1 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
        linarith
      have hR2 : 1 + M' ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ M' * (Real.exp 1 / ε₀) + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by positivity
        linarith
      have hR3 : |gammaE1| + 3 ≤
          1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei + (|gammaE1| + 3) := by
        have : 0 ≤ 1 + M' * (Real.exp 1 / ε₀) + M' + (1 / ε₀ + Real.pi) + K_mid_Ei := by positivity
        linarith
      have hK0_le : K_pos0 ≤ C := by
        have hS1 : K_pos0 ≤ K_neg + K_mid + K_pos0 + K_pos1 := by linarith
        have hm := mul_le_mul hS1 hR1 zero_le_one (by positivity)
        dsimp only [C]; linarith
      refine ⟨hbase.trans (mul_le_mul_of_nonneg_right hK0_le (Real.exp_pos _).le), ?_, ?_⟩
      · have hfac : ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ ≤
            1 + M' * Real.exp s := by
          calc ‖1 - t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖
              ≤ ‖(1 : ℂ)‖ + ‖t * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε‖ := norm_sub_le _ _
            _ = 1 + ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ := by
                rw [norm_one, norm_div, norm_mul, Complex.norm_exp, valleyPoint_re]
            _ ≤ 1 + M' * Real.exp s := by
                have hv : 1 ≤ ‖valleyPoint σ s ε‖ := by
                  have := abs_le_norm_valleyPoint σ s ε; rw [habs] at this; linarith
                have hdiv : ‖t‖ * Real.exp s / ‖valleyPoint σ s ε‖ ≤ ‖t‖ * Real.exp s :=
                  div_le_self (by positivity) hv
                have hm : ‖t‖ * Real.exp s ≤ M' * Real.exp s :=
                  mul_le_mul_of_nonneg_right htnorm' (Real.exp_pos _).le
                linarith
        rw [norm_mul]
        calc _ ≤ ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ * (1 + M' * Real.exp s) :=
              mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
          _ = ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ +
                M' * (Real.exp s * ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖) := by ring
          _ ≤ K_pos0 * Real.exp (-|s|) + M' * (K_pos1 * Real.exp (-|s|)) :=
              add_le_add hbase (mul_le_mul_of_nonneg_left hexp_base hM'_pos.le)
          _ = (K_pos0 + M' * K_pos1) * Real.exp (-|s|) := by ring
          _ ≤ C * Real.exp (-|s|) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              have hS1 : K_pos0 + K_pos1 ≤ K_neg + K_mid + K_pos0 + K_pos1 := by linarith
              have hm := mul_le_mul hS1 hR2 (by positivity) (by positivity)
              have hle2 : K_pos0 + M' * K_pos1 ≤ (K_pos0 + K_pos1) * (1 + M') := by nlinarith
              dsimp only [C]; linarith
      · have hEi_b := norm_Ei_complex_valleyPoint_le_large hσ hs1' hε_pos.le hε_half
        rw [norm_mul]
        calc _ ≤ ((|gammaE1| + 3) * Real.exp s) *
              ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖ :=
              mul_le_mul_of_nonneg_right hEi_b (norm_nonneg _)
          _ = (|gammaE1| + 3) *
              (Real.exp s * ‖Complex.exp (valleyPoint σ s ε - t * Ei_complex (valleyPoint σ s ε))‖) := by ring
          _ ≤ (|gammaE1| + 3) * (K_pos1 * Real.exp (-|s|)) :=
              mul_le_mul_of_nonneg_left hexp_base (by positivity)
          _ = ((|gammaE1| + 3) * K_pos1) * Real.exp (-|s|) := by ring
          _ ≤ C * Real.exp (-|s|) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              have hS1 : K_pos1 ≤ K_neg + K_mid + K_pos0 + K_pos1 := by linarith
              have hm := mul_le_mul hS1 hR3 (by positivity) (by positivity)
              dsimp only [C]; linarith

lemma integrable_exp_neg_abs : Integrable (fun s : ℝ => Real.exp (-|s|)) volume := by
  have h1 : IntegrableOn (fun s : ℝ => Real.exp (-|s|)) (Set.Iic 0) := by
    have hneg : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
        (fun x _ => by simp) measurableSet_Ioi
    rw [← integrable_indicator_iff measurableSet_Iic]
    rw [← integrable_indicator_iff measurableSet_Ioi] at hneg
    have hcomp := hneg.comp_neg
    refine hcomp.congr ?_
    have hae : (Set.Iic (0 : ℝ) : Set ℝ) =ᵐ[volume] Set.Iio (0 : ℝ) := Iio_ae_eq_Iic.symm
    filter_upwards [hae] with s hs
    by_cases h0 : s < 0
    · have hle : s ≤ 0 := le_of_lt h0
      have hpos : 0 < -s := by linarith
      simp [Set.indicator, hle, hpos, abs_of_nonpos hle]
    · by_cases heq0 : s = 0
      · exfalso
        have hmem1 : s ∈ Set.Iic (0 : ℝ) := by simp [heq0]
        have hmem2 : s ∉ Set.Iio (0 : ℝ) := by simp [heq0]
        exact hmem2 (hs.mp hmem1)
      · have hgt : 0 < s := lt_of_le_of_ne (not_lt.mp h0) (Ne.symm heq0)
        simp [Set.indicator, not_le.mpr hgt, not_lt.mpr (show -s ≤ 0 by linarith)]
  have h2 : IntegrableOn (fun s : ℝ => Real.exp (-|s|)) (Set.Ioi 0) := by
    have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
        (fun x _ => by simp) measurableSet_Ioi
    exact hexp.congr_fun (fun s hs => by simp [abs_of_pos (Set.mem_Ioi.mp hs)]) measurableSet_Ioi
  have hunion : IntegrableOn (fun s : ℝ => Real.exp (-|s|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    h1.union h2
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at hunion

/-- **Exact Integration by Parts on the Valley Contour**:
For every `u : ℝ` (`t = exp(-u) > 0`), `σ ∈ {-1, 1}`, and `0 < ε ≤ 1/2`,
`I_contour σ u ε = J_valley σ (Real.exp (-u)) ε`. -/
theorem I_contour_eq_J_valley {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) (u : ℝ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    I_contour σ u ε = J_valley σ (Real.exp (-u)) ε := by
  let t : ℝ := Real.exp (-u)
  have ht_pos : 0 < t := Real.exp_pos (-u)
  let f : ℝ → ℂ := fun s =>
    Complex.exp (valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε))
  let f' : ℝ → ℂ := fun s =>
    f s * (1 - (t : ℂ) * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε)
  have hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s := by
    intro s
    have hlin : HasDerivAt (fun x : ℝ => valleyPoint σ x ε) 1 s := by
      dsimp only [valleyPoint]
      simpa using (hasDerivAt_id s).ofReal_comp.add_const ((σ : ℂ) * I * (ε : ℂ))
    have hEi : HasDerivAt (fun x : ℝ => Ei_complex (valleyPoint σ x ε))
        (Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε * 1) s := by
      simpa [Function.comp_def] using
        (hasDerivAt_Ei_complex (valleyPoint_mem_slitPlane hσ hε0)).comp s hlin
    have hsub := hlin.fun_sub (hEi.const_mul (t : ℂ))
    refine hsub.cexp.congr_deriv ?_
    dsimp only [f, f']
    ring
  obtain ⟨C, hC, hCbound⟩ := valley_integrand_dom hσ (c₀ := t) (M := t) (ε₀ := ε) (ε₁ := ε)
    ht_pos hε0 hε1
  have hft_b : ∀ s : ℝ, ‖f s‖ ≤ C * Real.exp (-|s|) ∧ ‖f' s‖ ≤ C * Real.exp (-|s|) := by
    intro s
    have h := hCbound (t : ℂ) ε s (by simp) (by simp [abs_of_pos ht_pos]) le_rfl le_rfl
      (by simp; nlinarith)
    exact ⟨h.1, h.2.1⟩
  have hf_int : Integrable f volume := by
    have hc : Continuous f :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.add continuous_const).sub
          (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε0)))
    exact (integrable_exp_neg_abs.const_mul C).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun s => (hft_b s).1)
  have hf'_int : Integrable f' volume := by
    have hc_f : Continuous f :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.add continuous_const).sub
          (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε0)))
    have hc_v : Continuous (fun s : ℝ => valleyPoint σ s ε) :=
      Complex.continuous_ofReal.add continuous_const
    have hc_f' : Continuous f' :=
      hc_f.mul (continuous_const.sub ((continuous_const.mul (Complex.continuous_exp.comp hc_v)).div
        hc_v (fun s => valleyPoint_ne_zero hσ hε0)))
    exact (integrable_exp_neg_abs.const_mul C).mono' hc_f'.aestronglyMeasurable
      (Eventually.of_forall fun s => (hft_b s).2)
  have hzero : ∫ s : ℝ, f' s = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf'_int hf_int
  have halg : ∀ s : ℝ,
      (t : ℂ) * (Complex.exp (2 * valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε)) /
        valleyPoint σ s ε) = f s - f' s := by
    intro s
    dsimp only [f, f']
    have hexp2 : Complex.exp (2 * valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε)) =
        Complex.exp (valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε)) *
          Complex.exp (valleyPoint σ s ε) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hexp2]
    ring
  dsimp only [I_contour, J_valley]
  have h1 : Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) ^ 2 *
      ∫ s : ℝ, Complex.exp (2 * valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε)) /
        valleyPoint σ s ε =
      Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) *
      ∫ s : ℝ, (t : ℂ) * (Complex.exp (2 * valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε)) /
        valleyPoint σ s ε) := by
    rw [integral_const_mul]; ring
  change Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) ^ 2 * _ = _
  rw [h1]
  simp_rw [halg]
  rw [integral_sub hf_int hf'_int, hzero, sub_zero]

/-- **Exact Contour Invariance in `ε ∈ (0, 1/2)`**:
`J_valley σ (Real.exp (-u)) ε` is independent of `ε ∈ (0, 1/2)` for every `u : ℝ`! -/
theorem J_valley_const_in_eps {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) (u : ℝ) {ε₁ ε₂ : ℝ}
    (h1 : ε₁ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (h2 : ε₂ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    J_valley σ (Real.exp (-u)) ε₁ = J_valley σ (Real.exp (-u)) ε₂ := by
  let t : ℝ := Real.exp (-u)
  have ht_pos : 0 < t := Real.exp_pos (-u)
  let K : ℝ → ℂ := fun ε =>
    ∫ s : ℝ, Complex.exp (valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε))
  have hK_deriv : ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), HasDerivAt K 0 ε := by
    intro ε₀ hε₀
    let r : ℝ := min (ε₀ / 2) ((1 / 2 - ε₀) / 2)
    have hr : 0 < r := lt_min (half_pos hε₀.1) (half_pos (by linarith [hε₀.2]))
    have hlo : 0 < ε₀ - r := by
      have : r ≤ ε₀ / 2 := min_le_left _ _; linarith [hε₀.1]
    have hhi : ε₀ + r ≤ 1 / 2 := by
      have : r ≤ (1 / 2 - ε₀) / 2 := min_le_right _ _; linarith [hε₀.2]
    obtain ⟨C, hC, hCbound⟩ := valley_integrand_dom hσ (c₀ := t) (M := t)
      (ε₀ := ε₀ - r) (ε₁ := ε₀ + r) ht_pos hlo hhi
    let F : ℝ → ℝ → ℂ := fun ε s =>
      Complex.exp (valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε))
    let F' : ℝ → ℝ → ℂ := fun ε s =>
      ((σ : ℂ) * I) * (F ε s * (1 - (t : ℂ) * Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε))
    have hF_meas : ∀ᶠ ε in 𝓝 ε₀, AEStronglyMeasurable (F ε) volume := by
      filter_upwards [Metric.ball_mem_nhds ε₀ hr] with ε hε
      have hε_pos : 0 < ε := by
        have hd : |ε - ε₀| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hε
        linarith [(abs_lt.mp hd).1]
      have hc : Continuous (F ε) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.add continuous_const).sub
            (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε_pos)))
      exact hc.aestronglyMeasurable
    have hF_int : Integrable (F ε₀) volume := by
      have hc : Continuous (F ε₀) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.add continuous_const).sub
            (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε₀.1)))
      exact (integrable_exp_neg_abs.const_mul C).mono' hc.aestronglyMeasurable
        (Eventually.of_forall fun s =>
          (hCbound (t : ℂ) ε₀ s (by simp) (by simp [abs_of_pos ht_pos]) (by linarith) (by linarith)
            (by simp; nlinarith [hε₀.2])).1)
    have hF'_meas : AEStronglyMeasurable (F' ε₀) volume := by
      have hc_f : Continuous (F ε₀) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.add continuous_const).sub
            (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε₀.1)))
      have hc_v : Continuous (fun s : ℝ => valleyPoint σ s ε₀) :=
        Complex.continuous_ofReal.add continuous_const
      have hc : Continuous (F' ε₀) :=
        continuous_const.mul (hc_f.mul (continuous_const.sub
          ((continuous_const.mul (Complex.continuous_exp.comp hc_v)).div hc_v
            (fun s => valleyPoint_ne_zero hσ hε₀.1))))
      exact hc.aestronglyMeasurable
    have hbound_ae : ∀ᵐ s ∂volume, ∀ ε ∈ Metric.ball ε₀ r, ‖F' ε s‖ ≤ C * Real.exp (-|s|) := by
      filter_upwards with s ε hε
      have hd : |ε - ε₀| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hε
      have h1' : ε₀ - r ≤ ε := by linarith [(abs_lt.mp hd).1]
      have h2' : ε ≤ ε₀ + r := by linarith [(abs_lt.mp hd).2]
      dsimp only [F']
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [hσ1, one_mul]
      exact (hCbound (t : ℂ) ε s (by simp) (by simp [abs_of_pos ht_pos]) h1' h2'
        (by simp; nlinarith)).2.1
    have hdiff_ae : ∀ᵐ s ∂volume, ∀ ε ∈ Metric.ball ε₀ r, HasDerivAt (F · s) (F' ε s) ε := by
      filter_upwards with s ε hε
      have hd : |ε - ε₀| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hε
      have hε_pos : 0 < ε := by linarith [(abs_lt.mp hd).1]
      have hlin : HasDerivAt (fun e : ℝ => valleyPoint σ s e) ((σ : ℂ) * I) ε := by
        dsimp only [valleyPoint]
        simpa using ((hasDerivAt_id ε).ofReal_comp.const_mul ((σ : ℂ) * I)).const_add (s : ℂ)
      have hEi : HasDerivAt (fun e : ℝ => Ei_complex (valleyPoint σ s e))
          (Complex.exp (valleyPoint σ s ε) / valleyPoint σ s ε * ((σ : ℂ) * I)) ε :=
        (hasDerivAt_Ei_complex (valleyPoint_mem_slitPlane hσ hε_pos)).comp ε hlin
      have hsub := hlin.fun_sub (hEi.const_mul (t : ℂ))
      refine hsub.cexp.congr_deriv ?_
      dsimp only [F, F']
      ring
    have ⟨hF'_int, hK_d⟩ :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds ε₀ hr)
        hF_meas hF_int hF'_meas hbound_ae (integrable_exp_neg_abs.const_mul C) hdiff_ae
    have hzero : ∫ s : ℝ, F' ε₀ s = 0 := by
      have hs_deriv : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ((σ : ℂ) * I) * F ε₀ x) (F' ε₀ s) s := by
        intro s
        have hlin : HasDerivAt (fun x : ℝ => valleyPoint σ x ε₀) 1 s := by
          dsimp only [valleyPoint]
          simpa using (hasDerivAt_id s).ofReal_comp.add_const ((σ : ℂ) * I * (ε₀ : ℂ))
        have hEi : HasDerivAt (fun x : ℝ => Ei_complex (valleyPoint σ x ε₀))
            (Complex.exp (valleyPoint σ s ε₀) / valleyPoint σ s ε₀ * 1) s := by
          simpa [Function.comp_def] using
            (hasDerivAt_Ei_complex (valleyPoint_mem_slitPlane hσ hε₀.1)).comp s hlin
        have hsub := hlin.fun_sub (hEi.const_mul (t : ℂ))
        refine (hsub.cexp.const_mul ((σ : ℂ) * I)).congr_deriv ?_
        dsimp only [F, F']
        ring
      exact integral_eq_zero_of_hasDerivAt_of_integrable hs_deriv hF'_int (hF_int.const_mul _)
    rwa [hzero] at hK_d
  have hK_eq : K ε₁ = K ε₂ :=
    (convex_Ioo (0 : ℝ) (1 / 2)).is_const_of_fderivWithin_eq_zero
      (fun ε hε => (hK_deriv ε hε).differentiableAt.differentiableWithinAt)
      (fun ε hε => by
        rw [(hK_deriv ε hε).hasFDerivAt.hasFDerivWithinAt.fderivWithin
          ((isOpen_Ioo.uniqueDiffOn) ε hε)]
        ext; simp) h1 h2
  dsimp only [J_valley]
  change Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) * K ε₁ =
    Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) * K ε₂
  rw [hK_eq]

/-- **Exact Contour Collapse as `ε → 0⁺`**:
For every `u > 0` (`0 < t = exp (-u) < 1`) and `σ ∈ {-1, 1}`,
`J_valley σ (Real.exp (-u)) ε → R_integral (Real.exp (-u)) + exp (σ π i e^{-u}) T_integral (Real.exp (-u))`. -/
theorem tendsto_J_valley_zero {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun ε : ℝ => J_valley σ (Real.exp (-u)) ε) (𝓝[>] (0 : ℝ))
      (𝓝 (PakNthPrimeEngine.R_integral (Real.exp (-u)) +
        Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (Real.exp (-u) : ℂ)) *
          T_integral (Real.exp (-u)))) := by
  let t : ℝ := Real.exp (-u)
  have ht0 : 0 < t := Real.exp_pos (-u)
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsplit_J : ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2),
      J_valley σ (t : ℂ) ε =
        (t : ℂ) * (∫ x in Set.Ioi (0 : ℝ),
          Complex.exp (-(x : ℂ) + (σ : ℂ) * I * (ε : ℂ) +
            (t : ℂ) * E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ)))) +
        Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) *
          (∫ x in Set.Ioi (0 : ℝ),
            Complex.exp (valleyPoint σ x ε - (t : ℂ) * Ei_complex (valleyPoint σ x ε))) := by
    intro ε hε
    let f : ℝ → ℂ := fun s =>
      Complex.exp (valleyPoint σ s ε - (t : ℂ) * Ei_complex (valleyPoint σ s ε))
    obtain ⟨C, _, hCb⟩ := valley_integrand_dom hσ (c₀ := t) (M := t) (ε₀ := ε) (ε₁ := ε)
      ht0 hε.1 hε.2.le
    have hf_int : Integrable f volume := by
      have hc : Continuous f :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.add continuous_const).sub
            (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε.1)))
      exact (integrable_exp_neg_abs.const_mul C).mono' hc.aestronglyMeasurable
        (Eventually.of_forall fun s =>
          (hCb (t : ℂ) ε s (by simp) (by simp [abs_of_pos ht0]) le_rfl le_rfl
            (by simp; nlinarith [hε.2])).1)
    have hsplit : (∫ s : ℝ, f s) = (∫ s in Set.Iic (0 : ℝ), f s) + (∫ s in Set.Ioi (0 : ℝ), f s) := by
      rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          hf_int.integrableOn hf_int.integrableOn]
    dsimp only [J_valley]
    rw [hsplit, mul_add]
    congr 1
    rw [setIntegral_Iic_zero_eq_Ioi_zero_neg f, mul_comm (Complex.exp _) (t : ℂ), mul_assoc,
      ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp only [f]
    rw [Ei_complex_valleyPoint_branch (s := -x) hσ hε.1, ← Complex.exp_add]
    congr 1
    have harg : -valleyPoint σ (-x) ε = (x : ℂ) - (σ : ℂ) * I * (ε : ℂ) := by
      dsimp only [valleyPoint]; push_cast; ring
    rw [harg]
    dsimp only [valleyPoint]
    push_cast
    ring
  have hleft : Tendsto
      (fun ε : ℝ => (t : ℂ) * ∫ x in Set.Ioi (0 : ℝ),
        Complex.exp (-(x : ℂ) + (σ : ℂ) * I * (ε : ℂ) +
          (t : ℂ) * E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (PakNthPrimeEngine.R_integral (t : ℂ))) := by
    rw [PakNthPrimeEngine.R_integral]
    refine Tendsto.const_mul (t : ℂ) ?_
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => Real.exp (-x + t * PakNthPrimeEngine.E1 x)) ?_ ?_
      (integrableOn_exp_neg_add_mul_E1 ht1) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have heq : Set.EqOn
          (fun x : ℝ => Complex.exp (-(x : ℂ) + (σ : ℂ) * I * (ε : ℂ) +
            (t : ℂ) * E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ))))
          (fun x : ℝ => Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) *
            Complex.exp (valleyPoint σ (-x) ε - (t : ℂ) * Ei_complex (valleyPoint σ (-x) ε)))
          (Set.Ioi (0 : ℝ)) := by
        intro x _
        dsimp only
        rw [Ei_complex_valleyPoint_branch (s := -x) hσ hε, ← Complex.exp_add]
        congr 1
        have harg : -valleyPoint σ (-x) ε = (x : ℂ) - (σ : ℂ) * I * (ε : ℂ) := by
          dsimp only [valleyPoint]; push_cast; ring
        rw [harg]
        dsimp only [valleyPoint]; push_cast; ring
      have hc : Continuous (fun x : ℝ =>
          Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) *
            Complex.exp (valleyPoint σ (-x) ε - (t : ℂ) * Ei_complex (valleyPoint σ (-x) ε))) :=
        continuous_const.mul (Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.comp continuous_neg).add continuous_const).sub
            (continuous_const.mul ((continuous_Ei_complex_valleyPoint hσ hε).comp continuous_neg))))
      exact (hc.continuousOn.congr heq).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with ε _
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Complex.norm_exp]
      have hre : (-(x : ℂ) + (σ : ℂ) * I * (ε : ℂ) +
          (t : ℂ) * E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ))).re =
          -x + t * (E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ))).re := by
        simp [Complex.mul_re]
      rw [hre]
      have hre_E1 : (E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ))).re ≤ PakNthPrimeEngine.E1 x := by
        have hpos : 0 < ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ)).re := by simpa using hx
        have h1 := norm_E1_complex_le_E1 hpos
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_self, sub_zero] at h1
        exact (Complex.re_le_norm _).trans h1
      exact Real.exp_le_exp.mpr (by nlinarith)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hE1_lim : Tendsto (fun ε : ℝ => E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (PakNthPrimeEngine.E1 x : ℂ)) := by
        have hc_lin : Continuous (fun ε : ℝ => -(σ * ε)) := (continuous_const.mul continuous_id).neg
        have hlin : Tendsto (fun ε : ℝ => -(σ * ε)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
          simpa using hc_lin.tendsto (0 : ℝ)
        have h1 := ((tendsto_E1_complex_ofReal_add_I_mul hx).comp hlin).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        refine h1.congr fun ε => ?_
        simp only [Function.comp_apply]
        congr 1; push_cast; ring
      have harg_lim : Tendsto (fun ε : ℝ => -(x : ℂ) + (σ : ℂ) * I * (ε : ℂ) +
            (t : ℂ) * E1_complex ((x : ℂ) - (σ : ℂ) * I * (ε : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (-(x : ℂ) + (t : ℂ) * (PakNthPrimeEngine.E1 x : ℂ))) := by
        have h1 : Tendsto (fun ε : ℝ => -(x : ℂ) + (σ : ℂ) * I * (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (-(x : ℂ))) := by
          have hc : Continuous (fun ε : ℝ => -(x : ℂ) + (σ : ℂ) * I * (ε : ℂ)) :=
            continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
          simpa using (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        exact h1.add (hE1_lim.const_mul (t : ℂ))
      exact Complex.continuous_exp.continuousAt.tendsto.comp harg_lim
  have hright : Tendsto
      (fun ε : ℝ => Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * (t : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ),
          Complex.exp (valleyPoint σ x ε - (t : ℂ) * Ei_complex (valleyPoint σ x ε)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * (t : ℂ)) * T_integral (t : ℂ))) := by
    dsimp only [T_integral]
    rw [← mul_assoc]
    refine Tendsto.const_mul _ ?_
    let C1 : ℝ := Real.exp (1 - t * (gammaE1 - Real.exp 2))
    let C2 : ℝ := Real.exp (-t * (gammaE1 - 2) + 24 / t)
    let bound : ℝ → ℝ := fun x => if x ≤ 1 then C1 * x ^ (-t) else C2 * Real.exp (-x)
    have hbound_int : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
      constructor
      · have hrpow : IntegrableOn (fun x : ℝ => C1 * x ^ (-t)) (Set.Ioc 0 1) :=
          (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.const_mul C1
        exact hrpow.congr_fun (fun x hx => by simp [bound, hx.2]) measurableSet_Ioc
      · have hexp : IntegrableOn (fun x : ℝ => C2 * Real.exp (-x)) (Set.Ioi 1) :=
          ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 1).congr_fun
            (fun x _ => by simp) measurableSet_Ioi).const_mul C2
        exact hexp.congr_fun (fun x hx => by simp [bound, not_le.mpr (Set.mem_Ioi.mp hx)]) measurableSet_Ioi
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hc : Continuous (fun x : ℝ =>
          Complex.exp (valleyPoint σ x ε - (t : ℂ) * Ei_complex (valleyPoint σ x ε))) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.add continuous_const).sub
            (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ hε)))
      exact hc.aestronglyMeasurable
    · have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
      filter_upwards [hIoo] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Complex.norm_exp, Complex.sub_re, valleyPoint_re]
      have hre_t : ((t : ℂ) * Ei_complex (valleyPoint σ x ε)).re =
          t * (Ei_complex (valleyPoint σ x ε)).re := by simp
      rw [hre_t]
      dsimp only [bound]
      split_ifs with hx1
      · have hge := re_Ei_complex_valleyPoint_ge_small hσ hx hx1 hε.1.le hε.2.le
        have harg : x - t * (Ei_complex (valleyPoint σ x ε)).re ≤
            (1 - t * (gammaE1 - Real.exp 2)) + (-t) * Real.log x := by nlinarith
        calc Real.exp (x - t * (Ei_complex (valleyPoint σ x ε)).re)
            ≤ Real.exp ((1 - t * (gammaE1 - Real.exp 2)) + (-t) * Real.log x) :=
              Real.exp_le_exp.mpr harg
          _ = C1 * Real.exp ((-t) * Real.log x) := Real.exp_add _ _
          _ = C1 * x ^ (-t) := by rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
      · push Not at hx1
        have hge := re_mul_Ei_complex_valleyPoint_ge_large (t := (t : ℂ)) hσ hx1.le hε.1.le
          (by simpa using ht0) (by simp; nlinarith [hε.2])
        rw [hre_t] at hge
        simp only [Complex.ofReal_re] at hge
        have htail := tail_exp_div_dominates (a := t / 4) (by positivity) hx1.le
        have h24 : 6 / (t / 4) = 24 / t := by field_simp [ht0.ne']; ring
        rw [h24] at htail
        have harg : x - t * (Ei_complex (valleyPoint σ x ε)).re ≤
            (-t * (gammaE1 - 2) + 24 / t) + (-x) := by nlinarith
        calc Real.exp (x - t * (Ei_complex (valleyPoint σ x ε)).re)
            ≤ Real.exp ((-t * (gammaE1 - 2) + 24 / t) + (-x)) := Real.exp_le_exp.mpr harg
          _ = C2 * Real.exp (-x) := Real.exp_add _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hslit : (x : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hx)
      have hEi_cont : ContinuousAt Ei_complex (x : ℂ) :=
        (hasDerivAt_Ei_complex hslit).continuousAt
      have hlin : Tendsto (fun ε : ℝ => valleyPoint σ x ε) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
        have hc : Continuous (fun ε : ℝ => valleyPoint σ x ε) :=
          continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
        simpa [valleyPoint] using (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have hEi_lim : Tendsto (fun ε : ℝ => Ei_complex (valleyPoint σ x ε))
          (𝓝[>] (0 : ℝ)) (𝓝 (Ei_real x : ℂ)) := by
        rw [← Ei_complex_ofReal_pos hx]
        exact hEi_cont.tendsto.comp hlin
      exact Complex.continuous_exp.continuousAt.tendsto.comp (hlin.sub (hEi_lim.const_mul (t : ℂ)))
  have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  exact (hleft.add hright).congr' (Filter.mem_of_superset hIoo fun ε hε => (hsplit_J ε hε).symm)

/-- **Exact Contour-Collapse Identity for `I_+(u)`** (all `u > 0`):
`I_plus u = R_integral (exp (-u)) + exp (-π i exp (-u)) * T_integral (exp (-u))`. -/
theorem I_plus_eq_R_add_T {u : ℝ} (hu : 0 < u) :
    I_plus u = PakNthPrimeEngine.R_integral (Real.exp (-u)) +
      Complex.exp (-Real.pi * I * (Real.exp (-u) : ℂ)) * T_integral (Real.exp (-u)) := by
  have hconst : Tendsto (fun ε : ℝ => J_valley (-1) (Real.exp (-u)) ε) (𝓝[>] (0 : ℝ))
      (𝓝 (I_plus u)) := by
    have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset hIoo fun ε hε => ?_)
    have h1 := J_valley_const_in_eps (σ := -1) (Or.inl rfl) u (show (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) by norm_num) hε
    have h2 := I_contour_eq_J_valley (σ := -1) (Or.inl rfl) u (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    exact h2.trans h1
  have hlim := tendsto_J_valley_zero (σ := -1) (Or.inl rfl) hu
  have heq := tendsto_nhds_unique hconst hlim
  simpa using heq

/-- **Exact Contour-Collapse Identity for `I_-(u)`** (all `u > 0`):
`I_minus u = R_integral (exp (-u)) + exp (+π i exp (-u)) * T_integral (exp (-u))`. -/
theorem I_minus_eq_R_add_T {u : ℝ} (hu : 0 < u) :
    I_minus u = PakNthPrimeEngine.R_integral (Real.exp (-u)) +
      Complex.exp (Real.pi * I * (Real.exp (-u) : ℂ)) * T_integral (Real.exp (-u)) := by
  have hconst : Tendsto (fun ε : ℝ => J_valley 1 (Real.exp (-u)) ε) (𝓝[>] (0 : ℝ))
      (𝓝 (I_minus u)) := by
    have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset hIoo fun ε hε => ?_)
    have h1 := J_valley_const_in_eps (σ := 1) (Or.inr rfl) u (show (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) by norm_num) hε
    have h2 := I_contour_eq_J_valley (σ := 1) (Or.inr rfl) u (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    exact h2.trans h1
  have hlim := tendsto_J_valley_zero (σ := 1) (Or.inr rfl) hu
  have heq := tendsto_nhds_unique hconst hlim
  simpa using heq

/-- **UNCONDITIONAL EXACT STOKES RELATION** for the literal contour integrals `I_±(u)`:
For every `u > 0`,
`I_minus u = exp (2πi e^{-u}) * I_plus u - (exp (2πi e^{-u}) - 1) * R_integral (e^{-u})`. -/
theorem I_minus_stokes_relation {u : ℝ} (hu : 0 < u) :
    I_minus u =
      Complex.exp (2 * (Real.pi : ℂ) * I * (Real.exp (-u) : ℂ)) * I_plus u -
        (Complex.exp (2 * (Real.pi : ℂ) * I * (Real.exp (-u) : ℂ)) - 1) *
          PakNthPrimeEngine.R_integral (Real.exp (-u)) := by
  rw [I_plus_eq_R_add_T hu, I_minus_eq_R_add_T hu]
  set t : ℂ := (Real.exp (-u) : ℂ)
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * t) * Complex.exp (-Real.pi * I * t) =
      Complex.exp (Real.pi * I * t) := by
    rw [← Complex.exp_add]
    congr 1; ring
  calc PakNthPrimeEngine.R_integral t + Complex.exp ((Real.pi : ℂ) * I * t) * T_integral t
      = PakNthPrimeEngine.R_integral t +
          (Complex.exp (2 * (Real.pi : ℂ) * I * t) * Complex.exp (-Real.pi * I * t)) * T_integral t := by
        rw [hexp]
    _ = Complex.exp (2 * (Real.pi : ℂ) * I * t) *
          (PakNthPrimeEngine.R_integral t + Complex.exp (-Real.pi * I * t) * T_integral t) -
        (Complex.exp (2 * (Real.pi : ℂ) * I * t) - 1) * PakNthPrimeEngine.R_integral t := by ring

/-- **Exact Stokes Series Form** matching `PakNthPrimeEngine.pak_nth_prime_engine_eq_zero`:
For every `u > 0`,
`I_minus u = Y I_plus (2πi) u + ∑' m : ℕ, etaCoeff (m + 2) * exp (-(m + 2) * u)`. -/
theorem I_minus_stokes_series {u : ℝ} (hu : 0 < u) :
    I_minus u = PakNthPrimeEngine.Y I_plus (2 * Real.pi * I) u +
      ∑' m : ℕ, etaCoeff (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))) := by
  have ht_norm : ‖((Real.exp (-u) : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have heta := eta_integral_eq_tsum ht_norm
  have hstokes := I_minus_stokes_relation hu
  have hY : PakNthPrimeEngine.Y I_plus (2 * Real.pi * I) u =
      Complex.exp (2 * (Real.pi : ℂ) * I * (Real.exp (-u) : ℂ)) * I_plus u := by
    dsimp only [PakNthPrimeEngine.Y, PakNthPrimeEngine.expTau]
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have hsum : (∑' m : ℕ, etaCoeff (m + 2) * ((Real.exp (-u) : ℝ) : ℂ) ^ (m + 2)) =
      ∑' m : ℕ, etaCoeff (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))) := by
    congr 1; ext m
    rw [Complex.ofReal_exp, Complex.ofReal_neg, ← Complex.exp_nat_mul]
    congr 2; ring
  rw [hY, ← hsum, ← heta]
  dsimp only [eta_integral]
  rw [hstokes]
  ring

/-- Complex holomorphicity of `t ↦ J_valley σ t (1 / 4)` on the open sector `{0 < Re t, |Im t| < Re t}`. -/
theorem differentiableOn_J_valley_quarter {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) :
    DifferentiableOn ℂ (fun t : ℂ => J_valley σ t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := by
  intro t₀ ht₀
  have ht₀_re : 0 < t₀.re := ht₀.1
  have ht₀_sec : |t₀.im| < t₀.re := ht₀.2
  let r : ℝ := min (t₀.re / 4) ((t₀.re - |t₀.im|) / 4)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hc₀_pos : 0 < t₀.re / 2 := half_pos ht₀_re
  let M : ℝ := ‖t₀‖ + r
  obtain ⟨C, _, hCb⟩ := valley_integrand_dom hσ (c₀ := t₀.re / 2) (M := M)
    (ε₀ := 1 / 4) (ε₁ := 1 / 4) hc₀_pos (by norm_num) (by norm_num)
  have hball_props : ∀ t ∈ Metric.ball t₀ r,
      t₀.re / 2 ≤ t.re ∧ ‖t‖ ≤ M ∧ (1 / 4 : ℝ) * |t.im| ≤ (1 - 1 / 4) * t.re - t.re / 4 := by
    intro t ht
    have hdist : ‖t - t₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    have hre_diff : |t.re - t₀.re| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (t - t₀)) hdist
    have him_diff : |t.im - t₀.im| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_im] using Complex.abs_im_le_norm (t - t₀)) hdist
    have hr1 : r ≤ t₀.re / 4 := min_le_left _ _
    have hr2 : r ≤ (t₀.re - |t₀.im|) / 4 := min_le_right _ _
    have htre : t₀.re / 2 ≤ t.re := by linarith [(abs_lt.mp hre_diff).1]
    have htnorm : ‖t‖ ≤ M := by
      have htri : ‖t‖ ≤ ‖t - t₀‖ + ‖t₀‖ := by simpa using norm_add_le (t - t₀) t₀
      dsimp [M]; linarith
    have him_le : |t.im| ≤ t.re := by
      have htri : |t.im| - |t₀.im| ≤ |t.im - t₀.im| := abs_sub_abs_le_abs_sub t.im t₀.im
      linarith [(abs_lt.mp hre_diff).1]
    exact ⟨htre, htnorm, by linarith⟩
  let F : ℂ → ℝ → ℂ := fun t s =>
    Complex.exp (valleyPoint σ s (1 / 4) - t * Ei_complex (valleyPoint σ s (1 / 4)))
  let F' : ℂ → ℝ → ℂ := fun t s =>
    -(Ei_complex (valleyPoint σ s (1 / 4)) * F t s)
  have hF_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume := by
    refine Eventually.of_forall fun t => ?_
    have hc : Continuous (F t) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.add continuous_const).sub
          (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ (by norm_num))))
    exact hc.aestronglyMeasurable
  have hF_int : Integrable (F t₀) volume := by
    have hc : Continuous (F t₀) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.add continuous_const).sub
          (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ (by norm_num))))
    have hp := hball_props t₀ (Metric.mem_ball_self hr)
    exact (integrable_exp_neg_abs.const_mul C).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun s => (hCb t₀ (1 / 4) s hp.1 hp.2.1 le_rfl le_rfl hp.2.2).1)
  have hF'_meas : AEStronglyMeasurable (F' t₀) volume := by
    have hc_f : Continuous (F t₀) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.add continuous_const).sub
          (continuous_const.mul (continuous_Ei_complex_valleyPoint hσ (by norm_num))))
    have hc : Continuous (F' t₀) :=
      ((continuous_Ei_complex_valleyPoint hσ (by norm_num)).mul hc_f).neg
    exact hc.aestronglyMeasurable
  have hbound_ae : ∀ᵐ (s : ℝ) ∂volume, ∀ t ∈ Metric.ball t₀ r, ‖F' t s‖ ≤ C * Real.exp (-|s|) := by
    filter_upwards with s t ht
    have hp := hball_props t ht
    dsimp only [F']
    rw [norm_neg]
    exact (hCb t (1 / 4) s hp.1 hp.2.1 le_rfl le_rfl hp.2.2).2.2
  have hdiff_ae : ∀ᵐ (s : ℝ) ∂volume, ∀ t ∈ Metric.ball t₀ r, HasDerivAt (F · s) (F' t s) t := by
    filter_upwards with s t _
    have hmul : HasDerivAt (fun z : ℂ => z * Ei_complex (valleyPoint σ s (1 / 4)))
        (Ei_complex (valleyPoint σ s (1 / 4))) t := by
      simpa using (hasDerivAt_id t).mul_const (Ei_complex (valleyPoint σ s (1 / 4)))
    have hsub := hmul.const_sub (valleyPoint σ s (1 / 4))
    convert hsub.cexp using 1
    dsimp only [F, F']
    ring
  have hK_diff : DifferentiableAt ℂ (fun t : ℂ => ∫ s : ℝ, F t s) t₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hr)
      hF_meas hF_int hF'_meas hbound_ae (integrable_exp_neg_abs.const_mul C) hdiff_ae).2.differentiableAt
  have hpre : DifferentiableAt ℂ (fun t : ℂ => Complex.exp ((σ : ℂ) * (Real.pi : ℂ) * I * t) * t) t₀ :=
    (Complex.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id) t₀).mul
      (differentiableAt_id)
  exact (hpre.mul hK_diff).differentiableWithinAt

lemma isOpen_sector_re_gt_abs_im : IsOpen {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) Complex.continuous_re)

/-- **Global `C^∞` Smoothness of `I_plus`** on all of `ℝ` (automatically via complex holomorphicity!). -/
theorem contDiff_I_plus : ContDiff ℝ ⊤ I_plus := by
  have heq : I_plus = fun u : ℝ => J_valley (-1) (Real.exp (-u) : ℂ) (1 / 4) :=
    funext fun u => I_contour_eq_J_valley (σ := -1) (Or.inl rfl) u (by norm_num) (by norm_num)
  rw [heq]
  have han : AnalyticOnNhd ℂ (fun t : ℂ => J_valley (-1) t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    (differentiableOn_J_valley_quarter (Or.inl rfl)).analyticOnNhd isOpen_sector_re_gt_abs_im
  have hcd_C : ContDiffOn ℂ ⊤ (fun t : ℂ => J_valley (-1) t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    han.contDiffOn isOpen_sector_re_gt_abs_im.uniqueDiffOn
  have hcd_R : ContDiffOn ℝ ⊤ (fun t : ℂ => J_valley (-1) t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := hcd_C.restrict_scalars ℝ
  have hexp : ContDiff ℝ ⊤ (fun u : ℝ => (Real.exp (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_id.neg)
  refine contDiff_iff_contDiffAt.mpr fun u => ?_
  have hmem : ((Real.exp (-u) : ℝ) : ℂ) ∈ {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨Real.exp_pos _, Real.exp_pos _⟩
  exact (hcd_R.contDiffAt (isOpen_sector_re_gt_abs_im.mem_nhds hmem)).comp u hexp.contDiffAt

/-- **Global `C^∞` Smoothness of `I_minus`** on all of `ℝ`. -/
theorem contDiff_I_minus : ContDiff ℝ ⊤ I_minus := by
  have heq : I_minus = fun u : ℝ => J_valley 1 (Real.exp (-u) : ℂ) (1 / 4) :=
    funext fun u => I_contour_eq_J_valley (σ := 1) (Or.inr rfl) u (by norm_num) (by norm_num)
  rw [heq]
  have han : AnalyticOnNhd ℂ (fun t : ℂ => J_valley 1 t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    (differentiableOn_J_valley_quarter (Or.inr rfl)).analyticOnNhd isOpen_sector_re_gt_abs_im
  have hcd_C : ContDiffOn ℂ ⊤ (fun t : ℂ => J_valley 1 t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    han.contDiffOn isOpen_sector_re_gt_abs_im.uniqueDiffOn
  have hcd_R : ContDiffOn ℝ ⊤ (fun t : ℂ => J_valley 1 t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := hcd_C.restrict_scalars ℝ
  have hexp : ContDiff ℝ ⊤ (fun u : ℝ => (Real.exp (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_id.neg)
  refine contDiff_iff_contDiffAt.mpr fun u => ?_
  have hmem : ((Real.exp (-u) : ℝ) : ℂ) ∈ {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨Real.exp_pos _, Real.exp_pos _⟩
  exact (hcd_R.contDiffAt (isOpen_sector_re_gt_abs_im.mem_nhds hmem)).comp u hexp.contDiffAt

/-! ### 6. Direct Wiring into `PakNthPrimeEngine` and `NthPrime.series` -/

/-- **Master Pillar-1 + Engine Theorem (`pak_nth_prime_stokes_engine_eq_zero`)**:
All Pillar 1 hypotheses (`ContDiff ℝ ⊤ I_plus`, exact Stokes identity for `I_plus` / `I_minus`,
explicit `etaCoeff`, geometric bound `‖etaCoeff m‖ ≤ C * 2^m`, and unconditional infinite support
`{m ≥ 2 | etaCoeff m ≠ 0}.Infinite`) are completely discharged!
Only the polynomial jet bound on `I_plus` and the Log-Borel Bridge for `I_plus, I_minus` remain. -/
theorem pak_nth_prime_stokes_engine_eq_zero {r : ℕ}
    {CH : ℝ} {A : ℕ} (hCH : 0 < CH)
    (hHbound : ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv (j : ℕ) I_plus u‖ ≤ CH * u ^ A)
    (hbridge : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0))
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) P = 0 ∧
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) P = 0) :
    P = 0 := by
  obtain ⟨Cc, hCc, hc⟩ := etaCoeff_geom_bound
  exact PakNthPrimeEngine.pak_nth_prime_engine_eq_zero
    contDiff_I_plus hCc (by norm_num : (0 : ℝ) < 2) hc etaCoeff_infinite_support
    (u_stokes := 1) (fun u hu => I_minus_stokes_series (lt_of_lt_of_le zero_lt_one hu))
    hCH hHbound hbridge P hP

/-- The smooth normalized prime generating function along the real nome ray:
`h_prime(u) = e^{-2u} ∑_{n=1}^∞ p_n exp(-n e^{-u})`. -/
@[expose] def nthPrimeSmoothRay (u : ℝ) : ℂ :=
  PrimeNome.tRay u ^ 2 * PrimeNome.value NthPrime.series (PrimeNome.qRay u)

lemma nthPrimeSmoothRay_analytic (u : ℝ) : AnalyticAt ℝ nthPrimeSmoothRay u :=
  ((PrimeNome.tRay_analytic u).pow 2).mul
    (PrimeNome.ray_source_analytic NthPrime.series_diskCoeffBound 1 u)

/-- **Unconditional Autonomous ODE Transfer for `∑ p_n q^n`** to `nthPrimeSmoothRay`:
If `∑_{n=1}^∞ p_n q^n` satisfies any nontrivial algebraic differential equation over `ℂ(q)`,
then `h_prime(u) = e^{-2u} P_prime(e^{-e^{-u}})` satisfies a nonzero autonomous polynomial ODE
eventually as `u → +∞`. -/
theorem nthPrime_smooth_autonomous_transfer
    (hdep : ¬ AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series)) :
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) nthPrimeSmoothRay u) P = 0 := by
  have htrans := PrimeNome.autonomous_transfer_readout NthPrime.series_diskCoeffBound
    nthPrimeSmoothRay_analytic (by
      unfold PrimeNome.NomeReadout
      intro ι inst v x gt gs _ _
      exact (gt.pow 2).mul gs) hdep
  obtain ⟨J, Q, hQne, hQev⟩ := htrans
  cases J with
  | zero =>
    have hC : Q = MvPolynomial.C (Q.coeff 0) := by
      ext m
      have hm0 : m = 0 := Finsupp.ext fun i => Fin.elim0 i
      subst hm0
      simp
    refine ⟨0, MvPolynomial.C (Q.coeff 0), ?_, ?_⟩
    · intro h0
      apply hQne
      rw [hC]
      have hc0 : Q.coeff 0 = 0 := by simpa using congr_arg (MvPolynomial.eval 0) h0
      simp [hc0]
    · refine hQev.mono fun u hu => ?_
      rw [hC, MvPolynomial.eval_C] at hu
      simpa using hu
  | succ r =>
    exact ⟨r, Q, hQne, hQev⟩

/-- **Complete End-to-End Conditional Closure of Pak's Conjecture 2.5a (`∑ p_n q^n`)**:
Wiring `NthPrime.series` → `nthPrime_smooth_autonomous_transfer` → `I_±(u)` exact Stokes relation
→ `R_holomorphic_on_halfplane` + `etaCoeff_infinite_support` → `PakNthPrimeEngine.pak_nth_prime_engine_eq_zero`.
The ONLY remaining external hypotheses for zero-hypothesis Lean 4 closure of Pak 2.5a are:
1. Polynomial jet bounds on `I_plus` (`hI_bound`),
2. All-orders asymptotic transfer from `nthPrimeSmoothRay` to `I_plus` (`hasymp`), and
3. The Pillar 2 Log-Borel Bridge (`hbridge`). -/
theorem pak_2_5a_of_stokes_bridge
    (hI_bound : ∀ r : ℕ, ∃ CH > 0, ∃ A : ℕ,
      ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv (j : ℕ) I_plus u‖ ≤ CH * u ^ A)
    (hasymp : ∀ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) nthPrimeSmoothRay u) P = 0) →
      ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) P‖ ≤ C / u ^ N)
    (hbridge : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0)) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series) := by
  by_contra hdep
  obtain ⟨r, P, hPne, hPev⟩ := nthPrime_smooth_autonomous_transfer hdep
  obtain ⟨CH, hCH, A, hHbound⟩ := hI_bound r
  have hP_vanish := hbridge r P (hasymp r P hPev)
  exact hPne (pak_nth_prime_stokes_engine_eq_zero hCH hHbound (hbridge r) P hP_vanish)

/-! ### 7. Unconditional Positive-Measure Representation & Sharp Lower Bound `|c_m| ≥ 2π^{m-1}/(m-2)!`

Formalizes the complete discrete positive-measure representation of `R_integral` from
`positive-spectrum.md` and wires Codex's `PrimePencil.massApproximant_factored_affine_bound`
together with Mathlib's Euler sine product to prove unconditionally that for EVERY `m ≥ 2`:
`2 * Real.pi ^ (m - 1) / ((m - 2).factorial : ℝ) ≤ ‖etaCoeff m‖` (and in particular `etaCoeff m ≠ 0`). -/

/-- Prefix table of the positive Taylor coefficients `(a_n, b_n)` of `X(y)` and `exp(X(y))`
solving `y X'(y) = X(y) exp(X(y))`, `X(0) = 0`, `X'(0) = 1`, defined by plain structural recursion. -/
@[expose] def abPrefix : ℕ → (ℕ → ℝ × ℝ)
  | 0 => fun _ => (0, 1)
  | 1 => fun k => if k = 1 then (1, 1) else (0, 1)
  | n + 2 =>
    let prev := abPrefix (n + 1)
    let a_val : ℝ := (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.Ico 1 (n + 2), (prev (n + 2 - j)).1 * (prev j).2
    let b_val : ℝ := a_val + (1 / ((n + 2 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.Ico 1 (n + 2), (j : ℝ) * (prev j).1 * (prev (n + 2 - j)).2
    fun k => if k = n + 2 then (a_val, b_val) else prev k

/-- Exact Maclaurin coefficients `a_n = [y^n] X(y)` of the inverse `X = Φ⁻¹`. -/
@[expose] def xInvCoeff (n : ℕ) : ℝ := (abPrefix n n).1

/-- Exact Maclaurin coefficients `b_n = [y^n] exp(X(y))`. -/
@[expose] def expXInvCoeff (n : ℕ) : ℝ := (abPrefix n n).2

lemma abPrefix_eq_of_le {M k : ℕ} (hk : k ≤ M) : abPrefix M k = abPrefix k k := by
  induction M with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ M ih =>
    by_cases hkeq : k = M + 1
    · subst hkeq; rfl
    · have hkM : k ≤ M := by omega
      cases M with
      | zero =>
        have : k = 0 := by omega
        subst this; simp [abPrefix]
      | succ m =>
        have hne : k ≠ m + 2 := by omega
        change (if k = m + 2 then _ else abPrefix (m + 1) k) = abPrefix k k
        simp only [hne, ↓reduceIte]
        exact ih hkM

@[simp] lemma xInvCoeff_zero : xInvCoeff 0 = 0 := rfl
@[simp] lemma xInvCoeff_one : xInvCoeff 1 = 1 := by simp [xInvCoeff, abPrefix]
@[simp] lemma expXInvCoeff_zero : expXInvCoeff 0 = 1 := rfl
@[simp] lemma expXInvCoeff_one : expXInvCoeff 1 = 1 := by simp [expXInvCoeff, abPrefix]

lemma xInvCoeff_succ_succ (n : ℕ) :
    xInvCoeff (n + 2) = (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.Ico 1 (n + 2), xInvCoeff (n + 2 - j) * expXInvCoeff j := by
  dsimp only [xInvCoeff, expXInvCoeff]
  conv_lhs => rw [abPrefix]
  simp only [↓reduceIte]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hj2 : j < n + 2 := (Finset.mem_Ico.mp hj).2
  rw [abPrefix_eq_of_le (by omega : n + 2 - j ≤ n + 1), abPrefix_eq_of_le (by omega : j ≤ n + 1)]

lemma expXInvCoeff_succ_succ (n : ℕ) :
    expXInvCoeff (n + 2) = xInvCoeff (n + 2) + (1 / ((n + 2 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.Ico 1 (n + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (n + 2 - j) := by
  have ha := xInvCoeff_succ_succ n
  dsimp only [xInvCoeff, expXInvCoeff] at ha ⊢
  conv_lhs => rw [abPrefix]
  simp only [↓reduceIte]
  congr 1
  · rw [ha]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : j < n + 2 := (Finset.mem_Ico.mp hj).2
    rw [abPrefix_eq_of_le (by omega : n + 2 - j ≤ n + 1), abPrefix_eq_of_le (by omega : j ≤ n + 1)]
  · congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : j < n + 2 := (Finset.mem_Ico.mp hj).2
    rw [abPrefix_eq_of_le (by omega : j ≤ n + 1), abPrefix_eq_of_le (by omega : n + 2 - j ≤ n + 1)]

/-- Exact ODE recurrence for `a_n`: `n a_n = ∑_{j=0}^n a_{n-j} b_j` for all `n : ℕ`. -/
lemma nat_mul_xInvCoeff_eq_sum (n : ℕ) :
    (n : ℝ) * xInvCoeff n = ∑ j ∈ Finset.range (n + 1), xInvCoeff (n - j) * expXInvCoeff j := by
  cases n with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp [Finset.sum_range_succ]
    | succ k =>
      have ha := xInvCoeff_succ_succ k
      have hk1 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hmul : (((k + 1 : ℕ) : ℝ)) * xInvCoeff (k + 2) =
          ∑ j ∈ Finset.Ico 1 (k + 2), xInvCoeff (k + 2 - j) * expXInvCoeff j := by
        rw [ha, one_div, ← mul_assoc, mul_inv_cancel₀ hk1, one_mul]
      rw [Finset.sum_range_succ, Nat.sub_self, xInvCoeff_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ', Nat.sub_zero, expXInvCoeff_zero, mul_one]
      have hshift : (∑ x ∈ Finset.range (k + 1), xInvCoeff (k + 2 - (x + 1)) * expXInvCoeff (x + 1)) =
          ∑ j ∈ Finset.Ico 1 (k + 2), xInvCoeff (k + 2 - j) * expXInvCoeff j := by
        refine Finset.sum_bij (fun x _ => x + 1) ?_ ?_ ?_ ?_
        · intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_Ico]; omega
        · intro x₁ _ x₂ _ h; omega
        · intro j hj; simp only [Finset.mem_Ico] at hj
          exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro x _; rfl
      rw [hshift, ← hmul]
      push_cast; ring

/-- Exact exponential recurrence for `b_n`: `n b_n = ∑_{j=0}^n j a_j b_{n-j}` for all `n : ℕ`. -/
lemma nat_mul_expXInvCoeff_eq_sum (n : ℕ) :
    (n : ℝ) * expXInvCoeff n =
      ∑ j ∈ Finset.range (n + 1), (j : ℝ) * xInvCoeff j * expXInvCoeff (n - j) := by
  cases n with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp [Finset.sum_range_succ]
    | succ k =>
      have hb := expXInvCoeff_succ_succ k
      have hk2 : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hmul : (((k + 2 : ℕ) : ℝ)) * expXInvCoeff (k + 2) =
          (((k + 2 : ℕ) : ℝ)) * xInvCoeff (k + 2) +
            ∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) := by
        rw [hb, mul_add, one_div, ← mul_assoc, mul_inv_cancel₀ hk2, one_mul]
      rw [Finset.sum_range_succ, Nat.sub_self, expXInvCoeff_zero, mul_one]
      rw [Finset.sum_range_succ', Nat.cast_zero, zero_mul, zero_mul, add_zero]
      have hshift : (∑ x ∈ Finset.range (k + 1),
            (((x + 1 : ℕ) : ℝ)) * xInvCoeff (x + 1) * expXInvCoeff (k + 2 - (x + 1))) =
          ∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) := by
        refine Finset.sum_bij (fun x _ => x + 1) ?_ ?_ ?_ ?_
        · intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_Ico]; omega
        · intro x₁ _ x₂ _ h; omega
        · intro j hj; simp only [Finset.mem_Ico] at hj
          exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro x _; rfl
      rw [hshift, add_comm (∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j))]
      exact hmul

/-- Strict positivity of every coefficient `a_n` (`n ≥ 1`) and `b_n` (`n ≥ 0`). -/
theorem xInvCoeff_pos_and_expXInvCoeff_pos :
    ∀ n : ℕ, (1 ≤ n → 0 < xInvCoeff n) ∧ 0 < expXInvCoeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact ⟨fun h => by omega, by simp⟩
    | succ m =>
      cases m with
      | zero => exact ⟨fun _ => by simp, by simp⟩
      | succ k =>
        have ha : 0 < xInvCoeff (k + 2) := by
          rw [xInvCoeff_succ_succ]
          refine mul_pos (by positivity) ?_
          refine Finset.sum_pos (fun j hj => ?_) ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
          have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
          have hj2 : j < k + 2 := (Finset.mem_Ico.mp hj).2
          exact mul_pos ((ih (k + 2 - j) (by omega)).1 (by omega)) (ih j (by omega)).2
        have hb : 0 < expXInvCoeff (k + 2) := by
          rw [expXInvCoeff_succ_succ]
          have hnn : 0 ≤ ∑ j ∈ Finset.Ico 1 (k + 2),
              (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) := by
            refine Finset.sum_nonneg fun j hj => ?_
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            have hj2 : j < k + 2 := (Finset.mem_Ico.mp hj).2
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg j)
              ((ih j (by omega)).1 hj1).le) (ih (k + 2 - j) (by omega)).2.le
          have hterm : 0 ≤ (1 / ((k + 2 : ℕ) : ℝ)) *
              ∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) :=
            mul_nonneg (by positivity) hnn
          linarith
        exact ⟨fun _ => ha, hb⟩

theorem xInvCoeff_pos {n : ℕ} (hn : 1 ≤ n) : 0 < xInvCoeff n :=
  (xInvCoeff_pos_and_expXInvCoeff_pos n).1 hn

lemma xInvCoeff_nonneg (n : ℕ) : 0 ≤ xInvCoeff n := by
  cases n with
  | zero => simp
  | succ k => exact (xInvCoeff_pos (Nat.succ_pos k)).le

lemma expXInvCoeff_pos (n : ℕ) : 0 < expXInvCoeff n :=
  (xInvCoeff_pos_and_expXInvCoeff_pos n).2

/-- Elementary telescoping bound: `∑_{k=1}^N 1/k^2 ≤ 2 - 1/N` (hence `≤ 2`). -/
lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.Ico 1 (m + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => simp; norm_num
      | succ m =>
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 2)]
        have ih' := ih (by omega)
        have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
        have hm2 : (0 : ℝ) < (m + 2 : ℕ) := by positivity
        have hstep : (1 : ℝ) / (((m + 2 : ℕ) : ℝ)) ^ 2 ≤
            1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ) := by
          have hsub : 1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ) =
              1 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) := by
            field_simp [hm1.ne', hm2.ne']
            push_cast; ring
          rw [hsub]
          refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
          push_cast; nlinarith
        linarith
  cases N with
  | zero => simp
  | succ m =>
    have h := hstrong (m + 1) (by omega)
    have hpos : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
    linarith

lemma conv_inv_sq_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) ≤ 16 / (n : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hterm : ∀ j ∈ Finset.Ico 1 n,
      (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) ≤
      (4 / (n : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / (((n - j : ℕ) : ℝ)) ^ 2) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : j < n := (Finset.mem_Ico.mp hj).2
    have hj_pos : (0 : ℝ) < j := by positivity
    have hnj_pos : (0 : ℝ) < (n - j : ℕ) := by
      have : 1 ≤ n - j := by omega
      positivity
    have hsum_eq : (j : ℝ) + ((n - j : ℕ) : ℝ) = (n : ℝ) := by
      have : j + (n - j) = n := by omega
      exact_mod_cast this
    by_cases hmid : (n : ℝ) ≤ 2 * (j : ℝ)
    · have hj2_ge : (n : ℝ) ^ 2 / 4 ≤ (j : ℝ) ^ 2 := by nlinarith
      have h1 : (1 : ℝ) / (j : ℝ) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hj_pos 2) (pow_pos hn_pos 2)]; nlinarith
      have h2 : (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) ≤
          (4 / (n : ℝ) ^ 2) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) := by
        rw [show (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) =
            (1 / (j : ℝ) ^ 2) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hpos_extra : 0 ≤ (4 / (n : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by positivity
      linarith
    · have hmid' : (n : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by linarith
      have h1 : (1 : ℝ) / (((n - j : ℕ) : ℝ)) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hnj_pos 2) (pow_pos hn_pos 2)]; nlinarith
      have h2 : (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) ≤
          (4 / (n : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by
        rw [show (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) =
            (1 / (((n - j : ℕ) : ℝ)) ^ 2) * (1 / (j : ℝ) ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hpos_extra : 0 ≤ (4 / (n : ℝ) ^ 2) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) := by positivity
      linarith
  calc ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((((n - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 n, (4 / (n : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / (((n - j : ℕ) : ℝ)) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (4 / (n : ℝ) ^ 2) * ((∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (j : ℝ) ^ 2) +
          ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (((n - j : ℕ) : ℝ)) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (4 / (n : ℝ) ^ 2) * (2 + 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · have hsub : Finset.Ico 1 n ⊆ Finset.Ico 1 (n + 1) := Finset.Ico_subset_Ico_right (by omega)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
            (sum_inv_sq_le_two n)
        · have hbij : (∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (((n - j : ℕ) : ℝ)) ^ 2) =
              ∑ k ∈ Finset.Ico 1 n, (1 : ℝ) / (k : ℝ) ^ 2 := by
            refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
            · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
            · intro k hk; simp only [Finset.mem_Ico] at hk
              exact ⟨n - k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro j _; rfl
          rw [hbij]
          have hsub : Finset.Ico 1 n ⊆ Finset.Ico 1 (n + 1) := Finset.Ico_subset_Ico_right (by omega)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
            (sum_inv_sq_le_two n)
    _ = 16 / (n : ℝ) ^ 2 := by ring

lemma conv_inv_mul_sq_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2) ≤ 8 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hterm : ∀ j ∈ Finset.Ico 1 n,
      (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2) ≤
      (2 / (n : ℝ)) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) + 4 / (n : ℝ) ^ 2 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : j < n := (Finset.mem_Ico.mp hj).2
    have hj_pos : (0 : ℝ) < j := by positivity
    have hnj_pos : (0 : ℝ) < (n - j : ℕ) := by
      have : 1 ≤ n - j := by omega
      positivity
    have hsum_eq : (j : ℝ) + ((n - j : ℕ) : ℝ) = (n : ℝ) := by
      have : j + (n - j) = n := by omega
      exact_mod_cast this
    by_cases hmid : (n : ℝ) ≤ 2 * (j : ℝ)
    · have h1 : (1 : ℝ) / (j : ℝ) ≤ 2 / (n : ℝ) := by
        rw [div_le_div_iff₀ hj_pos hn_pos]; linarith
      have h2 : (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2) ≤
          (2 / (n : ℝ)) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) := by
        rw [show (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2) =
            (1 / (j : ℝ)) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hpos_extra : 0 ≤ 4 / (n : ℝ) ^ 2 := by positivity
      linarith
    · have hmid' : (n : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by linarith
      have hj_ge1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have h1 : (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2) ≤ 4 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hj_pos (pow_pos hnj_pos 2)) (pow_pos hn_pos 2)]
        have hsq : (n : ℝ) ^ 2 ≤ 4 * (((n - j : ℕ) : ℝ)) ^ 2 := by nlinarith
        nlinarith [pow_pos hnj_pos 2]
      have hpos_extra : 0 ≤ (2 / (n : ℝ)) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) := by positivity
      linarith
  calc ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((j : ℝ) * (((n - j : ℕ) : ℝ)) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 n, ((2 / (n : ℝ)) * (1 / (((n - j : ℕ) : ℝ)) ^ 2) + 4 / (n : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (2 / (n : ℝ)) * (∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (((n - j : ℕ) : ℝ)) ^ 2) +
          ((n - 1 : ℕ) : ℝ) * (4 / (n : ℝ) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (2 / (n : ℝ)) * 2 + (n : ℝ) * (4 / (n : ℝ) ^ 2) := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hbij : (∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (((n - j : ℕ) : ℝ)) ^ 2) =
              ∑ k ∈ Finset.Ico 1 n, (1 : ℝ) / (k : ℝ) ^ 2 := by
            refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
            · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
            · intro k hk; simp only [Finset.mem_Ico] at hk
              exact ⟨n - k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro j _; rfl
          rw [hbij]
          have hsub : Finset.Ico 1 n ⊆ Finset.Ico 1 (n + 1) := Finset.Ico_subset_Ico_right (by omega)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
            (sum_inv_sq_le_two n)
        · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Nat.sub_le n 1
    _ = 8 / (n : ℝ) := by field_simp [hn_pos.ne']; ring

/-- Elementary convergence bound (radius `≥ 1/64`) for both `xInvCoeff` and `expXInvCoeff`. -/
theorem xInvCoeff_expXInvCoeff_bound :
    ∀ n : ℕ, 1 ≤ n →
      xInvCoeff n ≤ (1 / 64 : ℝ) * (64 : ℝ) ^ n / (n : ℝ) ^ 2 ∧
      expXInvCoeff n ≤ (1 / 32 : ℝ) * (64 : ℝ) ^ n / (n : ℝ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        change xInvCoeff 1 ≤ _ ∧ expXInvCoeff 1 ≤ _
        simp only [xInvCoeff_one, expXInvCoeff_one]
        norm_num
      | succ k =>
        have hk2_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
        have ha : xInvCoeff (k + 2) ≤ (1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by
          rw [xInvCoeff_succ_succ]
          have hsum_le :
              ∑ j ∈ Finset.Ico 1 (k + 2), xInvCoeff (k + 2 - j) * expXInvCoeff j ≤
              ((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) *
                ∑ j ∈ Finset.Ico 1 (k + 2), (1 : ℝ) / ((((k + 2 - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun j hj => ?_
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            have hj2 : j < k + 2 := (Finset.mem_Ico.mp hj).2
            have ha_j := (ih (k + 2 - j) (by omega) (by omega)).1
            have hb_j := (ih j (by omega) hj1).2
            have hpow : (64 : ℝ) ^ (k + 2 - j) * (64 : ℝ) ^ j = (64 : ℝ) ^ (k + 2) := by
              rw [← pow_add, Nat.sub_add_cancel hj2.le]
            calc xInvCoeff (k + 2 - j) * expXInvCoeff j
                ≤ ((1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2 - j) / (((k + 2 - j : ℕ) : ℝ)) ^ 2) *
                    ((1 / 32 : ℝ) * (64 : ℝ) ^ j / (j : ℝ) ^ 2) :=
                  mul_le_mul ha_j hb_j (expXInvCoeff_pos j).le (by positivity)
              _ = ((1 / 64 : ℝ) * (1 / 32 : ℝ) * ((64 : ℝ) ^ (k + 2 - j) * (64 : ℝ) ^ j)) *
                    (1 / ((((k + 2 - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2)) := by ring
              _ = ((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) *
                    (1 / ((((k + 2 - j : ℕ) : ℝ)) ^ 2 * (j : ℝ) ^ 2)) := by rw [hpow]
          have hconv := conv_inv_sq_le (n := k + 2) (by omega)
          have h1div : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ k + 1 by omega)
          calc (1 / ((k + 1 : ℕ) : ℝ)) *
                ∑ j ∈ Finset.Ico 1 (k + 2), xInvCoeff (k + 2 - j) * expXInvCoeff j
              ≤ 1 * (((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) * (16 / (((k + 2 : ℕ) : ℝ)) ^ 2)) := by
                refine mul_le_mul h1div (hsum_le.trans (mul_le_mul_of_nonneg_left hconv (by positivity)))
                  (Finset.sum_nonneg fun j hj => mul_nonneg (xInvCoeff_nonneg _) (expXInvCoeff_pos _).le)
                  zero_le_one
            _ = (1 / 2 : ℝ) * ((1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2) := by ring
            _ ≤ (1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by
                have : 0 ≤ (1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by positivity
                linarith
        have hb : expXInvCoeff (k + 2) ≤ (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by
          rw [expXInvCoeff_succ_succ]
          have hsum_le :
              ∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) ≤
              ((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) *
                ∑ j ∈ Finset.Ico 1 (k + 2), (1 : ℝ) / ((j : ℝ) * (((k + 2 - j : ℕ) : ℝ)) ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun j hj => ?_
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            have hj2 : j < k + 2 := (Finset.mem_Ico.mp hj).2
            have hj_pos : (0 : ℝ) < j := by positivity
            have ha_j := (ih j (by omega) hj1).1
            have hb_j := (ih (k + 2 - j) (by omega) (by omega)).2
            have hpow : (64 : ℝ) ^ j * (64 : ℝ) ^ (k + 2 - j) = (64 : ℝ) ^ (k + 2) := by
              rw [← pow_add, Nat.add_sub_of_le hj2.le]
            calc (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j)
                ≤ (j : ℝ) * ((1 / 64 : ℝ) * (64 : ℝ) ^ j / (j : ℝ) ^ 2) *
                    ((1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2 - j) / (((k + 2 - j : ℕ) : ℝ)) ^ 2) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left ha_j hj_pos.le) hb_j
                    (expXInvCoeff_pos _).le (by positivity)
              _ = ((1 / 64 : ℝ) * (1 / 32 : ℝ) * ((64 : ℝ) ^ j * (64 : ℝ) ^ (k + 2 - j))) *
                    (1 / ((j : ℝ) * (((k + 2 - j : ℕ) : ℝ)) ^ 2)) := by
                  field_simp [hj_pos.ne']
              _ = ((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) *
                    (1 / ((j : ℝ) * (((k + 2 - j : ℕ) : ℝ)) ^ 2)) := by rw [hpow]
          have hconv := conv_inv_mul_sq_le (n := k + 2) (by omega)
          have hterm2 : (1 / ((k + 2 : ℕ) : ℝ)) *
              ∑ j ∈ Finset.Ico 1 (k + 2), (j : ℝ) * xInvCoeff j * expXInvCoeff (k + 2 - j) ≤
              (1 / 256 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by
            calc _ ≤ (1 / ((k + 2 : ℕ) : ℝ)) *
                  (((1 / 64 : ℝ) * (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2)) * (8 / ((k + 2 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left
                  (hsum_le.trans (mul_le_mul_of_nonneg_left hconv (by positivity))) (by positivity)
              _ = (1 / 256 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by ring
          have hnn : 0 ≤ (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by positivity
          have hcomb : (1 / 64 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 +
              (1 / 256 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 ≤
              (1 / 32 : ℝ) * (64 : ℝ) ^ (k + 2) / (((k + 2 : ℕ) : ℝ)) ^ 2 := by
            rw [mul_div_assoc, mul_div_assoc, mul_div_assoc]
            linarith
          linarith
        exact ⟨ha, hb⟩

/-- Radius constant `ρ = exp (-γ)` of `y = Φ(x) = ρ * exp (-E1(x))`. -/
@[expose] def rhoE1 : ℝ := Real.exp (-gammaE1)

lemma rhoE1_pos : 0 < rhoE1 := Real.exp_pos _

/-- Entire map `Φ(z) = z * exp (-Ein(z))`. -/
@[expose] def Phi_complex (z : ℂ) : ℂ := z * Complex.exp (-Ein_complex z)

/-- Real restriction `Φ(x) = x * exp (-Ein(x)) = ρ * exp (-E1(x))` on `x > 0`. -/
@[expose] def Phi_real (x : ℝ) : ℝ := x * Real.exp (-Ein_real x)

lemma Phi_complex_ofReal (x : ℝ) : Phi_complex (x : ℂ) = (Phi_real x : ℂ) := by
  dsimp only [Phi_complex, Phi_real]
  rw [Ein_complex_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

lemma Phi_real_eq_rho_mul_exp_neg_E1 {x : ℝ} (hx : 0 < x) :
    Phi_real x = rhoE1 * Real.exp (-PakNthPrimeEngine.E1 x) := by
  dsimp only [Phi_real, rhoE1]
  have hrel := E1_add_log_sub_Ein_real hx
  have h1 : Real.log x - Ein_real x = -gammaE1 - PakNthPrimeEngine.E1 x := by linarith
  calc x * Real.exp (-Ein_real x)
      = Real.exp (Real.log x) * Real.exp (-Ein_real x) := by rw [Real.exp_log hx]
    _ = Real.exp (Real.log x - Ein_real x) := by rw [sub_eq_add_neg, Real.exp_add]
    _ = Real.exp (-gammaE1 + -PakNthPrimeEngine.E1 x) := by rw [h1, sub_eq_add_neg]
    _ = Real.exp (-gammaE1) * Real.exp (-PakNthPrimeEngine.E1 x) := Real.exp_add _ _

lemma hasDerivAt_Phi_complex (z : ℂ) :
    HasDerivAt Phi_complex (Complex.exp (-Ein_complex z - z)) z := by
  by_cases hz : z = 0
  · subst hz
    have h0 : Ein_complex 0 = 0 := by simp [Ein_complex]
    have hE := (hasDerivAt_Ein_complex_sum 0).neg.cexp
    have hmul := (hasDerivAt_id (0 : ℂ)).mul hE
    refine hmul.congr_deriv ?_
    simp [h0]
  · have hE := (hasDerivAt_Ein_complex hz).neg.cexp
    have hmul := (hasDerivAt_id z).mul hE
    refine hmul.congr_deriv ?_
    have h1 : Complex.exp (-Ein_complex z) * (1 - (1 - Complex.exp (-z))) =
        Complex.exp (-Ein_complex z - z) := by
      rw [sub_sub_cancel, ← Complex.exp_add, sub_eq_add_neg]
    simp only [Pi.neg_apply, id_eq]
    rw [one_mul, ← h1]
    field_simp [hz]
    ring

lemma hasDerivAt_Phi_real (x : ℝ) :
    HasDerivAt Phi_real (Real.exp (-Ein_real x - x)) x := by
  have hc := (hasDerivAt_Phi_complex (x : ℂ)).comp x (hasDerivAt_id x).ofReal_comp
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hc
  have hfun : (⇑Complex.reCLM ∘ Phi_complex ∘ Complex.ofReal) = Phi_real :=
    funext fun t => by simp [Phi_complex_ofReal]
  rw [hfun] at hre
  refine hre.congr_deriv ?_
  rw [Ein_complex_ofReal]
  simp only [Complex.reCLM_apply, ← Complex.ofReal_neg, ← Complex.ofReal_sub,
    ← Complex.ofReal_exp, Complex.ofReal_one, mul_one, Complex.ofReal_re]

lemma strictMono_Phi_real : StrictMono Phi_real :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_Phi_real x).deriv]
    exact Real.exp_pos _

lemma tendsto_E1_atTop : Tendsto PakNthPrimeEngine.E1 atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x : ℝ => Real.exp (-x)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rw [Real.norm_of_nonneg (E1_pos hx_pos).le]
    exact (E1_le_exp_div hx_pos).trans (div_le_self (Real.exp_pos _).le hx)
  · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

lemma tendsto_E1_zero_right : Tendsto PakNthPrimeEngine.E1 (𝓝[>] (0 : ℝ)) atTop := by
  have hrel : ∀ᶠ x in 𝓝[>] (0 : ℝ), PakNthPrimeEngine.E1 x = -gammaE1 + Ein_real x - Real.log x := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    linarith [E1_add_log_sub_Ein_real hx]
  refine Filter.Tendsto.congr' (hrel.mono fun x hx => hx.symm) ?_
  have hEin_cont : Continuous Ein_real := by
    have h : Ein_real = fun x : ℝ => (Ein_complex (x : ℂ)).re := by
      ext x; simp [Ein_complex_ofReal]
    rw [h]
    exact Complex.continuous_re.comp (continuous_Ein_complex.comp Complex.continuous_ofReal)
  have h1 : Tendsto (fun x : ℝ => -gammaE1 + Ein_real x) (𝓝[>] (0 : ℝ)) (𝓝 (-gammaE1 + Ein_real 0)) :=
    (tendsto_const_nhds.add (hEin_cont.tendsto 0)).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  simpa [sub_eq_add_neg] using h1.add_atTop h2

lemma Phi_real_image_Ioi : Phi_real '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) rhoE1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Phi_real_eq_rho_mul_exp_neg_E1 hx]
    refine ⟨mul_pos rhoE1_pos (Real.exp_pos _), ?_⟩
    have hlt : Real.exp (-PakNthPrimeEngine.E1 x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith [E1_pos hx])
    nlinarith [rhoE1_pos]
  · intro ⟨hy0, hyr⟩
    have hcont : Continuous Phi_real :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_Phi_real x).continuousAt
    have hlim0 : Tendsto Phi_real (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto Phi_real (𝓝[>] (0 : ℝ)) (𝓝 (Phi_real 0)) :=
        (hasDerivAt_Phi_real 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rwa [show Phi_real 0 = 0 by simp [Phi_real]] at h1
    have hlimTop : Tendsto Phi_real atTop (𝓝 rhoE1) := by
      have hneg : Tendsto (fun x : ℝ => -PakNthPrimeEngine.E1 x) atTop (𝓝 0) := by
        simpa using tendsto_E1_atTop.neg
      have h1 : Tendsto (fun x : ℝ => rhoE1 * Real.exp (-PakNthPrimeEngine.E1 x)) atTop (𝓝 rhoE1) := by
        simpa using ((Real.continuous_exp.tendsto 0).comp hneg).const_mul rhoE1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (Phi_real_eq_rho_mul_exp_neg_E1 hx).symm
    obtain ⟨a, ha0, hay⟩ : ∃ a > 0, Phi_real a < y := by
      have hev := (hlim0.eventually (gt_mem_nhds hy0)).and self_mem_nhdsWithin
      obtain ⟨a, ha_lt, ha_pos⟩ := hev.exists
      exact ⟨a, ha_pos, ha_lt⟩
    obtain ⟨b, hb0, hby⟩ : ∃ b > a, y < Phi_real b := by
      have hev := (hlimTop.eventually (lt_mem_nhds hyr)).and (eventually_gt_atTop a)
      obtain ⟨b, hb_gt, hba⟩ := hev.exists
      exact ⟨b, hba, hb_gt⟩
    have hivt := intermediate_value_Icc (le_of_lt hb0)
      (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_Phi_real x).continuousAt).continuousOn
    obtain ⟨x, hxIcc, hxy⟩ := hivt ⟨hay.le, hby.le⟩
    exact ⟨x, lt_of_lt_of_le ha0 hxIcc.1, hxy⟩

lemma E1_image_Ioi : PakNthPrimeEngine.E1 '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact E1_pos hx
  · intro hv
    have hy_mem : rhoE1 * Real.exp (-v) ∈ Set.Ioo (0 : ℝ) rhoE1 := by
      refine ⟨mul_pos rhoE1_pos (Real.exp_pos _), ?_⟩
      have hlt : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hv])
      nlinarith [rhoE1_pos]
    rw [← Phi_real_image_Ioi] at hy_mem
    obtain ⟨x, hx, hxy⟩ := hy_mem
    rw [Phi_real_eq_rho_mul_exp_neg_E1 hx] at hxy
    have hexp : Real.exp (-PakNthPrimeEngine.E1 x) = Real.exp (-v) :=
      mul_left_cancel₀ rhoE1_pos.ne' hxy
    have hE1 : PakNthPrimeEngine.E1 x = v := neg_inj.mp (Real.exp_injective hexp)
    exact ⟨x, hx, hE1⟩

/-- Inverse function `xInv : ℝ → ℝ` of `Phi_real` on `(0, rhoE1)`. -/
@[expose] def xInv (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Ioo (0 : ℝ) rhoE1 then
    Classical.choose ((Phi_real_image_Ioi ▸ hy) : y ∈ Phi_real '' Set.Ioi (0 : ℝ))
  else 0

lemma xInv_pos {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) rhoE1) : 0 < xInv y := by
  dsimp only [xInv]
  simp only [hy, ↓reduceDIte]
  exact (Classical.choose_spec ((Phi_real_image_Ioi ▸ hy) : y ∈ Phi_real '' Set.Ioi (0 : ℝ))).1

lemma Phi_real_xInv {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) rhoE1) : Phi_real (xInv y) = y := by
  dsimp only [xInv]
  simp only [hy, ↓reduceDIte]
  exact (Classical.choose_spec ((Phi_real_image_Ioi ▸ hy) : y ∈ Phi_real '' Set.Ioi (0 : ℝ))).2

lemma xInv_Phi_real {x : ℝ} (hx : 0 < x) : xInv (Phi_real x) = x := by
  have hmem : Phi_real x ∈ Set.Ioo (0 : ℝ) rhoE1 := by
    rw [← Phi_real_image_Ioi]; exact ⟨x, hx, rfl⟩
  exact strictMono_Phi_real.injective (Phi_real_xInv hmem)

lemma strictMonoOn_xInv : StrictMonoOn xInv (Set.Ioo (0 : ℝ) rhoE1) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  by_contra hle
  push Not at hle
  have h := strictMono_Phi_real.monotone hle
  rw [Phi_real_xInv hy₁, Phi_real_xInv hy₂] at h
  linarith

lemma continuousOn_xInv : ContinuousOn xInv (Set.Ioo (0 : ℝ) rhoE1) := by
  intro y₀ hy₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let x₀ := xInv y₀
  have hx₀ : 0 < x₀ := xInv_pos hy₀
  let ε' := min (ε / 2) (x₀ / 2)
  have hε' : 0 < ε' := lt_min (half_pos hε) (half_pos hx₀)
  have hx_lo : 0 < x₀ - ε' := by
    have : ε' ≤ x₀ / 2 := min_le_right _ _; linarith
  have hPhi_lo : Phi_real (x₀ - ε') < y₀ := by
    rw [← Phi_real_xInv hy₀]; exact strictMono_Phi_real (by linarith)
  have hPhi_hi : y₀ < Phi_real (x₀ + ε') := by
    rw [← Phi_real_xInv hy₀]; exact strictMono_Phi_real (by linarith)
  let δ := min (y₀ - Phi_real (x₀ - ε')) (Phi_real (x₀ + ε') - y₀)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  refine ⟨δ, hδ, fun y hy hdist => ?_⟩
  have h1 : Phi_real (x₀ - ε') < y := by
    have : δ ≤ y₀ - Phi_real (x₀ - ε') := min_le_left _ _
    have hd : |y - y₀| < δ := by simpa [Real.dist_eq] using hdist
    linarith [(abs_lt.mp hd).1]
  have h2 : y < Phi_real (x₀ + ε') := by
    have : δ ≤ Phi_real (x₀ + ε') - y₀ := min_le_right _ _
    have hd : |y - y₀| < δ := by simpa [Real.dist_eq] using hdist
    linarith [(abs_lt.mp hd).2]
  have hx1 : x₀ - ε' < xInv y := by
    rw [← xInv_Phi_real hx_lo]
    have hmem : Phi_real (x₀ - ε') ∈ Set.Ioo (0 : ℝ) rhoE1 := by
      rw [← Phi_real_image_Ioi]; exact ⟨x₀ - ε', hx_lo, rfl⟩
    exact strictMonoOn_xInv hmem hy h1
  have hx2 : xInv y < x₀ + ε' := by
    rw [← xInv_Phi_real (by linarith : 0 < x₀ + ε')]
    have hmem : Phi_real (x₀ + ε') ∈ Set.Ioo (0 : ℝ) rhoE1 := by
      rw [← Phi_real_image_Ioi]; exact ⟨x₀ + ε', Set.mem_Ioi.mpr (by linarith), rfl⟩
    exact strictMonoOn_xInv hy hmem h2
  have hε'_lt : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Local power-series solutions `X_ser(y) = ∑ a_n y^n` and `B_ser(y) = ∑ b_n y^n`. -/
@[expose] def X_ser (y : ℝ) : ℝ := ∑' n : ℕ, xInvCoeff n * y ^ n
@[expose] def B_ser (y : ℝ) : ℝ := ∑' n : ℕ, expXInvCoeff n * y ^ n

lemma summable_xInv_deriv {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 64) :
    Summable (fun n : ℕ => (n : ℝ) * xInvCoeff n * r ^ n) ∧
    Summable (fun n : ℕ => xInvCoeff n * r ^ n) ∧
    Summable (fun n : ℕ => (n : ℝ) * expXInvCoeff n * r ^ n) ∧
    Summable (fun n : ℕ => expXInvCoeff n * r ^ n) := by
  have hq : 64 * r < 1 := by linarith
  have hgeom : Summable (fun n : ℕ => (64 * r) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hq
  have ha1 : Summable (fun n : ℕ => (n : ℝ) * xInvCoeff n * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by have := xInvCoeff_nonneg n; positivity)
      (fun n => ?_) hgeom
    cases n with
    | zero => simp
    | succ k =>
      have hb := (xInvCoeff_expXInvCoeff_bound (k + 1) (by omega)).1
      have hk_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk_ge1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
      calc ((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * r ^ (k + 1)
          ≤ ((k + 1 : ℕ) : ℝ) * ((1 / 64 : ℝ) * (64 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ)) ^ 2) * r ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hk_pos.le) (pow_nonneg hr0 _)
        _ = ((1 / 64 : ℝ) / ((k + 1 : ℕ) : ℝ)) * (64 * r) ^ (k + 1) := by
            rw [mul_pow]; field_simp [hk_pos.ne']
        _ ≤ 1 * (64 * r) ^ (k + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [div_le_one hk_pos]; linarith
        _ = (64 * r) ^ (k + 1) := one_mul _
  have ha0 : Summable (fun n : ℕ => xInvCoeff n * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by have := xInvCoeff_nonneg n; positivity)
      (fun n => ?_) ha1
    cases n with
    | zero => simp
    | succ k =>
      have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
      calc xInvCoeff (k + 1) * r ^ (k + 1)
          = 1 * (xInvCoeff (k + 1) * r ^ (k + 1)) := (one_mul _).symm
        _ ≤ ((k + 1 : ℕ) : ℝ) * (xInvCoeff (k + 1) * r ^ (k + 1)) :=
            mul_le_mul_of_nonneg_right hk1 (mul_nonneg (xInvCoeff_nonneg _) (pow_nonneg hr0 _))
        _ = ((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * r ^ (k + 1) := by ring
  have hb1 : Summable (fun n : ℕ => (n : ℝ) * expXInvCoeff n * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by have := (expXInvCoeff_pos n).le; positivity)
      (fun n => ?_) hgeom
    cases n with
    | zero => simp
    | succ k =>
      have hb := (xInvCoeff_expXInvCoeff_bound (k + 1) (by omega)).2
      have hk_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk_ge1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
      calc ((k + 1 : ℕ) : ℝ) * expXInvCoeff (k + 1) * r ^ (k + 1)
          ≤ ((k + 1 : ℕ) : ℝ) * ((1 / 32 : ℝ) * (64 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ)) ^ 2) * r ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hk_pos.le) (pow_nonneg hr0 _)
        _ = ((1 / 32 : ℝ) / ((k + 1 : ℕ) : ℝ)) * (64 * r) ^ (k + 1) := by
            rw [mul_pow]; field_simp [hk_pos.ne']
        _ ≤ 1 * (64 * r) ^ (k + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [div_le_one hk_pos]; linarith
        _ = (64 * r) ^ (k + 1) := one_mul _
  have hb0 : Summable (fun n : ℕ => expXInvCoeff n * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by have := (expXInvCoeff_pos n).le; positivity)
      (fun n => ?_) (hgeom.add hb1)
    cases n with
    | zero => simp
    | succ k =>
      have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
      have hnn : 0 ≤ (64 * r) ^ (k + 1) := by positivity
      have hle : expXInvCoeff (k + 1) * r ^ (k + 1) ≤
          ((k + 1 : ℕ) : ℝ) * expXInvCoeff (k + 1) * r ^ (k + 1) := by
        calc expXInvCoeff (k + 1) * r ^ (k + 1)
            = 1 * (expXInvCoeff (k + 1) * r ^ (k + 1)) := (one_mul _).symm
          _ ≤ ((k + 1 : ℕ) : ℝ) * (expXInvCoeff (k + 1) * r ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right hk1 (mul_nonneg (expXInvCoeff_pos _).le (pow_nonneg hr0 _))
          _ = ((k + 1 : ℕ) : ℝ) * expXInvCoeff (k + 1) * r ^ (k + 1) := by ring
      linarith
  exact ⟨ha1, ha0, hb1, hb0⟩

lemma hasDerivAt_X_ser_and_B_ser {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 64) :
    HasDerivAt X_ser (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * xInvCoeff (n + 1) * y ^ n) y ∧
    HasDerivAt B_ser (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * expXInvCoeff (n + 1) * y ^ n) y := by
  let R : ℝ := (y + 1 / 64) / 2
  have hR0 : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 / 64 := by dsimp [R]; linarith
  have hyR : y < R := by dsimp [R]; linarith
  have hsum := summable_xInv_deriv hR0.le hR1
  have huA : Summable (fun n : ℕ => (n : ℝ) * xInvCoeff n * R ^ (n - 1)) := by
    refine (hsum.1.mul_left R⁻¹).congr fun n => ?_
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ, mul_comm _ R]
      have hrew : R⁻¹ * (((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * (R * R ^ k)) =
          (R⁻¹ * R) * (((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * R ^ k) := by ring
      rw [hrew, inv_mul_cancel₀ hR0.ne', one_mul]
  have huB : Summable (fun n : ℕ => (n : ℝ) * expXInvCoeff n * R ^ (n - 1)) := by
    refine (hsum.2.2.1.mul_left R⁻¹).congr fun n => ?_
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ, mul_comm _ R]
      have hrew : R⁻¹ * (((k + 1 : ℕ) : ℝ) * expXInvCoeff (k + 1) * (R * R ^ k)) =
          (R⁻¹ * R) * (((k + 1 : ℕ) : ℝ) * expXInvCoeff (k + 1) * R ^ k) := by ring
      rw [hrew, inv_mul_cancel₀ hR0.ne', one_mul]
  have hX : HasDerivAt X_ser (∑' n : ℕ, (n : ℝ) * xInvCoeff n * y ^ (n - 1)) y := by
    refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-R) R)
      (g := fun n (z : ℝ) => xInvCoeff n * z ^ n)
      (g' := fun n (z : ℝ) => (n : ℝ) * xInvCoeff n * z ^ (n - 1))
      huA isOpen_Ioo isPreconnected_Ioo (fun n z _ => ?_) (fun n z hz => ?_)
      (show (0 : ℝ) ∈ Set.Ioo (-R) R by constructor <;> linarith)
      (by refine summable_of_ne_finset_zero (s := {0}) fun n hn => by simp [zero_pow (by simpa using hn)])
      ⟨by linarith, hyR⟩
    · cases n with
      | zero => simpa using hasDerivAt_const z (xInvCoeff 0)
      | succ k =>
        simpa [mul_assoc, mul_left_comm] using (hasDerivAt_pow (k + 1) z).const_mul (xInvCoeff (k + 1))
    · have hzR : |z| ≤ R := abs_le.mpr ⟨hz.1.le, hz.2.le⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
        abs_of_nonneg (xInvCoeff_nonneg n), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hzR _)
        (mul_nonneg (Nat.cast_nonneg n) (xInvCoeff_nonneg n))
  have hB : HasDerivAt B_ser (∑' n : ℕ, (n : ℝ) * expXInvCoeff n * y ^ (n - 1)) y := by
    refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-R) R)
      (g := fun n (z : ℝ) => expXInvCoeff n * z ^ n)
      (g' := fun n (z : ℝ) => (n : ℝ) * expXInvCoeff n * z ^ (n - 1))
      huB isOpen_Ioo isPreconnected_Ioo (fun n z _ => ?_) (fun n z hz => ?_)
      (show (0 : ℝ) ∈ Set.Ioo (-R) R by constructor <;> linarith)
      (by refine summable_of_ne_finset_zero (s := {0}) fun n hn => by simp [zero_pow (by simpa using hn)])
      ⟨by linarith, hyR⟩
    · cases n with
      | zero => simpa using hasDerivAt_const z (expXInvCoeff 0)
      | succ k =>
        simpa [mul_assoc, mul_left_comm] using (hasDerivAt_pow (k + 1) z).const_mul (expXInvCoeff (k + 1))
    · have hzR : |z| ≤ R := abs_le.mpr ⟨hz.1.le, hz.2.le⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
        abs_of_nonneg (expXInvCoeff_pos n).le, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hzR _)
        (mul_nonneg (Nat.cast_nonneg n) (expXInvCoeff_pos n).le)
  have hshiftA : (∑' n : ℕ, (n : ℝ) * xInvCoeff n * y ^ (n - 1)) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * xInvCoeff (n + 1) * y ^ n := by
    have h1 := (huA.of_nonneg_of_le (fun n => by have := xInvCoeff_nonneg n; positivity)
      (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le hyR.le _)
        (mul_nonneg (Nat.cast_nonneg n) (xInvCoeff_nonneg n)))).tsum_eq_zero_add
    simpa using h1
  have hshiftB : (∑' n : ℕ, (n : ℝ) * expXInvCoeff n * y ^ (n - 1)) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * expXInvCoeff (n + 1) * y ^ n := by
    have h1 := (huB.of_nonneg_of_le (fun n => by have := (expXInvCoeff_pos n).le; positivity)
      (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le hyR.le _)
        (mul_nonneg (Nat.cast_nonneg n) (expXInvCoeff_pos n).le))).tsum_eq_zero_add
    simpa using h1
  rw [hshiftA] at hX
  rw [hshiftB] at hB
  exact ⟨hX, hB⟩

/-- Exact local inverse identity `Phi_real (X_ser y) = y` on `0 < y < 1 / 64`. -/
theorem Phi_real_X_ser_eq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 64) :
    Phi_real (X_ser y) = y := by
  have hODE : ∀ z ∈ Set.Ioo (0 : ℝ) (1 / 64),
      HasDerivAt B_ser (deriv X_ser z * B_ser z) z ∧
      z * deriv X_ser z = X_ser z * B_ser z := by
    intro z hz
    obtain ⟨hXd, hBd⟩ := hasDerivAt_X_ser_and_B_ser hz.1 hz.2
    have hsum := summable_xInv_deriv hz.1.le hz.2
    have hX_norm : Summable (fun n : ℕ => ‖(n : ℝ) * xInvCoeff n * z ^ n‖) :=
      hsum.1.congr fun n => by
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (xInvCoeff_nonneg n)) (pow_nonneg hz.1.le n))]
    have hX0_norm : Summable (fun n : ℕ => ‖xInvCoeff n * z ^ n‖) :=
      hsum.2.1.congr fun n => by
        rw [Real.norm_of_nonneg (mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hz.1.le n))]
    have hB0_norm : Summable (fun n : ℕ => ‖expXInvCoeff n * z ^ n‖) :=
      hsum.2.2.2.congr fun n => by
        rw [Real.norm_of_nonneg (mul_nonneg (expXInvCoeff_pos n).le (pow_nonneg hz.1.le n))]
    have hzX' : z * deriv X_ser z = ∑' n : ℕ, (n : ℝ) * xInvCoeff n * z ^ n := by
      rw [hXd.deriv, ← tsum_mul_left]
      have hsplit := hsum.1.tsum_eq_zero_add
      simp only [Nat.cast_zero, zero_mul, zero_add] at hsplit
      rw [hsplit]
      congr 1; ext k; rw [pow_succ]; ring
    have hzB' : z * deriv B_ser z = ∑' n : ℕ, (n : ℝ) * expXInvCoeff n * z ^ n := by
      rw [hBd.deriv, ← tsum_mul_left]
      have hsplit := hsum.2.2.1.tsum_eq_zero_add
      simp only [Nat.cast_zero, zero_mul, zero_add] at hsplit
      rw [hsplit]
      congr 1; ext k; rw [pow_succ]; ring
    have hprod_B : (z * deriv X_ser z) * B_ser z = z * deriv B_ser z := by
      rw [hzX', hzB', B_ser, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hX_norm hB0_norm]
      congr 1; ext n
      rw [nat_mul_expXInvCoeff_eq_sum n, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hpow : z ^ j * z ^ (n - j) = z ^ n := by rw [← pow_add, Nat.add_sub_of_le hjn]
      calc (j : ℝ) * xInvCoeff j * z ^ j * (expXInvCoeff (n - j) * z ^ (n - j))
          = (j : ℝ) * xInvCoeff j * expXInvCoeff (n - j) * (z ^ j * z ^ (n - j)) := by ring
        _ = (j : ℝ) * xInvCoeff j * expXInvCoeff (n - j) * z ^ n := by rw [hpow]
    have hprod_X : X_ser z * B_ser z = z * deriv X_ser z := by
      rw [hzX', X_ser, B_ser, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hX0_norm hB0_norm]
      congr 1; ext n
      rw [nat_mul_xInvCoeff_eq_sum n, Finset.sum_mul, ← Finset.sum_range_reflect
        (fun j => xInvCoeff (n - j) * expXInvCoeff j * z ^ n) (n + 1)]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : n + 1 - 1 - j = n - j := by omega
      have h2 : n - (n - j) = j := by omega
      have hpow : z ^ j * z ^ (n - j) = z ^ n := by rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [h1, h2]
      calc xInvCoeff j * z ^ j * (expXInvCoeff (n - j) * z ^ (n - j))
          = xInvCoeff j * expXInvCoeff (n - j) * (z ^ j * z ^ (n - j)) := by ring
        _ = xInvCoeff j * expXInvCoeff (n - j) * z ^ n := by rw [hpow]
    have hBd_eq : deriv B_ser z = deriv X_ser z * B_ser z := by
      apply mul_left_cancel₀ hz.1.ne'
      linarith
    exact ⟨hBd_eq ▸ hBd.deriv ▸ hBd, hprod_X.symm⟩
  -- Step 1: B_ser z = exp (X_ser z) on (0, 1/64)
  have hB_eq : ∀ z ∈ Set.Ioo (0 : ℝ) (1 / 64), B_ser z = Real.exp (X_ser z) := by
    let g : ℝ → ℝ := fun z => B_ser z * Real.exp (-X_ser z)
    have hg_deriv : ∀ z ∈ Set.Ioo (0 : ℝ) (1 / 64), HasDerivAt g 0 z := by
      intro z hz
      have hBd := (hODE z hz).1
      have hXd := (hasDerivAt_X_ser_and_B_ser hz.1 hz.2).1
      have hE := hXd.neg.exp
      have hmul := hBd.mul hE
      refine hmul.congr_deriv ?_
      rw [hXd.deriv]; ring
    have hg_const : ∀ z₁ ∈ Set.Ioo (0 : ℝ) (1 / 64), ∀ z₂ ∈ Set.Ioo (0 : ℝ) (1 / 64),
        g z₁ = g z₂ := fun z₁ hz₁ z₂ hz₂ =>
      (convex_Ioo (0 : ℝ) (1 / 64)).is_const_of_fderivWithin_eq_zero
        (fun z hz => (hg_deriv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => by
          rw [(hg_deriv z hz).hasFDerivAt.hasFDerivWithinAt.fderivWithin (isOpen_Ioo.uniqueDiffOn z hz)]
          ext; simp) hz₁ hz₂
    have hX_tend : Tendsto X_ser (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hR : (0 : ℝ) < 1 / 128 := by norm_num
      have hsum := (summable_xInv_deriv hR.le (by norm_num)).2.1
      have hcont : ContinuousOn X_ser (Set.Ioo (-(1 / 128 : ℝ)) (1 / 128)) := by
        refine continuousOn_tsum (u := fun n => xInvCoeff n * (1 / 128 : ℝ) ^ n)
          (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) hsum
          (fun n z hz => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (xInvCoeff_nonneg n), abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg z) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) n) (xInvCoeff_nonneg n)
      have h0 : X_ser 0 = 0 := by
        dsimp only [X_ser]
        rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
        simp
      have hlim : Tendsto X_ser (𝓝[>] (0 : ℝ)) (𝓝 (X_ser 0)) :=
        (hcont.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
      rwa [h0] at hlim
    have hB_tend : Tendsto B_ser (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hR : (0 : ℝ) < 1 / 128 := by norm_num
      have hsum := (summable_xInv_deriv hR.le (by norm_num)).2.2.2
      have hcont : ContinuousOn B_ser (Set.Ioo (-(1 / 128 : ℝ)) (1 / 128)) := by
        refine continuousOn_tsum (u := fun n => expXInvCoeff n * (1 / 128 : ℝ) ^ n)
          (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) hsum
          (fun n z hz => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (expXInvCoeff_pos n).le, abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg z) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) n) (expXInvCoeff_pos n).le
      have h0 : B_ser 0 = 1 := by
        dsimp only [B_ser]
        rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
        simp
      have hlim : Tendsto B_ser (𝓝[>] (0 : ℝ)) (𝓝 (B_ser 0)) :=
        (hcont.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
      rwa [h0] at hlim
    have hg_tend : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hXneg : Tendsto (fun z : ℝ => -X_ser z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hX_tend.neg
      simpa [g, Real.exp_zero] using hB_tend.mul ((Real.continuous_exp.tendsto 0).comp hXneg)
    intro z hz
    have hconst_lim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g z)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 64)] with w hw
      exact hg_const z hz w hw
    have hgz1 : g z = 1 := tendsto_nhds_unique hconst_lim hg_tend
    dsimp only [g] at hgz1
    calc B_ser z = (B_ser z * Real.exp (-X_ser z)) * Real.exp (X_ser z) := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ = Real.exp (X_ser z) := by rw [hgz1, one_mul]
  -- Step 2: Phi_real (X_ser z) / z = 1 on (0, 1/64)
  have hX_pos : ∀ z ∈ Set.Ioo (0 : ℝ) (1 / 64), 0 < X_ser z := by
    intro z hz
    have hsum := (summable_xInv_deriv hz.1.le hz.2).2.1
    have h1 : xInvCoeff 1 * z ^ 1 ≤ X_ser z :=
      le_hasSum hsum.hasSum 1 (fun n _ => mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hz.1.le n))
    simp only [xInvCoeff_one, pow_one, one_mul] at h1
    linarith [hz.1]
  let q : ℝ → ℝ := fun z => Phi_real (X_ser z) / z
  have hq_deriv : ∀ z ∈ Set.Ioo (0 : ℝ) (1 / 64), HasDerivAt q 0 z := by
    intro z hz
    have hXd := (hasDerivAt_X_ser_and_B_ser hz.1 hz.2).1
    have hPhi := (hasDerivAt_Phi_real (X_ser z)).comp z hXd
    have hdiv := hPhi.div (hasDerivAt_id z) hz.1.ne'
    refine hdiv.congr_deriv ?_
    have hode := (hODE z hz).2
    rw [hB_eq z hz] at hode
    have h1 : Real.exp (-Ein_real (X_ser z) - X_ser z) * deriv X_ser z * z - Phi_real (X_ser z) * 1 = 0 := by
      have harg : Real.exp (-Ein_real (X_ser z) - X_ser z) =
          Real.exp (-Ein_real (X_ser z)) * Real.exp (-X_ser z) := by
        rw [sub_eq_add_neg, Real.exp_add]
      calc Real.exp (-Ein_real (X_ser z) - X_ser z) * deriv X_ser z * z - Phi_real (X_ser z) * 1
          = Real.exp (-Ein_real (X_ser z)) * Real.exp (-X_ser z) * (z * deriv X_ser z) -
              X_ser z * Real.exp (-Ein_real (X_ser z)) := by rw [harg, Phi_real]; ring
        _ = Real.exp (-Ein_real (X_ser z)) * Real.exp (-X_ser z) * (X_ser z * Real.exp (X_ser z)) -
              X_ser z * Real.exp (-Ein_real (X_ser z)) := by rw [hode]
        _ = Real.exp (-Ein_real (X_ser z)) * X_ser z * (Real.exp (-X_ser z) * Real.exp (X_ser z)) -
              X_ser z * Real.exp (-Ein_real (X_ser z)) := by ring
        _ = 0 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]; ring
    simp only [Function.comp_apply, id_eq]
    rw [← hXd.deriv, h1, zero_div]
  have hq_const : ∀ z₁ ∈ Set.Ioo (0 : ℝ) (1 / 64), ∀ z₂ ∈ Set.Ioo (0 : ℝ) (1 / 64),
      q z₁ = q z₂ := fun z₁ hz₁ z₂ hz₂ =>
    (convex_Ioo (0 : ℝ) (1 / 64)).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hq_deriv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [(hq_deriv z hz).hasFDerivAt.hasFDerivWithinAt.fderivWithin (isOpen_Ioo.uniqueDiffOn z hz)]
        ext; simp) hz₁ hz₂
  have hX_div_tend : Tendsto (fun z : ℝ => X_ser z / z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hR : (0 : ℝ) < 1 / 128 := by norm_num
    have hsum1 : Summable (fun n : ℕ => xInvCoeff (n + 1) * (1 / 128 : ℝ) ^ n) := by
      have h := (summable_xInv_deriv hR.le (by norm_num)).2.1
      have hshift := h.comp_injective Nat.succ_injective
      refine (hshift.mul_left (1 / 128 : ℝ)⁻¹).congr fun n => ?_
      simp only [Function.comp_apply, pow_succ]
      have hrew : (1 / 128 : ℝ)⁻¹ * (xInvCoeff (n + 1) * ((1 / 128 : ℝ) ^ n * (1 / 128 : ℝ))) =
          ((1 / 128 : ℝ)⁻¹ * (1 / 128 : ℝ)) * (xInvCoeff (n + 1) * (1 / 128 : ℝ) ^ n) := by ring
      rw [hrew, inv_mul_cancel₀ hR.ne', one_mul]
    let S1 : ℝ → ℝ := fun z => ∑' n : ℕ, xInvCoeff (n + 1) * z ^ n
    have hcont : ContinuousOn S1 (Set.Ioo (-(1 / 128 : ℝ)) (1 / 128)) := by
      refine continuousOn_tsum (u := fun n => xInvCoeff (n + 1) * (1 / 128 : ℝ) ^ n)
        (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) hsum1
        (fun n z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (xInvCoeff_nonneg _), abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg z) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) n) (xInvCoeff_nonneg _)
    have hS0 : S1 0 = 1 := by
      dsimp only [S1]
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
      simp
    have hlim : Tendsto S1 (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      rw [← hS0]
      exact (hcont.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 128)] with z hz
    dsimp only [S1, X_ser]
    have hsum := (summable_xInv_deriv hz.1.le (by linarith [hz.2])).2.1
    rw [hsum.tsum_eq_zero_add, xInvCoeff_zero, zero_mul, zero_add, ← tsum_div_const]
    congr 1; ext n
    rw [pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hz.1.ne']
  have hX_tend : Tendsto X_ser (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 := hX_div_tend.mul (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
    have h2 : Tendsto (fun z : ℝ => X_ser z / z * z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using h1
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z)
    exact div_mul_cancel₀ _ hz.ne'
  have hq_tend : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hEin_cont : Continuous Ein_real := by
      have h : Ein_real = fun x : ℝ => (Ein_complex (x : ℂ)).re := by
        ext x; simp [Ein_complex_ofReal]
      rw [h]
      exact Complex.continuous_re.comp (continuous_Ein_complex.comp Complex.continuous_ofReal)
    have hEin0 : Ein_real 0 = 0 := by simp [Ein_real]
    have hExp_tend : Tendsto (fun z : ℝ => Real.exp (-Ein_real (X_ser z))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hneg : Tendsto (fun z : ℝ => -Ein_real (X_ser z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa [hEin0] using ((hEin_cont.tendsto 0).comp hX_tend).neg
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hneg
    have hmul := hX_div_tend.mul hExp_tend
    refine (by simpa using hmul : Tendsto (fun z => X_ser z / z * Real.exp (-Ein_real (X_ser z))) _ _).congr fun z => ?_
    dsimp only [q, Phi_real]; ring
  have hconst_lim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (q y)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 64)] with z hz
    exact hq_const y ⟨hy0, hy1⟩ z hz
  have hqy1 : q y = 1 := tendsto_nhds_unique hconst_lim hq_tend
  dsimp only [q] at hqy1
  exact (div_eq_one_iff_eq hy0.ne').mp hqy1

/-- Termwise `k`-th complex derivative of a power series `∑' n, (a n : ℂ) * z^n` on `Metric.ball 0 r'`. -/
lemma iteratedDeriv_tsum_nonneg_coeff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r' : ℝ} (hr' : 0 < r')
    (hsum : Summable (fun n : ℕ => a n * r' ^ n)) :
    ∀ k : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r',
      iteratedDeriv k (fun w : ℂ => ∑' n : ℕ, (a n : ℂ) * w ^ n) z =
        ∑' n : ℕ, ((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ) * z ^ (n - k) := by
  have hbound_k : ∀ (k : ℕ) {s : ℝ}, 0 < s → s < r' →
      Summable (fun n : ℕ => ((n.descFactorial k : ℕ) : ℝ) * a n * s ^ (n - k)) := by
    intro k s hs0 hsr
    let q : ℝ := s / r'
    have hq0 : 0 < q := div_pos hs0 hr'
    have hq1 : q < 1 := (div_lt_one hr').mpr hsr
    have hq_inv : 1 < q⁻¹ := one_lt_inv₀ hq0 |>.mpr hq1
    have hlog_pos : 0 < Real.log q⁻¹ := Real.log_pos hq_inv
    let C : ℝ := (k.factorial : ℝ) / (Real.log q⁻¹) ^ k * (s⁻¹) ^ k
    refine Summable.of_nonneg_of_le (fun n => by have := ha n; positivity) (fun n => ?_)
      (hsum.mul_left C)
    by_cases hnk : n < k
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnk]; simp; have := ha n; positivity
    · push Not at hnk
      have hdesc_le : ((n.descFactorial k : ℕ) : ℝ) ≤ (n : ℝ) ^ k := by
        exact_mod_cast Nat.descFactorial_le_pow n k
      have hn_pow : (n : ℝ) ^ k * q ^ n ≤ (k.factorial : ℝ) / (Real.log q⁻¹) ^ k := by
        have h1 := Real.pow_div_factorial_le_exp ((n : ℝ) * Real.log q⁻¹) (by positivity) k
        have hfact : (0 : ℝ) < k.factorial := by positivity
        rw [mul_pow, div_le_iff₀ hfact] at h1
        have hexp : Real.exp ((n : ℝ) * Real.log q⁻¹) = (q ^ n)⁻¹ := by
          rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hq0), inv_pow]
        rw [hexp] at h1
        have hqn : 0 < q ^ n := pow_pos hq0 n
        have h2 : (n : ℝ) ^ k * (Real.log q⁻¹) ^ k * q ^ n ≤ (k.factorial : ℝ) := by
          have := mul_le_mul_of_nonneg_right h1 hqn.le
          rw [mul_right_comm (q ^ n)⁻¹, inv_mul_cancel₀ hqn.ne', one_mul] at this
          linarith
        rw [le_div_iff₀ (pow_pos hlog_pos k)]
        linarith
      have hs_pow : s ^ (n - k) = (s⁻¹) ^ k * q ^ n * r' ^ n := by
        have h1 : s ^ (n - k) * s ^ k = s ^ n := by rw [← pow_add, Nat.sub_add_cancel hnk]
        have h2 : q ^ n * r' ^ n = s ^ n := by rw [← mul_pow]; dsimp [q]; rw [div_mul_cancel₀ _ hr'.ne']
        have h3 : (s⁻¹) ^ k * s ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow]
        rw [mul_assoc, h2, ← h1]
        calc s ^ (n - k) = ((s⁻¹) ^ k * s ^ k) * s ^ (n - k) := by rw [h3, one_mul]
          _ = (s⁻¹) ^ k * (s ^ (n - k) * s ^ k) := by ring
      calc ((n.descFactorial k : ℕ) : ℝ) * a n * s ^ (n - k)
          ≤ (n : ℝ) ^ k * a n * ((s⁻¹) ^ k * q ^ n * r' ^ n) := by
            rw [hs_pow]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdesc_le (ha n)) (by positivity)
        _ = ((n : ℝ) ^ k * q ^ n) * (s⁻¹) ^ k * (a n * r' ^ n) := by ring
        _ ≤ ((k.factorial : ℝ) / (Real.log q⁻¹) ^ k) * (s⁻¹) ^ k * (a n * r' ^ n) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn_pow (by positivity))
              (mul_nonneg (ha n) (pow_nonneg hr'.le n))
        _ = C * (a n * r' ^ n) := by dsimp [C]
  intro k
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hznorm : ‖z‖ < r' := by simpa [Metric.mem_ball, dist_zero_right] using hz
    let s : ℝ := (‖z‖ + r') / 2
    have hs0 : 0 < s := by dsimp [s]; linarith [norm_nonneg z]
    have hsr : s < r' := by dsimp [s]; linarith
    have hzs : z ∈ Metric.ball (0 : ℂ) s := by
      rw [Metric.mem_ball, dist_zero_right]; dsimp [s]; linarith
    have hloc : iteratedDeriv k (fun w : ℂ => ∑' n : ℕ, (a n : ℂ) * w ^ n) =ᶠ[𝓝 z]
        fun w : ℂ => ∑' n : ℕ, ((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ) * w ^ (n - k) :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) ih
    rw [iteratedDeriv_succ, hloc.deriv_eq]
    have hu := hbound_k (k + 1) hs0 hsr
    have hconv0 : Summable (fun n : ℕ => ((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ) * (0 : ℂ) ^ (n - k)) := by
      refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) fun n hn => ?_
      have hgt : k < n := by simp only [Finset.mem_range] at hn; omega
      have hne : n - k ≠ 0 := by omega
      simp [zero_pow hne]
    have hd : HasDerivAt
        (fun w : ℂ => ∑' n : ℕ, ((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ) * w ^ (n - k))
        (∑' n : ℕ, ((n.descFactorial (k + 1) : ℕ) : ℂ) * (a n : ℂ) * z ^ (n - (k + 1))) z := by
      refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) s)
        (g := fun n (w : ℂ) => ((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ) * w ^ (n - k))
        (g' := fun n (w : ℂ) => ((n.descFactorial (k + 1) : ℕ) : ℂ) * (a n : ℂ) * w ^ (n - (k + 1)))
        hu Metric.isOpen_ball (convex_ball (0 : ℂ) s).isPreconnected
        (fun n w _ => ?_) (fun n w hw => ?_) (Metric.mem_ball_self hs0) hconv0 hzs
      · by_cases hnk : n ≤ k
        · have hsub0 : n - k = 0 := by omega
          have hdesc0 : n.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
          rw [hsub0, hdesc0]
          simpa using hasDerivAt_const w (((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ))
        · push Not at hnk
          have hsub : n - k = (n - (k + 1)) + 1 := by omega
          have hpow : HasDerivAt (fun y : ℂ => y ^ (n - k)) (((n - k : ℕ) : ℂ) * w ^ (n - (k + 1))) w := by
            rw [hsub]
            simpa [Nat.sub_add_cancel (show 1 ≤ n - k by omega)] using hasDerivAt_pow (n - (k + 1) + 1) w
          have hmul := hpow.const_mul (((n.descFactorial k : ℕ) : ℂ) * (a n : ℂ))
          refine hmul.congr_deriv ?_
          rw [Nat.descFactorial_succ]
          push_cast; ring
      · have hws : ‖w‖ ≤ s := (show ‖w‖ < s by simpa [Metric.mem_ball, dist_zero_right] using hw).le
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
          Real.norm_of_nonneg (ha n), norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hws _)
          (mul_nonneg (Nat.cast_nonneg _) (ha n))
    exact hd.deriv

/-- **Vivanti–Pringsheim Global Extension**:
For EVERY `y ∈ (0, rhoE1)`, `HasSum (fun n : ℕ => xInvCoeff n * y ^ n) (xInv y)`. -/
theorem hasSum_xInvCoeff_eq_xInv {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) rhoE1) :
    HasSum (fun n : ℕ => xInvCoeff n * y ^ n) (xInv y) := by
  let S_conv : Set ℝ := {r : ℝ | 0 < r ∧ r < rhoE1 ∧
    Summable (fun n : ℕ => xInvCoeff n * r ^ n) ∧
    (∑' n : ℕ, xInvCoeff n * r ^ n) = xInv r}
  have hS_nonempty : S_conv.Nonempty := by
    let r0 : ℝ := min (1 / 128) (rhoE1 / 2)
    have hr0_pos : 0 < r0 := lt_min (by norm_num) (half_pos rhoE1_pos)
    have hr0_lt64 : r0 < 1 / 64 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hr0_lt_rho : r0 < rhoE1 := lt_of_le_of_lt (min_le_right _ _) (half_lt_self rhoE1_pos)
    refine ⟨r0, hr0_pos, hr0_lt_rho, (summable_xInv_deriv hr0_pos.le hr0_lt64).2.1, ?_⟩
    have hPhi := Phi_real_X_ser_eq hr0_pos hr0_lt64
    have hXpos : 0 < X_ser r0 := by
      have hsum := (summable_xInv_deriv hr0_pos.le hr0_lt64).2.1
      have h1 := le_hasSum hsum.hasSum 1 (fun n _ => mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hr0_pos.le n))
      simp only [xInvCoeff_one, pow_one, one_mul] at h1
      change r0 ≤ X_ser r0 at h1
      linarith
    have := xInv_Phi_real hXpos
    rw [hPhi] at this
    exact this.symm
  have hS_bdd : BddAbove S_conv := ⟨rhoE1, fun _ hr => hr.2.1.le⟩
  have hS_down_of_summable : ∀ r : ℝ, 0 < r → r < rhoE1 →
      Summable (fun n : ℕ => xInvCoeff n * r ^ n) →
      ∀ z ∈ Set.Ioo (0 : ℝ) r, z ∈ S_conv := by
    intro r hr_pos hr_lt hr_sum z hz
    have hsum_z : Summable (fun n : ℕ => xInvCoeff n * z ^ n) :=
      hr_sum.of_nonneg_of_le (fun n => mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hz.1.le n))
        (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.1.le hz.2.le n) (xInvCoeff_nonneg n))
    have hfz : (∑' n : ℕ, xInvCoeff n * z ^ n) = xInv z := by
      -- Both `g(w) = ∑' n, a_n w^n` and `Phi_complex (g(w)) = w` on `ball 0 r` by identity theorem!
      let g : ℂ → ℂ := fun w => ∑' n : ℕ, (xInvCoeff n : ℂ) * w ^ n
      have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r) := by
        intro w hw
        have hwn : ‖w‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hw
        -- Use `hasDerivAt_tsum_of_isPreconnected` directly
        let s : ℝ := (‖w‖ + r) / 2
        have hs0 : 0 < s := by dsimp [s]; linarith [norm_nonneg w]
        have hsr : s < r := by dsimp [s]; linarith
        have hws : w ∈ Metric.ball (0 : ℂ) s := by rw [Metric.mem_ball, dist_zero_right]; dsimp [s]; linarith
        -- Dominating bound for derivative series on `ball 0 s`
        let q : ℝ := s / r
        have hq0 : 0 < q := div_pos hs0 hr_pos
        have hq1 : q < 1 := (div_lt_one hr_pos).mpr hsr
        have hlog_pos : 0 < Real.log q⁻¹ := Real.log_pos (one_lt_inv₀ hq0 |>.mpr hq1)
        let C1 : ℝ := (Real.log q⁻¹)⁻¹ * s⁻¹
        have hu1 : Summable (fun n : ℕ => (n : ℝ) * xInvCoeff n * s ^ (n - 1)) := by
          refine Summable.of_nonneg_of_le (fun n => by have := xInvCoeff_nonneg n; positivity)
            (fun n => ?_) (hr_sum.mul_left C1)
          cases n with
          | zero => simp
          | succ k =>
            simp only [Nat.add_sub_cancel]
            have h1 := Real.pow_div_factorial_le_exp (((k + 1 : ℕ) : ℝ) * Real.log q⁻¹) (by positivity) 1
            simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
            have hexp : Real.exp (((k + 1 : ℕ) : ℝ) * Real.log q⁻¹) = (q ^ (k + 1))⁻¹ := by
              rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hq0), inv_pow]
            rw [hexp] at h1
            have hqn : 0 < q ^ (k + 1) := pow_pos hq0 (k + 1)
            have hnk : ((k + 1 : ℕ) : ℝ) * q ^ (k + 1) ≤ (Real.log q⁻¹)⁻¹ := by
              rw [show (Real.log q⁻¹)⁻¹ = 1 / Real.log q⁻¹ by rw [one_div], le_div_iff₀ hlog_pos]
              have := mul_le_mul_of_nonneg_right h1 hqn.le
              rw [inv_mul_cancel₀ hqn.ne'] at this
              linarith
            have hs_eq : s ^ k = s⁻¹ * q ^ (k + 1) * r ^ (k + 1) := by
              have hqr : q ^ (k + 1) * r ^ (k + 1) = s ^ (k + 1) := by
                rw [← mul_pow]; dsimp [q]; rw [div_mul_cancel₀ _ hr_pos.ne']
              rw [mul_assoc, hqr, pow_succ, ← mul_assoc, mul_comm s⁻¹, mul_assoc,
                inv_mul_cancel₀ hs0.ne', mul_one]
            rw [hs_eq]
            calc ((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * (s⁻¹ * q ^ (k + 1) * r ^ (k + 1))
                = (((k + 1 : ℕ) : ℝ) * q ^ (k + 1)) * s⁻¹ * (xInvCoeff (k + 1) * r ^ (k + 1)) := by ring
              _ ≤ (Real.log q⁻¹)⁻¹ * s⁻¹ * (xInvCoeff (k + 1) * r ^ (k + 1)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnk (by positivity))
                    (mul_nonneg (xInvCoeff_nonneg _) (pow_nonneg hr_pos.le _))
              _ = C1 * (xInvCoeff (k + 1) * r ^ (k + 1)) := rfl
        have hd_w : HasDerivAt g (∑' n : ℕ, (n : ℂ) * (xInvCoeff n : ℂ) * w ^ (n - 1)) w := by
          refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) s)
            (g := fun n (y : ℂ) => (xInvCoeff n : ℂ) * y ^ n)
            (g' := fun n (y : ℂ) => (n : ℂ) * (xInvCoeff n : ℂ) * y ^ (n - 1))
            hu1 Metric.isOpen_ball (convex_ball (0 : ℂ) s).isPreconnected
            (fun n y _ => ?_) (fun n y hy => ?_) (Metric.mem_ball_self hs0)
            (by refine summable_of_ne_finset_zero (s := {0}) fun n hn => by simp [zero_pow (by simpa using hn)])
            hws
          · cases n with
            | zero => simpa using hasDerivAt_const y (xInvCoeff 0 : ℂ)
            | succ k =>
              simpa [mul_assoc, mul_left_comm] using (hasDerivAt_pow (k + 1) y).const_mul (xInvCoeff (k + 1) : ℂ)
          · have hys : ‖y‖ ≤ s := (show ‖y‖ < s by simpa [Metric.mem_ball, dist_zero_right] using hy).le
            rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
              Real.norm_of_nonneg (xInvCoeff_nonneg n), norm_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hys _)
              (mul_nonneg (Nat.cast_nonneg n) (xInvCoeff_nonneg n))
        exact hd_w.differentiableAt.differentiableWithinAt
      have hPhi_diff : DifferentiableOn ℂ (fun w => Phi_complex (g w)) (Metric.ball (0 : ℂ) r) :=
        DifferentiableOn.comp (f := g) (g := Phi_complex)
          (fun w _ => (hasDerivAt_Phi_complex w).differentiableAt.differentiableWithinAt)
          hg_diff (Set.mapsTo_univ _ _)
      have hPhi_an : AnalyticOnNhd ℂ (fun w => Phi_complex (g w)) (Metric.ball (0 : ℂ) r) :=
        hPhi_diff.analyticOnNhd Metric.isOpen_ball
      have hid_an : AnalyticOnNhd ℂ id (Metric.ball (0 : ℂ) r) :=
        differentiable_id.differentiableOn.analyticOnNhd Metric.isOpen_ball
      let r1 : ℝ := min (1 / 128) (r / 2)
      have hr1_pos : 0 < r1 := lt_min (by norm_num) (half_pos hr_pos)
      have hfreq : ∃ᶠ w in 𝓝[≠] ((r1 : ℝ) : ℂ), Phi_complex (g w) = id w := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin] at hU
        obtain ⟨V, hVopen, hr1V, hVU⟩ := hU
        obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hVopen (r1 : ℂ) hr1V
        let wR : ℝ := r1 + min (ε / 2) (min (1 / 256) (r / 4))
        have hwR_gt : r1 < wR := by dsimp [wR]; linarith [lt_min (half_pos hεpos) (lt_min (by norm_num : (0 : ℝ) < 1 / 256) (by linarith [hr_pos] : (0 : ℝ) < r / 4))]
        have hwR_lt64 : wR < 1 / 64 := by
          have h1 : r1 ≤ 1 / 128 := min_le_left _ _
          have h2 : min (ε / 2) (min (1 / 256) (r / 4)) ≤ 1 / 256 := le_trans (min_le_right _ _) (min_le_left _ _)
          dsimp [wR]; linarith
        have hwR_ball : (wR : ℂ) ∈ Metric.ball (r1 : ℂ) ε := by
          rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have h2 : min (ε / 2) (min (1 / 256) (r / 4)) ≤ ε / 2 := min_le_left _ _
          rw [abs_of_pos (by linarith)]; dsimp [wR]; linarith
        have hwR_ne : (wR : ℂ) ≠ (r1 : ℂ) := by
          intro h; have := Complex.ofReal_injective h; linarith
        refine ⟨(wR : ℂ), hVU ⟨hεball hwR_ball, hwR_ne⟩, ?_⟩
        have hg_ofReal : g (wR : ℂ) = (X_ser wR : ℂ) := by
          have hs := Complex.ofRealCLM.hasSum ((summable_xInv_deriv (by linarith) hwR_lt64).2.1).hasSum
          have hts : (∑' n : ℕ, ((xInvCoeff n * wR ^ n : ℝ) : ℂ)) = (X_ser wR : ℂ) := hs.tsum_eq
          rw [← hts]; dsimp only [g]; congr 1; ext n; push_cast; rfl
        rw [hg_ofReal, Phi_complex_ofReal, Phi_real_X_ser_eq (by linarith) hwR_lt64]
        rfl
      have hr1_mem : (r1 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr1_pos.le]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr_pos)
      have heq_ball : Set.EqOn (fun w => Phi_complex (g w)) id (Metric.ball (0 : ℂ) r) :=
        hPhi_an.eqOn_of_preconnected_of_frequently_eq hid_an (convex_ball (0 : ℂ) r).isPreconnected
          hr1_mem hfreq
      have hz_mem : (z : ℂ) ∈ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hz.1.le]
        exact hz.2
      have hgz_ofReal : g (z : ℂ) = ((∑' n : ℕ, xInvCoeff n * z ^ n : ℝ) : ℂ) := by
        have hs := Complex.ofRealCLM.hasSum hsum_z.hasSum
        have hts : (∑' n : ℕ, ((xInvCoeff n * z ^ n : ℝ) : ℂ)) = ((∑' n : ℕ, xInvCoeff n * z ^ n : ℝ) : ℂ) :=
          hs.tsum_eq
        rw [← hts]; dsimp only [g]; congr 1; ext n; push_cast; rfl
      have hPhi_z : Phi_real (∑' n : ℕ, xInvCoeff n * z ^ n) = z := by
        have hc : Phi_complex (g (z : ℂ)) = (z : ℂ) := heq_ball hz_mem
        rw [hgz_ofReal, Phi_complex_ofReal] at hc
        exact Complex.ofReal_injective hc
      have hXpos_z : 0 < ∑' n : ℕ, xInvCoeff n * z ^ n := by
        have h1 := le_hasSum hsum_z.hasSum 1 (fun n _ => mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hz.1.le n))
        simp only [xInvCoeff_one, pow_one, one_mul] at h1
        linarith [hz.1]
      have := xInv_Phi_real hXpos_z
      rw [hPhi_z] at this
      exact this.symm
    exact ⟨hz.1, lt_trans hz.2 hr_lt, hsum_z, hfz⟩
  have hS_down : ∀ r ∈ S_conv, ∀ z ∈ Set.Ioo (0 : ℝ) r, z ∈ S_conv :=
    fun r hr => hS_down_of_summable r hr.1 hr.2.1 hr.2.2.1
  -- Now prove R := sSup S_conv equals rhoE1!
  let R : ℝ := sSup S_conv
  have hR_pos : 0 < R := by
    obtain ⟨r0, hr0⟩ := hS_nonempty
    exact lt_of_lt_of_le hr0.1 (le_csSup hS_bdd hr0)
  have hR_le : R ≤ rhoE1 := csSup_le hS_nonempty fun _ hr => hr.2.1.le
  have hR_eq : R = rhoE1 := by
    by_contra hne
    have hR_lt : R < rhoE1 := lt_of_le_of_ne hR_le hne
    have hR_mem : R ∈ Set.Ioo (0 : ℝ) rhoE1 := ⟨hR_pos, hR_lt⟩
    let x₀ : ℝ := xInv R
    have hx₀_pos : 0 < x₀ := xInv_pos hR_mem
    have hPhi_x₀ : Phi_complex (x₀ : ℂ) = (R : ℂ) := by
      rw [Phi_complex_ofReal, Phi_real_xInv hR_mem]
    have hPhi_contDiff : ContDiff ℂ ⊤ Phi_complex :=
      ((Differentiable.differentiableOn fun z => (hasDerivAt_Phi_complex z).differentiableAt).analyticOnNhd
        isOpen_univ).contDiffOn isOpen_univ.uniqueDiffOn |> fun h => contDiffOn_univ.mp h
    have hPhi_strict : ∀ z : ℂ, HasStrictDerivAt Phi_complex (Complex.exp (-Ein_complex z - z)) z := by
      intro z
      have h1 := hPhi_contDiff.hasStrictDerivAt (by simp) (x := z)
      rw [(hasDerivAt_Phi_complex z).deriv] at h1
      exact h1
    have hder_ne : Complex.exp (-Ein_complex (x₀ : ℂ) - (x₀ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    let ψ : ℂ → ℂ := (hPhi_strict (x₀ : ℂ)).localInverse Phi_complex _ (x₀ : ℂ) hder_ne
    have hleft : ∀ᶠ z in 𝓝 (x₀ : ℂ), ψ (Phi_complex z) = z :=
      (hPhi_strict (x₀ : ℂ)).eventually_left_inverse hder_ne
    have hright : ∀ᶠ w in 𝓝 (R : ℂ), Phi_complex (ψ w) = w := by
      rw [← hPhi_x₀]; exact (hPhi_strict (x₀ : ℂ)).eventually_right_inverse hder_ne
    have hψ_cont : ContinuousAt ψ (R : ℂ) := by
      rw [← hPhi_x₀]; exact ((hPhi_strict (x₀ : ℂ)).to_localInverse hder_ne).hasDerivAt.continuousAt
    have hψ_R : ψ (R : ℂ) = (x₀ : ℂ) := by
      rw [← hPhi_x₀]; exact hleft.self_of_nhds
    obtain ⟨η, hη_pos, hη_left⟩ := Metric.eventually_nhds_iff.mp hleft
    obtain ⟨δ1, hδ1_pos, hδ1_right⟩ := Metric.eventually_nhds_iff.mp hright
    obtain ⟨δ2, hδ2_pos, hδ2_maps⟩ := Metric.continuousAt_iff.mp hψ_cont η hη_pos
    have hcont_xInv_R : ContinuousAt xInv R :=
      continuousOn_xInv.continuousAt (Ioo_mem_nhds hR_pos hR_lt)
    obtain ⟨δ3, hδ3_pos, hδ3_xInv⟩ := Metric.continuousAt_iff.mp hcont_xInv_R η hη_pos
    let δ : ℝ := min (min δ1 δ2) (min δ3 (min (R / 2) ((rhoE1 - R) / 2)))
    have hδ_pos : 0 < δ := lt_min (lt_min hδ1_pos hδ2_pos)
      (lt_min hδ3_pos (lt_min (half_pos hR_pos) (half_pos (by linarith))))
    have hδ_le1 : δ ≤ δ1 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ_le2 : δ ≤ δ2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ_le3 : δ ≤ δ3 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_leR : δ ≤ R / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ_le_rho : δ ≤ (rhoE1 - R) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hψ_diff : DifferentiableOn ℂ ψ (Metric.ball (R : ℂ) δ) := by
      intro w hw
      have hwd : dist w (R : ℂ) < δ := Metric.mem_ball.mp hw
      have hψw_ball : ψ w ∈ Metric.ball (x₀ : ℂ) η := by
        rw [Metric.mem_ball, ← hψ_R]; exact hδ2_maps (lt_of_lt_of_le hwd hδ_le2)
      have hPhi_ψw : Phi_complex (ψ w) = w := hδ1_right (lt_of_lt_of_le hwd hδ_le1)
      have hleft_loc : ∀ᶠ z in 𝓝 (ψ w), ψ (Phi_complex z) = z :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hψw_ball) fun z hz => hη_left hz
      have hsd := (hPhi_strict (ψ w)).to_local_left_inverse (Complex.exp_ne_zero _) hleft_loc
      rw [hPhi_ψw] at hsd
      exact hsd.hasDerivAt.differentiableAt.differentiableWithinAt
    have hψ_real : ∀ u ∈ Set.Ioo (R - δ) (R + δ), ψ (u : ℂ) = (xInv u : ℂ) := by
      intro u hu
      have hu_mem : u ∈ Set.Ioo (0 : ℝ) rhoE1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hdist : dist u R < δ3 := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hx_dist : dist ((xInv u : ℝ) : ℂ) (x₀ : ℂ) < η := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa [Real.dist_eq, x₀] using hδ3_xInv hdist
      have h1 := hη_left hx_dist
      rw [Phi_complex_ofReal, Phi_real_xInv hu_mem] at h1
      exact h1
    -- Pick `r' ∈ S_conv` very close to `R`, and `r₀ < r'` inside `(R - δ/4, R)`
    obtain ⟨r', hr'S, hr'_gt⟩ := exists_lt_of_lt_csSup hS_nonempty (show R - δ / 8 < R by linarith)
    have hr'_le : r' ≤ R := le_csSup hS_bdd hr'S
    let r₀ : ℝ := r' - δ / 16
    have hr₀_pos : 0 < r₀ := by dsimp [r₀]; linarith
    have hr₀_lt_r' : r₀ < r' := by dsimp [r₀]; linarith
    have hr₀_gt : R - δ / 4 < r₀ := by dsimp [r₀]; linarith
    have hr₀_le_R : r₀ < R := by linarith
    let h_step : ℝ := δ / 2
    let r₁ : ℝ := r₀ + h_step
    have hr₁_gt_R : R < r₁ := by dsimp [r₁, h_step]; linarith
    have hr₁_lt_rho : r₁ < rhoE1 := by dsimp [r₁, h_step]; linarith
    have hball_sub : Metric.ball (r₀ : ℂ) (3 * δ / 4) ⊆ Metric.ball (R : ℂ) δ := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have hdiff : ‖(r₀ : ℂ) - (R : ℂ)‖ < δ / 4 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
      calc ‖w - (R : ℂ)‖ = ‖(w - (r₀ : ℂ)) + ((r₀ : ℂ) - (R : ℂ))‖ := by ring_nf
        _ ≤ ‖w - (r₀ : ℂ)‖ + ‖(r₀ : ℂ) - (R : ℂ)‖ := norm_add_le _ _
        _ < 3 * δ / 4 + δ / 4 := add_lt_add hw hdiff
        _ = δ := by ring
    have hr₁_in_ball : (r₁ : ℂ) ∈ Metric.ball (r₀ : ℂ) (3 * δ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have : r₁ - r₀ = δ / 2 := by dsimp [r₁, h_step]; ring
      rw [this, abs_of_pos (by linarith)]; linarith
    have htaylor := Complex.hasSum_taylorSeries_on_ball (hψ_diff.mono hball_sub) hr₁_in_ball
    -- Identify `iteratedDeriv k ψ (r₀ : ℂ)` with the termwise derivative of `g(w) = ∑' n, a_n w^n`!
    let g : ℂ → ℂ := fun w => ∑' n : ℕ, (xInvCoeff n : ℂ) * w ^ n
    have hg_eq_ψ : ∀ᶠ w in 𝓝 (r₀ : ℂ), g w = ψ w := by
      let ρ_int : ℝ := min (r' - r₀) (r₀ - (R - δ))
      have hρ_int : 0 < ρ_int := lt_min (by linarith) (by linarith)
      have hsub1 : Metric.ball (r₀ : ℂ) ρ_int ⊆ Metric.ball (0 : ℂ) r' := by
        intro w hw
        rw [Metric.mem_ball, dist_zero_right]
        have hd : ‖w - (r₀ : ℂ)‖ < ρ_int := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hle : ρ_int ≤ r' - r₀ := min_le_left _ _
        calc ‖w‖ ≤ ‖w - (r₀ : ℂ)‖ + ‖(r₀ : ℂ)‖ := by simpa using norm_add_le (w - (r₀ : ℂ)) (r₀ : ℂ)
          _ = ‖w - (r₀ : ℂ)‖ + r₀ := by rw [Complex.norm_real, Real.norm_of_nonneg hr₀_pos.le]
          _ < r' := by linarith
      have hsub2 : Metric.ball (r₀ : ℂ) ρ_int ⊆ Metric.ball (R : ℂ) δ :=
        fun w hw => hball_sub (by
          rw [Metric.mem_ball] at hw ⊢
          have hle : ρ_int ≤ r' - r₀ := min_le_left _ _
          have hle' : r' - r₀ ≤ δ / 16 := by dsimp [r₀]; linarith
          linarith)
      have hg_an : AnalyticOnNhd ℂ g (Metric.ball (r₀ : ℂ) ρ_int) := by
        have hdiff : DifferentiableOn ℂ g (Metric.ball (r₀ : ℂ) ρ_int) := by
          intro w hw
          have hwn : ‖w‖ < r' := by simpa [Metric.mem_ball, dist_zero_right] using hsub1 hw
          let s : ℝ := (‖w‖ + r') / 2
          have hs0 : 0 < s := by dsimp [s]; linarith [norm_nonneg w]
          have hsr : s < r' := by dsimp [s]; linarith
          have hws : w ∈ Metric.ball (0 : ℂ) s := by rw [Metric.mem_ball, dist_zero_right]; dsimp [s]; linarith
          let q : ℝ := s / r'
          have hq0 : 0 < q := div_pos hs0 hr'S.1
          have hq1 : q < 1 := (div_lt_one hr'S.1).mpr hsr
          have hlog_pos : 0 < Real.log q⁻¹ := Real.log_pos (one_lt_inv₀ hq0 |>.mpr hq1)
          let C1 : ℝ := (Real.log q⁻¹)⁻¹ * s⁻¹
          have hu1 : Summable (fun n : ℕ => (n : ℝ) * xInvCoeff n * s ^ (n - 1)) := by
            refine Summable.of_nonneg_of_le (fun n => by have := xInvCoeff_nonneg n; positivity)
              (fun n => ?_) (hr'S.2.2.1.mul_left C1)
            cases n with
            | zero => simp
            | succ k =>
              simp only [Nat.add_sub_cancel]
              have h1 := Real.pow_div_factorial_le_exp (((k + 1 : ℕ) : ℝ) * Real.log q⁻¹) (by positivity) 1
              simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
              have hexp : Real.exp (((k + 1 : ℕ) : ℝ) * Real.log q⁻¹) = (q ^ (k + 1))⁻¹ := by
                rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hq0), inv_pow]
              rw [hexp] at h1
              have hqn : 0 < q ^ (k + 1) := pow_pos hq0 (k + 1)
              have hnk : ((k + 1 : ℕ) : ℝ) * q ^ (k + 1) ≤ (Real.log q⁻¹)⁻¹ := by
                rw [show (Real.log q⁻¹)⁻¹ = 1 / Real.log q⁻¹ by rw [one_div], le_div_iff₀ hlog_pos]
                have := mul_le_mul_of_nonneg_right h1 hqn.le
                rw [inv_mul_cancel₀ hqn.ne'] at this
                linarith
              have hs_eq : s ^ k = s⁻¹ * q ^ (k + 1) * r' ^ (k + 1) := by
                have hqr : q ^ (k + 1) * r' ^ (k + 1) = s ^ (k + 1) := by
                  rw [← mul_pow]; dsimp [q]; rw [div_mul_cancel₀ _ hr'S.1.ne']
                rw [mul_assoc, hqr, pow_succ, ← mul_assoc, mul_comm s⁻¹, mul_assoc,
                  inv_mul_cancel₀ hs0.ne', mul_one]
              rw [hs_eq]
              calc ((k + 1 : ℕ) : ℝ) * xInvCoeff (k + 1) * (s⁻¹ * q ^ (k + 1) * r' ^ (k + 1))
                  = (((k + 1 : ℕ) : ℝ) * q ^ (k + 1)) * s⁻¹ * (xInvCoeff (k + 1) * r' ^ (k + 1)) := by ring
                _ ≤ (Real.log q⁻¹)⁻¹ * s⁻¹ * (xInvCoeff (k + 1) * r' ^ (k + 1)) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnk (by positivity))
                      (mul_nonneg (xInvCoeff_nonneg _) (pow_nonneg hr'S.1.le _))
                _ = C1 * (xInvCoeff (k + 1) * r' ^ (k + 1)) := rfl
          have hd_w : HasDerivAt g (∑' n : ℕ, (n : ℂ) * (xInvCoeff n : ℂ) * w ^ (n - 1)) w := by
            refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) s)
              (g := fun n (y : ℂ) => (xInvCoeff n : ℂ) * y ^ n)
              (g' := fun n (y : ℂ) => (n : ℂ) * (xInvCoeff n : ℂ) * y ^ (n - 1))
              hu1 Metric.isOpen_ball (convex_ball (0 : ℂ) s).isPreconnected
              (fun n y _ => ?_) (fun n y hy => ?_) (Metric.mem_ball_self hs0)
              (by refine summable_of_ne_finset_zero (s := {0}) fun n hn => by simp [zero_pow (by simpa using hn)])
              hws
            · cases n with
              | zero => simpa using hasDerivAt_const y (xInvCoeff 0 : ℂ)
              | succ k =>
                simpa [mul_assoc, mul_left_comm] using (hasDerivAt_pow (k + 1) y).const_mul (xInvCoeff (k + 1) : ℂ)
            · have hys : ‖y‖ ≤ s := (show ‖y‖ < s by simpa [Metric.mem_ball, dist_zero_right] using hy).le
              rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
                Real.norm_of_nonneg (xInvCoeff_nonneg n), norm_pow]
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hys _)
                (mul_nonneg (Nat.cast_nonneg n) (xInvCoeff_nonneg n))
          exact hd_w.differentiableAt.differentiableWithinAt
        exact hdiff.analyticOnNhd Metric.isOpen_ball
      have hψ_an : AnalyticOnNhd ℂ ψ (Metric.ball (r₀ : ℂ) ρ_int) :=
        (hψ_diff.mono hsub2).analyticOnNhd Metric.isOpen_ball
      have hfreq : ∃ᶠ w in 𝓝[≠] (r₀ : ℂ), g w = ψ w := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin] at hU
        obtain ⟨V, hVopen, hr₀V, hVU⟩ := hU
        obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hVopen (r₀ : ℂ) hr₀V
        let u : ℝ := r₀ + min (ε / 2) (ρ_int / 2)
        have hu_gt : r₀ < u := by dsimp [u]; linarith [lt_min (half_pos hεpos) (half_pos hρ_int)]
        have hu_lt_r' : u < r' := by
          have : min (ε / 2) (ρ_int / 2) ≤ ρ_int / 2 := min_le_right _ _
          have : ρ_int ≤ r' - r₀ := min_le_left _ _
          dsimp [u]; linarith
        have hu_Ioo : u ∈ Set.Ioo (R - δ) (R + δ) := ⟨by linarith, by linarith⟩
        have hu_ball : (u : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
          rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          have : min (ε / 2) (ρ_int / 2) ≤ ε / 2 := min_le_left _ _
          dsimp [u]; linarith
        have hu_ne : (u : ℂ) ≠ (r₀ : ℂ) := fun h => by have := Complex.ofReal_injective h; linarith
        refine ⟨(u : ℂ), hVU ⟨hεball hu_ball, hu_ne⟩, ?_⟩
        have huS : u ∈ S_conv := hS_down r' hr'S u ⟨by linarith, hu_lt_r'⟩
        have hgu : g (u : ℂ) = ((∑' n : ℕ, xInvCoeff n * u ^ n : ℝ) : ℂ) := by
          have hs := Complex.ofRealCLM.hasSum huS.2.2.1.hasSum
          have hts : (∑' n : ℕ, ((xInvCoeff n * u ^ n : ℝ) : ℂ)) =
              ((∑' n : ℕ, xInvCoeff n * u ^ n : ℝ) : ℂ) := hs.tsum_eq
          rw [← hts]; dsimp only [g]; congr 1; ext n; push_cast; rfl
        rw [hgu, huS.2.2.2, hψ_real u hu_Ioo]
      have heq := hg_an.eqOn_of_preconnected_of_frequently_eq hψ_an
        (convex_ball (r₀ : ℂ) ρ_int).isPreconnected (Metric.mem_ball_self hρ_int) hfreq
      exact Filter.mem_of_superset (Metric.ball_mem_nhds (r₀ : ℂ) hρ_int) heq
    have hg_iter : ∀ k : ℕ, iteratedDeriv k g =ᶠ[𝓝 (r₀ : ℂ)] iteratedDeriv k ψ := by
      intro k
      induction k with
      | zero => exact hg_eq_ψ
      | succ k ih =>
        have h1 : deriv (iteratedDeriv k g) =ᶠ[𝓝 (r₀ : ℂ)] deriv (iteratedDeriv k ψ) :=
          ih.deriv
        simpa [iteratedDeriv_succ] using h1
    have hsum_desc : ∀ k : ℕ,
        Summable (fun n : ℕ => ((n.descFactorial k : ℕ) : ℝ) * xInvCoeff n * r₀ ^ (n - k)) := by
      intro k
      let q : ℝ := r₀ / r'
      have hq0 : 0 < q := div_pos hr₀_pos hr'S.1
      have hq1 : q < 1 := (div_lt_one hr'S.1).mpr hr₀_lt_r'
      have hlog_pos : 0 < Real.log q⁻¹ := Real.log_pos (one_lt_inv₀ hq0 |>.mpr hq1)
      let Ck : ℝ := (k.factorial : ℝ) / (Real.log q⁻¹) ^ k * (r₀⁻¹) ^ k
      have hCk_nn : 0 ≤ Ck :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog_pos.le k))
          (pow_nonneg (inv_nonneg.mpr hr₀_pos.le) k)
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (xInvCoeff_nonneg n)) (pow_nonneg hr₀_pos.le _))
        (fun n => ?_) (hr'S.2.2.1.mul_left Ck)
      by_cases hnk : n < k
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnk]
        simp only [Nat.cast_zero, zero_mul]
        exact mul_nonneg hCk_nn (mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hr'S.1.le n))
      · push Not at hnk
        have hdesc_le : ((n.descFactorial k : ℕ) : ℝ) ≤ (n : ℝ) ^ k := by
          exact_mod_cast Nat.descFactorial_le_pow n k
        have hn_pow : (n : ℝ) ^ k * q ^ n ≤ (k.factorial : ℝ) / (Real.log q⁻¹) ^ k := by
          have h1 := Real.pow_div_factorial_le_exp ((n : ℝ) * Real.log q⁻¹) (by positivity) k
          have hfact : (0 : ℝ) < k.factorial := by positivity
          rw [mul_pow, div_le_iff₀ hfact] at h1
          have hexp : Real.exp ((n : ℝ) * Real.log q⁻¹) = (q ^ n)⁻¹ := by
            rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hq0), inv_pow]
          rw [hexp] at h1
          have hqn : 0 < q ^ n := pow_pos hq0 n
          have h2 : (n : ℝ) ^ k * (Real.log q⁻¹) ^ k * q ^ n ≤ (k.factorial : ℝ) := by
            have := mul_le_mul_of_nonneg_right h1 hqn.le
            rw [mul_right_comm (q ^ n)⁻¹, inv_mul_cancel₀ hqn.ne', one_mul] at this
            linarith
          rw [le_div_iff₀ (pow_pos hlog_pos k)]; linarith
        have hs_pow : r₀ ^ (n - k) = (r₀⁻¹) ^ k * q ^ n * r' ^ n := by
          have h1 : r₀ ^ (n - k) * r₀ ^ k = r₀ ^ n := by rw [← pow_add, Nat.sub_add_cancel hnk]
          have h2 : q ^ n * r' ^ n = r₀ ^ n := by rw [← mul_pow]; dsimp [q]; rw [div_mul_cancel₀ _ hr'S.1.ne']
          have h3 : (r₀⁻¹) ^ k * r₀ ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr₀_pos.ne', one_pow]
          rw [mul_assoc, h2, ← h1]
          calc r₀ ^ (n - k) = ((r₀⁻¹) ^ k * r₀ ^ k) * r₀ ^ (n - k) := by rw [h3, one_mul]
            _ = (r₀⁻¹) ^ k * (r₀ ^ (n - k) * r₀ ^ k) := by ring
        calc ((n.descFactorial k : ℕ) : ℝ) * xInvCoeff n * r₀ ^ (n - k)
            ≤ (n : ℝ) ^ k * xInvCoeff n * ((r₀⁻¹) ^ k * q ^ n * r' ^ n) := by
              rw [hs_pow]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdesc_le (xInvCoeff_nonneg n))
                (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr₀_pos.le) k) (pow_nonneg hq0.le n))
                  (pow_nonneg hr'S.1.le n))
          _ = ((n : ℝ) ^ k * q ^ n) * (r₀⁻¹) ^ k * (xInvCoeff n * r' ^ n) := by ring
          _ ≤ ((k.factorial : ℝ) / (Real.log q⁻¹) ^ k) * (r₀⁻¹) ^ k * (xInvCoeff n * r' ^ n) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hn_pow (pow_nonneg (inv_nonneg.mpr hr₀_pos.le) k))
                (mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg hr'S.1.le n))
          _ = Ck * (xInvCoeff n * r' ^ n) := rfl
    have hchoose_real : ∀ n k : ℕ,
        (n.choose k : ℝ) = ((n.descFactorial k : ℕ) : ℝ) / (k.factorial : ℝ) := by
      intro n k
      have hne : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [eq_div_iff hne, mul_comm]
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose n k).symm
    have hsum_choose : ∀ k : ℕ,
        Summable (fun n : ℕ => (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k) := by
      intro k
      refine ((hsum_desc k).mul_left ((k.factorial : ℝ)⁻¹ * h_step ^ k)).congr fun n => ?_
      rw [hchoose_real n k]
      ring
    have hcoeff_k : ∀ k : ℕ,
        ((k.factorial : ℂ)⁻¹ • ((r₁ : ℂ) - (r₀ : ℂ)) ^ k • iteratedDeriv k ψ (r₀ : ℂ)).re =
        ∑' n : ℕ, (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k := by
      intro k
      rw [← (hg_iter k).self_of_nhds]
      have hr₀_ball : (r₀ : ℂ) ∈ Metric.ball (0 : ℂ) r' := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr₀_pos.le]
        exact hr₀_lt_r'
      rw [iteratedDeriv_tsum_nonneg_coeff xInvCoeff_nonneg hr'S.1 hr'S.2.2.1 k (r₀ : ℂ) hr₀_ball]
      have hterm_eq : ∀ n : ℕ,
          (k.factorial : ℂ)⁻¹ * (((r₁ : ℂ) - (r₀ : ℂ)) ^ k *
            (((n.descFactorial k : ℕ) : ℂ) * (xInvCoeff n : ℂ) * (r₀ : ℂ) ^ (n - k))) =
          (((n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k : ℝ) : ℂ) := by
        intro n
        have hr10 : (r₁ : ℂ) - (r₀ : ℂ) = (h_step : ℂ) := by
          rw [← Complex.ofReal_sub]; congr 1; dsimp [r₁]; ring
        rw [hr10, hchoose_real n k]
        push_cast
        ring
      have hmul_tsum :
          (k.factorial : ℂ)⁻¹ • ((r₁ : ℂ) - (r₀ : ℂ)) ^ k •
            (∑' n : ℕ, ((n.descFactorial k : ℕ) : ℂ) * (xInvCoeff n : ℂ) * (r₀ : ℂ) ^ (n - k)) =
          ∑' n : ℕ, (((n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k : ℝ) : ℂ) := by
        simp only [smul_eq_mul, ← tsum_mul_left]
        congr 1; ext n; exact hterm_eq n
      rw [hmul_tsum]
      have hofReal := (Complex.ofRealCLM.hasSum (hsum_choose k).hasSum).tsum_eq
      change (∑' n : ℕ, Complex.ofRealCLM ((n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k)).re = _
      rw [hofReal]
      simp [Complex.ofRealCLM_apply]
    -- Now apply Tonelli to conclude `∑' n, a_n r₁^n ≤ xInv r₁ < ∞`!
    have hh_pos : 0 < h_step := half_pos hδ_pos
    have htaylor_re : HasSum (fun k : ℕ =>
        ∑' n : ℕ, (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k) (xInv r₁) := by
      have hre := Complex.reCLM.hasSum htaylor
      have hψr1 : (ψ (r₁ : ℂ)).re = xInv r₁ := by
        rw [hψ_real r₁ ⟨by dsimp [r₁, h_step, r₀]; linarith, by dsimp [r₁, h_step, r₀]; linarith⟩]; simp
      change HasSum _ (ψ (r₁ : ℂ)).re at hre
      rw [hψr1] at hre
      exact hre.congr_fun fun k => (hcoeff_k k).symm
    have hfub : ∀ N : ℕ, (∑ n ∈ Finset.range N, xInvCoeff n * r₁ ^ n) ≤ xInv r₁ := by
      intro N
      have hbin : ∀ n : ℕ, xInvCoeff n * r₁ ^ n =
          ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k := by
        intro n
        have h1 : r₁ ^ n = (h_step + r₀) ^ n := by dsimp [r₁]; ring_nf
        rw [h1, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hpad : ∀ n ∈ Finset.range N, xInvCoeff n * r₁ ^ n =
          ∑ k ∈ Finset.range N, (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k := by
        intro n hn
        rw [hbin n]
        have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
        refine Finset.sum_subset (Finset.range_mono hnN) fun k _ hk => ?_
        have hgt : n < k := by simp only [Finset.mem_range] at hk; omega
        rw [Nat.choose_eq_zero_of_lt hgt]; simp
      calc ∑ n ∈ Finset.range N, xInvCoeff n * r₁ ^ n
          = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N,
              (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k :=
            Finset.sum_congr rfl hpad
        _ = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N,
              (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k := Finset.sum_comm
        _ ≤ ∑ k ∈ Finset.range N, ∑' n : ℕ,
              (n.choose k : ℝ) * xInvCoeff n * r₀ ^ (n - k) * h_step ^ k :=
            Finset.sum_le_sum fun k _ => sum_le_hasSum (Finset.range N)
              (fun n _ => by have := xInvCoeff_nonneg n; positivity) (hsum_choose k).hasSum
        _ ≤ xInv r₁ :=
            sum_le_hasSum (Finset.range N)
              (fun k _ => tsum_nonneg fun n => by have := xInvCoeff_nonneg n; positivity) htaylor_re
    have hsum_r1 : Summable (fun n : ℕ => xInvCoeff n * r₁ ^ n) :=
      summable_of_sum_range_le (fun n => mul_nonneg (xInvCoeff_nonneg n) (pow_nonneg (by linarith) n)) hfub
    let r₁' : ℝ := (R + r₁) / 2
    have hr1'_S : r₁' ∈ S_conv :=
      hS_down_of_summable r₁ (by linarith) hr₁_lt_rho hsum_r1 r₁' ⟨by dsimp [r₁']; linarith, by dsimp [r₁']; linarith⟩
    have hle_R : r₁' ≤ R := le_csSup hS_bdd hr1'_S
    dsimp [r₁'] at hle_R
    linarith
  -- Since `R = rhoE1` and `y < rhoE1`, pick `r ∈ S_conv` with `y < r < rhoE1` and apply `hS_down`!
  obtain ⟨r, hrS, hyr⟩ := exists_lt_of_lt_csSup hS_nonempty (hR_eq ▸ hy.2)
  have hyS : y ∈ S_conv := hS_down r hrS y ⟨hy.1, hyr⟩
  exact hyS.2.2.2 ▸ hyS.2.2.1.hasSum

/-- Positive discrete spectral weights `w_n = a_{n+1} ρ^{n+1} / (n + 1)` corresponding to the
inverse poles `1 / (n + 1)` (`n : ℕ`) in `R(t) = t ∑' n, w_n / (1 - t / (n + 1))`. -/
@[expose] def primeMeasureWeight (n : ℕ) : ℝ :=
  xInvCoeff (n + 1) * rhoE1 ^ (n + 1) / ((n + 1 : ℕ) : ℝ)

theorem primeMeasureWeight_pos (n : ℕ) : 0 < primeMeasureWeight n :=
  div_pos (mul_pos (xInvCoeff_pos (Nat.succ_pos n)) (pow_pos rhoE1_pos (n + 1))) (by positivity)

lemma integrableOn_exp_neg_nat_mul_pow (m k : ℕ) (hm : 1 ≤ m) :
    IntegrableOn (fun v : ℝ => Real.exp (-((m : ℕ) : ℝ) * v) * v ^ k) (Set.Ioi (0 : ℝ)) volume := by
  have hm_pos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast (show 0 < m by omega)
  let C : ℝ := (k.factorial : ℝ) / ((m : ℝ) / 2) ^ k
  have hdom : IntegrableOn (fun v : ℝ => C * Real.exp (-((m : ℝ) / 2) * v)) (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith : -((m : ℝ) / 2) < 0) 0).const_mul C
  refine hdom.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_pow k)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv_pos : 0 < v := Set.mem_Ioi.mp hv
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv_pos.le k))]
  have h1 := Real.pow_div_factorial_le_exp (((m : ℝ) / 2) * v) (by positivity) k
  have hfact : (0 : ℝ) < k.factorial := by positivity
  rw [mul_pow, div_le_iff₀ hfact] at h1
  have hv_le : v ^ k ≤ C * Real.exp (((m : ℝ) / 2) * v) := by
    dsimp only [C]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) / 2) ^ k)]
    linarith
  calc Real.exp (-(m : ℝ) * v) * v ^ k
      ≤ Real.exp (-(m : ℝ) * v) * (C * Real.exp (((m : ℝ) / 2) * v)) :=
        mul_le_mul_of_nonneg_left hv_le (Real.exp_pos _).le
    _ = C * (Real.exp (-(m : ℝ) * v) * Real.exp (((m : ℝ) / 2) * v)) := by ring
    _ = C * Real.exp (-((m : ℝ) / 2) * v) := by
        rw [← Real.exp_add]; congr 2; ring

lemma integral_exp_neg_nat_mul_pow (m k : ℕ) (hm : 1 ≤ m) :
    ∫ v in Set.Ioi (0 : ℝ), Real.exp (-((m : ℕ) : ℝ) * v) * v ^ k =
      (k.factorial : ℝ) / ((m : ℕ) : ℝ) ^ (k + 1) := by
  have hm_pos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast (show 0 < m by omega)
  induction k with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    have hF : ∀ v ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -Real.exp (-(m : ℝ) * x) / (m : ℝ)) (Real.exp (-(m : ℝ) * v)) v := by
      intro v _
      have hd := (((hasDerivAt_id v).const_mul (-(m : ℝ))).exp).neg.div_const (m : ℝ)
      refine hd.congr_deriv ?_
      simp only [id_eq]
      field_simp [hm_pos.ne']
    have htop : Tendsto (fun x : ℝ => -Real.exp (-(m : ℝ) * x) / (m : ℝ)) atTop (𝓝 0) := by
      have hexp : Tendsto (fun x : ℝ => Real.exp (-(m : ℝ) * x)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id)
      simpa using (hexp.neg).div_const (m : ℝ)
    have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hF
      (integrableOn_exp_mul_Ioi (by linarith : -(m : ℝ) < 0) 0) htop
    simpa [neg_div, neg_neg, one_div] using hint
  | succ k ih =>
    let F : ℝ → ℝ := fun v => -(Real.exp (-(m : ℝ) * v) * v ^ (k + 1)) / (m : ℝ)
    let f' : ℝ → ℝ := fun v =>
      Real.exp (-(m : ℝ) * v) * v ^ (k + 1) -
        (((k + 1 : ℕ) : ℝ) / (m : ℝ)) * (Real.exp (-(m : ℝ) * v) * v ^ k)
    have hF : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt F (f' v) v := by
      intro v _
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(m : ℝ) * x)) (-(m : ℝ) * Real.exp (-(m : ℝ) * v)) v := by
        simpa [mul_comm] using ((hasDerivAt_id v).const_mul (-(m : ℝ))).exp
      have h2 : HasDerivAt (fun x : ℝ => x ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * v ^ k) v :=
        hasDerivAt_pow (k + 1) v
      have hd := (h1.mul h2).neg.div_const (m : ℝ)
      refine hd.congr_deriv ?_
      dsimp only [f']
      field_simp [hm_pos.ne']
      ring
    have htop : Tendsto F atTop (𝓝 0) := by
      let C : ℝ := ((k + 1).factorial : ℝ) / ((m : ℝ) / 2) ^ (k + 1)
      have hlim : Tendsto (fun v : ℝ => (C / (m : ℝ)) * Real.exp (-((m : ℝ) / 2) * v)) atTop (𝓝 0) := by
        have hexp : Tendsto (fun v : ℝ => Real.exp (-((m : ℝ) / 2) * v)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id)
        simpa using hexp.const_mul (C / (m : ℝ))
      refine squeeze_zero_norm' (a := fun v : ℝ => (C / (m : ℝ)) * Real.exp (-((m : ℝ) / 2) * v)) ?_ hlim
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hm_pos,
        abs_of_pos (mul_pos (Real.exp_pos _) (pow_pos hv (k + 1)))]
      have h1 := Real.pow_div_factorial_le_exp (((m : ℝ) / 2) * v) (by positivity) (k + 1)
      have hfact : (0 : ℝ) < (k + 1).factorial := by positivity
      rw [mul_pow, div_le_iff₀ hfact] at h1
      have hv_le : v ^ (k + 1) ≤ C * Real.exp (((m : ℝ) / 2) * v) := by
        dsimp only [C]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) / 2) ^ (k + 1))]
        linarith
      calc Real.exp (-(m : ℝ) * v) * v ^ (k + 1) / (m : ℝ)
          ≤ Real.exp (-(m : ℝ) * v) * (C * Real.exp (((m : ℝ) / 2) * v)) / (m : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv_le (Real.exp_pos _).le) hm_pos.le
        _ = (C / (m : ℝ)) * (Real.exp (-(m : ℝ) * v) * Real.exp (((m : ℝ) / 2) * v)) := by ring
        _ = (C / (m : ℝ)) * Real.exp (-((m : ℝ) / 2) * v) := by
            rw [← Real.exp_add]; congr 2; ring
    have hint1 := integrableOn_exp_neg_nat_mul_pow m (k + 1) hm
    have hint2 := (integrableOn_exp_neg_nat_mul_pow m k hm).const_mul (((k + 1 : ℕ) : ℝ) / (m : ℝ))
    have hzero := integral_Ioi_of_hasDerivAt_of_tendsto' hF (hint1.sub hint2) htop
    have hF0 : F 0 = 0 := by simp [F]
    rw [hF0, sub_self] at hzero
    have hsplit : (∫ v in Set.Ioi (0 : ℝ), f' v) =
        (∫ v in Set.Ioi (0 : ℝ), Real.exp (-(m : ℝ) * v) * v ^ (k + 1)) -
        (((k + 1 : ℕ) : ℝ) / (m : ℝ)) * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-(m : ℝ) * v) * v ^ k) := by
      dsimp only [f']
      rw [MeasureTheory.integral_sub hint1 hint2, MeasureTheory.integral_const_mul]
    rw [hsplit, ih] at hzero
    have hgoal : ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(m : ℝ) * v) * v ^ (k + 1) =
        (((k + 1 : ℕ) : ℝ) / (m : ℝ)) * ((k.factorial : ℝ) / (m : ℝ) ^ (k + 1)) := by linarith
    rw [hgoal, Nat.factorial_succ]
    push_cast
    rw [pow_succ]
    field_simp [hm_pos.ne']
    ring

/-- Exact positive discrete moment representation:
`R_momentCoeff k = ∑' n : ℕ, primeMeasureWeight n / (n + 1) ^ k` for every `k : ℕ`. -/
theorem hasSum_primeMeasureWeight_div_pow (k : ℕ) :
    HasSum (fun n : ℕ => primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k) (R_momentCoeff k) := by
  have hE1_inj : Set.InjOn PakNthPrimeEngine.E1 (Set.Ioi (0 : ℝ)) := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hPhi : Phi_real x₁ = Phi_real x₂ := by
      rw [Phi_real_eq_rho_mul_exp_neg_E1 (Set.mem_Ioi.mp hx₁),
        Phi_real_eq_rho_mul_exp_neg_E1 (Set.mem_Ioi.mp hx₂), heq]
    exact strictMono_Phi_real.injective hPhi
  let g : ℝ → ℝ := fun v => xInv (rhoE1 * Real.exp (-v)) * v ^ k
  have hcov_eq : ∀ x ∈ Set.Ioi (0 : ℝ),
      |-Real.exp (-x) / x| • g (PakNthPrimeEngine.E1 x) =
        Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k := by
    intro x hx
    have hx_pos : 0 < x := Set.mem_Ioi.mp hx
    dsimp only [g]
    rw [smul_eq_mul, abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hx_pos,
      ← Phi_real_eq_rho_mul_exp_neg_E1 hx_pos, xInv_Phi_real hx_pos]
    field_simp [hx_pos.ne']
  have hE1_int : IntegrableOn (fun x : ℝ => Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k)
      (Set.Ioi (0 : ℝ)) volume := by
    simpa only [E1_eq_Eone] using PrimePencil.pencilMoment_integrable k
  have hg_int : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    rw [← E1_image_Ioi,
      MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        (fun x hx => (E1_hasDerivAt hx).hasDerivWithinAt) hE1_inj]
    exact hE1_int.congr_fun (fun x hx => (hcov_eq x hx).symm) measurableSet_Ioi
  have hcov_int : (∫ v in Set.Ioi (0 : ℝ), g v) =
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k := by
    calc (∫ v in Set.Ioi (0 : ℝ), g v)
        = ∫ v in PakNthPrimeEngine.E1 '' Set.Ioi (0 : ℝ), g v := by rw [E1_image_Ioi]
      _ = ∫ x in Set.Ioi (0 : ℝ), |-Real.exp (-x) / x| • g (PakNthPrimeEngine.E1 x) :=
          MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
            (fun x hx => (E1_hasDerivAt hx).hasDerivWithinAt) hE1_inj g
      _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcov_eq
  -- Expand `g v = ∑' n, u n v` pointwise on `v > 0` and apply Dominated Convergence!
  let u : ℕ → ℝ → ℝ := fun n v =>
    xInvCoeff (n + 1) * rhoE1 ^ (n + 1) * (Real.exp (-((n + 1 : ℕ) : ℝ) * v) * v ^ k)
  have hu_nn : ∀ n : ℕ, ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ u n v := by
    intro n v hv
    have hv_pos : 0 < v := Set.mem_Ioi.mp hv
    dsimp only [u]
    have ha := (xInvCoeff_pos (Nat.succ_pos n)).le
    have hr := rhoE1_pos.le
    positivity
  have hu_hasSum : ∀ v ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ => u n v) (g v) := by
    intro v hv
    have hv_pos : 0 < v := Set.mem_Ioi.mp hv
    have hy_mem : rhoE1 * Real.exp (-v) ∈ Set.Ioo (0 : ℝ) rhoE1 := by
      refine ⟨mul_pos rhoE1_pos (Real.exp_pos _), ?_⟩
      have hlt : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      nlinarith [rhoE1_pos]
    have hs := hasSum_xInvCoeff_eq_xInv hy_mem
    have hs_shift : HasSum (fun n : ℕ => xInvCoeff (n + 1) * (rhoE1 * Real.exp (-v)) ^ (n + 1))
        (xInv (rhoE1 * Real.exp (-v))) := by
      rw [← hasSum_nat_add_iff' 1] at hs
      simpa [xInvCoeff_zero] using hs
    have hs_mul := hs_shift.mul_right (v ^ k)
    refine hs_mul.congr_fun fun n => ?_
    dsimp only [u]
    rw [mul_pow, ← Real.exp_nat_mul]
    have harg : ((n + 1 : ℕ) : ℝ) * (-v) = -((n + 1 : ℕ) : ℝ) * v := by ring
    rw [harg]
    ring
  have hu_int : ∀ n : ℕ, IntegrableOn (u n) (Set.Ioi (0 : ℝ)) volume := fun n =>
    (integrableOn_exp_neg_nat_mul_pow (n + 1) k (Nat.succ_pos n)).const_mul _
  have hu_val : ∀ n : ℕ, (∫ v in Set.Ioi (0 : ℝ), u n v) =
      (k.factorial : ℝ) * (primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k) := by
    intro n
    dsimp only [u, primeMeasureWeight]
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_nat_mul_pow (n + 1) k (Nat.succ_pos n)]
    have hn_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [pow_succ (((n + 1 : ℕ) : ℝ)) k]
    field_simp [hn_ne]
  have hdct : Tendsto (fun N : ℕ => ∫ v in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.range N, u n v)
      atTop (𝓝 (∫ v in Set.Ioi (0 : ℝ), g v)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (bound := g)
      (fun N => (MeasureTheory.integrable_finsetSum (Finset.range N) fun n _ => hu_int n).aestronglyMeasurable)
      hg_int (fun N => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hnn : 0 ≤ ∑ n ∈ Finset.range N, u n v := Finset.sum_nonneg fun n _ => hu_nn n v hv
      rw [Real.norm_of_nonneg hnn]
      exact sum_le_hasSum (Finset.range N) (fun n _ => hu_nn n v hv) (hu_hasSum v hv)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (hu_hasSum v hv).tendsto_sum_nat
  have hdct' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (k.factorial : ℝ) * (primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k))
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k)) := by
    rw [← hcov_int]
    refine hdct.congr fun N => ?_
    rw [MeasureTheory.integral_finsetSum _ fun n _ => hu_int n]
    exact Finset.sum_congr rfl fun n _ => hu_val n
  have hsum_scaled : HasSum (fun n : ℕ =>
      (k.factorial : ℝ) * (primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k))
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n => by have := (primeMeasureWeight_pos n).le; positivity) _).mpr hdct'
  have hfinal := hsum_scaled.mul_left ((k.factorial : ℝ)⁻¹)
  have hfact_ne : (k.factorial : ℝ) ≠ 0 := by positivity
  have hfinal' : HasSum (fun n : ℕ => primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k)
      ((k.factorial : ℝ)⁻¹ * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (PakNthPrimeEngine.E1 x) ^ k) :=
    hfinal.congr_fun fun n => by rw [← mul_assoc, inv_mul_cancel₀ hfact_ne, one_mul]
  simpa only [R_momentCoeff, PrimePencil.pencilMoment, E1_eq_Eone, div_eq_inv_mul] using hfinal'

/-- The discrete spectral measure has exact total mass `1`: `∑' n, primeMeasureWeight n = 1`. -/
theorem hasSum_primeMeasureWeight : HasSum primeMeasureWeight 1 := by
  have h := hasSum_primeMeasureWeight_div_pow 0
  rw [R_momentCoeff_zero] at h
  simpa using h

/-- **Exact Positive-Measure Representation of `R(t)` on `‖t‖ < 1`**:
`R_integral t = t * ∑' n : ℕ, primeMeasureWeight n / (1 - t / (n + 1))`. -/
theorem R_integral_eq_positive_measure {t : ℂ} (ht : ‖t‖ < 1) :
    PakNthPrimeEngine.R_integral t =
      t * ∑' n : ℕ, (primeMeasureWeight n : ℂ) / (1 - t / ((n + 1 : ℕ) : ℂ)) := by
  rw [R_integral_eq_tsum ht]
  have hpow : ∀ k : ℕ, (R_momentCoeff k : ℂ) * t ^ (k + 1) =
      t * ((R_momentCoeff k : ℂ) * t ^ k) := fun k => by rw [pow_succ]; ring
  simp_rw [hpow, tsum_mul_left]
  congr 1
  let f : ℕ × ℕ → ℂ := fun p =>
    (primeMeasureWeight p.1 : ℂ) * (t / ((p.1 + 1 : ℕ) : ℂ)) ^ p.2
  have hf_norm_sum : Summable (fun p : ℕ × ℕ => ‖f p‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun n => ?_, ?_⟩
    · have hq : ‖t / ((n + 1 : ℕ) : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_natCast]
        exact lt_of_le_of_lt (div_le_self (norm_nonneg t) (by exact_mod_cast (show 1 ≤ n + 1 by omega))) ht
      have hg := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left (primeMeasureWeight n)
      refine hg.congr fun k => ?_
      dsimp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (primeMeasureWeight_pos n).le, norm_pow]
    · have h1m : 0 < 1 - ‖t‖ := by linarith
      refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => norm_nonneg _) (fun n => ?_)
        (hasSum_primeMeasureWeight.summable.mul_right (1 - ‖t‖)⁻¹)
      have hq : ‖t / ((n + 1 : ℕ) : ℂ)‖ ≤ ‖t‖ := by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_self (norm_nonneg t) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
      have hts_eq : (∑' k : ℕ, ‖f (n, k)‖) ≤ ∑' k : ℕ, primeMeasureWeight n * ‖t‖ ^ k := by
        have hs1 : Summable (fun k : ℕ => ‖f (n, k)‖) := by
          have hq' : ‖t / ((n + 1 : ℕ) : ℂ)‖ < 1 := lt_of_le_of_lt hq ht
          refine ((summable_geometric_of_lt_one (norm_nonneg _) hq').mul_left (primeMeasureWeight n)).congr fun k => ?_
          dsimp only [f]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (primeMeasureWeight_pos n).le, norm_pow]
        have hs2 : Summable (fun k : ℕ => primeMeasureWeight n * ‖t‖ ^ k) :=
          (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left (primeMeasureWeight n)
        refine hs1.tsum_le_tsum (fun k => ?_) hs2
        dsimp only [f]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (primeMeasureWeight_pos n).le, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq k) (primeMeasureWeight_pos n).le
      refine hts_eq.trans ?_
      rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg t) ht]
  have hf_sum : Summable f := hf_norm_sum.of_norm
  have hcol : ∀ k : ℕ, (R_momentCoeff k : ℂ) * t ^ k = ∑' n : ℕ, f (n, k) := by
    intro k
    have hs := (Complex.ofRealCLM.hasSum (hasSum_primeMeasureWeight_div_pow k)).mul_right (t ^ k)
    have hts : (∑' n : ℕ, ((primeMeasureWeight n / ((n + 1 : ℕ) : ℝ) ^ k : ℝ) : ℂ) * t ^ k) =
        (R_momentCoeff k : ℂ) * t ^ k := hs.tsum_eq
    rw [← hts]
    congr 1; ext n
    dsimp only [f]
    push_cast
    rw [div_pow]
    ring
  have hrow : ∀ n : ℕ, (∑' k : ℕ, f (n, k)) =
      (primeMeasureWeight n : ℂ) / (1 - t / ((n + 1 : ℕ) : ℂ)) := by
    intro n
    have hq : ‖t / ((n + 1 : ℕ) : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_natCast]
      exact lt_of_le_of_lt (div_le_self (norm_nonneg t) (by exact_mod_cast (show 1 ≤ n + 1 by omega))) ht
    dsimp only [f]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq, ← div_eq_mul_inv]
  simp_rw [hcol]
  rw [Summable.tsum_comm (f := fun n k => f (n, k)) hf_sum]
  exact tsum_congr hrow

/-- Identification of our explicit convolution coefficients `etaCoeff m` with the Maclaurin
derivatives `iteratedDeriv m eta_integral 0 / m!`. -/
theorem etaCoeff_eq_iteratedDeriv {m : ℕ} (hm : 2 ≤ m) :
    etaCoeff m = iteratedDeriv m eta_integral 0 / (m.factorial : ℂ) := by
  let c : ℕ → ℂ := fun n => if 2 ≤ n then etaCoeff n else 0
  let a : ℕ → ℂ := fun n => iteratedDeriv n eta_integral 0 / (n.factorial : ℂ)
  let d : ℕ → ℂ := fun n => c n - a n
  have hball_sub : Metric.ball (0 : ℂ) (1 / 2) ⊆ {z : ℂ | z.re < 1} := by
    intro z hz
    have hzn : ‖z‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact lt_of_le_of_lt (Complex.re_le_norm z) (by linarith)
  have hdiff_half : DifferentiableOn ℂ eta_integral (Metric.ball (0 : ℂ) (1 / 2)) :=
    eta_holomorphic_on_halfplane.mono hball_sub
  have ha_hasSum : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), HasSum (fun n : ℕ => a n * z ^ n) (eta_integral z) := by
    intro z hz
    have ht := Complex.hasSum_taylorSeries_on_ball hdiff_half hz
    refine ht.congr_fun fun n => ?_
    dsimp only [a]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hc_hasSum : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), HasSum (fun n : ℕ => c n * z ^ n) (eta_integral z) := by
    intro z hz
    have hzn : ‖z‖ < 1 := lt_trans (by simpa [Metric.mem_ball, dist_zero_right] using hz) (by norm_num)
    have hs := hasSum_eta_integral hzn
    rw [← hasSum_nat_add_iff' 2]
    have hfin : (∑ i ∈ Finset.range 2, c i * z ^ i) = 0 := by
      simp [c, Finset.sum_range_succ]
    rw [hfin, sub_zero]
    refine hs.congr_fun fun n => ?_
    dsimp only [c]
    have hge : 2 ≤ n + 2 := by omega
    simp only [hge, ↓reduceIte]
  have hd_zero_ball : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), HasSum (fun n : ℕ => d n * z ^ n) 0 := by
    intro z hz
    simpa [d, sub_mul, sub_self] using (hc_hasSum z hz).sub (ha_hasSum z hz)
  have hd_summable_eighth : Summable (fun n : ℕ => ‖d n‖ * (1 / 8 : ℝ) ^ n) := by
    have h14 : ((1 / 4 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 2) := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
      norm_num
    have htend : Tendsto (fun n : ℕ => d n * ((1 / 4 : ℝ) : ℂ) ^ n) atTop (𝓝 0) :=
      (hd_zero_ball _ h14).summable.tendsto_atTop_zero
    have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖d n * ((1 / 4 : ℝ) : ℂ) ^ n‖ ≤ M := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend 1 zero_lt_one
      refine ⟨1 + ∑ i ∈ Finset.range N, ‖d i * ((1 / 4 : ℝ) : ℂ) ^ i‖,
        add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _), fun n => ?_⟩
      by_cases hn : n < N
      · have hle : ‖d n * ((1 / 4 : ℝ) : ℂ) ^ n‖ ≤ ∑ i ∈ Finset.range N, ‖d i * ((1 / 4 : ℝ) : ℂ) ^ i‖ :=
          Finset.single_le_sum (f := fun i => ‖d i * ((1 / 4 : ℝ) : ℂ) ^ i‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hn)
        linarith
      · push Not at hn
        have hlt := hN n hn
        rw [dist_zero_right] at hlt
        have hnn : 0 ≤ ∑ i ∈ Finset.range N, ‖d i * ((1 / 4 : ℝ) : ℂ) ^ i‖ :=
          Finset.sum_nonneg fun _ _ => norm_nonneg _
        linarith
    obtain ⟨M, hMnn, hM⟩ := hbdd
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left M)
    have hn4 : ‖d n‖ * (1 / 4 : ℝ) ^ n ≤ M := by
      simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hM n
    have h8 : (1 / 8 : ℝ) ^ n = (1 / 4 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
    rw [h8, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hn4 (by positivity)
  have hd_all_zero : ∀ k : ℕ, d k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      let S : ℝ → ℂ := fun r => ∑' j : ℕ, d (k + j) * (r : ℂ) ^ j
      have hS_sum : Summable (fun j : ℕ => ‖d (k + j)‖ * (1 / 8 : ℝ) ^ j) := by
        have hshift := hd_summable_eighth.comp_injective
          (i := fun j : ℕ => k + j) (fun a b h => Nat.add_left_cancel h)
        refine (hshift.mul_left ((8 : ℝ) ^ k)).congr fun j => ?_
        simp only [Function.comp_apply, pow_add]
        have h8 : (8 : ℝ) ^ k * (1 / 8 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        calc (8 : ℝ) ^ k * (‖d (k + j)‖ * ((1 / 8 : ℝ) ^ k * (1 / 8 : ℝ) ^ j))
            = ((8 : ℝ) ^ k * (1 / 8 : ℝ) ^ k) * (‖d (k + j)‖ * (1 / 8 : ℝ) ^ j) := by ring
          _ = ‖d (k + j)‖ * (1 / 8 : ℝ) ^ j := by rw [h8, one_mul]
      have hS_cont : ContinuousOn S (Set.Ioo (-(1 / 8 : ℝ)) (1 / 8)) := by
        refine continuousOn_tsum (u := fun j => ‖d (k + j)‖ * (1 / 8 : ℝ) ^ j)
          (fun j => (continuous_const.mul ((Complex.continuous_ofReal).pow j)).continuousOn) hS_sum
          (fun j r hr => ?_)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg r) (abs_le.mpr ⟨hr.1.le, hr.2.le⟩) j) (norm_nonneg _)
      have hS0 : S 0 = d k := by
        dsimp only [S]
        rw [tsum_eq_single 0 (fun j hj => by simp [zero_pow hj])]
        simp
      have hS_tend : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (d k)) := by
        have hlim : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (S 0)) :=
          (hS_cont.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
        rwa [hS0] at hlim
      have hS_zero : ∀ r ∈ Set.Ioo (0 : ℝ) (1 / 8), S r = 0 := by
        intro r hr
        have hr_ball : (r : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 2) := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
          linarith [hr.2]
        have hs := hd_zero_ball (r : ℂ) hr_ball
        rw [← hasSum_nat_add_iff' k] at hs
        have hfin : (∑ i ∈ Finset.range k, d i * (r : ℂ) ^ i) = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]
        rw [hfin, sub_zero] at hs
        have hfac : (r : ℂ) ^ k * S r = 0 := by
          dsimp only [S]
          rw [← tsum_mul_left]
          have hs' : HasSum (fun j : ℕ => (r : ℂ) ^ k * (d (k + j) * (r : ℂ) ^ j)) 0 := by
            refine hs.congr_fun fun j => ?_
            rw [Nat.add_comm k j, pow_add]; ring
          exact hs'.tsum_eq
        have hr_ne : (r : ℂ) ^ k ≠ 0 := pow_ne_zero k (Complex.ofReal_ne_zero.mpr hr.1.ne')
        exact (mul_eq_zero.mp hfac).resolve_left hr_ne
      have hS_tend0 : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 8)] with r hr
        exact (hS_zero r hr).symm
      exact tendsto_nhds_unique hS_tend hS_tend0
  have hdm := hd_all_zero m
  dsimp only [d, c, a] at hdm
  simp only [hm, ↓reduceIte] at hdm
  exact sub_eq_zero.mp hdm

/-- Local uniform convergence of Codex's pole-cleared positive-mass approximants
`PrimePencil.massApproximant Real.pi (Finset.range (N + 1)) (fun n => (n + 1)⁻¹) primeMeasureWeight`
to `fun z => Complex.sin (π * z) * R_integral z` on `Metric.ball 0 (1 / 2)`. -/
theorem tendstoLocallyUniformlyOn_primeMassApproximant :
    TendstoLocallyUniformlyOn
      (fun N z => (PrimePencil.massApproximant Real.pi (Finset.range (N + 1))
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) primeMeasureWeight).eval z)
      (fun z => Complex.sin ((Real.pi : ℂ) * z) * PakNthPrimeEngine.R_integral z)
      atTop (Metric.ball (0 : ℂ) (1 / 2)) := by
  let a : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 2)
  have hK_compact : IsCompact K := isCompact_closedBall (0 : ℂ) (1 / 2)
  -- Step 1: Uniform convergence of Euler's sine product on `K = closedBall 0 (1 / 2)`
  let A_seq : ℕ → ℂ → ℂ := fun N z =>
    (Real.pi : ℂ) * z * ∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j)
  let A_lim : ℂ → ℂ := fun z => Complex.sin ((Real.pi : ℂ) * z)
  have hA_lim_eq : ∀ z : ℂ, (Real.pi : ℂ) * z * (∏' j : ℕ, (1 + sineTerm z j)) = A_lim z := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [A_lim]
    · rw [euler_sineTerm_tprod hz]
      dsimp only [A_lim]
      have hpz : (Real.pi : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz
      exact mul_div_cancel₀ _ hpz
  have hA_unif : TendstoUniformlyOn A_seq A_lim atTop K := by
    have hprod := (multipliableUniformlyOn_euler_sin_prod_on_compact hK_compact).hasProdUniformlyOn
    have hfin := hprod.tendstoUniformlyOn_finsetRange
    rw [Metric.tendstoUniformlyOn_iff] at hfin ⊢
    intro ε hε
    let M : ℝ := Real.pi / 2 + 1
    have hM_pos : 0 < M := by dsimp [M]; linarith [Real.pi_pos]
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hfin (ε / M) (div_pos hε hM_pos))] with N hN z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz
    have hdist := hN z hz
    rw [dist_eq_norm] at hdist ⊢
    rw [← hA_lim_eq z]
    dsimp only [A_seq]
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hleM : Real.pi * ‖z‖ ≤ M := by dsimp [M]; nlinarith [Real.pi_pos]
    calc Real.pi * ‖z‖ * ‖(∏' j : ℕ, (1 + sineTerm z j)) - ∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j)‖
        ≤ M * ‖(∏' j : ℕ, (1 + sineTerm z j)) - ∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j)‖ :=
          mul_le_mul_of_nonneg_right hleM (norm_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left hdist hM_pos
      _ = ε := mul_div_cancel₀ ε hM_pos.ne'
  -- Step 2: Uniform convergence of the discrete resolvent sum on `K = closedBall 0 (1 / 2)`
  let B_seq : ℕ → ℂ → ℂ := fun N z =>
    z * ∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)
  let B_lim : ℂ → ℂ := PakNthPrimeEngine.R_integral
  have hden_ge : ∀ (i : ℕ) (z : ℂ), z ∈ K → (1 / 2 : ℝ) ≤ ‖1 - (a i : ℂ) * z‖ := by
    intro i z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz
    have ha_le : ‖(a i : ℂ) * z‖ ≤ 1 / 2 := by
      dsimp only [a]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
      exact (div_le_self (norm_nonneg z) (by exact_mod_cast (show 1 ≤ i + 1 by omega))).trans hzn
    have htri := norm_sub_norm_le (1 : ℂ) ((a i : ℂ) * z)
    rw [norm_one] at htri
    linarith
  have hterm_le : ∀ (i : ℕ) (z : ℂ), z ∈ K →
      ‖(primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)‖ ≤ 2 * primeMeasureWeight i := by
    intro i z hz
    have hd := hden_ge i z hz
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (primeMeasureWeight_pos i).le]
    calc primeMeasureWeight i / ‖1 - (a i : ℂ) * z‖
        ≤ primeMeasureWeight i / (1 / 2) :=
          div_le_div_of_nonneg_left (primeMeasureWeight_pos i).le (by norm_num) hd
      _ = 2 * primeMeasureWeight i := by ring
  have hB_seq_bdd : ∀ (N : ℕ) (z : ℂ), z ∈ K → ‖B_seq N z‖ ≤ 1 := by
    intro N z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [B_seq]
    rw [norm_mul]
    have hsum_le : ‖∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)‖ ≤ 2 := by
      calc ‖∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)‖
          ≤ ∑ i ∈ Finset.range (N + 1), ‖(primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (N + 1), (2 * primeMeasureWeight i) :=
            Finset.sum_le_sum fun i _ => hterm_le i z hz
        _ = 2 * ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i := (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
            (sum_le_hasSum (Finset.range (N + 1)) (fun i _ => (primeMeasureWeight_pos i).le)
              hasSum_primeMeasureWeight) (by norm_num)
        _ = 2 := by ring
    calc ‖z‖ * ‖∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)‖
        ≤ (1 / 2) * 2 := mul_le_mul hzn hsum_le (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hB_unif : TendstoUniformlyOn B_seq B_lim atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htail : Tendsto (fun N : ℕ => 1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i) atTop (𝓝 0) := by
      have h := hasSum_primeMeasureWeight.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      simpa [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
    filter_upwards [Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp htail ε hε)] with N hN z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz
    have hzn1 : ‖z‖ < 1 := lt_of_le_of_lt hzn (by norm_num)
    have hBlim_eq : B_lim z = z * ∑' i : ℕ, (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z) := by
      dsimp only [B_lim, a]
      rw [R_integral_eq_positive_measure hzn1]
      congr 1; apply tsum_congr; intro i
      push_cast
      rw [inv_mul_eq_div]
    have hsum_z : Summable (fun i : ℕ => (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)) :=
      (hasSum_primeMeasureWeight.summable.mul_left 2).of_norm_bounded fun i => hterm_le i z hz
    rw [dist_eq_norm, hBlim_eq]
    dsimp only [B_seq]
    rw [← mul_sub, norm_mul]
    have hsub_eq : (∑' i : ℕ, (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)) -
        (∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)) =
        ∑' j : ℕ, (primeMeasureWeight (j + (N + 1)) : ℂ) / (1 - (a (j + (N + 1)) : ℂ) * z) := by
      have hs := hsum_z.sum_add_tsum_nat_add (N + 1)
      exact (eq_sub_of_add_eq' hs).symm
    rw [hsub_eq]
    have htail_norm : ‖∑' j : ℕ, (primeMeasureWeight (j + (N + 1)) : ℂ) /
          (1 - (a (j + (N + 1)) : ℂ) * z)‖ ≤
        2 * (1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i) := by
      have hsum_shift : Summable (fun j : ℕ => 2 * primeMeasureWeight (j + (N + 1))) :=
        (hasSum_primeMeasureWeight.summable.mul_left 2).comp_injective (add_left_injective (N + 1))
      have h1 : ‖∑' j : ℕ, (primeMeasureWeight (j + (N + 1)) : ℂ) /
            (1 - (a (j + (N + 1)) : ℂ) * z)‖ ≤
          ∑' j : ℕ, ‖(primeMeasureWeight (j + (N + 1)) : ℂ) /
            (1 - (a (j + (N + 1)) : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm (hsum_shift.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun j => hterm_le (j + (N + 1)) z hz))
      have h2 : (∑' j : ℕ, ‖(primeMeasureWeight (j + (N + 1)) : ℂ) /
            (1 - (a (j + (N + 1)) : ℂ) * z)‖) ≤
          ∑' j : ℕ, (2 * primeMeasureWeight (j + (N + 1))) :=
        (hsum_shift.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun j => hterm_le (j + (N + 1)) z hz)).tsum_le_tsum (fun j => hterm_le (j + (N + 1)) z hz)
          hsum_shift
      have htail_w : (∑' j : ℕ, primeMeasureWeight (j + (N + 1))) =
          1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i := by
        have hs := hasSum_primeMeasureWeight.summable.sum_add_tsum_nat_add (N + 1)
        rw [hasSum_primeMeasureWeight.tsum_eq] at hs
        linarith
      calc _ ≤ ∑' j : ℕ, (2 * primeMeasureWeight (j + (N + 1))) := h1.trans h2
        _ = 2 * ∑' j : ℕ, primeMeasureWeight (j + (N + 1)) := tsum_mul_left
        _ = 2 * (1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i) := by rw [htail_w]
    have htail_lt : 1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i < ε := by
      have hdist := hN
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
        have := sum_le_hasSum (Finset.range (N + 1)) (fun i _ => (primeMeasureWeight_pos i).le)
          hasSum_primeMeasureWeight
        linarith)] at hdist
      exact hdist
    calc ‖z‖ * ‖∑' j : ℕ, (primeMeasureWeight (j + (N + 1)) : ℂ) /
          (1 - (a (j + (N + 1)) : ℂ) * z)‖
        ≤ (1 / 2) * (2 * (1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i)) :=
          mul_le_mul hzn htail_norm (norm_nonneg _) (by norm_num)
      _ = 1 - ∑ i ∈ Finset.range (N + 1), primeMeasureWeight i := by ring
      _ < ε := htail_lt
  -- Step 3: Uniform convergence of the product `A_seq * B_seq` to `A_lim * B_lim` on `K`
  have hprod_unif : TendstoUniformlyOn (fun N z => A_seq N z * B_seq N z)
      (fun z => A_lim z * B_lim z) atTop K := by
    have hA_bdd : ∃ MA : ℝ, 0 < MA ∧ ∀ z ∈ K, ‖A_lim z‖ ≤ MA := by
      obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn
        (Complex.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      exact ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
        fun z hz => (hM z hz).trans (le_max_left _ _)⟩
    obtain ⟨MA, hMA_pos, hMA⟩ := hA_bdd
    rw [Metric.tendstoUniformlyOn_iff] at hA_unif hB_unif ⊢
    intro ε hε
    filter_upwards [hA_unif (ε / 2) (half_pos hε),
      hB_unif (ε / (2 * MA)) (div_pos hε (by positivity))] with N hNA hNB z hz
    rw [dist_eq_norm]
    have hsplit : A_lim z * B_lim z - A_seq N z * B_seq N z =
        (A_lim z - A_seq N z) * B_seq N z + A_lim z * (B_lim z - B_seq N z) := by ring
    rw [hsplit]
    have h1 : ‖(A_lim z - A_seq N z) * B_seq N z‖ < ε / 2 := by
      rw [norm_mul]
      have hA_lt : ‖A_lim z - A_seq N z‖ < ε / 2 := by simpa [dist_eq_norm] using hNA z hz
      calc ‖A_lim z - A_seq N z‖ * ‖B_seq N z‖
          ≤ ‖A_lim z - A_seq N z‖ * 1 := mul_le_mul_of_nonneg_left (hB_seq_bdd N z hz) (norm_nonneg _)
        _ < ε / 2 := by linarith
    have h2 : ‖A_lim z * (B_lim z - B_seq N z)‖ < ε / 2 := by
      rw [norm_mul]
      have hB_lt : ‖B_lim z - B_seq N z‖ < ε / (2 * MA) := by simpa [dist_eq_norm] using hNB z hz
      calc ‖A_lim z‖ * ‖B_lim z - B_seq N z‖
          ≤ MA * ‖B_lim z - B_seq N z‖ := mul_le_mul_of_nonneg_right (hMA z hz) (norm_nonneg _)
        _ < MA * (ε / (2 * MA)) := mul_lt_mul_of_pos_left hB_lt hMA_pos
        _ = ε / 2 := by field_simp [hMA_pos.ne']
    calc ‖(A_lim z - A_seq N z) * B_seq N z + A_lim z * (B_lim z - B_seq N z)‖
        ≤ ‖(A_lim z - A_seq N z) * B_seq N z‖ + ‖A_lim z * (B_lim z - B_seq N z)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  -- Step 4: Identify `A_seq N z * B_seq N z` with `(massApproximant ...).eval z` on `K`
  have heq_on : ∀ N : ℕ, ∀ z ∈ K,
      A_seq N z * B_seq N z =
        (PrimePencil.massApproximant Real.pi (Finset.range (N + 1)) a primeMeasureWeight).eval z := by
    intro N z hz
    have hnz : ∀ i ∈ Finset.range (N + 1), 1 - (a i : ℂ) * z ≠ 0 := by
      intro i _
      have hd := hden_ge i z hz
      intro h0
      rw [h0, norm_zero] at hd
      linarith
    rw [PrimePencil.eval_massApproximant Real.pi (Finset.range (N + 1)) a primeMeasureWeight z hnz]
    have hprod_eq : (∏ j ∈ Finset.range (N + 1), (1 + (a j : ℂ) * z)) *
          (∏ j ∈ Finset.range (N + 1), (1 - (a j : ℂ) * z)) =
        ∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only [a, sineTerm]
      push_cast
      have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      field_simp [hj]
      ring
    dsimp only [A_seq, B_seq]
    calc (Real.pi : ℂ) * z * (∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j)) *
          (z * ∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z))
        = z ^ 2 * ((Real.pi : ℂ) * (∏ j ∈ Finset.range (N + 1), (1 + sineTerm z j)) *
            ∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)) := by ring
      _ = z ^ 2 * ((Real.pi : ℂ) * ((∏ j ∈ Finset.range (N + 1), (1 + (a j : ℂ) * z)) *
            (∏ j ∈ Finset.range (N + 1), (1 - (a j : ℂ) * z))) *
            ∑ i ∈ Finset.range (N + 1), (primeMeasureWeight i : ℂ) / (1 - (a i : ℂ) * z)) := by
          rw [hprod_eq]
      _ = _ := by ring
  have hmass_unif : TendstoUniformlyOn
      (fun N z => (PrimePencil.massApproximant Real.pi (Finset.range (N + 1)) a primeMeasureWeight).eval z)
      (fun z => A_lim z * B_lim z) atTop K :=
    hprod_unif.congr (Eventually.of_forall heq_on)
  exact (hmass_unif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn

/-- **Unconditional Sharp Lower Bound on Every Taylor Coefficient of `η(t)`**
(Codex's Positive-Spectrum Half-Plane Bound wired directly to `R_integral` and `etaCoeff`!):
For EVERY `m ≥ 2`, `2 * π^{m - 1} / (m - 2)! ≤ ‖etaCoeff m‖`. -/
theorem etaCoeff_lower_bound {m : ℕ} (hm : 2 ≤ m) :
    2 * Real.pi ^ (m - 1) / ((m - 2).factorial : ℝ) ≤ ‖etaCoeff m‖ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 2 := ⟨m - 2, by omega⟩
  have hbound := PrimePencil.massApproximant_factored_affine_bound Real.pi_pos
    (fun N => Finset.range (N + 1))
    (fun N => ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩)
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹)
    primeMeasureWeight
    (fun _ i _ => by positivity)
    (fun _ i _ => primeMeasureWeight_pos i)
    (hasSum_primeMeasureWeight.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    Metric.isOpen_ball (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
    tendstoLocallyUniformlyOn_primeMassApproximant k
  have hfn : (fun z : ℂ => -2 * I * Complex.exp (I * (Real.pi : ℂ) * z) *
      (Complex.sin ((Real.pi : ℂ) * z) * PakNthPrimeEngine.R_integral z)) = eta_integral :=
    funext fun z => (eta_integral_eq_sin_mul z).symm
  rw [hfn, ← etaCoeff_eq_iteratedDeriv (by omega : 2 ≤ k + 2)] at hbound
  simpa using hbound

/-- **Unconditional Non-Vanishing of EVERY Taylor Coefficient `c_m` (`m ≥ 2`) of `η(t)`**:
Every single Stokes displacement coefficient `etaCoeff m` (`m ≥ 2`) is strictly nonzero! -/
theorem etaCoeff_ne_zero {m : ℕ} (hm : 2 ≤ m) : etaCoeff m ≠ 0 := by
  intro h0
  have hlb := etaCoeff_lower_bound hm
  rw [h0, norm_zero] at hlb
  have hpos : 0 < 2 * Real.pi ^ (m - 1) / ((m - 2).factorial : ℝ) := by
    have := Real.pi_pos
    positivity
  linarith

end
end PakPrimes.PakNthPrimeStokes
