module

public import PakPrimes.PakNthPrimeStokes
public import PakPrimes.NthPrimeAbelError
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

/-! # Pak Conjecture 2.5a (`∑ p_n q^n`) — Closure of `hI_bound`, `hasymp`, and Sectorial Watson Reduction

This module attacks and discharges the remaining hypotheses of
`PakPrimes.PakNthPrimeStokes.pak_2_5a_of_stokes_bridge`:

1. **Unconditional discharge of `hI_bound` (`I_plus_poly_jet_bound`)**:
   - Holomorphicity of `T_integral` on `{t : ℂ | 0 < t.re ∧ t.re < 1}` and of the holomorphic
     extension `I_plus_holo z = R_integral (exp (-z)) + exp (-π i exp (-z)) * T_integral (exp (-z))`
     on the half-strip `halfStrip = {z : ℂ | 1/2 < z.re ∧ |z.im| < 1/2}`.
   - Sharp linear bound `‖T_integral (exp (-z))‖ ≤ C * (z.re + 1)` via exact integration by parts
     on `∫_1^M exp(x - σ Ei(x)) dx`.
   - Cauchy's iterated derivative estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`)
     on `sphere (u : ℂ) (1/4)` yielding `‖iteratedDeriv j I_plus u‖ ≤ CH * u ^ 1` for all `j` and `u ≥ 1`.
2. **Discharge of `hasymp` from `Main.PNTAllOrders` (`hasymp_of_pnt`)**:
   - Exact telescopic 4-piece comparison `nthPrimeSmoothRay → S_invLi → J_invLi → T(e^{-u}) → I_plus`.
   - Exponential jet decay `O(u e^{-u})` for the contour-to-real difference, the `li⁻¹` change-of-variables
     difference, and the Riemann-sum difference, combined with `NthPrime.prime_inverseLi_abelSumJetError`.
   - Polynomial jet-difference transfer `hasymp_of_jet_diff`.
3. **Watson / Phragmén–Lindelöf uniqueness on a sector of opening `> π` & `hbridge` reduction**:
   - Pure Mathlib complex-analytic proof of `watson_uniqueness_sector`, `watson_uniqueness_gevrey1`,
     and `watson_uniqueness_rotated_sector` (covering Codex's repaired sector `[-3π/4, π/3]`).
   - Complex-conjugation symmetry `I_minus u = star (I_plus u)` on `ℝ` and real-analyticity reduction,
     cutting the two-sided `hbridge` to a one-sided (or sectorial) criterion.
4. **Master export theorems** wiring directly into `PakNthPrimeStokes.pak_2_5a_of_stokes_bridge`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.PakNthPrimeClosure

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology BigOperators

noncomputable section

open PakPrimes.PakNthPrimeStokes

/-! ### 1. Holomorphicity of `T_integral`, Linear Strip Bound, and Unconditional `hI_bound` -/

/-- The inner positive-axis integral `∫_{x > 0} exp (x - t * Ei(x)) dx`. -/
@[expose] def T_inner (t : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))

lemma T_integral_eq_mul_T_inner (t : ℂ) : T_integral t = t * T_inner t := rfl

/-- Exact derivative of `Ei_real` on `(0, ∞)`: `Ei'(x) = exp x / x`. -/
theorem hasDerivAt_Ei_real {x : ℝ} (hx : 0 < x) :
    HasDerivAt Ei_real (Real.exp x / x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hein : HasDerivAt (fun y : ℝ => Ein_real (-y))
      (((1 - Real.exp (-(-x))) / (-x)) * (-1)) x :=
    (hasDerivAt_Ein_real (neg_ne_zero.mpr hx.ne')).comp x (hasDerivAt_id x).neg
  have htot := (hlog.const_add gammaE1).fun_sub hein
  refine htot.congr_deriv ?_
  rw [neg_neg]
  field_simp [hx.ne']
  ring

lemma continuousOn_Ei_real : ContinuousOn Ei_real (Set.Ioi (0 : ℝ)) :=
  fun _ hx => (hasDerivAt_Ei_real hx).continuousAt.continuousWithinAt

/-- Elementary upper bound on `|Ei_real x|` for `0 < x ≤ 1`. -/
lemma abs_Ei_real_le_small {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Ei_real x| ≤ |gammaE1| + Real.exp 1 + (-Real.log x) := by
  dsimp only [Ei_real]
  have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have hein : |Ein_real (-x)| ≤ Real.exp 1 := by
    have h1 : ‖Ein_complex ((-x : ℝ) : ℂ)‖ ≤ Real.exp ‖((-x : ℝ) : ℂ)‖ :=
      norm_Ein_complex_le _
    rw [Ein_complex_ofReal, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_pos hx0] at h1
    exact h1.trans (Real.exp_le_exp.mpr hx1)
  calc |gammaE1 + Real.log x - Ein_real (-x)|
      ≤ |gammaE1 + Real.log x| + |Ein_real (-x)| := abs_sub _ _
    _ ≤ (|gammaE1| + |Real.log x|) + Real.exp 1 := by
        linarith [abs_add_le gammaE1 (Real.log x)]
    _ = |gammaE1| + Real.exp 1 + (-Real.log x) := by
        rw [abs_of_nonpos hlog_nonpos]; ring

/-- Lower bound on `Ei_real x` for `x ≥ 1`: `gammaE1 - 2 + exp x / x ≤ Ei_real x`. -/
lemma Ei_real_ge_large {x : ℝ} (hx : 1 ≤ x) :
    gammaE1 - 2 + Real.exp x / x ≤ Ei_real x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hge := Ei_real_ge hx_pos
  have hdiv : (Real.exp x - 1 - x) / x = Real.exp x / x - 1 / x - 1 := by
    field_simp [hx_pos.ne']
  have h1x : 1 / x ≤ 1 := by rw [div_le_one hx_pos]; exact hx
  linarith

/-- Uniform norm identity for the `T_inner` integrand. -/
lemma norm_cexp_sub_mul_Ei_real (t : ℂ) (x : ℝ) :
    ‖Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖ =
      Real.exp (x - t.re * Ei_real x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Global integrability of `x ↦ exp (x - σ * Ei_real x)` on `(0, ∞)` for `0 < σ < 1`. -/
lemma integrableOn_exp_sub_mul_Ei_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    IntegrableOn (fun x : ℝ => Real.exp (x - σ * Ei_real x)) (Set.Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => ‖Complex.exp ((x : ℂ) - (σ : ℂ) * (Ei_real x : ℂ))‖) (Set.Ioi 0) :=
    (integrableOn_T_integrand (t := (σ : ℂ)) (by simpa using h0) (by simpa using h1)).norm
  exact h.congr_fun (fun x _ => by dsimp only; rw [norm_cexp_sub_mul_Ei_real, Complex.ofReal_re]) measurableSet_Ioi

/-- Dominated differentiation under the integral sign for `T_inner` on `{0 < Re t < 1}`. -/
theorem hasDerivAt_T_inner {t₀ : ℂ} (h0 : 0 < t₀.re) (h1 : t₀.re < 1) :
    HasDerivAt T_inner
      (∫ x in Set.Ioi (0 : ℝ),
        -(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t₀ * (Ei_real x : ℂ)))
      t₀ := by
  let r : ℝ := min (t₀.re / 4) ((1 - t₀.re) / 4)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  let σ_lo : ℝ := t₀.re - r
  let σ_hi : ℝ := t₀.re + r
  have hσ_lo_pos : 0 < σ_lo := by
    have : r ≤ t₀.re / 4 := min_le_left _ _
    dsimp [σ_lo]; linarith
  have hσ_hi_lt : σ_hi < 1 := by
    have : r ≤ (1 - t₀.re) / 4 := min_le_right _ _
    dsimp [σ_hi]; linarith
  let δ1 : ℝ := (1 - σ_hi) / 2
  have hδ1 : 0 < δ1 := by dsimp [δ1]; linarith
  let α1 : ℝ := σ_hi + δ1
  have hα1_lt : α1 < 1 := by dsimp [α1, δ1]; linarith
  let δ2 : ℝ := σ_lo / 2
  have hδ2 : 0 < δ2 := by dsimp [δ2]; linarith
  let B : ℝ := |gammaE1 - 2|
  let K1 : ℝ := (|gammaE1| + Real.exp 1 + δ1⁻¹) * Real.exp (1 + |gammaE1|)
  let K2 : ℝ := (B * Real.exp (δ2 * B) + δ2⁻¹) * Real.exp B
  let bound : ℝ → ℝ := fun x =>
    if x ≤ 1 then K1 * x ^ (-α1) else K2 * Real.exp (x - δ2 * Ei_real x)
  have hbound_int : IntegrableOn bound (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
    constructor
    · have hrpow : IntegrableOn (fun x : ℝ => K1 * x ^ (-α1)) (Set.Ioc 0 1) :=
        (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.const_mul K1
      exact hrpow.congr_fun (fun x hx => by simp [bound, hx.2]) measurableSet_Ioc
    · have hexp : IntegrableOn (fun x : ℝ => K2 * Real.exp (x - δ2 * Ei_real x)) (Set.Ioi 1) :=
        ((integrableOn_exp_sub_mul_Ei_real hδ2 (by dsimp [δ2, σ_lo]; linarith)).mono_set
          (Set.Ioi_subset_Ioi zero_le_one)).const_mul K2
      exact hexp.congr_fun (fun x hx => by simp [bound, not_le.mpr (Set.mem_Ioi.mp hx)]) measurableSet_Ioi
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable
        (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
    refine Eventually.of_forall fun t => ?_
    have hc : ContinuousOn (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) (Set.Ioi 0) :=
      Complex.continuous_exp.comp_continuousOn
        (Complex.continuous_ofReal.continuousOn.sub
          (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn continuousOn_Ei_real)))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => -(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t₀ * (Ei_real x : ℂ)))
      (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn
        (fun x : ℝ => -(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t₀ * (Ei_real x : ℂ))) (Set.Ioi 0) :=
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_Ei_real).neg.mul
        (Complex.continuous_exp.comp_continuousOn
          (Complex.continuous_ofReal.continuousOn.sub
            (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn continuousOn_Ei_real))))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hbound_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ∀ t ∈ Metric.ball t₀ r,
      ‖-(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have hdist : ‖t - t₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    have hre_abs : |t.re - t₀.re| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (t - t₀)) hdist
    have htre_lo : σ_lo ≤ t.re := by dsimp [σ_lo]; linarith [(abs_lt.mp hre_abs).1]
    have htre_hi : t.re ≤ σ_hi := by dsimp [σ_hi]; linarith [(abs_lt.mp hre_abs).2]
    have htre_pos : 0 < t.re := lt_of_lt_of_le hσ_lo_pos htre_lo
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_cexp_sub_mul_Ei_real]
    dsimp only [bound]
    split_ifs with hx1
    · have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
      have hlog_le : -Real.log x ≤ δ1⁻¹ * x ^ (-δ1) := by
        have h1 : δ1 * (-Real.log x) ≤ Real.exp (δ1 * (-Real.log x)) :=
          le_trans (by linarith) (Real.add_one_le_exp _)
        have h2 : Real.exp (δ1 * (-Real.log x)) = x ^ (-δ1) := by
          rw [Real.rpow_def_of_pos hx]; congr 1; ring
        rw [h2] at h1
        rw [← div_eq_inv_mul, le_div_iff₀ hδ1, mul_comm]
        exact h1
      have h1_le_rpow : (1 : ℝ) ≤ x ^ (-δ1) := by
        rw [Real.rpow_def_of_pos hx]
        exact Real.one_le_exp (by nlinarith)
      have hEi_abs : |Ei_real x| ≤ (|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1) := by
        have hsmall := abs_Ei_real_le_small hx hx1
        have hnn : 0 ≤ |gammaE1| + Real.exp 1 := by positivity
        calc |Ei_real x| ≤ |gammaE1| + Real.exp 1 + (-Real.log x) := hsmall
          _ ≤ (|gammaE1| + Real.exp 1) * x ^ (-δ1) + δ1⁻¹ * x ^ (-δ1) := by nlinarith
          _ = (|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1) := by ring
      have hge := Ei_real_ge_log hx
      have harg : x - t.re * Ei_real x ≤ (1 + |gammaE1|) + (-σ_hi) * Real.log x := by
        have hg : -t.re * gammaE1 ≤ |gammaE1| := by
          have ht1 : t.re ≤ 1 := by linarith
          calc -t.re * gammaE1 ≤ |-t.re * gammaE1| := le_abs_self _
            _ = t.re * |gammaE1| := by rw [abs_mul, abs_neg, abs_of_pos htre_pos]
            _ ≤ 1 * |gammaE1| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
            _ = |gammaE1| := one_mul _
        nlinarith [hx1, htre_hi, hlog_nonpos]
      have hexp_le : Real.exp (x - t.re * Ei_real x) ≤ Real.exp (1 + |gammaE1|) * x ^ (-σ_hi) := by
        calc Real.exp (x - t.re * Ei_real x)
            ≤ Real.exp ((1 + |gammaE1|) + (-σ_hi) * Real.log x) := Real.exp_le_exp.mpr harg
          _ = Real.exp (1 + |gammaE1|) * Real.exp ((-σ_hi) * Real.log x) := Real.exp_add _ _
          _ = Real.exp (1 + |gammaE1|) * x ^ (-σ_hi) := by
              rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
      calc |Ei_real x| * Real.exp (x - t.re * Ei_real x)
          ≤ ((|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1)) *
              (Real.exp (1 + |gammaE1|) * x ^ (-σ_hi)) :=
            mul_le_mul hEi_abs hexp_le (Real.exp_pos _).le (by positivity)
        _ = K1 * (x ^ (-σ_hi) * x ^ (-δ1)) := by dsimp [K1]; ring
        _ = K1 * x ^ (-α1) := by
            rw [← Real.rpow_add hx]; congr 2; dsimp [α1]; ring
    · push Not at hx1
      have hge_large := Ei_real_ge_large hx1.le
      have hB_le : -B ≤ Ei_real x := by
        have hexp_nn : 0 ≤ Real.exp x / x := by positivity
        have h1 : -B ≤ gammaE1 - 2 := neg_abs_le _
        linarith
      have hEi_abs : |Ei_real x| ≤ (B * Real.exp (δ2 * B) + δ2⁻¹) * Real.exp (δ2 * Ei_real x) := by
        have h1 : (1 : ℝ) ≤ Real.exp (δ2 * B) * Real.exp (δ2 * Ei_real x) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        have h2 : Ei_real x ≤ δ2⁻¹ * Real.exp (δ2 * Ei_real x) := by
          rw [← div_eq_inv_mul, le_div_iff₀ hδ2, mul_comm]
          exact le_trans (by linarith) (Real.add_one_le_exp _)
        by_cases hsign : 0 ≤ Ei_real x
        · rw [abs_of_nonneg hsign]
          nlinarith [Real.exp_pos (δ2 * B), Real.exp_pos (δ2 * Ei_real x), abs_nonneg (gammaE1 - 2)]
        · push Not at hsign
          rw [abs_of_neg hsign]
          have hleB : -Ei_real x ≤ B := by linarith
          nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (gammaE1 - 2)),
            Real.exp_pos (δ2 * Ei_real x), inv_pos.mpr hδ2]
      have hsub_nn : 0 ≤ t.re - 2 * δ2 := by dsimp [δ2]; linarith
      have hsub_le1 : t.re - 2 * δ2 ≤ 1 := by dsimp [δ2]; linarith
      have hshift : -(t.re - 2 * δ2) * Ei_real x ≤ B := by
        have h1 : -(t.re - 2 * δ2) * Ei_real x ≤ (t.re - 2 * δ2) * B := by nlinarith
        have h2 : (t.re - 2 * δ2) * B ≤ 1 * B := mul_le_mul_of_nonneg_right hsub_le1 (abs_nonneg _)
        linarith
      have hexp_prod : Real.exp (δ2 * Ei_real x) * Real.exp (x - t.re * Ei_real x) ≤
          Real.exp B * Real.exp (x - δ2 * Ei_real x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc |Ei_real x| * Real.exp (x - t.re * Ei_real x)
          ≤ ((B * Real.exp (δ2 * B) + δ2⁻¹) * Real.exp (δ2 * Ei_real x)) *
              Real.exp (x - t.re * Ei_real x) :=
            mul_le_mul_of_nonneg_right hEi_abs (Real.exp_pos _).le
        _ = (B * Real.exp (δ2 * B) + δ2⁻¹) *
              (Real.exp (δ2 * Ei_real x) * Real.exp (x - t.re * Ei_real x)) := by ring
        _ ≤ (B * Real.exp (δ2 * B) + δ2⁻¹) * (Real.exp B * Real.exp (x - δ2 * Ei_real x)) :=
            mul_le_mul_of_nonneg_left hexp_prod (by positivity)
        _ = K2 * Real.exp (x - δ2 * Ei_real x) := by dsimp [K2]; ring
  have hdiff_ae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ t ∈ Metric.ball t₀ r,
      HasDerivAt (fun z : ℂ => Complex.exp ((x : ℂ) - z * (Ei_real x : ℂ)))
        (-(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) t := by
    filter_upwards with x t _
    have h1 : HasDerivAt (fun z : ℂ => (x : ℂ) - z * (Ei_real x : ℂ)) (-(Ei_real x : ℂ)) t := by
      have hmul : HasDerivAt (fun z : ℂ => z * (Ei_real x : ℂ)) (Ei_real x : ℂ) t := by
        simpa using (hasDerivAt_id t).mul_const (Ei_real x : ℂ)
      exact hmul.const_sub (x : ℂ)
    convert h1.cexp using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hr)
    hF_meas (integrableOn_T_integrand h0 h1) hF'_meas hbound_ae hbound_int hdiff_ae).2

/-- **Holomorphicity of `T_integral`** on the open strip `{t : ℂ | 0 < t.re ∧ t.re < 1}`. -/
theorem differentiableOn_T_integral :
    DifferentiableOn ℂ T_integral {t : ℂ | 0 < t.re ∧ t.re < 1} := fun t ht =>
  ((hasDerivAt_id t).mul (hasDerivAt_T_inner ht.1 ht.2)).differentiableAt.differentiableWithinAt

/-- Open half-strip `{z : ℂ | 1/2 < Re z ∧ |Im z| < 1/2}` on which `I_plus` extends holomorphically. -/
@[expose] def halfStrip : Set ℂ := {z : ℂ | (1 / 2 : ℝ) < z.re ∧ |z.im| < 1 / 2}

lemma isOpen_halfStrip : IsOpen halfStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

/-- For `|θ| ≤ 1/2`, `1/2 ≤ cos θ`. -/
lemma half_le_cos_of_abs_le_half {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hpi3 : (1 / 2 : ℝ) ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
  have habs_le : |θ| ≤ Real.pi / 3 := hθ.trans hpi3
  have hcos : Real.cos (Real.pi / 3) ≤ Real.cos |θ| :=
    Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg θ, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ habs_le
  rw [Real.cos_pi_div_three, Real.cos_abs] at hcos
  exact hcos

lemma exp_neg_half_lt_three_fourths : Real.exp (-(1 / 2 : ℝ)) < 3 / 4 := by
  have h1 : (1 + (1 / 2 : ℝ)) ≤ Real.exp (1 / 2 : ℝ) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  rw [inv_lt_comm₀ hpos (by norm_num : (0 : ℝ) < 3 / 4)]
  norm_num at h1 ⊢
  linarith

/-- Mapping properties of `z ↦ exp (-z)` on the closed strip `{1/2 ≤ Re z ∧ |Im z| ≤ 1/2}`. -/
lemma exp_neg_strip_bounds {z : ℂ} (hre : (1 / 2 : ℝ) ≤ z.re) (him : |z.im| ≤ 1 / 2) :
    (1 / 2 : ℝ) * Real.exp (-z.re) ≤ (Complex.exp (-z)).re ∧
    (Complex.exp (-z)).re ≤ Real.exp (-z.re) ∧
    (Complex.exp (-z)).re < 3 / 4 ∧
    ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
  have hnorm : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    rw [Complex.norm_exp, Complex.neg_re]
  have hre_eq : (Complex.exp (-z)).re = Real.exp (-z.re) * Real.cos z.im := by
    rw [Complex.exp_re, Complex.neg_re, Complex.neg_im, Real.cos_neg]
  have hcos_lo : (1 / 2 : ℝ) ≤ Real.cos z.im := half_le_cos_of_abs_le_half him
  have hcos_hi : Real.cos z.im ≤ 1 := Real.cos_le_one z.im
  have hexp_pos : 0 < Real.exp (-z.re) := Real.exp_pos _
  have hlo : (1 / 2 : ℝ) * Real.exp (-z.re) ≤ (Complex.exp (-z)).re := by
    rw [hre_eq]; nlinarith
  have hhi : (Complex.exp (-z)).re ≤ Real.exp (-z.re) := by
    rw [hre_eq]; nlinarith
  have hlt : (Complex.exp (-z)).re < 3 / 4 :=
    lt_of_le_of_lt (hhi.trans (Real.exp_le_exp.mpr (by linarith))) exp_neg_half_lt_three_fourths
  exact ⟨hlo, hhi, hlt, hnorm⟩

/-- Holomorphic extension of `I_plus` to `halfStrip`. -/
@[expose] def I_plus_holo (z : ℂ) : ℂ :=
  PakNthPrimeEngine.R_integral (Complex.exp (-z)) +
    Complex.exp (-Real.pi * I * Complex.exp (-z)) * T_integral (Complex.exp (-z))

lemma I_plus_holo_ofReal {u : ℝ} (hu : 0 < u) : I_plus_holo (u : ℂ) = I_plus u := by
  rw [I_plus_eq_R_add_T hu]
  dsimp only [I_plus_holo]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]

theorem differentiableOn_I_plus_holo : DifferentiableOn ℂ I_plus_holo halfStrip := by
  intro z hz
  have hb := exp_neg_strip_bounds hz.1.le hz.2.le
  have ht0 : 0 < (Complex.exp (-z)).re := lt_of_lt_of_le (by positivity) hb.1
  have ht1 : (Complex.exp (-z)).re < 1 := by linarith [hb.2.2.1]
  have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w)) z :=
    Complex.differentiable_exp.comp differentiable_id.neg |>.differentiableAt
  have hR_open : IsOpen {t : ℂ | t.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hR : DifferentiableAt ℂ (fun w : ℂ => PakNthPrimeEngine.R_integral (Complex.exp (-w))) z :=
    show DifferentiableAt ℂ (PakNthPrimeEngine.R_integral ∘ fun w : ℂ => Complex.exp (-w)) z from
      (R_holomorphic_on_halfplane.differentiableAt (hR_open.mem_nhds ht1)).comp z hexp
  have hT_open : IsOpen {t : ℂ | 0 < t.re ∧ t.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter hR_open
  have hT : DifferentiableAt ℂ (fun w : ℂ => T_integral (Complex.exp (-w))) z :=
    show DifferentiableAt ℂ (T_integral ∘ fun w : ℂ => Complex.exp (-w)) z from
      (differentiableOn_T_integral.differentiableAt (hT_open.mem_nhds ⟨ht0, ht1⟩)).comp z hexp
  have hfac : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-Real.pi * I * Complex.exp (-w))) z :=
    (Complex.differentiable_exp.differentiableAt).comp _ (hexp.const_mul _)
  exact (hR.add (hfac.mul hT)).differentiableWithinAt

/-- Exponential bound on `R_integral (exp (-z))` on `{Re z ≥ 1/2}`. -/
lemma exists_norm_R_integral_exp_neg_le :
    ∃ C_R > 0, ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re →
      ‖PakNthPrimeEngine.R_integral (Complex.exp (-z))‖ ≤ C_R * Real.exp (-z.re) := by
  let I₀ : ℝ := ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + (3 / 4 : ℝ) * PakNthPrimeEngine.E1 x)
  have hI₀_nn : 0 ≤ I₀ :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => (Real.exp_pos _).le
  refine ⟨I₀ + 1, by linarith, fun z hz => ?_⟩
  rw [R_integral_eq_mul_R_inner, norm_mul, Complex.norm_exp, Complex.neg_re]
  have ht_re : (Complex.exp (-z)).re ≤ 3 / 4 := by
    have h1 : (Complex.exp (-z)).re ≤ ‖Complex.exp (-z)‖ := Complex.re_le_norm _
    rw [Complex.norm_exp, Complex.neg_re] at h1
    exact (h1.trans (Real.exp_le_exp.mpr (by linarith))).trans exp_neg_half_lt_three_fourths.le
  have hR_le : ‖R_inner (Complex.exp (-z))‖ ≤ I₀ := by
    dsimp only [R_inner, I₀]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (integrableOn_cexp_neg_add_mul_E1 (by linarith)).norm
      (integrableOn_exp_neg_add_mul_E1 (by norm_num : (3 / 4 : ℝ) < 1)) measurableSet_Ioi ?_
    intro x hx
    rw [norm_cexp_neg_add_mul_E1]
    exact Real.exp_le_exp.mpr (by nlinarith [E1_pos hx])
  calc Real.exp (-z.re) * ‖R_inner (Complex.exp (-z))‖
      ≤ Real.exp (-z.re) * (I₀ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = (I₀ + 1) * Real.exp (-z.re) := mul_comm _ _

/-- Elementary inequality `exp (x / 2) / 2 ≤ exp x / x` for all `x > 0`. -/
lemma half_exp_half_le_exp_div {x : ℝ} (hx : 0 < x) :
    Real.exp (x / 2) / 2 ≤ Real.exp x / x := by
  have h1 : x / 2 ≤ Real.exp (x / 2) := le_trans (by linarith) (Real.add_one_le_exp (x / 2))
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hx]
  have hexp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  nlinarith [Real.exp_pos (x / 2)]

/-- Sharp linear bound on `T_integral (exp (-z))` on `{1/2 ≤ Re z, |Im z| ≤ 1/2}` via exact IBP! -/
theorem exists_norm_T_integral_exp_neg_le :
    ∃ C_T > 0, ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → |z.im| ≤ 1 / 2 →
      ‖T_integral (Complex.exp (-z))‖ ≤ C_T * (z.re + 1) := by
  let I₁ : ℝ := ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-(3 / 4 : ℝ))
  have hI₁_nn : 0 ≤ I₁ :=
    setIntegral_nonneg measurableSet_Ioc fun x hx => Real.rpow_nonneg hx.1.le _
  let C₀ : ℝ := Real.exp (1 + |gammaE1|) * I₁
  let B : ℝ := |gammaE1 - 2|
  let C₁ : ℝ := Real.exp |Ei_real 1|
  let C₂ : ℝ := Real.exp B
  let C_T : ℝ := C₀ + 2 * (C₁ + 21 * C₂) + 8 * C₂ + 1
  have hCT : 0 < C_T := by dsimp [C_T, C₀, C₁, C₂]; positivity
  refine ⟨C_T, hCT, fun z hre him => ?_⟩
  set t : ℂ := Complex.exp (-z)
  set σ : ℝ := t.re
  have hb := exp_neg_strip_bounds hre him
  have hσ_lo : (1 / 2 : ℝ) * Real.exp (-z.re) ≤ σ := hb.1
  have hσ_hi : σ ≤ Real.exp (-z.re) := hb.2.1
  have hσ_lt : σ < 3 / 4 := hb.2.2.1
  have ht_norm : ‖t‖ = Real.exp (-z.re) := hb.2.2.2
  have hσ_pos : 0 < σ := lt_of_lt_of_le (by positivity) hσ_lo
  have hσ_lt1 : σ < 1 := by linarith
  have ht_le_2σ : ‖t‖ ≤ 2 * σ := by rw [ht_norm]; linarith
  have hint := integrableOn_T_integrand hσ_pos hσ_lt1
  have hsplit : T_inner t =
      (∫ x in Set.Ioc (0 : ℝ) 1, Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) +
      (∫ x in Set.Ioi (1 : ℝ), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) := by
    dsimp only [T_inner]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self)
        (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  have hsmall : ‖∫ x in Set.Ioc (0 : ℝ) 1, Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖ ≤ C₀ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hrpow : IntegrableOn (fun x : ℝ => Real.exp (1 + |gammaE1|) * x ^ (-(3 / 4 : ℝ))) (Set.Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).1.const_mul _
    calc (∫ x in Set.Ioc (0 : ℝ) 1, ‖Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖)
        ≤ ∫ x in Set.Ioc (0 : ℝ) 1, Real.exp (1 + |gammaE1|) * x ^ (-(3 / 4 : ℝ)) := by
          refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self).norm hrpow
            measurableSet_Ioc fun x hx => ?_
          rw [norm_cexp_sub_mul_Ei_real]
          have hge := Ei_real_ge_log hx.1
          have hlog_np : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
          have hg : -σ * gammaE1 ≤ |gammaE1| := by
            calc -σ * gammaE1 ≤ |-σ * gammaE1| := le_abs_self _
              _ = σ * |gammaE1| := by rw [abs_mul, abs_neg, abs_of_pos hσ_pos]
              _ ≤ 1 * |gammaE1| := mul_le_mul_of_nonneg_right hσ_lt1.le (abs_nonneg _)
              _ = |gammaE1| := one_mul _
          have harg : x - σ * Ei_real x ≤ (1 + |gammaE1|) + (-(3 / 4 : ℝ)) * Real.log x := by
            nlinarith [hx.2]
          calc Real.exp (x - σ * Ei_real x)
              ≤ Real.exp ((1 + |gammaE1|) + (-(3 / 4 : ℝ)) * Real.log x) := Real.exp_le_exp.mpr harg
            _ = Real.exp (1 + |gammaE1|) * Real.exp ((-(3 / 4 : ℝ)) * Real.log x) := Real.exp_add _ _
            _ = Real.exp (1 + |gammaE1|) * x ^ (-(3 / 4 : ℝ)) := by
                rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]
      _ = C₀ := by rw [integral_const_mul]
  -- Large part via exact FTC on [1, M] and M → ∞
  let X : ℝ := 4 * (z.re + 5)
  have hX_ge : 1 ≤ X := by dsimp [X]; linarith
  have htail_bound : ∀ x : ℝ, X ≤ x → Real.exp (-σ * Ei_real x) ≤ C₂ * Real.exp (-x) := by
    intro x hx
    have hx1 : 1 ≤ x := hX_ge.trans hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hge := Ei_real_ge_large hx1
    have hexp5 : (32 : ℝ) ≤ Real.exp 5 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hpow : (2 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      exact hpow
    have hσ_exp4 : (16 : ℝ) ≤ σ * Real.exp (x / 4) := by
      have harg : 5 ≤ -z.re + x / 4 := by dsimp [X] at hx; linarith
      calc (16 : ℝ) = (1 / 2 : ℝ) * 32 := by norm_num
        _ ≤ (1 / 2 : ℝ) * Real.exp 5 := by linarith
        _ ≤ (1 / 2 : ℝ) * Real.exp (-z.re + x / 4) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
        _ = ((1 / 2 : ℝ) * Real.exp (-z.re)) * Real.exp (x / 4) := by rw [Real.exp_add]; ring
        _ ≤ σ * Real.exp (x / 4) := mul_le_mul_of_nonneg_right hσ_lo (Real.exp_pos _).le
    have hlin : x / 4 ≤ Real.exp (x / 4) := le_trans (by linarith) (Real.add_one_le_exp (x / 4))
    have hhalf := half_exp_half_le_exp_div hx_pos
    have hprod : 2 * x ≤ σ * (Real.exp x / x) := by
      have hexp2 : Real.exp (x / 2) = Real.exp (x / 4) * Real.exp (x / 4) := by
        rw [← Real.exp_add]; congr 1; ring
      calc 2 * x = (1 / 2 : ℝ) * (16 * (x / 4)) := by ring
        _ ≤ (1 / 2 : ℝ) * ((σ * Real.exp (x / 4)) * Real.exp (x / 4)) := by
            have hmul := mul_le_mul hσ_exp4 hlin (by positivity) (by positivity)
            linarith
        _ = σ * (Real.exp (x / 2) / 2) := by rw [hexp2]; ring
        _ ≤ σ * (Real.exp x / x) := mul_le_mul_of_nonneg_left hhalf hσ_pos.le
    have hnegB : -σ * (gammaE1 - 2) ≤ B := by
      calc -σ * (gammaE1 - 2) ≤ |-σ * (gammaE1 - 2)| := le_abs_self _
        _ = σ * B := by rw [abs_mul, abs_neg, abs_of_pos hσ_pos]
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right hσ_lt1.le (abs_nonneg _)
        _ = B := one_mul _
    have harg : -σ * Ei_real x ≤ B + (-x) := by nlinarith
    calc Real.exp (-σ * Ei_real x) ≤ Real.exp (B + (-x)) := Real.exp_le_exp.mpr harg
      _ = C₂ * Real.exp (-x) := Real.exp_add _ _
  have hbulk_bound : ∀ x : ℝ, 1 ≤ x → Real.exp (-σ * Ei_real x) ≤ C₂ := by
    intro x hx1
    have hge := Ei_real_ge_large hx1
    have hexp_nn : 0 ≤ Real.exp x / x := by positivity
    have hnegB : -σ * (gammaE1 - 2) ≤ B := by
      calc -σ * (gammaE1 - 2) ≤ |-σ * (gammaE1 - 2)| := le_abs_self _
        _ = σ * B := by rw [abs_mul, abs_neg, abs_of_pos hσ_pos]
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right hσ_lt1.le (abs_nonneg _)
        _ = B := one_mul _
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hM_bound : ∀ M : ℝ, 1 ≤ M →
      σ * ∫ x in (1 : ℝ)..M, Real.exp (x - σ * Ei_real x) ≤ C₁ + C₂ * (X + 1) := by
    intro M hM
    have hF_deriv : ∀ x ∈ Set.uIcc (1 : ℝ) M,
        HasDerivAt (fun y : ℝ => -y * Real.exp (-σ * Ei_real y))
          (σ * Real.exp (x - σ * Ei_real x) - Real.exp (-σ * Ei_real x)) x := by
      intro x hx
      rw [Set.uIcc_of_le hM] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      have hEi := hasDerivAt_Ei_real hx_pos
      have hexp := (hEi.const_mul (-σ)).exp
      have hmul := (hasDerivAt_id x).neg.mul hexp
      refine hmul.congr_deriv ?_
      have hsub : Real.exp (x - σ * Ei_real x) = Real.exp x * Real.exp (-σ * Ei_real x) := by
        rw [sub_eq_add_neg, ← neg_mul, Real.exp_add]
      rw [hsub]
      simp only [Pi.neg_apply, id_eq]
      field_simp [hx_pos.ne']
      ring
    have hcont1 : ContinuousOn (fun x : ℝ => Real.exp (x - σ * Ei_real x)) (Set.uIcc (1 : ℝ) M) := by
      rw [Set.uIcc_of_le hM]
      exact Real.continuous_exp.comp_continuousOn
        (continuousOn_id.sub (continuousOn_const.mul
          (continuousOn_Ei_real.mono fun x hx => lt_of_lt_of_le zero_lt_one hx.1)))
    have hcont2 : ContinuousOn (fun x : ℝ => Real.exp (-σ * Ei_real x)) (Set.uIcc (1 : ℝ) M) := by
      rw [Set.uIcc_of_le hM]
      exact Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_Ei_real.mono fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
      ((hcont1.const_mul σ).sub hcont2).intervalIntegrable
    rw [intervalIntegral.integral_sub (hcont1.const_mul σ).intervalIntegrable hcont2.intervalIntegrable,
      intervalIntegral.integral_const_mul] at hftc
    have hbdry : -M * Real.exp (-σ * Ei_real M) - (-1 * Real.exp (-σ * Ei_real 1)) ≤ C₁ := by
      have hM_np : -M * Real.exp (-σ * Ei_real M) ≤ 0 := by nlinarith [Real.exp_pos (-σ * Ei_real M)]
      have h1_le : Real.exp (-σ * Ei_real 1) ≤ C₁ := by
        apply Real.exp_le_exp.mpr
        calc -σ * Ei_real 1 ≤ |-σ * Ei_real 1| := le_abs_self _
          _ = σ * |Ei_real 1| := by rw [abs_mul, abs_neg, abs_of_pos hσ_pos]
          _ ≤ 1 * |Ei_real 1| := mul_le_mul_of_nonneg_right hσ_lt1.le (abs_nonneg _)
          _ = |Ei_real 1| := one_mul _
      linarith
    have hint2_le : ∫ x in (1 : ℝ)..M, Real.exp (-σ * Ei_real x) ≤ C₂ * (X + 1) := by
      let g : ℝ → ℝ := fun x => if x ≤ X then C₂ else C₂ * Real.exp (-x)
      have hg_int_Ioc : IntegrableOn (fun x : ℝ => if x ≤ X then C₂ else C₂ * Real.exp (-x)) (Set.Ioi 1) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi hX_ge, integrableOn_union]
        constructor
        · exact (integrableOn_const (C := C₂) (hs := measure_Ioc_lt_top.ne)).congr_fun
            (fun x hx => by simp [hx.2]) measurableSet_Ioc
        · have hexp : IntegrableOn (fun x : ℝ => C₂ * Real.exp (-x)) (Set.Ioi X) :=
            ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) X).congr_fun
              (fun x _ => by simp) measurableSet_Ioi).const_mul C₂
          exact hexp.congr_fun (fun x hx => by simp [not_le.mpr (Set.mem_Ioi.mp hx)]) measurableSet_Ioi
      have hg_int_val : ∫ x in Set.Ioi (1 : ℝ), g x ≤ C₂ * (X + 1) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi hX_ge,
          setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hg_int_Ioc.mono_set Set.Ioc_subset_Ioi_self)
            (hg_int_Ioc.mono_set (Set.Ioi_subset_Ioi hX_ge))]
        have hpart1 : ∫ x in Set.Ioc (1 : ℝ) X, g x = C₂ * (X - 1) := by
          have hcongr : (∫ x in Set.Ioc (1 : ℝ) X, g x) = ∫ _ in Set.Ioc (1 : ℝ) X, C₂ :=
            setIntegral_congr_fun measurableSet_Ioc fun x hx => by simp [g, hx.2]
          rw [hcongr, setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith)]
          ring
        have hpart2 : ∫ x in Set.Ioi X, g x = C₂ * Real.exp (-X) := by
          have hcongr : (∫ x in Set.Ioi X, g x) = ∫ x in Set.Ioi X, C₂ * Real.exp (-x) :=
            setIntegral_congr_fun measurableSet_Ioi fun x hx => by
              simp [g, not_le.mpr (Set.mem_Ioi.mp hx)]
          rw [hcongr, integral_const_mul]
          have he : ∫ x in Set.Ioi X, Real.exp (-x) = Real.exp (-X) := by
            have := integral_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) X
            simpa using this
          rw [he]
        rw [hpart1, hpart2]
        have hexp_le1 : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        nlinarith [Real.exp_pos B]
      have hmono : ∫ x in (1 : ℝ)..M, Real.exp (-σ * Ei_real x) ≤ ∫ x in Set.Ioc (1 : ℝ) M, g x := by
        rw [intervalIntegral.integral_of_le hM]
        rw [Set.uIcc_of_le hM] at hcont2
        refine setIntegral_mono_on (hcont2.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          (hg_int_Ioc.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun x hx => ?_
        dsimp only [g]
        split_ifs with hxX
        · exact hbulk_bound x hx.1.le
        · exact htail_bound x (le_of_not_ge hxX)
      have hsub : ∫ x in Set.Ioc (1 : ℝ) M, g x ≤ ∫ x in Set.Ioi (1 : ℝ), g x := by
        refine setIntegral_mono_set hg_int_Ioc ?_ (Eventually.of_forall Set.Ioc_subset_Ioi_self)
        filter_upwards with x
        dsimp only [g]; split_ifs <;> positivity
      exact (hmono.trans hsub).trans hg_int_val
    linarith
  have hlarge_real : σ * ∫ x in Set.Ioi (1 : ℝ), Real.exp (x - σ * Ei_real x) ≤ C₁ + C₂ * (X + 1) := by
    have hint_large : IntegrableOn (fun x : ℝ => Real.exp (x - σ * Ei_real x)) (Set.Ioi 1) :=
      (integrableOn_exp_sub_mul_Ei_real hσ_pos hσ_lt1).mono_set (Set.Ioi_subset_Ioi zero_le_one)
    have htend : Tendsto (fun M : ℝ => σ * ∫ x in (1 : ℝ)..M, Real.exp (x - σ * Ei_real x))
        atTop (𝓝 (σ * ∫ x in Set.Ioi (1 : ℝ), Real.exp (x - σ * Ei_real x))) :=
      (intervalIntegral_tendsto_integral_Ioi 1 hint_large tendsto_id).const_mul σ
    exact le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, hM_bound⟩)
  have hlarge : ‖∫ x in Set.Ioi (1 : ℝ), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖ ≤
      (C₁ + C₂ * (X + 1)) / σ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have heq : (∫ x in Set.Ioi (1 : ℝ), ‖Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖) =
        ∫ x in Set.Ioi (1 : ℝ), Real.exp (x - σ * Ei_real x) :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => norm_cexp_sub_mul_Ei_real t x
    rw [heq, le_div_iff₀ hσ_pos, mul_comm]
    exact hlarge_real
  have hT_le : ‖T_integral t‖ ≤ ‖t‖ * C₀ + 2 * (C₁ + C₂ * (X + 1)) := by
    rw [T_integral_eq_mul_T_inner, norm_mul, hsplit]
    have htri : ‖(∫ x in Set.Ioc (0 : ℝ) 1, Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) +
        (∫ x in Set.Ioi (1 : ℝ), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ)))‖ ≤
        C₀ + (C₁ + C₂ * (X + 1)) / σ :=
      (norm_add_le _ _).trans (add_le_add hsmall hlarge)
    calc ‖t‖ * ‖_ + _‖ ≤ ‖t‖ * (C₀ + (C₁ + C₂ * (X + 1)) / σ) :=
          mul_le_mul_of_nonneg_left htri (norm_nonneg t)
      _ = ‖t‖ * C₀ + (‖t‖ / σ) * (C₁ + C₂ * (X + 1)) := by ring
      _ ≤ ‖t‖ * C₀ + 2 * (C₁ + C₂ * (X + 1)) := by
          have hdiv : ‖t‖ / σ ≤ 2 := (div_le_iff₀ hσ_pos).mpr ht_le_2σ
          have hnn : 0 ≤ C₁ + C₂ * (X + 1) := by positivity
          nlinarith
  have ht_le1 : ‖t‖ ≤ 1 := by
    rw [ht_norm]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hC0_nn : 0 ≤ C₀ := by positivity
  calc ‖T_integral t‖ ≤ ‖t‖ * C₀ + 2 * (C₁ + C₂ * (X + 1)) := hT_le
    _ ≤ 1 * C₀ + 2 * (C₁ + C₂ * (4 * (z.re + 5) + 1)) := by nlinarith
    _ = (C₀ + 2 * (C₁ + 21 * C₂)) + 8 * C₂ * z.re := by ring
    _ ≤ C_T * (z.re + 1) := by
        dsimp only [C_T]
        nlinarith [Real.exp_pos |Ei_real 1|, Real.exp_pos B]

/-- Uniform linear bound on `I_plus_holo` on `{1/2 ≤ Re z ∧ |Im z| ≤ 1/2}`. -/
theorem exists_norm_I_plus_holo_le :
    ∃ C_I > 0, ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → |z.im| ≤ 1 / 2 →
      ‖I_plus_holo z‖ ≤ C_I * (z.re + 1) := by
  obtain ⟨C_R, hCR, hR⟩ := exists_norm_R_integral_exp_neg_le
  obtain ⟨C_T, hCT, hT⟩ := exists_norm_T_integral_exp_neg_le
  refine ⟨C_R + Real.exp Real.pi * C_T, by positivity, fun z hre him => ?_⟩
  dsimp only [I_plus_holo]
  have hfac : ‖Complex.exp (-Real.pi * I * Complex.exp (-z))‖ ≤ Real.exp Real.pi := by
    rw [Complex.norm_exp]
    have hre_arg : (-Real.pi * I * Complex.exp (-z)).re = Real.pi * (Complex.exp (-z)).im := by
      simp [Complex.mul_re]
    rw [hre_arg]
    have him_le : (Complex.exp (-z)).im ≤ 1 := by
      have h1 : (Complex.exp (-z)).im ≤ ‖Complex.exp (-z)‖ := Complex.im_le_norm _
      rw [Complex.norm_exp, Complex.neg_re] at h1
      exact h1.trans (Real.exp_le_one_iff.mpr (by linarith))
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hexp_le1 : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc ‖PakNthPrimeEngine.R_integral (Complex.exp (-z)) +
          Complex.exp (-Real.pi * I * Complex.exp (-z)) * T_integral (Complex.exp (-z))‖
      ≤ ‖PakNthPrimeEngine.R_integral (Complex.exp (-z))‖ +
          ‖Complex.exp (-Real.pi * I * Complex.exp (-z))‖ * ‖T_integral (Complex.exp (-z))‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ C_R * Real.exp (-z.re) + Real.exp Real.pi * (C_T * (z.re + 1)) :=
        add_le_add (hR z hre) (mul_le_mul hfac (hT z hre him) (norm_nonneg _) (Real.exp_pos _).le)
    _ ≤ (C_R + Real.exp Real.pi * C_T) * (z.re + 1) := by nlinarith

/-- Iterated real derivative of the restriction of a complex-holomorphic function equals
its iterated complex derivative. -/
theorem iteratedDeriv_comp_ofReal_eq {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) :
    ∀ (n : ℕ) {u : ℝ}, (u : ℂ) ∈ U →
      iteratedDeriv n (fun x : ℝ => f (x : ℂ)) u = iteratedDeriv n f (u : ℂ) := by
  intro n
  induction n generalizing f with
  | zero => intro u _; simp
  | succ n ih =>
    intro u hu
    have hf' : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
    have hloc : (fun x : ℝ => deriv (fun y : ℝ => f (y : ℂ)) x) =ᶠ[𝓝 u]
        (fun x : ℝ => deriv f (x : ℂ)) := by
      have hopen : IsOpen ((Complex.ofReal : ℝ → ℂ) ⁻¹' U) := hU.preimage Complex.continuous_ofReal
      filter_upwards [hopen.mem_nhds hu] with x hx
      have hd : HasDerivAt f (deriv f (x : ℂ)) (x : ℂ) :=
        (hf.differentiableAt (hU.mem_nhds hx)).hasDerivAt
      simpa using hd.comp_ofReal.deriv
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hloc.iteratedDeriv_eq]
    exact ih hf' hu

/-- **General Cauchy Iterated-Derivative Estimate on `halfStrip`**:
If `f` is holomorphic on `halfStrip` and bounded by `M` on `sphere (u : ℂ) (1/4)` (for `u ≥ 1`),
then `‖iteratedDeriv n (fun x : ℝ => f (x : ℂ)) u‖ ≤ n.factorial * 4 ^ n * M`. -/
theorem norm_iteratedDeriv_ofReal_le_of_halfStrip {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f halfStrip) {u M : ℝ} (hu : 1 ≤ u)
    (hM : ∀ z ∈ Metric.sphere (u : ℂ) (1 / 4), ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (fun x : ℝ => f (x : ℂ)) u‖ ≤ (n.factorial : ℝ) * 4 ^ n * M := by
  have hu_mem : (u : ℂ) ∈ halfStrip := by
    simp only [halfStrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨by linarith, by norm_num⟩
  rw [iteratedDeriv_comp_ofReal_eq isOpen_halfStrip hf n hu_mem]
  have hsub : Metric.closedBall (u : ℂ) (1 / 4) ⊆ halfStrip := by
    intro z hz
    have hd : ‖z - (u : ℂ)‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hre0 : |z.re - u| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (u : ℂ))
    have him0 : |z.im| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - (u : ℂ))
    have hre : |z.re - u| ≤ 1 / 4 := hre0.trans hd
    have him : |z.im| ≤ 1 / 4 := him0.trans hd
    exact ⟨by linarith [(abs_le.mp hre).1], by linarith⟩
  have hdiff : DiffContOnCl ℂ f (Metric.ball (u : ℂ) (1 / 4)) := by
    have hcl : closure (Metric.ball (u : ℂ) (1 / 4)) ⊆ halfStrip :=
      (Metric.closure_ball_subset_closedBall).trans hsub
    exact ⟨hf.mono (Metric.ball_subset_closedBall.trans hsub), hf.continuousOn.mono hcl⟩
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1 / 4) hdiff hM
  refine hcauchy.trans_eq ?_
  rw [one_div, inv_pow, div_inv_eq_mul]
  ring

/-- **UNCONDITIONAL DISCHARGE OF HYPOTHESIS 1 (`hI_bound`)**:
For every jet order `r : ℕ`, there exists `CH > 0` such that for all `j : Fin (r + 1)` and
all `u ≥ 1`, `‖iteratedDeriv j I_plus u‖ ≤ CH * u ^ 1` (linear growth!). -/
theorem I_plus_poly_jet_bound (r : ℕ) :
    ∃ CH > 0, ∃ A : ℕ, ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv (j : ℕ) I_plus u‖ ≤ CH * u ^ A := by
  obtain ⟨C_I, hCI, hI_bound⟩ := exists_norm_I_plus_holo_le
  refine ⟨((r.factorial : ℝ) * 4 ^ r) * (3 * C_I), by positivity, 1, fun j u hu => ?_⟩
  have hloc : I_plus =ᶠ[𝓝 u] (fun x : ℝ => I_plus_holo (x : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < u by linarith)] with x hx
    exact (I_plus_holo_ofReal hx).symm
  rw [hloc.iteratedDeriv_eq]
  have hMsph : ∀ z ∈ Metric.sphere (u : ℂ) (1 / 4), ‖I_plus_holo z‖ ≤ 3 * C_I * u := by
    intro z hz
    have hd : ‖z - (u : ℂ)‖ = 1 / 4 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hre0 : |z.re - u| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (u : ℂ))
    have him0 : |z.im| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - (u : ℂ))
    have hre : |z.re - u| ≤ 1 / 4 := hre0.trans hd.le
    have him : |z.im| ≤ 1 / 4 := him0.trans hd.le
    have hzre_lo : (1 / 2 : ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
    have hzre_hi : z.re ≤ u + 1 / 4 := by linarith [(abs_le.mp hre).2]
    have h1 := hI_bound z hzre_lo (by linarith)
    nlinarith
  have hcauchy := norm_iteratedDeriv_ofReal_le_of_halfStrip differentiableOn_I_plus_holo hu hMsph (j : ℕ)
  have hj_le : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.isLt
  have hfac_le : ((j : ℕ).factorial : ℝ) ≤ (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj_le
  have hpow_le : (4 : ℝ) ^ (j : ℕ) ≤ (4 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hj_le
  have hcoeff : ((j : ℕ).factorial : ℝ) * 4 ^ (j : ℕ) ≤ (r.factorial : ℝ) * 4 ^ r :=
    mul_le_mul hfac_le hpow_le (by positivity) (by positivity)
  rw [pow_one]
  calc ‖iteratedDeriv (j : ℕ) (fun x : ℝ => I_plus_holo (x : ℂ)) u‖
      ≤ ((j : ℕ).factorial : ℝ) * 4 ^ (j : ℕ) * (3 * C_I * u) := hcauchy
    _ ≤ ((r.factorial : ℝ) * 4 ^ r) * (3 * C_I * u) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = ((r.factorial : ℝ) * 4 ^ r) * (3 * C_I) * u := by ring

/-! ### 2. All-Orders Asymptotic Transfer `nthPrimeSmoothRay ↔ I_plus` from `Main.PNTAllOrders` (`hasymp`) -/

/-- Elementary complex exponential perturbation bound: `‖exp w - 1‖ ≤ ‖w‖ * exp ‖w‖`. -/
lemma norm_cexp_sub_one_le (w : ℂ) : ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * w)) (w * Complex.exp ((s : ℂ) * w)) s := by
    intro s _
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * w) w s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const w
    convert h1.cexp using 1
    ring
  have hcont : ContinuousOn (fun s : ℝ => w * Complex.exp ((s : ℂ) * w)) (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hftc
  rw [← hftc]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖w * Complex.exp ((s : ℂ) * w)‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg w)
    have hre : ((s : ℂ) * w).re = s * w.re := by simp
    rw [hre]
    calc s * w.re ≤ s * ‖w‖ := mul_le_mul_of_nonneg_left (Complex.re_le_norm w) hs.1.le
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa using hle

/-- Exponential decay helper: for any `c > 0`, `C > 0`, `N : ℕ`, there exists `C' > 0` such that
`C * u * exp (-u) ≤ C' / u ^ N` for all `u ≥ 1`. -/
lemma mul_exp_neg_le_div_pow (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∃ C' > 0, ∀ u : ℝ, 1 ≤ u → C * u * Real.exp (-u) ≤ C' / u ^ N := by
  refine ⟨C * ((N + 1).factorial : ℝ), by positivity, fun u hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hpow := Real.pow_div_factorial_le_exp u hu_pos.le (N + 1)
  have hfact : (0 : ℝ) < ((N + 1).factorial : ℝ) := by positivity
  have h1 : u ^ (N + 1) ≤ ((N + 1).factorial : ℝ) * Real.exp u := by
    have := (div_le_iff₀ hfact).mp hpow
    linarith
  have h2 : u * Real.exp (-u) ≤ ((N + 1).factorial : ℝ) / u ^ N := by
    rw [le_div_iff₀ (pow_pos hu_pos N), Real.exp_neg]
    have hexp_pos : 0 < Real.exp u := Real.exp_pos u
    rw [mul_assoc, mul_comm (Real.exp u)⁻¹, ← mul_assoc, ← pow_succ']
    calc u ^ (N + 1) * (Real.exp u)⁻¹
        ≤ (((N + 1).factorial : ℝ) * Real.exp u) * (Real.exp u)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hexp_pos.le)
      _ = ((N + 1).factorial : ℝ) := by field_simp [hexp_pos.ne']
  calc C * u * Real.exp (-u) = C * (u * Real.exp (-u)) := by ring
    _ ≤ C * (((N + 1).factorial : ℝ) / u ^ N) := mul_le_mul_of_nonneg_left h2 hC.le
    _ = (C * ((N + 1).factorial : ℝ)) / u ^ N := by ring

/-- **General Exponential-Decay Cauchy Transfer on `halfStrip`**:
If `f` is holomorphic on `halfStrip` and satisfies `‖f z‖ ≤ C * (z.re + 1) * exp (-z.re)` on
`{1/2 ≤ z.re ∧ |z.im| ≤ 1/2}`, then every real derivative `iteratedDeriv j (f ∘ ofReal) u`
decays exponentially `≤ C_j * u * exp (-u)` on `[1, ∞)`. -/
theorem norm_iteratedDeriv_ofReal_exp_decay_of_halfStrip {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f halfStrip) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → |z.im| ≤ 1 / 2 →
      ‖f z‖ ≤ C * (z.re + 1) * Real.exp (-z.re)) (j : ℕ) :
    ∃ Cj > 0, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv j (fun x : ℝ => f (x : ℂ)) u‖ ≤ Cj * u * Real.exp (-u) := by
  let Cj : ℝ := (j.factorial : ℝ) * 4 ^ j * (3 * C * Real.exp (1 / 4))
  refine ⟨Cj, by positivity, fun u hu => ?_⟩
  have hMsph : ∀ z ∈ Metric.sphere (u : ℂ) (1 / 4),
      ‖f z‖ ≤ (3 * C * Real.exp (1 / 4)) * u * Real.exp (-u) := by
    intro z hz
    have hd : ‖z - (u : ℂ)‖ = 1 / 4 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hre0 : |z.re - u| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (u : ℂ))
    have him0 : |z.im| ≤ ‖z - (u : ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - (u : ℂ))
    have hre : |z.re - u| ≤ 1 / 4 := hre0.trans hd.le
    have him : |z.im| ≤ 1 / 4 := him0.trans hd.le
    have hzre_lo : (1 / 2 : ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
    have hzre_hi : z.re ≤ u + 1 / 4 := by linarith [(abs_le.mp hre).2]
    have h1 := hbound z hzre_lo (by linarith)
    have hexp : Real.exp (-z.re) ≤ Real.exp (1 / 4) * Real.exp (-u) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hre).1])
    have hlin : C * (z.re + 1) ≤ 3 * C * u := by nlinarith
    calc ‖f z‖ ≤ C * (z.re + 1) * Real.exp (-z.re) := h1
      _ ≤ (3 * C * u) * (Real.exp (1 / 4) * Real.exp (-u)) :=
          mul_le_mul hlin hexp (Real.exp_pos _).le (by positivity)
      _ = (3 * C * Real.exp (1 / 4)) * u * Real.exp (-u) := by ring
  have hcauchy := norm_iteratedDeriv_ofReal_le_of_halfStrip hf hu hMsph j
  refine hcauchy.trans_eq ?_
  dsimp only [Cj]
  ring

/-! #### Piece (D): Exponential Jet Decay of `I_plus u - T_integral (exp (-u))` -/

/-- Holomorphic difference `I_plus_holo z - T_integral (exp (-z))` on `halfStrip`. -/
@[expose] def diff_I_T_holo (z : ℂ) : ℂ :=
  I_plus_holo z - T_integral (Complex.exp (-z))

lemma differentiableOn_T_exp_neg :
    DifferentiableOn ℂ (fun w : ℂ => T_integral (Complex.exp (-w))) halfStrip := by
  intro z hz
  have hb := exp_neg_strip_bounds hz.1.le hz.2.le
  have ht0 : 0 < (Complex.exp (-z)).re := lt_of_lt_of_le (by positivity) hb.1
  have ht1 : (Complex.exp (-z)).re < 1 := by linarith [hb.2.2.1]
  have hT_open : IsOpen {t : ℂ | 0 < t.re ∧ t.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w)) z :=
    Complex.differentiable_exp.comp differentiable_id.neg |>.differentiableAt
  exact (show DifferentiableAt ℂ (T_integral ∘ fun w : ℂ => Complex.exp (-w)) z from
    (differentiableOn_T_integral.differentiableAt (hT_open.mem_nhds ⟨ht0, ht1⟩)).comp z hexp).differentiableWithinAt

/-- **Piece (D)**: Every derivative of `u ↦ I_plus u - T_integral (exp (-u))` decays as
`O(u * exp (-u))` on `[1, ∞)`. -/
theorem I_plus_sub_T_jet_exp_decay (j : ℕ) :
    ∃ C > 0, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv j (fun v : ℝ => I_plus v - T_integral (Real.exp (-v))) u‖ ≤
        C * u * Real.exp (-u) := by
  obtain ⟨C_R, hCR, hR⟩ := exists_norm_R_integral_exp_neg_le
  obtain ⟨C_T, hCT, hT⟩ := exists_norm_T_integral_exp_neg_le
  have hdiff : DifferentiableOn ℂ diff_I_T_holo halfStrip :=
    differentiableOn_I_plus_holo.sub differentiableOn_T_exp_neg
  have hbound : ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → |z.im| ≤ 1 / 2 →
      ‖diff_I_T_holo z‖ ≤ (C_R + Real.pi * Real.exp Real.pi * C_T) * (z.re + 1) * Real.exp (-z.re) := by
    intro z hre him
    have heq : diff_I_T_holo z =
        PakNthPrimeEngine.R_integral (Complex.exp (-z)) +
          (Complex.exp (-Real.pi * I * Complex.exp (-z)) - 1) * T_integral (Complex.exp (-z)) := by
      dsimp only [diff_I_T_holo, I_plus_holo]; ring
    rw [heq]
    have hwnorm : ‖-Real.pi * I * Complex.exp (-z)‖ = Real.pi * Real.exp (-z.re) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one, Complex.norm_exp, Complex.neg_re]
    have hwle : ‖-Real.pi * I * Complex.exp (-z)‖ ≤ Real.pi := by
      rw [hwnorm]
      have : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.pi_pos]
    have hexp_sub : ‖Complex.exp (-Real.pi * I * Complex.exp (-z)) - 1‖ ≤
        Real.pi * Real.exp Real.pi * Real.exp (-z.re) := by
      have h1 := norm_cexp_sub_one_le (-Real.pi * I * Complex.exp (-z))
      rw [hwnorm] at h1
      have h2 : Real.exp (Real.pi * Real.exp (-z.re)) ≤ Real.exp Real.pi :=
        Real.exp_le_exp.mpr (by rw [← hwnorm]; exact hwle)
      calc ‖Complex.exp (-Real.pi * I * Complex.exp (-z)) - 1‖
          ≤ Real.pi * Real.exp (-z.re) * Real.exp (Real.pi * Real.exp (-z.re)) := h1
        _ ≤ Real.pi * Real.exp (-z.re) * Real.exp Real.pi :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.pi * Real.exp Real.pi * Real.exp (-z.re) := by ring
    calc ‖PakNthPrimeEngine.R_integral (Complex.exp (-z)) +
            (Complex.exp (-Real.pi * I * Complex.exp (-z)) - 1) * T_integral (Complex.exp (-z))‖
        ≤ ‖PakNthPrimeEngine.R_integral (Complex.exp (-z))‖ +
            ‖Complex.exp (-Real.pi * I * Complex.exp (-z)) - 1‖ * ‖T_integral (Complex.exp (-z))‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ C_R * Real.exp (-z.re) +
            (Real.pi * Real.exp Real.pi * Real.exp (-z.re)) * (C_T * (z.re + 1)) :=
          add_le_add (hR z hre) (mul_le_mul hexp_sub (hT z hre him) (norm_nonneg _) (by positivity))
      _ ≤ (C_R + Real.pi * Real.exp Real.pi * C_T) * (z.re + 1) * Real.exp (-z.re) := by
          have hre1 : 1 ≤ z.re + 1 := by linarith
          have h1 : C_R * Real.exp (-z.re) ≤ C_R * (z.re + 1) * Real.exp (-z.re) := by
            have hCR1 : C_R * 1 ≤ C_R * (z.re + 1) := mul_le_mul_of_nonneg_left hre1 hCR.le
            rw [mul_one] at hCR1
            exact mul_le_mul_of_nonneg_right hCR1 (Real.exp_pos _).le
          linarith
  obtain ⟨Cj, hCj, hCj_bound⟩ :=
    norm_iteratedDeriv_ofReal_exp_decay_of_halfStrip hdiff (by positivity) hbound j
  refine ⟨Cj, hCj, fun u hu => ?_⟩
  have hloc : (fun v : ℝ => I_plus v - T_integral (Real.exp (-v))) =ᶠ[𝓝 u]
      (fun x : ℝ => diff_I_T_holo (x : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < u by linarith)] with x hx
    dsimp only [diff_I_T_holo]
    rw [I_plus_holo_ofReal hx, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hloc.iteratedDeriv_eq]
  exact hCj_bound u hu

/-! #### Piece (C): Exact Change-of-Variables & Exponential Jet Decay of `J_invLi u - T_integral (exp (-u))` -/

/-- The continuous smoothed `li⁻¹` Laplace integral:
`J_invLi u = exp (-2u) * ∫_{v > 0} inverseLi v * exp (-exp(-u) * v) dv`. -/
@[expose] def J_invLi (u : ℝ) : ℝ :=
  (Real.exp (-u)) ^ 2 * ∫ v in Set.Ioi (0 : ℝ), NthPrime.inverseLi v * Real.exp (-(Real.exp (-u)) * v)

/-- Exact identity `Main.li (exp x) = Ei_real x - Ei_real (log 2)` for `x ≥ log 2`. -/
theorem li_exp_eq_Ei_real_sub {x : ℝ} (hx : Real.log 2 ≤ x) :
    Main.li (Real.exp x) = Ei_real x - Ei_real (Real.log 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hftc_Ei : ∫ y in (Real.log 2)..x, (Real.exp y / y) = Ei_real x - Ei_real (Real.log 2) := by
    have hderiv : ∀ y ∈ Set.uIcc (Real.log 2) x, HasDerivAt Ei_real (Real.exp y / y) y := by
      intro y hy
      rw [Set.uIcc_of_le hx] at hy
      exact hasDerivAt_Ei_real (lt_of_lt_of_le hlog2_pos hy.1)
    have hcont : ContinuousOn (fun y : ℝ => Real.exp y / y) (Set.uIcc (Real.log 2) x) := by
      rw [Set.uIcc_of_le hx]
      exact Real.continuous_exp.continuousOn.div continuousOn_id
        fun y hy => (lt_of_lt_of_le hlog2_pos hy.1).ne'
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hsub : ∫ y in (Real.log 2)..x, (Real.log (Real.exp y))⁻¹ * Real.exp y =
      ∫ v in (Real.exp (Real.log 2))..(Real.exp x), (Real.log v)⁻¹ := by
    have hderiv : ∀ y ∈ Set.uIcc (Real.log 2) x, HasDerivAt Real.exp (Real.exp y) y :=
      fun y _ => Real.hasDerivAt_exp y
    have hcont_exp : ContinuousOn Real.exp (Set.uIcc (Real.log 2) x) := Real.continuous_exp.continuousOn
    have hcont_f : ContinuousOn (fun v : ℝ => (Real.log v)⁻¹) (Real.exp '' Set.uIcc (Real.log 2) x) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.uIcc_of_le hx] at hy
      have hy_pos : 0 < y := lt_of_lt_of_le hlog2_pos hy.1
      have hlog_ne : Real.log (Real.exp y) ≠ 0 := by rw [Real.log_exp]; exact hy_pos.ne'
      exact ((Real.continuousAt_log (Real.exp_pos y).ne').inv₀ hlog_ne).continuousWithinAt
    simpa [mul_comm] using
      intervalIntegral.integral_comp_mul_deriv' hderiv hcont_exp hcont_f
  have hcongr : ∫ y in (Real.log 2)..x, (Real.log (Real.exp y))⁻¹ * Real.exp y =
      ∫ y in (Real.log 2)..x, (Real.exp y / y) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [Real.log_exp, inv_mul_eq_div]
  calc Main.li (Real.exp x)
      = ∫ v in (Real.exp (Real.log 2))..(Real.exp x), (Real.log v)⁻¹ := by
        rw [Main.li, Real.exp_log (by norm_num)]
    _ = ∫ y in (Real.log 2)..x, (Real.log (Real.exp y))⁻¹ * Real.exp y := hsub.symm
    _ = ∫ y in (Real.log 2)..x, (Real.exp y / y) := hcongr
    _ = Ei_real x - Ei_real (Real.log 2) := hftc_Ei

/-- Strict monotonicity of `Main.li` on `[2, ∞)`. -/
lemma li_strictMonoOn : StrictMonoOn Main.li (Set.Ici (2 : ℝ)) := by
  intro a ha b hb hab
  have ha2 : 2 ≤ a := ha
  have hcont : ∀ {c d : ℝ}, 2 ≤ c → c ≤ d → IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume c d := by
    intro c d hc hcd
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hcd]
    intro v hv
    have hv1 : 1 < v := by linarith [hv.1]
    exact ((Real.continuousAt_log (by linarith : v ≠ 0)).inv₀ (Real.log_pos hv1).ne').continuousWithinAt
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hcont le_rfl ha2) (hcont ha2 hab.le)
  change Main.li a + ∫ v in a..b, (Real.log v)⁻¹ = Main.li b at hadd
  have hpos : 0 < ∫ v in a..b, (Real.log v)⁻¹ := by
    refine intervalIntegral.integral_pos hab ?_ (fun v hv => ?_) ⟨a, ⟨le_rfl, hab.le⟩, ?_⟩
    · intro v hv
      have hv1 : 1 < v := by linarith [hv.1]
      exact ((Real.continuousAt_log (by linarith : v ≠ 0)).inv₀ (Real.log_pos hv1).ne').continuousWithinAt
    · have hv1 : 1 < v := by linarith [hv.1]
      exact (inv_pos.mpr (Real.log_pos hv1)).le
    · have ha1 : 1 < a := by linarith
      exact inv_pos.mpr (Real.log_pos ha1)
  linarith

/-- Exact inversion identity `inverseLi (Ei_real x - Ei_real (log 2)) = exp x` for `x ≥ log 2`. -/
theorem inverseLi_Ei_real_sub {x : ℝ} (hx : Real.log 2 ≤ x) :
    NthPrime.inverseLi (Ei_real x - Ei_real (Real.log 2)) = Real.exp x := by
  have hexp2 : 2 ≤ Real.exp x := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hx
  have hv_eq : Ei_real x - Ei_real (Real.log 2) = Main.li (Real.exp x) :=
    (li_exp_eq_Ei_real_sub hx).symm
  have hv_nn : 0 ≤ Ei_real x - Ei_real (Real.log 2) := by
    rw [hv_eq]
    have hli2 : Main.li 2 = 0 := by simp [Main.li]
    rw [← hli2]
    rcases eq_or_lt_of_le hexp2 with h | h
    · rw [h]
    · exact (li_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hexp2) h).le
  obtain ⟨hmem, hli⟩ := NthPrime.inverseLi_spec hv_nn
  exact li_strictMonoOn.injOn (Set.mem_Ici.mpr hmem.1) (Set.mem_Ici.mpr hexp2) (hli.trans hv_eq)

/-- Global integrability of `v ↦ inverseLi v * exp (-t * v)` on `(0, ∞)` for `t > 0`. -/
lemma integrableOn_inverseLi_mul_exp {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => NthPrime.inverseLi v * Real.exp (-t * v)) (Set.Ioi 0) := by
  have hcont_inv : ContinuousOn NthPrime.inverseLi (Set.Ioi (0 : ℝ)) :=
    fun v hv => (NthPrime.inverseLi_hasDerivAt hv).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun v : ℝ => NthPrime.inverseLi v * Real.exp (-t * v))
      (volume.restrict (Set.Ioi 0)) :=
    (hcont_inv.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  let K : ℝ := 16 * (1 + 2 / (t / 2) + 2 / (t / 2) ^ 2)
  have hdom : IntegrableOn (fun v : ℝ => K * Real.exp (-(t / 2) * v)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul K
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := hv
  have hspec := (NthPrime.inverseLi_spec (le_of_lt hv0)).1
  rw [Real.norm_of_nonneg (mul_nonneg (by linarith [hspec.1]) (Real.exp_pos _).le)]
  have hle : NthPrime.inverseLi v ≤ 16 * (v + 1) ^ 2 := by
    have h2 : (4 * (v + 1)) ^ 2 = 16 * (v + 1) ^ 2 := by ring
    linarith [hspec.2]
  have h1 : v ≤ (1 / (t / 2)) * Real.exp ((t / 2) * v) := by
    have ha : (t / 2) * v ≤ Real.exp ((t / 2) * v) := le_trans (by linarith) (Real.add_one_le_exp _)
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (half_pos ht), mul_comm]
    exact ha
  have h2 : v ^ 2 ≤ (2 / (t / 2) ^ 2) * Real.exp ((t / 2) * v) := by
    have ha : ((t / 2) * v) ^ 2 / 2 ≤ Real.exp ((t / 2) * v) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp ((t / 2) * v) (by positivity) 2
    have ht2 : (0 : ℝ) < (t / 2) ^ 2 := by positivity
    rw [mul_pow] at ha
    rw [div_mul_eq_mul_div, le_div_iff₀ ht2]
    linarith
  have h1e : (1 : ℝ) ≤ Real.exp ((t / 2) * v) := Real.one_le_exp (by positivity)
  have hquad : 16 * (v + 1) ^ 2 ≤ K * Real.exp ((t / 2) * v) := by
    dsimp only [K]
    have hlin : (v + 1) ^ 2 = v ^ 2 + 2 * v + 1 := by ring
    rw [hlin]
    have h2v : 2 * v ≤ (2 / (t / 2)) * Real.exp ((t / 2) * v) := by
      calc 2 * v ≤ 2 * ((1 / (t / 2)) * Real.exp ((t / 2) * v)) := by linarith
        _ = (2 / (t / 2)) * Real.exp ((t / 2) * v) := by ring
    linarith
  calc NthPrime.inverseLi v * Real.exp (-t * v)
      ≤ (16 * (v + 1) ^ 2) * Real.exp (-t * v) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ ≤ (K * Real.exp ((t / 2) * v)) * Real.exp (-t * v) := mul_le_mul_of_nonneg_right hquad (Real.exp_pos _).le
    _ = K * (Real.exp ((t / 2) * v) * Real.exp (-t * v)) := by ring
    _ = K * Real.exp (-(t / 2) * v) := by rw [← Real.exp_add]; congr 2; ring

/-- **Exact Closed-Form Identity for `J_invLi u`**:
For every `u > 0`, with `t = exp (-u)` and `c₀ = Ei_real (log 2)`,
`J_invLi u = exp (c₀ * t) * t * (∫ x in Ioi (log 2), exp (x - t * Ei_real x)) + 2 * t`. -/
theorem J_invLi_eq_tail_Ei {u : ℝ} (hu : 0 < u) :
    J_invLi u =
      Real.exp (Ei_real (Real.log 2) * Real.exp (-u)) * Real.exp (-u) *
        (∫ x in Set.Ioi (Real.log 2), Real.exp (x - Real.exp (-u) * Ei_real x)) +
      2 * Real.exp (-u) := by
  set t : ℝ := Real.exp (-u)
  set c₀ : ℝ := Ei_real (Real.log 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let φ : ℝ → ℝ := fun x => Ei_real x - c₀
  have hφ_deriv : ∀ x > 0, HasDerivAt φ (Real.exp x / x) x :=
    fun x hx => (hasDerivAt_Ei_real hx).sub_const c₀
  have hφ_strictMono : StrictMonoOn φ (Set.Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (hφ_deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Ioi] at hx
        have hx_pos : 0 < x := hx
        rw [(hφ_deriv x hx_pos).deriv]
        positivity)
  have hφ_tendsto : Tendsto φ atTop atTop := by
    refine tendsto_atTop_mono' atTop (f₁ := fun x => gammaE1 - 2 - c₀ + x / 4)
      (Filter.eventually_atTop.mpr ⟨1, fun x hx => ?_⟩) ?_
    · show gammaE1 - 2 - c₀ + x / 4 ≤ φ x
      have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have hge := Ei_real_ge_large hx
      have hhalf := half_exp_half_le_exp_div hx_pos
      have hlin : 1 + x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
      dsimp only [φ]; linarith
    · exact tendsto_atTop_add_const_left atTop (gammaE1 - 2 - c₀)
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  have hint_v : IntegrableOn (fun v : ℝ => NthPrime.inverseLi v * Real.exp (-t * v)) (Set.Ioi 0) :=
    integrableOn_inverseLi_mul_exp ht0
  have hint_x : IntegrableOn (fun x : ℝ => Real.exp (x - t * Ei_real x)) (Set.Ioi 0) :=
    integrableOn_exp_sub_mul_Ei_real ht0 ht1
  -- Step 1: Exact identity on `(φ a, ∞)` for every `a > log 2`
  have hstep_a : ∀ a : ℝ, Real.log 2 < a →
      t ^ 2 * (∫ v in Set.Ioi (φ a), NthPrime.inverseLi v * Real.exp (-t * v)) =
        Real.exp (c₀ * t) * t * (∫ x in Set.Ioi a, Real.exp (x - t * Ei_real x)) +
        Real.exp (c₀ * t) * t * Real.exp (a - t * Ei_real a) := by
    intro a ha
    have ha_pos : 0 < a := lt_trans hlog2_pos ha
    have hφa_pos : 0 < φ a := by
      have h0 : φ (Real.log 2) = 0 := sub_self c₀
      rw [← h0]
      exact hφ_strictMono hlog2_pos ha_pos ha
    have hM_eq : ∀ M : ℝ, a ≤ M →
        t ^ 2 * (∫ v in (φ a)..(φ M), NthPrime.inverseLi v * Real.exp (-t * v)) =
          Real.exp (c₀ * t) * t * (∫ x in a..M, Real.exp (x - t * Ei_real x)) +
          Real.exp (c₀ * t) * t * (Real.exp (a - t * Ei_real a) - Real.exp (M - t * Ei_real M)) := by
      intro M hM
      have hsub : ∫ x in a..M, (NthPrime.inverseLi (φ x) * Real.exp (-t * φ x)) * (Real.exp x / x) =
          ∫ v in (φ a)..(φ M), NthPrime.inverseLi v * Real.exp (-t * v) := by
        have hd : ∀ x ∈ Set.uIcc a M, HasDerivAt φ (Real.exp x / x) x := by
          intro x hx; rw [Set.uIcc_of_le hM] at hx
          exact hφ_deriv x (lt_of_lt_of_le ha_pos hx.1)
        have hcd : ContinuousOn (fun x : ℝ => Real.exp x / x) (Set.uIcc a M) := by
          rw [Set.uIcc_of_le hM]
          exact Real.continuous_exp.continuousOn.div continuousOn_id
            fun x hx => (lt_of_lt_of_le ha_pos hx.1).ne'
        have hcf : ContinuousOn (fun v : ℝ => NthPrime.inverseLi v * Real.exp (-t * v)) (φ '' Set.uIcc a M) := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Set.uIcc_of_le hM] at hx
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have hφx_pos : 0 < φ x := lt_of_lt_of_le hφa_pos
            (hφ_strictMono.monotoneOn ha_pos hx_pos hx.1)
          exact ((NthPrime.inverseLi_hasDerivAt hφx_pos).continuousAt.mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).continuousWithinAt
        simpa [mul_comm] using intervalIntegral.integral_comp_mul_deriv' hd hcd hcf
      have hcongr : ∫ x in a..M, (NthPrime.inverseLi (φ x) * Real.exp (-t * φ x)) * (Real.exp x / x) =
          Real.exp (c₀ * t) * ∫ x in a..M, Real.exp (2 * x - t * Ei_real x) / x := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le hM] at hx
        have hx_log2 : Real.log 2 ≤ x := ha.le.trans hx.1
        rw [show φ x = Ei_real x - Ei_real (Real.log 2) from rfl, inverseLi_Ei_real_sub hx_log2]
        have hexp : Real.exp (c₀ * t) * Real.exp (2 * x - t * Ei_real x) =
            Real.exp x * Real.exp (-t * (Ei_real x - c₀)) * Real.exp x := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1; ring
        change Real.exp x * Real.exp (-t * (Ei_real x - c₀)) * (Real.exp x / x) =
          Real.exp (c₀ * t) * (Real.exp (2 * x - t * Ei_real x) / x)
        rw [mul_div_assoc', mul_div_assoc', ← hexp]
      have hftc : ∫ x in a..M, (Real.exp (x - t * Ei_real x) - t * (Real.exp (2 * x - t * Ei_real x) / x)) =
          Real.exp (M - t * Ei_real M) - Real.exp (a - t * Ei_real a) := by
        have hd : ∀ x ∈ Set.uIcc a M,
            HasDerivAt (fun y : ℝ => Real.exp (y - t * Ei_real y))
              (Real.exp (x - t * Ei_real x) - t * (Real.exp (2 * x - t * Ei_real x) / x)) x := by
          intro x hx
          rw [Set.uIcc_of_le hM] at hx
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have h1 := ((hasDerivAt_id x).sub ((hasDerivAt_Ei_real hx_pos).const_mul t)).exp
          refine h1.congr_deriv ?_
          have hexp2 : Real.exp (2 * x - t * Ei_real x) = Real.exp (x - t * Ei_real x) * Real.exp x := by
            rw [← Real.exp_add]; congr 1; ring
          simp only [Pi.sub_apply, id_eq]
          rw [hexp2]
          ring
        have hc1 : ContinuousOn (fun x : ℝ => Real.exp (x - t * Ei_real x)) (Set.uIcc a M) := by
          rw [Set.uIcc_of_le hM]
          exact Real.continuous_exp.comp_continuousOn
            (continuousOn_id.sub (continuousOn_const.mul
              (continuousOn_Ei_real.mono fun x (hx : x ∈ Set.Icc a M) => lt_of_lt_of_le ha_pos hx.1)))
        have hc2 : ContinuousOn (fun x : ℝ => t * (Real.exp (2 * x - t * Ei_real x) / x)) (Set.uIcc a M) := by
          rw [Set.uIcc_of_le hM]
          exact continuousOn_const.mul
            ((Real.continuous_exp.comp_continuousOn
              ((continuousOn_const.mul continuousOn_id).sub (continuousOn_const.mul
                (continuousOn_Ei_real.mono fun x (hx : x ∈ Set.Icc a M) => lt_of_lt_of_le ha_pos hx.1)))).div
              continuousOn_id fun x (hx : x ∈ Set.Icc a M) => (lt_of_lt_of_le ha_pos hx.1).ne')
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.sub hc2).intervalIntegrable
      have hc1 : ContinuousOn (fun x : ℝ => Real.exp (x - t * Ei_real x)) (Set.uIcc a M) := by
        rw [Set.uIcc_of_le hM]
        exact Real.continuous_exp.comp_continuousOn
          (continuousOn_id.sub (continuousOn_const.mul
            (continuousOn_Ei_real.mono fun x (hx : x ∈ Set.Icc a M) => lt_of_lt_of_le ha_pos hx.1)))
      have hc2 : ContinuousOn (fun x : ℝ => Real.exp (2 * x - t * Ei_real x) / x) (Set.uIcc a M) := by
        rw [Set.uIcc_of_le hM]
        exact (Real.continuous_exp.comp_continuousOn
          ((continuousOn_const.mul continuousOn_id).sub (continuousOn_const.mul
            (continuousOn_Ei_real.mono fun x (hx : x ∈ Set.Icc a M) => lt_of_lt_of_le ha_pos hx.1)))).div
          continuousOn_id fun x (hx : x ∈ Set.Icc a M) => (lt_of_lt_of_le ha_pos hx.1).ne'
      rw [intervalIntegral.integral_sub hc1.intervalIntegrable (hc2.const_mul t).intervalIntegrable,
        intervalIntegral.integral_const_mul] at hftc
      rw [← hsub, hcongr]
      have hmul_eq : t ^ 2 * (Real.exp (c₀ * t) * ∫ x in a..M, Real.exp (2 * x - t * Ei_real x) / x) =
          Real.exp (c₀ * t) * t * (t * ∫ x in a..M, Real.exp (2 * x - t * Ei_real x) / x) := by ring
      rw [hmul_eq]
      have hibp : t * ∫ x in a..M, Real.exp (2 * x - t * Ei_real x) / x =
          (∫ x in a..M, Real.exp (x - t * Ei_real x)) +
            (Real.exp (a - t * Ei_real a) - Real.exp (M - t * Ei_real M)) := by linarith
      rw [hibp]; ring
    have hlhs : Tendsto (fun M : ℝ => t ^ 2 * ∫ v in (φ a)..(φ M), NthPrime.inverseLi v * Real.exp (-t * v))
        atTop (𝓝 (t ^ 2 * ∫ v in Set.Ioi (φ a), NthPrime.inverseLi v * Real.exp (-t * v))) :=
      (intervalIntegral_tendsto_integral_Ioi (φ a)
        (hint_v.mono_set (Set.Ioi_subset_Ioi hφa_pos.le)) hφ_tendsto).const_mul (t ^ 2)
    have htail_zero : Tendsto (fun M : ℝ => Real.exp (M - t * Ei_real M)) atTop (𝓝 0) := by
      refine squeeze_zero_norm'
        (a := fun M : ℝ => Real.exp (-t * (gammaE1 - 2) + 6 / t) * Real.exp (-M))
        (Filter.eventually_atTop.mpr ⟨1, fun M hM => ?_⟩) ?_
      · show ‖Real.exp (M - t * Ei_real M)‖ ≤ Real.exp (-t * (gammaE1 - 2) + 6 / t) * Real.exp (-M)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
        have hge := Ei_real_ge_large hM
        have hdom := tail_exp_div_dominates ht0 hM
        exact Real.exp_le_exp.mpr (by nlinarith)
      · have h0 : Tendsto (fun M : ℝ => Real.exp (-M)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
        simpa using h0.const_mul (Real.exp (-t * (gammaE1 - 2) + 6 / t))
    have hrhs : Tendsto
        (fun M : ℝ => Real.exp (c₀ * t) * t * (∫ x in a..M, Real.exp (x - t * Ei_real x)) +
          Real.exp (c₀ * t) * t * (Real.exp (a - t * Ei_real a) - Real.exp (M - t * Ei_real M)))
        atTop (𝓝 (Real.exp (c₀ * t) * t * (∫ x in Set.Ioi a, Real.exp (x - t * Ei_real x)) +
          Real.exp (c₀ * t) * t * Real.exp (a - t * Ei_real a))) := by
      have h1 := (intervalIntegral_tendsto_integral_Ioi a
        (hint_x.mono_set (Set.Ioi_subset_Ioi ha_pos.le)) tendsto_id).const_mul (Real.exp (c₀ * t) * t)
      have h2 := ((tendsto_const_nhds (x := Real.exp (a - t * Ei_real a))).sub htail_zero).const_mul
        (Real.exp (c₀ * t) * t)
      simpa using h1.add h2
    exact tendsto_nhds_unique hlhs (hrhs.congr' (Filter.eventually_atTop.mpr ⟨a, fun M hM => (hM_eq M hM).symm⟩))
  -- Step 2: Take `a → (log 2)⁺`
  have hφ_lim : Tendsto φ (𝓝[>] (Real.log 2)) (𝓝 0) := by
    have hc : ContinuousAt φ (Real.log 2) := (hφ_deriv (Real.log 2) hlog2_pos).continuousAt
    have h0 : φ (Real.log 2) = 0 := sub_self c₀
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlhs_lim : Tendsto
      (fun a : ℝ => t ^ 2 * ∫ v in Set.Ioi (φ a), NthPrime.inverseLi v * Real.exp (-t * v))
      (𝓝[>] (Real.log 2)) (𝓝 (J_invLi u)) := by
    dsimp only [J_invLi]
    refine Tendsto.const_mul (t ^ 2) ?_
    have hdiff_zero : Tendsto
        (fun a : ℝ => ∫ v in Set.Ioc (0 : ℝ) (φ a), NthPrime.inverseLi v * Real.exp (-t * v))
        (𝓝[>] (Real.log 2)) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using hφ_lim.const_mul (64 : ℝ))
      have hsmall : ∀ᶠ a in 𝓝[>] (Real.log 2), a ∈ Set.Ioi (Real.log 2) ∧ φ a < 1 :=
        Filter.inter_mem self_mem_nhdsWithin (hφ_lim (Iio_mem_nhds zero_lt_one))
      filter_upwards [hsmall] with a ⟨ha, hφa1⟩
      have hφa_pos : 0 < φ a := by
        have h0 : φ (Real.log 2) = 0 := sub_self c₀
        rw [← h0]
        exact hφ_strictMono hlog2_pos (lt_trans hlog2_pos ha) ha
      calc ‖∫ v in Set.Ioc (0 : ℝ) (φ a), NthPrime.inverseLi v * Real.exp (-t * v)‖
          ≤ ∫ v in Set.Ioc (0 : ℝ) (φ a), ‖NthPrime.inverseLi v * Real.exp (-t * v)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Set.Ioc (0 : ℝ) (φ a), (64 : ℝ) := by
            refine setIntegral_mono_on (hint_v.mono_set Set.Ioc_subset_Ioi_self).norm
              (integrableOn_const (C := (64 : ℝ)) (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun v hv => ?_
            have hspec := (NthPrime.inverseLi_spec hv.1.le).1
            rw [Real.norm_of_nonneg (mul_nonneg (by linarith [hspec.1]) (Real.exp_pos _).le)]
            have hle64 : NthPrime.inverseLi v ≤ 64 := by
              have hv1 : v ≤ 1 := hv.2.trans hφa1.le
              have : (4 * (v + 1)) ^ 2 ≤ 64 := by nlinarith [hv.1]
              exact hspec.2.trans this
            have hexp1 : Real.exp (-t * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
            nlinarith [hspec.1, Real.exp_pos (-t * v)]
        _ = 64 * φ a := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc, sub_zero,
              ENNReal.toReal_ofReal hφa_pos.le, mul_comm]
    have hlim : Tendsto
        (fun a : ℝ => (∫ v in Set.Ioi (0 : ℝ), NthPrime.inverseLi v * Real.exp (-t * v)) -
          ∫ v in Set.Ioc (0 : ℝ) (φ a), NthPrime.inverseLi v * Real.exp (-t * v))
        (𝓝[>] (Real.log 2)) (𝓝 (∫ v in Set.Ioi (0 : ℝ), NthPrime.inverseLi v * Real.exp (-t * v))) := by
      simpa using tendsto_const_nhds.sub hdiff_zero
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : Real.log 2 < a)
    have hφa_pos : 0 < φ a := by
      have h0 : φ (Real.log 2) = 0 := sub_self c₀
      rw [← h0]
      exact hφ_strictMono hlog2_pos (lt_trans hlog2_pos ha) ha
    have hsplit := setIntegral_union (μ := volume) (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := φ a))
      measurableSet_Ioi (hint_v.mono_set Set.Ioc_subset_Ioi_self)
      (hint_v.mono_set (Set.Ioi_subset_Ioi hφa_pos.le))
    rw [Set.Ioc_union_Ioi_eq_Ioi hφa_pos.le] at hsplit
    linarith
  have hrhs_lim : Tendsto
      (fun a : ℝ => Real.exp (c₀ * t) * t * (∫ x in Set.Ioi a, Real.exp (x - t * Ei_real x)) +
        Real.exp (c₀ * t) * t * Real.exp (a - t * Ei_real a))
      (𝓝[>] (Real.log 2))
      (𝓝 (Real.exp (c₀ * t) * t * (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x)) +
        2 * t)) := by
    have htail_lim : Tendsto
        (fun a : ℝ => ∫ x in Set.Ioi a, Real.exp (x - t * Ei_real x))
        (𝓝[>] (Real.log 2)) (𝓝 (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x))) := by
      have hdiff_zero : Tendsto
          (fun a : ℝ => ∫ x in Set.Ioc (Real.log 2) a, Real.exp (x - t * Ei_real x))
          (𝓝[>] (Real.log 2)) (𝓝 0) := by
        have hcont_at : ContinuousAt (fun x : ℝ => Real.exp (x - t * Ei_real x)) (Real.log 2) :=
          Real.continuous_exp.continuousAt.comp
            (continuousAt_id.sub (continuousAt_const.mul (hasDerivAt_Ei_real hlog2_pos).continuousAt))
        have hprim := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
          (f := fun x : ℝ => Real.exp (x - t * Ei_real x))
          (a := Real.log 2) (b₁ := Real.log 2) (b₂ := Real.log 2 + 1)
          ((Real.continuous_exp.comp_continuousOn
            (continuousOn_id.sub (continuousOn_const.mul
              (continuousOn_Ei_real.mono fun x hx => by
                rw [Set.uIcc_of_le (by linarith)] at hx; exact lt_of_lt_of_le hlog2_pos hx.1)))).intervalIntegrable)
          (Set.left_mem_uIcc)
        have hc0 : ContinuousWithinAt (fun a : ℝ => ∫ x in (Real.log 2)..a, Real.exp (x - t * Ei_real x))
            (Set.Ioi (Real.log 2)) (Real.log 2) := by
          have hsub : Set.Icc (Real.log 2) (Real.log 2 + 1) ∈ 𝓝[>] (Real.log 2) :=
            Icc_mem_nhdsGT (by linarith)
          exact (hprim (Real.log 2) Set.left_mem_uIcc).mono_of_mem_nhdsWithin
            (by rw [Set.uIcc_of_le (by linarith)]; exact hsub)
        have h0 : Tendsto (fun a : ℝ => ∫ x in (Real.log 2)..a, Real.exp (x - t * Ei_real x))
            (𝓝[>] (Real.log 2)) (𝓝 0) := by
          simpa [intervalIntegral.integral_same] using hc0.tendsto
        refine h0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with a (ha : Real.log 2 < a)
        exact intervalIntegral.integral_of_le ha.le
      have hlim : Tendsto
          (fun a : ℝ => (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x)) -
            ∫ x in Set.Ioc (Real.log 2) a, Real.exp (x - t * Ei_real x))
          (𝓝[>] (Real.log 2)) (𝓝 (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x))) := by
        simpa using tendsto_const_nhds.sub hdiff_zero
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a (ha : Real.log 2 < a)
      have hsplit := setIntegral_union (μ := volume) (Set.Ioc_disjoint_Ioi_same (a := Real.log 2) (b := a))
        measurableSet_Ioi
        (hint_x.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hlog2_pos.le)))
        (hint_x.mono_set (Set.Ioi_subset_Ioi (lt_trans hlog2_pos ha).le))
      rw [Set.Ioc_union_Ioi_eq_Ioi ha.le] at hsplit
      linarith
    have hbdry_lim : Tendsto
        (fun a : ℝ => Real.exp (c₀ * t) * t * Real.exp (a - t * Ei_real a))
        (𝓝[>] (Real.log 2)) (𝓝 (2 * t)) := by
      have hc : ContinuousAt (fun a : ℝ => Real.exp (c₀ * t) * t * Real.exp (a - t * Ei_real a)) (Real.log 2) :=
        continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
          (continuousAt_id.sub (continuousAt_const.mul (hasDerivAt_Ei_real hlog2_pos).continuousAt)))
      have hval : Real.exp (c₀ * t) * t * Real.exp (Real.log 2 - t * Ei_real (Real.log 2)) = 2 * t := by
        have h1 : Real.exp (c₀ * t) * Real.exp (Real.log 2 - t * c₀) = 2 := by
          rw [← Real.exp_add]
          have : c₀ * t + (Real.log 2 - t * c₀) = Real.log 2 := by ring
          rw [this, Real.exp_log (by norm_num)]
        change Real.exp (c₀ * t) * t * Real.exp (Real.log 2 - t * c₀) = 2 * t
        calc Real.exp (c₀ * t) * t * Real.exp (Real.log 2 - t * c₀)
            = (Real.exp (c₀ * t) * Real.exp (Real.log 2 - t * c₀)) * t := by ring
          _ = 2 * t := by rw [h1]
      rw [← hval]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (htail_lim.const_mul (Real.exp (c₀ * t) * t)).add hbdry_lim
  exact tendsto_nhds_unique hlhs_lim
    (hrhs_lim.congr' (Filter.mem_of_superset self_mem_nhdsWithin fun a ha => (hstep_a a ha).symm))

/-- Holomorphic short-interval integral `∫_{x ∈ (0, log 2]} exp (x - t * Ei(x)) dx` on `{Re t < 1}`. -/
@[expose] def T_short (t : ℂ) : ℂ :=
  ∫ x in Set.Ioc (0 : ℝ) (Real.log 2), Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2
    _ = 1 := Real.log_exp 1

lemma integrableOn_T_short {t : ℂ} (ht1 : t.re < 1) :
    IntegrableOn (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ)))
      (Set.Ioc (0 : ℝ) (Real.log 2)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ)))
      (volume.restrict (Set.Ioc 0 (Real.log 2))) :=
    (Complex.continuous_exp.comp_continuousOn
      (Complex.continuous_ofReal.continuousOn.sub
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_Ei_real.mono Set.Ioc_subset_Ioi_self))))).aestronglyMeasurable measurableSet_Ioc
  let σ : ℝ := max t.re 0
  have hσ_lt1 : σ < 1 := max_lt ht1 zero_lt_one
  have hrpow : IntegrableOn (fun x : ℝ => Real.exp (1 + |t.re| * |gammaE1| + |t.re| * Real.exp 1) * x ^ (-σ))
      (Set.Ioc 0 (Real.log 2)) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Real.log 2) (by linarith)).1.const_mul _)
  refine hrpow.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx1 : x ≤ 1 := hx.2.trans log_two_le_one
  rw [norm_cexp_sub_mul_Ei_real]
  have hlog_np : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx1
  have hge := Ei_real_ge_log hx.1
  have hsmall := abs_Ei_real_le_small hx.1 hx1
  have harg : x - t.re * Ei_real x ≤ (1 + |t.re| * |gammaE1| + |t.re| * Real.exp 1) + (-σ) * Real.log x := by
    by_cases htre : 0 ≤ t.re
    · have hσ_eq : σ = t.re := max_eq_left htre
      have hg : -t.re * gammaE1 ≤ |t.re| * |gammaE1| := by
        calc -t.re * gammaE1 ≤ |-t.re * gammaE1| := le_abs_self _
          _ = |t.re| * |gammaE1| := by rw [abs_mul, abs_neg]
      rw [hσ_eq]; nlinarith [Real.exp_pos 1, abs_nonneg t.re]
    · push Not at htre
      have hσ_eq : σ = 0 := max_eq_right htre.le
      have hneg : -t.re * Ei_real x ≤ |t.re| * (|gammaE1| + Real.exp 1 + (-Real.log x)) := by
        calc -t.re * Ei_real x ≤ |-t.re * Ei_real x| := le_abs_self _
          _ = |t.re| * |Ei_real x| := by rw [abs_mul, abs_neg]
          _ ≤ |t.re| * (|gammaE1| + Real.exp 1 + (-Real.log x)) :=
              mul_le_mul_of_nonneg_left hsmall (abs_nonneg _)
      -- Actually for t.re < 0, -t.re * (-log x) ≥ 0, wait: Ei_real x ≤ |gammaE1| + exp 1 when x ≤ 1!
      -- Because log x ≤ 0 and -Ein(-x) ≤ exp 1!
      have hEi_upper : Ei_real x ≤ |gammaE1| + Real.exp 1 := by
        dsimp only [Ei_real]
        have hein : |Ein_real (-x)| ≤ Real.exp 1 := by
          have h1 : ‖Ein_complex ((-x : ℝ) : ℂ)‖ ≤ Real.exp ‖((-x : ℝ) : ℂ)‖ := norm_Ein_complex_le _
          rw [Ein_complex_ofReal, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_neg, abs_of_pos hx.1] at h1
          exact h1.trans (Real.exp_le_exp.mpr hx1)
        linarith [le_abs_self gammaE1, neg_abs_le (Ein_real (-x))]
      have hprod : -t.re * Ei_real x ≤ |t.re| * (|gammaE1| + Real.exp 1) := by
        rw [abs_of_neg htre]
        exact mul_le_mul_of_nonneg_left hEi_upper (by linarith)
      rw [hσ_eq]; linarith
  calc Real.exp (x - t.re * Ei_real x)
      ≤ Real.exp ((1 + |t.re| * |gammaE1| + |t.re| * Real.exp 1) + (-σ) * Real.log x) :=
        Real.exp_le_exp.mpr harg
    _ = Real.exp (1 + |t.re| * |gammaE1| + |t.re| * Real.exp 1) * Real.exp ((-σ) * Real.log x) :=
        Real.exp_add _ _
    _ = Real.exp (1 + |t.re| * |gammaE1| + |t.re| * Real.exp 1) * x ^ (-σ) := by
        rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]

theorem differentiableOn_T_short :
    DifferentiableOn ℂ T_short {t : ℂ | 0 < t.re ∧ t.re < 1} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀.1
  have h1 : t₀.re < 1 := ht₀.2
  let r : ℝ := min (t₀.re / 4) ((1 - t₀.re) / 4)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  let σ_hi : ℝ := t₀.re + r
  have hσ_hi_lt : σ_hi < 1 := by
    have : r ≤ (1 - t₀.re) / 4 := min_le_right _ _
    dsimp [σ_hi]; linarith
  let δ1 : ℝ := (1 - σ_hi) / 2
  have hδ1 : 0 < δ1 := by dsimp [δ1]; linarith
  let α1 : ℝ := σ_hi + δ1
  have hα1_lt : α1 < 1 := by dsimp [α1, δ1]; linarith
  let K1 : ℝ := (|gammaE1| + Real.exp 1 + δ1⁻¹) * Real.exp (1 + |gammaE1|)
  have hbound_int : IntegrableOn (fun x : ℝ => K1 * x ^ (-α1)) (Set.Ioc 0 (Real.log 2)) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Real.log 2) (by linarith)).1.const_mul K1
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ)))
        (volume.restrict (Set.Ioc 0 (Real.log 2))) :=
    Eventually.of_forall fun t =>
      (Complex.continuous_exp.comp_continuousOn
        (Complex.continuous_ofReal.continuousOn.sub
          (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
            (continuousOn_Ei_real.mono Set.Ioc_subset_Ioi_self))))).aestronglyMeasurable measurableSet_Ioc
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => -(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t₀ * (Ei_real x : ℂ)))
      (volume.restrict (Set.Ioc 0 (Real.log 2))) :=
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_Ei_real.mono Set.Ioc_subset_Ioi_self)).neg.mul
      (Complex.continuous_exp.comp_continuousOn
        (Complex.continuous_ofReal.continuousOn.sub
          (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
            (continuousOn_Ei_real.mono Set.Ioc_subset_Ioi_self)))))).aestronglyMeasurable measurableSet_Ioc
  have hbound_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 (Real.log 2))), ∀ t ∈ Metric.ball t₀ r,
      ‖-(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))‖ ≤ K1 * x ^ (-α1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx t ht
    have hx1 : x ≤ 1 := hx.2.trans log_two_le_one
    have hdist : ‖t - t₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    have hre_abs : |t.re - t₀.re| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (t - t₀)) hdist
    have htre_pos : 0 < t.re := by
      have : r ≤ t₀.re / 4 := min_le_left _ _
      linarith [(abs_lt.mp hre_abs).1]
    have htre_hi : t.re ≤ σ_hi := by dsimp [σ_hi]; linarith [(abs_lt.mp hre_abs).2]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_cexp_sub_mul_Ei_real]
    have hlog_np : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx1
    have hlog_le : -Real.log x ≤ δ1⁻¹ * x ^ (-δ1) := by
      have h1' : δ1 * (-Real.log x) ≤ Real.exp (δ1 * (-Real.log x)) :=
        le_trans (by linarith) (Real.add_one_le_exp _)
      have h2' : Real.exp (δ1 * (-Real.log x)) = x ^ (-δ1) := by
        rw [Real.rpow_def_of_pos hx.1]; congr 1; ring
      rw [h2'] at h1'
      rw [← div_eq_inv_mul, le_div_iff₀ hδ1, mul_comm]
      exact h1'
    have h1_le_rpow : (1 : ℝ) ≤ x ^ (-δ1) := by
      rw [Real.rpow_def_of_pos hx.1]
      exact Real.one_le_exp (by nlinarith)
    have hEi_abs : |Ei_real x| ≤ (|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1) := by
      have hsmall := abs_Ei_real_le_small hx.1 hx1
      have hnn : 0 ≤ |gammaE1| + Real.exp 1 := by positivity
      calc |Ei_real x| ≤ |gammaE1| + Real.exp 1 + (-Real.log x) := hsmall
        _ ≤ (|gammaE1| + Real.exp 1) * x ^ (-δ1) + δ1⁻¹ * x ^ (-δ1) := by nlinarith
        _ = (|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1) := by ring
    have hge := Ei_real_ge_log hx.1
    have harg : x - t.re * Ei_real x ≤ (1 + |gammaE1|) + (-σ_hi) * Real.log x := by
      have hg : -t.re * gammaE1 ≤ |gammaE1| := by
        have ht1' : t.re ≤ 1 := by linarith
        calc -t.re * gammaE1 ≤ |-t.re * gammaE1| := le_abs_self _
          _ = t.re * |gammaE1| := by rw [abs_mul, abs_neg, abs_of_pos htre_pos]
          _ ≤ 1 * |gammaE1| := mul_le_mul_of_nonneg_right ht1' (abs_nonneg _)
          _ = |gammaE1| := one_mul _
      nlinarith [hx1, htre_hi, hlog_np]
    have hexp_le : Real.exp (x - t.re * Ei_real x) ≤ Real.exp (1 + |gammaE1|) * x ^ (-σ_hi) := by
      calc Real.exp (x - t.re * Ei_real x)
          ≤ Real.exp ((1 + |gammaE1|) + (-σ_hi) * Real.log x) := Real.exp_le_exp.mpr harg
        _ = Real.exp (1 + |gammaE1|) * Real.exp ((-σ_hi) * Real.log x) := Real.exp_add _ _
        _ = Real.exp (1 + |gammaE1|) * x ^ (-σ_hi) := by
            rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]
    calc |Ei_real x| * Real.exp (x - t.re * Ei_real x)
        ≤ ((|gammaE1| + Real.exp 1 + δ1⁻¹) * x ^ (-δ1)) *
            (Real.exp (1 + |gammaE1|) * x ^ (-σ_hi)) :=
          mul_le_mul hEi_abs hexp_le (Real.exp_pos _).le (by positivity)
      _ = K1 * (x ^ (-σ_hi) * x ^ (-δ1)) := by dsimp [K1]; ring
      _ = K1 * x ^ (-α1) := by rw [← Real.rpow_add hx.1]; congr 2; dsimp [α1]; ring
  have hdiff_ae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioc 0 (Real.log 2))), ∀ t ∈ Metric.ball t₀ r,
      HasDerivAt (fun z : ℂ => Complex.exp ((x : ℂ) - z * (Ei_real x : ℂ)))
        (-(Ei_real x : ℂ) * Complex.exp ((x : ℂ) - t * (Ei_real x : ℂ))) t := by
    filter_upwards with x t _
    have h1' : HasDerivAt (fun z : ℂ => (x : ℂ) - z * (Ei_real x : ℂ)) (-(Ei_real x : ℂ)) t := by
      have hmul : HasDerivAt (fun z : ℂ => z * (Ei_real x : ℂ)) (Ei_real x : ℂ) t := by
        simpa using (hasDerivAt_id t).mul_const (Ei_real x : ℂ)
      exact hmul.const_sub (x : ℂ)
    convert h1'.cexp using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hr)
    hF_meas (integrableOn_T_short h1) hF'_meas hbound_ae hbound_int hdiff_ae).2.differentiableAt.differentiableWithinAt

/-- Holomorphic difference `(J_invLi u : ℂ) - T_integral (exp (-u))` extended to `halfStrip`. -/
@[expose] def diff_J_T_holo (z : ℂ) : ℂ :=
  let t : ℂ := Complex.exp (-z)
  let c₀ : ℂ := (Ei_real (Real.log 2) : ℂ)
  (Complex.exp (c₀ * t) - 1) * T_integral t - Complex.exp (c₀ * t) * t * T_short t + 2 * t

lemma diff_J_T_holo_ofReal {u : ℝ} (hu : 0 < u) :
    diff_J_T_holo (u : ℂ) = (J_invLi u : ℂ) - T_integral (Real.exp (-u)) := by
  set t : ℝ := Real.exp (-u)
  set c₀ : ℝ := Ei_real (Real.log 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit : T_inner (t : ℂ) = T_short (t : ℂ) +
      ((∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x) : ℝ) : ℂ) := by
    have hint := integrableOn_T_integrand (t := (t : ℂ)) (by simpa using ht0) (by simpa using ht1)
    dsimp only [T_inner, T_short]
    rw [← Set.Ioc_union_Ioi_eq_Ioi hlog2_pos.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self)
        (hint.mono_set (Set.Ioi_subset_Ioi hlog2_pos.le))]
    congr 1
    change ∫ x in Set.Ioi (Real.log 2), Complex.exp ((x : ℂ) - (t : ℂ) * (Ei_real x : ℂ)) =
      Complex.ofRealCLM (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x))
    rw [← Complex.ofRealCLM.integral_comp_comm
      ((integrableOn_exp_sub_mul_Ei_real ht0 ht1).mono_set (Set.Ioi_subset_Ioi hlog2_pos.le))]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp [Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_mul]
  have hJ := J_invLi_eq_tail_Ei hu
  dsimp only [diff_J_T_holo]
  have hexp_t : Complex.exp (-(u : ℂ)) = (t : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hexp_t, hJ, T_integral_eq_mul_T_inner, hsplit]
  change (Complex.exp ((c₀ : ℂ) * (t : ℂ)) - 1) *
      ((t : ℂ) * (T_short (t : ℂ) + ((∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x) : ℝ) : ℂ))) -
      Complex.exp ((c₀ : ℂ) * (t : ℂ)) * (t : ℂ) * T_short (t : ℂ) + 2 * (t : ℂ) =
    ((Real.exp (c₀ * t) * t * (∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x)) + 2 * t : ℝ) : ℂ) -
      (t : ℂ) * (T_short (t : ℂ) + ((∫ x in Set.Ioi (Real.log 2), Real.exp (x - t * Ei_real x) : ℝ) : ℂ))
  push_cast
  ring

/-- **Piece (C)**: Every derivative of `u ↦ (J_invLi u : ℂ) - T_integral (exp (-u))` decays as
`O(u * exp (-u))` on `[1, ∞)`. -/
theorem J_invLi_sub_T_jet_exp_decay (j : ℕ) :
    ∃ C > 0, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ) - T_integral (Real.exp (-v))) u‖ ≤
        C * u * Real.exp (-u) := by
  obtain ⟨C_T, hCT, hT⟩ := exists_norm_T_integral_exp_neg_le
  let c₀ : ℝ := Ei_real (Real.log 2)
  have hdiff : DifferentiableOn ℂ diff_J_T_holo halfStrip := by
    intro z hz
    have hb := exp_neg_strip_bounds hz.1.le hz.2.le
    have ht0 : 0 < (Complex.exp (-z)).re := lt_of_lt_of_le (by positivity) hb.1
    have ht1 : (Complex.exp (-z)).re < 1 := by linarith [hb.2.2.1]
    have hT_open : IsOpen {t : ℂ | 0 < t.re ∧ t.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w)) z :=
      Complex.differentiable_exp.comp differentiable_id.neg |>.differentiableAt
    have hT_d : DifferentiableAt ℂ (fun w : ℂ => T_integral (Complex.exp (-w))) z :=
      show DifferentiableAt ℂ (T_integral ∘ fun w : ℂ => Complex.exp (-w)) z from
        (differentiableOn_T_integral.differentiableAt (hT_open.mem_nhds ⟨ht0, ht1⟩)).comp z hexp
    have hTs_d : DifferentiableAt ℂ (fun w : ℂ => T_short (Complex.exp (-w))) z :=
      show DifferentiableAt ℂ (T_short ∘ fun w : ℂ => Complex.exp (-w)) z from
        (differentiableOn_T_short.differentiableAt (hT_open.mem_nhds ⟨ht0, ht1⟩)).comp z hexp
    have hfac : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((c₀ : ℂ) * Complex.exp (-w))) z :=
      Complex.differentiable_exp.differentiableAt.comp _ (hexp.const_mul (c₀ : ℂ))
    exact (((hfac.sub (differentiableAt_const 1)).mul hT_d).sub
      ((hfac.mul hexp).mul hTs_d)).add (hexp.const_mul 2) |>.differentiableWithinAt
  let I_sh : ℝ := ∫ x in Set.Ioc (0 : ℝ) (Real.log 2), x ^ (-(3 / 4 : ℝ))
  have hIsh_nn : 0 ≤ I_sh :=
    setIntegral_nonneg measurableSet_Ioc fun x hx => Real.rpow_nonneg hx.1.le _
  let C_sh : ℝ := Real.exp (1 + |gammaE1|) * I_sh
  let C_C : ℝ := |c₀| * Real.exp |c₀| * C_T + Real.exp |c₀| * C_sh + 2
  have hbound : ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → |z.im| ≤ 1 / 2 →
      ‖diff_J_T_holo z‖ ≤ C_C * (z.re + 1) * Real.exp (-z.re) := by
    intro z hre him
    have hb := exp_neg_strip_bounds hre him
    set t : ℂ := Complex.exp (-z)
    have ht_norm : ‖t‖ = Real.exp (-z.re) := hb.2.2.2
    have ht_le1 : ‖t‖ ≤ 1 := by rw [ht_norm]; exact Real.exp_le_one_iff.mpr (by linarith)
    have hσ_pos : 0 < t.re := lt_of_lt_of_le (by positivity) hb.1
    have hσ_lt : t.re < 3 / 4 := hb.2.2.1
    have hct_norm : ‖(c₀ : ℂ) * t‖ = |c₀| * Real.exp (-z.re) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ht_norm]
    have hexp_sub : ‖Complex.exp ((c₀ : ℂ) * t) - 1‖ ≤ |c₀| * Real.exp |c₀| * Real.exp (-z.re) := by
      have h1 := norm_cexp_sub_one_le ((c₀ : ℂ) * t)
      rw [hct_norm] at h1
      have h2 : Real.exp (|c₀| * Real.exp (-z.re)) ≤ Real.exp |c₀| :=
        Real.exp_le_exp.mpr (by
          have : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          nlinarith [abs_nonneg c₀])
      calc ‖Complex.exp ((c₀ : ℂ) * t) - 1‖
          ≤ |c₀| * Real.exp (-z.re) * Real.exp (|c₀| * Real.exp (-z.re)) := h1
        _ ≤ |c₀| * Real.exp (-z.re) * Real.exp |c₀| := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = |c₀| * Real.exp |c₀| * Real.exp (-z.re) := by ring
    have hexp_fac : ‖Complex.exp ((c₀ : ℂ) * t)‖ ≤ Real.exp |c₀| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc ((c₀ : ℂ) * t).re ≤ ‖(c₀ : ℂ) * t‖ := Complex.re_le_norm _
        _ = |c₀| * Real.exp (-z.re) := hct_norm
        _ ≤ |c₀| * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (abs_nonneg _)
        _ = |c₀| := mul_one _
    have hTsh_le : ‖T_short t‖ ≤ C_sh := by
      dsimp only [T_short, C_sh, I_sh]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine setIntegral_mono_on (integrableOn_T_short (by linarith)).norm
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Real.log 2) (by norm_num)).1.const_mul _)
        measurableSet_Ioc fun x hx => ?_
      have hx1 : x ≤ 1 := hx.2.trans log_two_le_one
      rw [norm_cexp_sub_mul_Ei_real]
      have hge := Ei_real_ge_log hx.1
      have hlog_np : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx1
      have hg : -t.re * gammaE1 ≤ |gammaE1| := by
        calc -t.re * gammaE1 ≤ |-t.re * gammaE1| := le_abs_self _
          _ = t.re * |gammaE1| := by rw [abs_mul, abs_neg, abs_of_pos hσ_pos]
          _ ≤ 1 * |gammaE1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ = |gammaE1| := one_mul _
      have harg : x - t.re * Ei_real x ≤ (1 + |gammaE1|) + (-(3 / 4 : ℝ)) * Real.log x := by nlinarith
      calc Real.exp (x - t.re * Ei_real x)
          ≤ Real.exp ((1 + |gammaE1|) + (-(3 / 4 : ℝ)) * Real.log x) := Real.exp_le_exp.mpr harg
        _ = Real.exp (1 + |gammaE1|) * Real.exp ((-(3 / 4 : ℝ)) * Real.log x) := Real.exp_add _ _
        _ = Real.exp (1 + |gammaE1|) * x ^ (-(3 / 4 : ℝ)) := by
            rw [Real.rpow_def_of_pos hx.1, mul_comm (Real.log x)]
    dsimp only [diff_J_T_holo]
    change ‖(Complex.exp ((c₀ : ℂ) * t) - 1) * T_integral t - Complex.exp ((c₀ : ℂ) * t) * t * T_short t + 2 * t‖ ≤
      C_C * (z.re + 1) * Real.exp (-z.re)
    have h1 : ‖(Complex.exp ((c₀ : ℂ) * t) - 1) * T_integral t - Complex.exp ((c₀ : ℂ) * t) * t * T_short t + 2 * t‖ ≤
        ‖(Complex.exp ((c₀ : ℂ) * t) - 1) * T_integral t‖ +
        ‖Complex.exp ((c₀ : ℂ) * t) * t * T_short t‖ + ‖(2 : ℂ) * t‖ := by
      calc _ ≤ ‖(Complex.exp ((c₀ : ℂ) * t) - 1) * T_integral t - Complex.exp ((c₀ : ℂ) * t) * t * T_short t‖ + ‖(2 : ℂ) * t‖ :=
            norm_add_le _ _
        _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
    have hp1 : ‖(Complex.exp ((c₀ : ℂ) * t) - 1) * T_integral t‖ ≤
        (|c₀| * Real.exp |c₀| * C_T) * (z.re + 1) * Real.exp (-z.re) := by
      rw [norm_mul]
      calc _ ≤ (|c₀| * Real.exp |c₀| * Real.exp (-z.re)) * (C_T * (z.re + 1)) :=
            mul_le_mul hexp_sub (hT z hre him) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hp2 : ‖Complex.exp ((c₀ : ℂ) * t) * t * T_short t‖ ≤
        (Real.exp |c₀| * C_sh) * Real.exp (-z.re) := by
      rw [norm_mul, norm_mul, ht_norm]
      have h12 : ‖Complex.exp ((c₀ : ℂ) * t)‖ * Real.exp (-z.re) ≤ Real.exp |c₀| * Real.exp (-z.re) :=
        mul_le_mul_of_nonneg_right hexp_fac (Real.exp_pos _).le
      calc _ ≤ (Real.exp |c₀| * Real.exp (-z.re)) * C_sh :=
            mul_le_mul h12 hTsh_le (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hp3 : ‖(2 : ℂ) * t‖ = 2 * Real.exp (-z.re) := by
      rw [norm_mul, ht_norm]; norm_num
    have hCsh_nn : 0 ≤ C_sh := by dsimp [C_sh]; positivity
    have hre1 : 1 ≤ z.re + 1 := by linarith
    have h2' : (Real.exp |c₀| * C_sh + 2) * Real.exp (-z.re) ≤
        (Real.exp |c₀| * C_sh + 2) * (z.re + 1) * Real.exp (-z.re) := by
      have ha : (Real.exp |c₀| * C_sh + 2) * 1 ≤ (Real.exp |c₀| * C_sh + 2) * (z.re + 1) :=
        mul_le_mul_of_nonneg_left hre1 (by positivity)
      rw [mul_one] at ha
      exact mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le
    dsimp only [C_C]
    linarith
  obtain ⟨Cj, hCj, hCj_bound⟩ :=
    norm_iteratedDeriv_ofReal_exp_decay_of_halfStrip hdiff (by dsimp [C_C, C_sh]; positivity) hbound j
  refine ⟨Cj, hCj, fun u hu => ?_⟩
  have hloc : (fun v : ℝ => (J_invLi v : ℂ) - T_integral (Real.exp (-v))) =ᶠ[𝓝 u]
      (fun x : ℝ => diff_J_T_holo (x : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < u by linarith)] with x hx
    exact (diff_J_T_holo_ofReal hx).symm
  rw [hloc.iteratedDeriv_eq]
  exact hCj_bound u hu

/-! #### Piece (B): Exponential Jet Decay of `S_invLi u - J_invLi u` (Riemann-Sum MVT Bound) -/

/-- Sequence `n ↦ inverseLi (n + 1)`. -/
@[expose] def invLiSeq (n : ℕ) : ℝ := NthPrime.inverseLi (n + 1 : ℝ)

/-- Discrete smoothed `li⁻¹` sum `S_invLi u = t^2 ∑_{n=0}^∞ inverseLi (n+1) exp(-t(n+1))`. -/
@[expose] def S_invLi (u : ℝ) : ℝ :=
  ∑' n : ℕ, NthPrime.abelPolyTerm invLiSeq 1 n u

/-- Continuous polynomial-weighted `li⁻¹` Laplace integral. -/
@[expose] def abelIntPoly (P : Polynomial ℝ) (u : ℝ) : ℝ :=
  let t : ℝ := Real.exp (-u)
  t ^ 2 * ∫ v in Set.Ioi (0 : ℝ), NthPrime.inverseLi v * P.eval (t * v) * Real.exp (-(t * v))

lemma abelIntPoly_one : abelIntPoly 1 = J_invLi := by
  ext u
  simp [abelIntPoly, J_invLi]

/-- Elementary exponential absorption of monomials on `[0, ∞)`. -/
lemma pow_mul_exp_neg_mul_le (k : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-a * x) ≤ ((2 / a) ^ k * (k.factorial : ℝ)) * Real.exp (-(a / 2) * x) := by
  have h := Real.pow_div_factorial_le_exp ((a / 2) * x) (by positivity) k
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hfact).mp h
  have hpow : x ^ k = (2 / a) ^ k * ((a / 2) * x) ^ k := by
    rw [← mul_pow]; congr 1; field_simp [ha.ne']
  have hh : x ^ k ≤ (2 / a) ^ k * (k.factorial : ℝ) * Real.exp ((a / 2) * x) := by
    rw [hpow]
    calc (2 / a) ^ k * ((a / 2) * x) ^ k
        ≤ (2 / a) ^ k * (Real.exp ((a / 2) * x) * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (2 / a) ^ k * (k.factorial : ℝ) * Real.exp ((a / 2) * x) := by ring
  calc x ^ k * Real.exp (-a * x)
      ≤ ((2 / a) ^ k * (k.factorial : ℝ) * Real.exp ((a / 2) * x)) * Real.exp (-a * x) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = ((2 / a) ^ k * (k.factorial : ℝ)) * (Real.exp ((a / 2) * x) * Real.exp (-a * x)) := by ring
    _ = ((2 / a) ^ k * (k.factorial : ℝ)) * Real.exp (-(a / 2) * x) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Any polynomial `P` satisfies `|P.eval y| ≤ C * (1 + y ^ d)` on `[0, ∞)`. -/
lemma exists_poly_abs_le (P : Polynomial ℝ) :
    ∃ C > 0, ∀ y : ℝ, 0 ≤ y → |P.eval y| ≤ C * (1 + y ^ P.natDegree) := by
  refine ⟨(∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k|) + 1, by
    have : 0 ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith, fun y hy => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  have htri : |∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * y ^ k| ≤
      ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * (1 + y ^ P.natDegree) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg hy]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hk_le : k ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hy1 : y ≤ 1
    · have : y ^ k ≤ 1 := pow_le_one₀ hy hy1
      linarith [pow_nonneg hy P.natDegree]
    · push Not at hy1
      have : y ^ k ≤ y ^ P.natDegree := pow_le_pow_right₀ hy1.le hk_le
      linarith
  rw [← Finset.sum_mul] at htri
  have h1 : (0 : ℝ) ≤ 1 + y ^ P.natDegree := by positivity
  nlinarith

/-- Quadratic growth of `invLiSeq` and `Nat.nth Nat.Prime`. -/
lemma abs_invLiSeq_le (n : ℕ) : |invLiSeq n| ≤ 16 * ((n : ℝ) + 2) ^ 2 := by
  have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)).1
  dsimp only [invLiSeq]
  rw [abs_of_nonneg (by linarith [hspec.1])]
  have h2 : (4 * ((n : ℝ) + 1 + 1)) ^ 2 = 16 * ((n : ℝ) + 2) ^ 2 := by ring
  linarith [hspec.2]

/-- Summable local bound for `abelPolyTerm` on any sequence with quadratic growth. -/
lemma abelPoly_localBound_quad {a : ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (ha : ∀ n : ℕ, |a n| ≤ A * ((n : ℝ) + 2) ^ 2) (P : Polynomial ℝ) (x : ℝ) :
    ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n u, u ∈ Set.Ioo (x - 1) (x + 1) → |NthPrime.abelPolyTerm a P n u| ≤ B n := by
  obtain ⟨CP, hCP, hP⟩ := exists_poly_abs_le P
  let d := P.natDegree
  let T := Real.exp (-(x - 1))
  let τ := Real.exp (-(x + 1))
  let r := Real.exp (-τ)
  have hτ : 0 < τ := Real.exp_pos _
  have hr : 0 < r := Real.exp_pos _
  have hlt : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hτ)
  let K : ℝ := T ^ 2 * (4 * A) * CP * (1 + T ^ d)
  have hs0 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2) * r ^ (n + 1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_pos hr])).comp_injective Nat.succ_injective
  have hsd : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (d + 2)) * r ^ (n + 1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (d + 2) (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_pos hr])).comp_injective Nat.succ_injective
  refine ⟨fun n => K * ((((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ (d + 2)) * r ^ (n + 1)), ?_, ?_⟩
  · have hadd := (hs0.add hsd).mul_left K
    exact hadd.congr fun n => by ring
  · intro n u hu
    have hT : Real.exp (-u) ≤ T := Real.exp_le_exp.mpr (neg_le_neg hu.1.le)
    have hlow : τ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg hu.2.le)
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hkernel : Real.exp (-(Real.exp (-u) * ((n : ℝ) + 1))) ≤ r ^ (n + 1) := by
      dsimp [r]; rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      push_cast; nlinarith
    have ha' : |a n| ≤ 4 * A * ((n : ℝ) + 1) ^ 2 := by
      have hsq : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
      calc |a n| ≤ A * ((n : ℝ) + 2) ^ 2 := ha n
        _ ≤ A * (4 * ((n : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hsq hA.le
        _ = 4 * A * ((n : ℝ) + 1) ^ 2 := by ring
    have hPe : |P.eval (Real.exp (-u) * ((n : ℝ) + 1))| ≤
        CP * (1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d) := by
      have h1 := hP (Real.exp (-u) * ((n : ℝ) + 1)) (by positivity)
      have hpow : (Real.exp (-u) * ((n : ℝ) + 1)) ^ d ≤ T ^ d * ((n : ℝ) + 1) ^ d := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hT d) (by positivity)
      have hT1 : (1 : ℝ) ≤ 1 + T ^ d := by linarith [pow_nonneg (Real.exp_pos (-(x - 1))).le d]
      have h1y : 1 + (Real.exp (-u) * ((n : ℝ) + 1)) ^ d ≤ (1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d) := by
        nlinarith [pow_nonneg (Real.exp_pos (-(x - 1))).le d, pow_nonneg hn1_pos.le d]
      calc |P.eval (Real.exp (-u) * ((n : ℝ) + 1))|
          ≤ CP * (1 + (Real.exp (-u) * ((n : ℝ) + 1)) ^ d) := h1
        _ ≤ CP * ((1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d)) := mul_le_mul_of_nonneg_left h1y hCP.le
        _ = CP * (1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d) := by ring
    dsimp only [NthPrime.abelPolyTerm]
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hpow2 : Real.exp (-u) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hT 2
    have h12 : Real.exp (-u) ^ 2 * |a n| ≤ T ^ 2 * (4 * A * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul hpow2 ha' (abs_nonneg _) (by positivity)
    have h123 : Real.exp (-u) ^ 2 * |a n| * |P.eval (Real.exp (-u) * ((n : ℝ) + 1))| ≤
        (T ^ 2 * (4 * A * ((n : ℝ) + 1) ^ 2)) * (CP * (1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d)) :=
      mul_le_mul h12 hPe (abs_nonneg _) (by positivity)
    calc Real.exp (-u) ^ 2 * |a n| * |P.eval (Real.exp (-u) * ((n : ℝ) + 1))| *
            Real.exp (-(Real.exp (-u) * ((n : ℝ) + 1)))
        ≤ ((T ^ 2 * (4 * A * ((n : ℝ) + 1) ^ 2)) * (CP * (1 + T ^ d) * (1 + ((n : ℝ) + 1) ^ d))) *
            r ^ (n + 1) :=
          mul_le_mul h123 hkernel (Real.exp_pos _).le (by positivity)
      _ = K * ((((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ (d + 2)) * r ^ (n + 1)) := by
          dsimp only [K]; push_cast; rw [pow_add]; ring

/-- Termwise differentiation of `abelPolySum` for any sequence with quadratic growth. -/
theorem hasDerivAt_abelPolySum_quad {a : ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (ha : ∀ n : ℕ, |a n| ≤ A * ((n : ℝ) + 2) ^ 2) (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun u => ∑' n, NthPrime.abelPolyTerm a P n u)
      (∑' n, NthPrime.abelPolyTerm a (NthPrime.abelJetStep P) n x) x := by
  have hx : x ∈ Set.Ioo (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨B, hB, hbound⟩ := abelPoly_localBound_quad hA ha (NthPrime.abelJetStep P) x
  obtain ⟨C, hC, hbase⟩ := abelPoly_localBound_quad hA ha P x
  exact hasDerivAt_tsum_of_isPreconnected hB isOpen_Ioo isPreconnected_Ioo
    (fun n u _ => NthPrime.abelPolyTerm_hasDerivAt a P n u)
    (fun n u hu => by simpa only [Real.norm_eq_abs] using hbound n u hu) hx
    (hC.of_norm_bounded fun n => hbase n x hx) hx

theorem iteratedDeriv_S_invLi (k : ℕ) :
    iteratedDeriv k S_invLi =
      fun u => ∑' n, NthPrime.abelPolyTerm invLiSeq (NthPrime.abelJetStep^[k] 1) n u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun u =>
      (hasDerivAt_abelPolySum_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le _ u).deriv

theorem contDiff_S_invLi (n : ℕ) : ContDiff ℝ n S_invLi := by
  have hgen : ∀ (m : ℕ) (P : Polynomial ℝ),
      ContDiff ℝ m (fun u => ∑' k, NthPrime.abelPolyTerm invLiSeq P k u) := by
    intro m
    induction m with
    | zero =>
      intro P
      rw [Nat.cast_zero, contDiff_zero]
      exact Differentiable.continuous fun u =>
        (hasDerivAt_abelPolySum_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le P u).differentiableAt
    | succ m ih =>
      intro P
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun u => (hasDerivAt_abelPolySum_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le P u).differentiableAt,
        by simp, ?_⟩
      have hd : deriv (fun u => ∑' k, NthPrime.abelPolyTerm invLiSeq P k u) =
          fun u => ∑' k, NthPrime.abelPolyTerm invLiSeq (NthPrime.abelJetStep P) k u :=
        funext fun u =>
          (hasDerivAt_abelPolySum_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le P u).deriv
      rw [hd]
      exact ih (NthPrime.abelJetStep P)
  exact hgen n 1

/-- Global integrability of the `abelIntPoly` integrand on `(0, ∞)`. -/
lemma integrableOn_abelIntPoly (P : Polynomial ℝ) (u : ℝ) :
    IntegrableOn (fun v : ℝ => NthPrime.inverseLi v * P.eval (Real.exp (-u) * v) *
      Real.exp (-(Real.exp (-u) * v))) (Set.Ioi 0) := by
  set t : ℝ := Real.exp (-u)
  have ht : 0 < t := Real.exp_pos _
  obtain ⟨CP, hCP, hP⟩ := exists_poly_abs_le P
  let d := P.natDegree
  have hcont_inv : ContinuousOn NthPrime.inverseLi (Set.Ioi (0 : ℝ)) :=
    fun v hv => (NthPrime.inverseLi_hasDerivAt hv).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => NthPrime.inverseLi v * P.eval (t * v) * Real.exp (-(t * v)))
      (volume.restrict (Set.Ioi 0)) :=
    ((hcont_inv.mul (P.continuous.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  let K : ℝ := 64 * CP * (1 + t ^ d) *
    ((2 / t) ^ 0 * (0 : ℕ).factorial + (2 / t) ^ 2 * (2 : ℕ).factorial +
      (2 / t) ^ d * d.factorial + (2 / t) ^ (d + 2) * (d + 2).factorial)
  have hdom : IntegrableOn (fun v : ℝ => K * Real.exp (-(t / 2) * v)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul K
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := hv
  have hspec := (NthPrime.inverseLi_spec hv0.le).1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by linarith [hspec.1]),
    abs_of_pos (Real.exp_pos _)]
  have hinv_le : NthPrime.inverseLi v ≤ 64 * (1 + v ^ 2) := by
    have : (4 * (v + 1)) ^ 2 ≤ 64 * (1 + v ^ 2) := by nlinarith [sq_nonneg (v - 1)]
    exact hspec.2.trans this
  have hP_le : |P.eval (t * v)| ≤ CP * (1 + t ^ d) * (1 + v ^ d) := by
    have h1 := hP (t * v) (by positivity)
    rw [mul_pow] at h1
    have h2 : 1 + t ^ d * v ^ d ≤ (1 + t ^ d) * (1 + v ^ d) := by nlinarith [pow_nonneg ht.le d, pow_nonneg hv0.le d]
    calc |P.eval (t * v)| ≤ CP * (1 + t ^ d * v ^ d) := h1
      _ ≤ CP * ((1 + t ^ d) * (1 + v ^ d)) := mul_le_mul_of_nonneg_left h2 hCP.le
      _ = CP * (1 + t ^ d) * (1 + v ^ d) := by ring
  have hprod : NthPrime.inverseLi v * |P.eval (t * v)| ≤
      64 * CP * (1 + t ^ d) * (1 + v ^ 2 + v ^ d + v ^ (d + 2)) := by
    have hmul := mul_le_mul hinv_le hP_le (abs_nonneg _) (by positivity)
    refine hmul.trans_eq ?_
    rw [pow_add]; ring
  have hb0 := pow_mul_exp_neg_mul_le 0 ht hv0.le
  have hb2 := pow_mul_exp_neg_mul_le 2 ht hv0.le
  have hbd := pow_mul_exp_neg_mul_le d ht hv0.le
  have hbd2 := pow_mul_exp_neg_mul_le (d + 2) ht hv0.le
  have hexp_eq : Real.exp (-(t * v)) = Real.exp (-t * v) := by congr 1; ring
  rw [hexp_eq]
  calc NthPrime.inverseLi v * |P.eval (t * v)| * Real.exp (-t * v)
      ≤ 64 * CP * (1 + t ^ d) * (1 + v ^ 2 + v ^ d + v ^ (d + 2)) * Real.exp (-t * v) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = 64 * CP * (1 + t ^ d) *
          (v ^ 0 * Real.exp (-t * v) + v ^ 2 * Real.exp (-t * v) +
            v ^ d * Real.exp (-t * v) + v ^ (d + 2) * Real.exp (-t * v)) := by
        simp only [pow_zero]; ring
    _ ≤ 64 * CP * (1 + t ^ d) *
          (((2 / t) ^ 0 * (0 : ℕ).factorial) * Real.exp (-(t / 2) * v) +
            ((2 / t) ^ 2 * (2 : ℕ).factorial) * Real.exp (-(t / 2) * v) +
            ((2 / t) ^ d * d.factorial) * Real.exp (-(t / 2) * v) +
            ((2 / t) ^ (d + 2) * (d + 2).factorial) * Real.exp (-(t / 2) * v)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = K * Real.exp (-(t / 2) * v) := by dsimp only [K]; ring

/-- Dominated differentiation of `abelIntPoly P`: `(abelIntPoly P)' = abelIntPoly (abelJetStep P)`. -/
theorem hasDerivAt_abelIntPoly (P : Polynomial ℝ) (u₀ : ℝ) :
    HasDerivAt (abelIntPoly P) (abelIntPoly (NthPrime.abelJetStep P) u₀) u₀ := by
  let F : ℝ → ℝ → ℝ := fun u v =>
    (Real.exp (-u)) ^ 2 * NthPrime.inverseLi v * P.eval (Real.exp (-u) * v) *
      Real.exp (-(Real.exp (-u) * v))
  let F' : ℝ → ℝ → ℝ := fun u v =>
    (Real.exp (-u)) ^ 2 * NthPrime.inverseLi v * (NthPrime.abelJetStep P).eval (Real.exp (-u) * v) *
      Real.exp (-(Real.exp (-u) * v))
  have hEq : abelIntPoly P = fun u => ∫ v in Set.Ioi (0 : ℝ), F u v := by
    ext u; dsimp only [abelIntPoly, F]
    rw [← integral_const_mul]
    congr 1; ext v; ring
  have hEq' : abelIntPoly (NthPrime.abelJetStep P) u₀ = ∫ v in Set.Ioi (0 : ℝ), F' u₀ v := by
    dsimp only [abelIntPoly, F']
    rw [← integral_const_mul]
    congr 1; ext v; ring
  rw [hEq, hEq']
  let T := Real.exp (-(u₀ - 1))
  let τ := Real.exp (-(u₀ + 1))
  have hτ : 0 < τ := Real.exp_pos _
  obtain ⟨CQ, hCQ, hQ⟩ := exists_poly_abs_le (NthPrime.abelJetStep P)
  let d := (NthPrime.abelJetStep P).natDegree
  let K : ℝ := T ^ 2 * 64 * CQ * (1 + T ^ d) *
    ((2 / τ) ^ 0 * (0 : ℕ).factorial + (2 / τ) ^ 2 * (2 : ℕ).factorial +
      (2 / τ) ^ d * d.factorial + (2 / τ) ^ (d + 2) * (d + 2).factorial)
  have hbound_int : IntegrableOn (fun v : ℝ => K * Real.exp (-(τ / 2) * v)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul K
  have hF_meas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 0)) := by
    refine Eventually.of_forall fun u => ?_
    have h1 := (integrableOn_abelIntPoly P u).const_mul ((Real.exp (-u)) ^ 2)
    have hcongr : (fun v => (Real.exp (-u)) ^ 2 *
        (NthPrime.inverseLi v * P.eval (Real.exp (-u) * v) * Real.exp (-(Real.exp (-u) * v)))) = F u := by
      ext v; dsimp only [F]; ring
    rw [hcongr] at h1
    exact h1.aestronglyMeasurable
  have hF_int : IntegrableOn (F u₀) (Set.Ioi 0) := by
    have h1 := (integrableOn_abelIntPoly P u₀).const_mul ((Real.exp (-u₀)) ^ 2)
    have hcongr : (fun v => (Real.exp (-u₀)) ^ 2 *
        (NthPrime.inverseLi v * P.eval (Real.exp (-u₀) * v) * Real.exp (-(Real.exp (-u₀) * v)))) = F u₀ := by
      ext v; dsimp only [F]; ring
    rwa [hcongr] at h1
  have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Set.Ioi 0)) := by
    have h1 := (integrableOn_abelIntPoly (NthPrime.abelJetStep P) u₀).const_mul ((Real.exp (-u₀)) ^ 2)
    have hcongr : (fun v => (Real.exp (-u₀)) ^ 2 *
        (NthPrime.inverseLi v * (NthPrime.abelJetStep P).eval (Real.exp (-u₀) * v) *
          Real.exp (-(Real.exp (-u₀) * v)))) = F' u₀ := by
      ext v; dsimp only [F']; ring
    rw [hcongr] at h1
    exact h1.aestronglyMeasurable
  have hbound_ae : ∀ᵐ v ∂(volume.restrict (Set.Ioi 0)), ∀ u ∈ Metric.ball u₀ 1,
      ‖F' u v‖ ≤ K * Real.exp (-(τ / 2) * v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv u hu
    have hv0 : 0 < v := hv
    have hd : |u - u₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hu
    have hT : Real.exp (-u) ≤ T := Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hd).1])
    have hτ_le : τ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hd).2])
    have hspec := (NthPrime.inverseLi_spec hv0.le).1
    dsimp only [F']
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _),
      abs_of_pos (by linarith [hspec.1]), abs_of_pos (Real.exp_pos _)]
    have hinv_le : NthPrime.inverseLi v ≤ 64 * (1 + v ^ 2) := by
      have : (4 * (v + 1)) ^ 2 ≤ 64 * (1 + v ^ 2) := by nlinarith [sq_nonneg (v - 1)]
      exact hspec.2.trans this
    have hQ_le : |(NthPrime.abelJetStep P).eval (Real.exp (-u) * v)| ≤
        CQ * (1 + T ^ d) * (1 + v ^ d) := by
      have h1 := hQ (Real.exp (-u) * v) (by positivity)
      rw [mul_pow] at h1
      have hpow : Real.exp (-u) ^ d ≤ T ^ d := pow_le_pow_left₀ (Real.exp_pos _).le hT d
      have h2 : 1 + Real.exp (-u) ^ d * v ^ d ≤ (1 + T ^ d) * (1 + v ^ d) := by
        nlinarith [pow_nonneg (Real.exp_pos (-u)).le d, pow_nonneg hv0.le d,
          pow_nonneg (Real.exp_pos (-(u₀ - 1))).le d]
      calc |(NthPrime.abelJetStep P).eval (Real.exp (-u) * v)|
          ≤ CQ * (1 + Real.exp (-u) ^ d * v ^ d) := h1
        _ ≤ CQ * ((1 + T ^ d) * (1 + v ^ d)) := mul_le_mul_of_nonneg_left h2 hCQ.le
        _ = CQ * (1 + T ^ d) * (1 + v ^ d) := by ring
    have hexp_le : Real.exp (-(Real.exp (-u) * v)) ≤ Real.exp (-τ * v) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpow2 : Real.exp (-u) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hT 2
    have hprod : Real.exp (-u) ^ 2 * NthPrime.inverseLi v *
        |(NthPrime.abelJetStep P).eval (Real.exp (-u) * v)| ≤
        T ^ 2 * 64 * CQ * (1 + T ^ d) * (1 + v ^ 2 + v ^ d + v ^ (d + 2)) := by
      have h12 : Real.exp (-u) ^ 2 * NthPrime.inverseLi v ≤ T ^ 2 * (64 * (1 + v ^ 2)) :=
        mul_le_mul hpow2 hinv_le (by linarith [hspec.1]) (by positivity)
      have h123 := mul_le_mul h12 hQ_le (abs_nonneg _) (by positivity)
      refine h123.trans_eq ?_; rw [pow_add]; ring
    have hb0 := pow_mul_exp_neg_mul_le 0 hτ hv0.le
    have hb2 := pow_mul_exp_neg_mul_le 2 hτ hv0.le
    have hbd := pow_mul_exp_neg_mul_le d hτ hv0.le
    have hbd2 := pow_mul_exp_neg_mul_le (d + 2) hτ hv0.le
    calc Real.exp (-u) ^ 2 * NthPrime.inverseLi v *
            |(NthPrime.abelJetStep P).eval (Real.exp (-u) * v)| * Real.exp (-(Real.exp (-u) * v))
        ≤ (T ^ 2 * 64 * CQ * (1 + T ^ d) * (1 + v ^ 2 + v ^ d + v ^ (d + 2))) * Real.exp (-τ * v) :=
          mul_le_mul hprod hexp_le (Real.exp_pos _).le (by positivity)
      _ = T ^ 2 * 64 * CQ * (1 + T ^ d) *
            (v ^ 0 * Real.exp (-τ * v) + v ^ 2 * Real.exp (-τ * v) +
              v ^ d * Real.exp (-τ * v) + v ^ (d + 2) * Real.exp (-τ * v)) := by
          simp only [pow_zero]; ring
      _ ≤ T ^ 2 * 64 * CQ * (1 + T ^ d) *
            (((2 / τ) ^ 0 * (0 : ℕ).factorial) * Real.exp (-(τ / 2) * v) +
              ((2 / τ) ^ 2 * (2 : ℕ).factorial) * Real.exp (-(τ / 2) * v) +
              ((2 / τ) ^ d * d.factorial) * Real.exp (-(τ / 2) * v) +
              ((2 / τ) ^ (d + 2) * (d + 2).factorial) * Real.exp (-(τ / 2) * v)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = K * Real.exp (-(τ / 2) * v) := by dsimp only [K]; ring
  have hdiff_ae : ∀ᵐ v ∂(volume.restrict (Set.Ioi 0)), ∀ u ∈ Metric.ball u₀ 1,
      HasDerivAt (F · v) (F' u v) u := by
    filter_upwards with v u _
    have ht : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
      simpa using (hasDerivAt_id u).neg.exp
    have hy : HasDerivAt (fun x : ℝ => Real.exp (-x) * v) (-(Real.exp (-u) * v)) u := by
      simpa [neg_mul] using ht.mul_const v
    have htot := (((ht.pow 2).mul_const (NthPrime.inverseLi v)).mul
      ((P.hasDerivAt (Real.exp (-u) * v)).comp u hy)).mul hy.neg.exp
    refine htot.congr_deriv ?_
    dsimp only [F', NthPrime.abelJetStep]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Function.comp_apply,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u₀ zero_lt_one)
    hF_meas hF_int hF'_meas hbound_ae hbound_int hdiff_ae).2

theorem iteratedDeriv_J_invLi (k : ℕ) :
    iteratedDeriv k J_invLi = abelIntPoly (NthPrime.abelJetStep^[k] 1) := by
  rw [← abelIntPoly_one]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun u => (hasDerivAt_abelIntPoly _ u).deriv

theorem contDiff_J_invLi (n : ℕ) : ContDiff ℝ n J_invLi := by
  have hgen : ∀ (m : ℕ) (P : Polynomial ℝ), ContDiff ℝ m (abelIntPoly P) := by
    intro m
    induction m with
    | zero =>
      intro P
      rw [Nat.cast_zero, contDiff_zero]
      exact Differentiable.continuous fun u => (hasDerivAt_abelIntPoly P u).differentiableAt
    | succ m ih =>
      intro P
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun u => (hasDerivAt_abelIntPoly P u).differentiableAt, by simp, ?_⟩
      have hd : deriv (abelIntPoly P) = abelIntPoly (NthPrime.abelJetStep P) :=
        funext fun u => (hasDerivAt_abelIntPoly P u).deriv
      rw [hd]
      exact ih (NthPrime.abelJetStep P)
  rw [← abelIntPoly_one]
  exact hgen n 1

/-- Linear-log growth bound on `inverseLi`: for all `v ≥ 1`,
`inverseLi v ≤ 64 + 2 * v * log (4 * (v + 1))`. -/
lemma inverseLi_le_linear_log {v : ℝ} (hv : 1 ≤ v) :
    NthPrime.inverseLi v ≤ 64 + 2 * v * Real.log (4 * (v + 1)) := by
  rcases eq_or_lt_of_le hv with rfl | hv1
  · have h1 := (NthPrime.inverseLi_spec zero_le_one).1.2
    have hlog : 0 ≤ Real.log (4 * ((1 : ℝ) + 1)) := Real.log_nonneg (by norm_num)
    nlinarith
  · have hcont : ContinuousOn NthPrime.inverseLi (Set.Icc 1 v) :=
      fun x hx => (NthPrime.inverseLi_hasDerivAt (lt_of_lt_of_le zero_lt_one hx.1)).continuousAt.continuousWithinAt
    have hdiff : ∀ x ∈ Set.Ioo 1 v, HasDerivAt NthPrime.inverseLi (Real.log (NthPrime.inverseLi x)) x :=
      fun x hx => NthPrime.inverseLi_hasDerivAt (lt_trans zero_lt_one hx.1)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope NthPrime.inverseLi
      (fun x => Real.log (NthPrime.inverseLi x)) hv1 hcont hdiff
    have hc_spec := (NthPrime.inverseLi_spec (lt_trans zero_lt_one hc.1).le).1
    have hc_pos : 0 < c := lt_trans zero_lt_one hc.1
    have hlog_le : Real.log (NthPrime.inverseLi c) ≤ 2 * Real.log (4 * (v + 1)) := by
      have h1 : NthPrime.inverseLi c ≤ (4 * (v + 1)) ^ 2 :=
        hc_spec.2.trans (pow_le_pow_left₀ (by positivity) (by linarith [hc.2]) 2)
      calc Real.log (NthPrime.inverseLi c)
          ≤ Real.log ((4 * (v + 1)) ^ 2) := Real.log_le_log (by linarith [hc_spec.1]) h1
        _ = 2 * Real.log (4 * (v + 1)) := by rw [Real.log_pow]; norm_num
    have hdiff_le : NthPrime.inverseLi v - NthPrime.inverseLi 1 ≤ (v - 1) * (2 * Real.log (4 * (v + 1))) := by
      have hsub_pos : 0 < v - 1 := sub_pos.mpr hv1
      rw [eq_div_iff hsub_pos.ne'] at hslope
      nlinarith
    have h1_le : NthPrime.inverseLi 1 ≤ 64 := by
      have h := (NthPrime.inverseLi_spec zero_le_one).1.2
      norm_num at h; exact h
    have hlog_nn : 0 ≤ Real.log (4 * (v + 1)) := Real.log_nonneg (by linarith)
    nlinarith

/-- Geometric sum helper: `t * ∑' n : ℕ, exp (-t * (n + 1) / 2) ≤ 2` for `t > 0`. -/
lemma t_mul_tsum_exp_neg_half_le {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => t * Real.exp (-(t * ((n : ℝ) + 1)) / 2)) ∧
      (∑' n : ℕ, t * Real.exp (-(t * ((n : ℝ) + 1)) / 2)) ≤ 2 := by
  let r := Real.exp (-t / 2)
  have hr : 0 < r := Real.exp_pos _
  have hlt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (n : ℕ) : t * Real.exp (-(t * ((n : ℝ) + 1)) / 2) = (t * r) * r ^ n := by
    dsimp [r]; rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [he]
  have hs := summable_geometric_of_lt_one hr.le hlt
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr.le hlt, ← div_eq_mul_inv,
    div_le_iff₀ (sub_pos.mpr hlt)]
  have hex : r * Real.exp (t / 2) = 1 := by
    dsimp [r]; rw [← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero]
  have hend := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t / 2)) hr.le
  rw [hex] at hend
  nlinarith

/-- **Piece (B)**: Riemann-sum MVT bound for every polynomial weight `P`:
`|∑' n, abelPolyTerm invLiSeq P n u - abelIntPoly P u| ≤ C * u * exp (-u)` on `[1, ∞)`. -/
theorem abelPolySum_sub_abelIntPoly_exp_decay (P : Polynomial ℝ) :
    ∃ C > 0, ∀ u : ℝ, 1 ≤ u →
      |(∑' n : ℕ, NthPrime.abelPolyTerm invLiSeq P n u) - abelIntPoly P u| ≤
        C * u * Real.exp (-u) := by
  obtain ⟨CP, hCP, hP⟩ := exists_poly_abs_le P
  obtain ⟨CP', hCP', hP'⟩ := exists_poly_abs_le P.derivative
  let d := max P.natDegree P.derivative.natDegree
  let M_poly : ℝ := (CP + CP') * 2
  have hM_poly_pos : 0 < M_poly := by dsimp [M_poly]; positivity
  -- Constant absorbing `(1 + y^d) * (1 + y^2) * exp (-y) ≤ K_abs * exp (-y / 2)`
  let K0 : ℝ := (2 : ℝ) ^ 0 * (0 : ℕ).factorial
  let K1 : ℝ := (2 : ℝ) ^ 1 * (1 : ℕ).factorial
  let K2 : ℝ := (2 : ℝ) ^ 2 * (2 : ℕ).factorial
  let Kd : ℝ := (2 : ℝ) ^ d * d.factorial
  let Kd1 : ℝ := (2 : ℝ) ^ (d + 1) * (d + 1).factorial
  let Kd2 : ℝ := (2 : ℝ) ^ (d + 2) * (d + 2).factorial
  let K_abs : ℝ := K0 + K1 + K2 + Kd + Kd1 + Kd2
  let C_n0 : ℝ := 128 * CP * 2
  let C_step : ℝ := 80 * Real.exp 1 * M_poly * K_abs
  let C_tot : ℝ := C_n0 + 2 * C_step + 1
  refine ⟨C_tot, by dsimp [C_tot, C_n0, C_step, K_abs, K0, K1, K2, Kd, Kd1, Kd2]; positivity,
    fun u hu => ?_⟩
  set t : ℝ := Real.exp (-u)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  let F : ℝ → ℝ := fun v => NthPrime.inverseLi v * P.eval (t * v) * Real.exp (-(t * v))
  -- Split `∫_{Ioi 0} F = ∑' n, ∫_{Ioc n (n+1)} F`
  have hIoi_eq : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc (n : ℝ) ((n : ℝ) + 1) := by
    ext v
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hv
      let k := ⌈v⌉₊ - 1
      refine ⟨k, ?_, ?_⟩
      · have hpos : 0 < ⌈v⌉₊ := Nat.ceil_pos.mpr hv
        have hlt : (k : ℝ) < v := by
          by_contra h
          push Not at h
          have : ⌈v⌉₊ ≤ k := Nat.ceil_le.mpr h
          omega
        exact hlt
      · have hpos : 0 < ⌈v⌉₊ := Nat.ceil_pos.mpr hv
        have heq : (k : ℝ) + 1 = (⌈v⌉₊ : ℝ) := by
          dsimp [k]; exact_mod_cast Nat.sub_add_cancel hpos
        rw [heq]
        exact Nat.le_ceil v
    · rintro ⟨n, hn1, _⟩
      exact lt_of_le_of_lt (Nat.cast_nonneg n) hn1
  have hdisj : Pairwise (fun m n : ℕ => Disjoint (Set.Ioc (m : ℝ) ((m : ℝ) + 1)) (Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro x hxm hxn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
      linarith [hxm.2, hxn.1]
    · have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
      linarith [hxm.1, hxn.2]
  have hint_F : IntegrableOn F (Set.Ioi 0) := integrableOn_abelIntPoly P u
  have hint_split : ∫ v in Set.Ioi (0 : ℝ), F v = ∑' n : ℕ, ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v := by
    rw [hIoi_eq]
    exact MeasureTheory.integral_iUnion (fun _ => measurableSet_Ioc) hdisj (hIoi_eq ▸ hint_F)
  have hsum_F : Summable (fun n : ℕ => t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v) := by
    have h1 : Summable (fun n : ℕ => ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v) :=
      (MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ioc) hdisj
        (hIoi_eq ▸ hint_F)).summable
    exact h1.mul_left (t ^ 2)
  have hsum_S : Summable (fun n : ℕ => NthPrime.abelPolyTerm invLiSeq P n u) := by
    obtain ⟨B, hB, hbound⟩ := abelPoly_localBound_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le P u
    exact hB.of_norm_bounded fun n => hbound n u ⟨by linarith, by linarith⟩
  have hdiff_eq : (∑' n : ℕ, NthPrime.abelPolyTerm invLiSeq P n u) - abelIntPoly P u =
      ∑' n : ℕ, (t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v) := by
    have hJ : abelIntPoly P u = ∑' n : ℕ, t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v := by
      change t ^ 2 * ∫ v in Set.Ioi (0 : ℝ), F v = _
      rw [hint_split, tsum_mul_left]
    rw [hJ, ← hsum_S.tsum_sub hsum_F]
    congr 1; ext n
    dsimp only [NthPrime.abelPolyTerm, invLiSeq, F]
    ring
  -- Bound each term `n = 0` and `n ≥ 1`
  have hterm_0 : |t ^ 2 * F ((0 : ℕ) + 1 : ℝ) - t ^ 2 * ∫ v in Set.Ioc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1 : ℝ), F v| ≤
      C_n0 * u * t := by
    have hF_le : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |F v| ≤ 64 * CP * 2 := by
      intro v hv
      have hv0 : 0 < v := hv.1
      have hspec := (NthPrime.inverseLi_spec hv0.le).1
      have hinv : NthPrime.inverseLi v ≤ 64 := by
        have : (4 * (v + 1)) ^ 2 ≤ 64 := by nlinarith [hv.1, hv.2]
        exact hspec.2.trans this
      have htv_le1 : t * v ≤ 1 := by nlinarith [hv.1, hv.2]
      have hP_le : |P.eval (t * v)| ≤ CP * 2 := by
        have h1 := hP (t * v) (by positivity)
        have hpow : (t * v) ^ P.natDegree ≤ 1 := pow_le_one₀ (by positivity) htv_le1
        nlinarith
      have hexp_le : Real.exp (-(t * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
      dsimp only [F]
      rw [abs_mul, abs_mul, abs_of_pos (by linarith [hspec.1]), abs_of_pos (Real.exp_pos _)]
      calc NthPrime.inverseLi v * |P.eval (t * v)| * Real.exp (-(t * v))
          ≤ (64 * (CP * 2)) * 1 := mul_le_mul (mul_le_mul hinv hP_le (abs_nonneg _) (by positivity))
            hexp_le (Real.exp_pos _).le (by positivity)
        _ = 64 * CP * 2 := by ring
    have hF1 : |F 1| ≤ 64 * CP * 2 := hF_le 1 ⟨zero_lt_one, le_rfl⟩
    have hFint : |∫ v in Set.Ioc (0 : ℝ) 1, F v| ≤ 64 * CP * 2 := by
      calc |∫ v in Set.Ioc (0 : ℝ) 1, F v|
          ≤ ∫ v in Set.Ioc (0 : ℝ) 1, |F v| := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm F
        _ ≤ ∫ _ in Set.Ioc (0 : ℝ) 1, (64 * CP * 2) :=
            setIntegral_mono_on (hint_F.mono_set Set.Ioc_subset_Ioi_self).norm
              (integrableOn_const (C := 64 * CP * 2) (hs := measure_Ioc_lt_top.ne))
              measurableSet_Ioc hF_le
        _ = 64 * CP * 2 := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]
            simp
    simp only [Nat.cast_zero, zero_add]
    rw [← mul_sub, abs_mul, abs_pow, abs_of_pos ht0]
    have hsub : |F 1 - ∫ v in Set.Ioc (0 : ℝ) 1, F v| ≤ C_n0 := by
      dsimp only [C_n0]; linarith [abs_sub (F 1) (∫ v in Set.Ioc (0 : ℝ) 1, F v)]
    have ht2_le : t ^ 2 ≤ u * t := by nlinarith
    calc t ^ 2 * |F 1 - ∫ v in Set.Ioc (0 : ℝ) 1, F v|
        ≤ (u * t) * C_n0 := mul_le_mul ht2_le hsub (abs_nonneg _) (by positivity)
      _ = C_n0 * u * t := by ring
  have hterm_succ : ∀ k : ℕ,
      |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v| ≤
        (C_step * u * t) * (t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) := by
    intro k
    let n : ℕ := k + 1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_pos k
    set y : ℝ := t * ((n : ℝ) + 1)
    have hy0 : 0 < y := by positivity
    -- MVT derivative bound on `[n, n + 1]`
    have hF_deriv_bound : ∀ ξ ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt F
          ((Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ) +
            NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))) ξ ∧
        |(Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ) +
            NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))| ≤ C_step * u * Real.exp (-y / 2) := by
      intro ξ hξ
      have hξ_pos : 0 < ξ := lt_of_lt_of_le zero_lt_one (hn1.trans hξ.1)
      have hξ1 : 1 ≤ ξ := hn1.trans hξ.1
      have hderiv : HasDerivAt F
          ((Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ) +
            NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))) ξ := by
        have h1 := NthPrime.inverseLi_hasDerivAt hξ_pos
        have hlin : HasDerivAt (fun x : ℝ => t * x) t ξ := by
          simpa using (hasDerivAt_id ξ).const_mul t
        have h2 := (P.hasDerivAt (t * ξ)).comp ξ hlin
        have h3 := hlin.neg.exp
        refine ((h1.mul h2).mul h3).congr_deriv ?_
        simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply]
        ring
      refine ⟨hderiv, ?_⟩
      -- Bound log(4(ξ+1)) ≤ 2 + u + 2y
      have hlog4 : Real.log 4 ≤ 2 := by
        have h4 : (4 : ℝ) ≤ Real.exp 2 := by
          have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
          rw [← Real.exp_nat_mul] at hsq; norm_num at hsq; exact hsq
        calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h4
          _ = 2 := Real.log_exp 2
      have hlog_bound : Real.log (4 * (ξ + 1)) ≤ 2 + u + 2 * y := by
        have hle : 4 * (ξ + 1) ≤ 4 * ((n : ℝ) + 2) := by linarith [hξ.2]
        have hpos1 : 0 < 4 * (ξ + 1) := by positivity
        have hfac : 4 * ((n : ℝ) + 2) = 4 * Real.exp u * (t * ((n : ℝ) + 2)) := by
          dsimp [t]; rw [Real.exp_neg]; field_simp [(Real.exp_pos u).ne']
        have hlog_eq : Real.log (4 * ((n : ℝ) + 2)) = Real.log 4 + u + Real.log (t * ((n : ℝ) + 2)) := by
          rw [hfac, Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp]
        have hlog_lin : Real.log (t * ((n : ℝ) + 2)) ≤ t * ((n : ℝ) + 2) := by
          linarith [Real.log_le_sub_one_of_pos (show 0 < t * ((n : ℝ) + 2) by positivity)]
        have h2y : t * ((n : ℝ) + 2) ≤ 2 * y := by dsimp [y]; nlinarith
        calc Real.log (4 * (ξ + 1)) ≤ Real.log (4 * ((n : ℝ) + 2)) := Real.log_le_log hpos1 hle
          _ = Real.log 4 + u + Real.log (t * ((n : ℝ) + 2)) := hlog_eq
          _ ≤ 2 + u + 2 * y := by linarith
      have hlog_inv_le : |Real.log (NthPrime.inverseLi ξ)| ≤ 4 + 2 * u + 4 * y := by
        have hspec := (NthPrime.inverseLi_spec hξ_pos.le).1
        have hnn : 0 ≤ Real.log (NthPrime.inverseLi ξ) := Real.log_nonneg (by linarith [hspec.1])
        rw [abs_of_nonneg hnn]
        have h1 : Real.log (NthPrime.inverseLi ξ) ≤ 2 * Real.log (4 * (ξ + 1)) := by
          calc Real.log (NthPrime.inverseLi ξ) ≤ Real.log ((4 * (ξ + 1)) ^ 2) :=
                Real.log_le_log (by linarith [hspec.1]) hspec.2
            _ = 2 * Real.log (4 * (ξ + 1)) := by rw [Real.log_pow]; norm_num
        linarith
      have ht_inv_le : NthPrime.inverseLi ξ * t ≤ 64 + 2 * y * (2 + u + 2 * y) := by
        have h1 := inverseLi_le_linear_log hξ1
        have hξ_le : t * ξ ≤ y := by dsimp [y]; nlinarith [hξ.2]
        have hlog_nn : 0 ≤ Real.log (4 * (ξ + 1)) := Real.log_nonneg (by linarith)
        have h2 : (2 * ξ * Real.log (4 * (ξ + 1))) * t = 2 * (t * ξ) * Real.log (4 * (ξ + 1)) := by ring
        calc NthPrime.inverseLi ξ * t
            ≤ (64 + 2 * ξ * Real.log (4 * (ξ + 1))) * t := mul_le_mul_of_nonneg_right h1 ht0.le
          _ = 64 * t + 2 * (t * ξ) * Real.log (4 * (ξ + 1)) := by ring
          _ ≤ 64 * 1 + 2 * y * (2 + u + 2 * y) := by
              have h2ξ : 2 * (t * ξ) ≤ 2 * y := by linarith
              have hm := mul_le_mul h2ξ hlog_bound hlog_nn (by positivity)
              linarith
          _ = 64 + 2 * y * (2 + u + 2 * y) := by ring
      -- Bound |P(tξ)| and |P'(tξ) - P(tξ)| by M_poly * (1 + y^d)
      have hty_le : t * ξ ≤ y := by dsimp [y]; nlinarith [hξ.2]
      have hpow_le : ∀ m : ℕ, m ≤ d → (t * ξ) ^ m ≤ 1 + y ^ d := by
        intro m hm
        have h1 : (t * ξ) ^ m ≤ y ^ m := pow_le_pow_left₀ (by positivity) hty_le m
        by_cases hy1 : y ≤ 1
        · have : y ^ m ≤ 1 := pow_le_one₀ hy0.le hy1
          linarith [pow_nonneg hy0.le d]
        · push Not at hy1
          have : y ^ m ≤ y ^ d := pow_le_pow_right₀ hy1.le hm
          linarith
      have hP_b : |P.eval (t * ξ)| ≤ M_poly * (1 + y ^ d) := by
        have h1 := hP (t * ξ) (by positivity)
        have h2 := hpow_le P.natDegree (le_max_left _ _)
        have h1y : 1 + (t * ξ) ^ P.natDegree ≤ 2 * (1 + y ^ d) := by linarith [pow_nonneg hy0.le d]
        dsimp only [M_poly]
        have hnn : 0 ≤ 1 + y ^ d := by positivity
        nlinarith
      have hPd_b : |P.derivative.eval (t * ξ) - P.eval (t * ξ)| ≤ M_poly * (1 + y ^ d) := by
        have h1 := hP (t * ξ) (by positivity)
        have h2 := hP' (t * ξ) (by positivity)
        have hp1 := hpow_le P.natDegree (le_max_left _ _)
        have hp2 := hpow_le P.derivative.natDegree (le_max_right _ _)
        have h1y1 : 1 + (t * ξ) ^ P.natDegree ≤ 2 * (1 + y ^ d) := by linarith [pow_nonneg hy0.le d]
        have h1y2 : 1 + (t * ξ) ^ P.derivative.natDegree ≤ 2 * (1 + y ^ d) := by linarith [pow_nonneg hy0.le d]
        have htri := abs_sub (P.derivative.eval (t * ξ)) (P.eval (t * ξ))
        dsimp only [M_poly]
        nlinarith
      have hexp_b : Real.exp (-(t * ξ)) ≤ Real.exp 1 * Real.exp (-y) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [y]
        nlinarith [hξ.1, ht1]
      have hcoeff_sum : |Real.log (NthPrime.inverseLi ξ)| + NthPrime.inverseLi ξ * t ≤
          80 * u * (1 + y + y ^ 2) := by
        have hu1 : 1 ≤ u := hu
        nlinarith [sq_nonneg y]
      have hmain : |Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ) +
            NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))| ≤
          80 * u * M_poly * (1 + y + y ^ 2) * (1 + y ^ d) := by
        have hinv_nn : 0 ≤ NthPrime.inverseLi ξ * t := by
          have hspec := (NthPrime.inverseLi_spec hξ_pos.le).1
          have hinv_pos : 0 < NthPrime.inverseLi ξ := by linarith [hspec.1]
          positivity
        calc _ ≤ |Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ)| +
                |NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))| :=
              abs_add_le _ _
          _ = |Real.log (NthPrime.inverseLi ξ)| * |P.eval (t * ξ)| +
                (NthPrime.inverseLi ξ * t) * |P.derivative.eval (t * ξ) - P.eval (t * ξ)| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hinv_nn]
          _ ≤ |Real.log (NthPrime.inverseLi ξ)| * (M_poly * (1 + y ^ d)) +
                (NthPrime.inverseLi ξ * t) * (M_poly * (1 + y ^ d)) :=
              add_le_add (mul_le_mul_of_nonneg_left hP_b (abs_nonneg _))
                (mul_le_mul_of_nonneg_left hPd_b hinv_nn)
          _ = (|Real.log (NthPrime.inverseLi ξ)| + NthPrime.inverseLi ξ * t) * (M_poly * (1 + y ^ d)) := by ring
          _ ≤ (80 * u * (1 + y + y ^ 2)) * (M_poly * (1 + y ^ d)) :=
              mul_le_mul_of_nonneg_right hcoeff_sum (by positivity)
          _ = 80 * u * M_poly * (1 + y + y ^ 2) * (1 + y ^ d) := by ring
      have habs_poly : (1 + y + y ^ 2) * (1 + y ^ d) * Real.exp (-y) ≤ K_abs * Real.exp (-y / 2) := by
        have h0 := pow_mul_exp_neg_mul_le 0 zero_lt_one hy0.le
        have h1 := pow_mul_exp_neg_mul_le 1 zero_lt_one hy0.le
        have h2 := pow_mul_exp_neg_mul_le 2 zero_lt_one hy0.le
        have hd0 := pow_mul_exp_neg_mul_le d zero_lt_one hy0.le
        have hd1 := pow_mul_exp_neg_mul_le (d + 1) zero_lt_one hy0.le
        have hd2 := pow_mul_exp_neg_mul_le (d + 2) zero_lt_one hy0.le
        simp only [div_one, neg_one_mul] at h0 h1 h2 hd0 hd1 hd2
        have hneg_half : -(1 / 2 : ℝ) * y = -y / 2 := by ring
        rw [hneg_half] at h0 h1 h2 hd0 hd1 hd2
        have hexpand : (1 + y + y ^ 2) * (1 + y ^ d) =
            y ^ 0 + y ^ 1 + y ^ 2 + y ^ d + y ^ (d + 1) + y ^ (d + 2) := by
          simp only [pow_zero, pow_one, pow_add]; ring
        rw [hexpand]
        dsimp only [K_abs, K0, K1, K2, Kd, Kd1, Kd2]
        have hsum_exp : (y ^ 0 + y ^ 1 + y ^ 2 + y ^ d + y ^ (d + 1) + y ^ (d + 2)) * Real.exp (-y) =
            y ^ 0 * Real.exp (-y) + y ^ 1 * Real.exp (-y) + y ^ 2 * Real.exp (-y) +
            y ^ d * Real.exp (-y) + y ^ (d + 1) * Real.exp (-y) + y ^ (d + 2) * Real.exp (-y) := by ring
        rw [hsum_exp]
        linarith
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc _ ≤ (80 * u * M_poly * (1 + y + y ^ 2) * (1 + y ^ d)) * (Real.exp 1 * Real.exp (-y)) :=
            mul_le_mul hmain hexp_b (Real.exp_pos _).le (by positivity)
        _ = (80 * Real.exp 1 * M_poly * u) * ((1 + y + y ^ 2) * (1 + y ^ d) * Real.exp (-y)) := by ring
        _ ≤ (80 * Real.exp 1 * M_poly * u) * (K_abs * Real.exp (-y / 2)) :=
            mul_le_mul_of_nonneg_left habs_poly (by positivity)
        _ = C_step * u * Real.exp (-y / 2) := by dsimp only [C_step]; ring
    -- Apply MVT on `[v, n+1]` for each `v ∈ Ioc n (n+1)`
    have hdiff_v : ∀ v ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1),
        |F ((n : ℝ) + 1) - F v| ≤ C_step * u * Real.exp (-y / 2) := by
      intro v hv
      rcases eq_or_lt_of_le hv.2 with rfl | hv_lt
      · rw [sub_self, abs_zero]; dsimp only [C_step, K_abs, K0, K1, K2, Kd, Kd1, Kd2]; positivity
      · have hcont : ContinuousOn F (Set.Icc v ((n : ℝ) + 1)) := fun ξ hξ =>
          (hF_deriv_bound ξ ⟨hv.1.le.trans hξ.1, hξ.2⟩).1.continuousAt.continuousWithinAt
        have hderiv : ∀ ξ ∈ Set.Ioo v ((n : ℝ) + 1),
            HasDerivAt F
              ((Real.log (NthPrime.inverseLi ξ) * P.eval (t * ξ) +
                NthPrime.inverseLi ξ * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
                Real.exp (-(t * ξ))) ξ := fun ξ hξ =>
          (hF_deriv_bound ξ ⟨hv.1.le.trans hξ.1.le, hξ.2.le⟩).1
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F _ hv_lt hcont hderiv
        have hsub_pos : 0 < (n : ℝ) + 1 - v := sub_pos.mpr hv_lt
        have hsub_le1 : (n : ℝ) + 1 - v ≤ 1 := by linarith [hv.1]
        rw [eq_div_iff hsub_pos.ne'] at hslope
        rw [← hslope, abs_mul, abs_of_pos hsub_pos]
        have hb := (hF_deriv_bound c ⟨hv.1.le.trans hc.1.le, hc.2.le⟩).2
        calc _ ≤ (C_step * u * Real.exp (-y / 2)) * 1 :=
              mul_le_mul hb hsub_le1 hsub_pos.le (by dsimp [C_step, K_abs, K0, K1, K2, Kd, Kd1, Kd2]; positivity)
          _ = C_step * u * Real.exp (-y / 2) := mul_one _
    -- Integrate over `Ioc n (n+1)`
    have hint_sub : F ((n : ℝ) + 1) - ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v =
        ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (F ((n : ℝ) + 1) - F v) := by
      rw [integral_sub (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        (hint_F.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Nat.cast_nonneg n))))]
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]
      simp
    have hnorm_sub : |F ((n : ℝ) + 1) - ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v| ≤
        C_step * u * Real.exp (-y / 2) := by
      rw [hint_sub]
      calc |∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (F ((n : ℝ) + 1) - F v)|
          ≤ ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), |F ((n : ℝ) + 1) - F v| := by
            simpa only [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (fun v => F ((n : ℝ) + 1) - F v)
        _ ≤ ∫ _ in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (C_step * u * Real.exp (-y / 2)) :=
            setIntegral_mono_on
              ((integrableOn_const (hs := measure_Ioc_lt_top.ne)).sub
                (hint_F.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Nat.cast_nonneg n))))).norm
              (integrableOn_const (C := C_step * u * Real.exp (-y / 2)) (hs := measure_Ioc_lt_top.ne))
              measurableSet_Ioc hdiff_v
        _ = C_step * u * Real.exp (-y / 2) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]
            simp
    change |t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v| ≤
      (C_step * u * t) * (t * Real.exp (-(t * ((n : ℝ) + 1)) / 2))
    rw [← mul_sub, abs_mul, abs_pow, abs_of_pos ht0]
    calc t ^ 2 * |F ((n : ℝ) + 1) - ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v|
        ≤ t ^ 2 * (C_step * u * Real.exp (-y / 2)) := mul_le_mul_of_nonneg_left hnorm_sub (by positivity)
      _ = (C_step * u * t) * (t * Real.exp (-(t * ((n : ℝ) + 1)) / 2)) := by dsimp [y]; ring
  -- Combine n = 0 and ∑_{k=0}^∞ term(k+1)
  obtain ⟨hgeom_sum, hgeom_le⟩ := t_mul_tsum_exp_neg_half_le ht0
  have hmaj_succ : Summable (fun k : ℕ =>
      (C_step * u * t) * (t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2))) :=
    (hgeom_sum.comp_injective Nat.succ_injective).mul_left (C_step * u * t)
  have hnorm_sum_succ : Summable (fun k : ℕ =>
      |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) -
        t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v|) :=
    hmaj_succ.of_nonneg_of_le (fun _ => abs_nonneg _) hterm_succ
  have hsum_all_abs : Summable (fun n : ℕ =>
      |t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v|) :=
    (summable_nat_add_iff 1).mp hnorm_sum_succ
  rw [hdiff_eq]
  have hle_tsum := norm_tsum_le_tsum_norm
    (f := fun n : ℕ => t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v)
    (by simpa only [Real.norm_eq_abs] using hsum_all_abs)
  simp only [Real.norm_eq_abs] at hle_tsum
  have hsplit_sum := hsum_all_abs.tsum_eq_zero_add
  have hsucc_le : (∑' k : ℕ, |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) -
        t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v|) ≤
      2 * C_step * u * t := by
    have h1 := hnorm_sum_succ.tsum_le_tsum hterm_succ hmaj_succ
    rw [tsum_mul_left] at h1
    have htail_le : (∑' k : ℕ, t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) ≤
        ∑' n : ℕ, t * Real.exp (-(t * ((n : ℝ) + 1)) / 2) := by
      have hsp := hgeom_sum.tsum_eq_zero_add
      have h0_nn : 0 ≤ t * Real.exp (-(t * ((0 : ℝ) + 1)) / 2) := by positivity
      linarith
    have hCstep_nn : 0 ≤ C_step * u * t := by
      dsimp only [C_step, K_abs, K0, K1, K2, Kd, Kd1, Kd2]; positivity
    calc _ ≤ (C_step * u * t) * (∑' k : ℕ, t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) := h1
      _ ≤ (C_step * u * t) * 2 := mul_le_mul_of_nonneg_left (htail_le.trans hgeom_le) hCstep_nn
      _ = 2 * C_step * u * t := by ring
  calc |∑' n : ℕ, (t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v)|
      ≤ ∑' n : ℕ, |t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v| := hle_tsum
    _ = |t ^ 2 * F ((0 : ℕ) + 1 : ℝ) - t ^ 2 * ∫ v in Set.Ioc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1 : ℝ), F v| +
          ∑' k : ℕ, |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) -
            t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v| := by
        simpa [Nat.cast_add, Nat.cast_one] using hsplit_sum
    _ ≤ C_n0 * u * t + 2 * C_step * u * t := add_le_add hterm_0 hsucc_le
    _ ≤ C_tot * u * t := by dsimp only [C_tot]; nlinarith [ht0]

/-- **Piece (B) for all jet orders `j`**:
`|iteratedDeriv j S_invLi u - iteratedDeriv j J_invLi u| ≤ C * u * exp (-u)` on `[1, ∞)`. -/
theorem S_invLi_sub_J_invLi_jet_exp_decay (j : ℕ) :
    ∃ C > 0, ∀ u : ℝ, 1 ≤ u →
      |iteratedDeriv j S_invLi u - iteratedDeriv j J_invLi u| ≤ C * u * Real.exp (-u) := by
  rw [iteratedDeriv_S_invLi, iteratedDeriv_J_invLi]
  exact abelPolySum_sub_abelIntPoly_exp_decay (NthPrime.abelJetStep^[j] 1)

/-! #### Piece (A): Identification of `nthPrimeSmoothRay - S_invLi` with `NthPrimeAbelError` -/

/-- `iteratedDeriv` commutes with `Complex.ofReal : ℝ → ℂ`. -/
lemma iteratedDeriv_ofReal_comp (f : ℝ → ℝ) (k : ℕ) :
    iteratedDeriv k (fun u : ℝ => (f u : ℂ)) = fun u : ℝ => ((iteratedDeriv k f u : ℝ) : ℂ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext u
    rw [iteratedDeriv_succ]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k f) u
    · exact (hd.hasDerivAt.ofReal_comp).deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ)) u := by
        intro h
        have hre := Complex.reCLM.differentiableAt.comp u h
        have hfun : (⇑Complex.reCLM ∘ fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ)) = iteratedDeriv k f := by
          ext x; simp
        rw [hfun] at hre
        exact hd hre
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd,
        Complex.ofReal_zero]

/-- Exact series identity matching `nthPrimeSmoothRay` to `abelPolyTerm` on `Nat.nth Nat.Prime`. -/
theorem nthPrimeSmoothRay_eq_abelPolySum (u : ℝ) :
    nthPrimeSmoothRay u =
      ((∑' n : ℕ, NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u : ℝ) : ℂ) := by
  set t : ℝ := Real.exp (-u)
  have ht : 0 < t := Real.exp_pos _
  have hsum_prime : Summable (fun n : ℕ => NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u) := by
    have hquad : ∀ n : ℕ, |(Nat.nth Nat.Prime n : ℝ)| ≤ 16 * ((n : ℝ) + 2) ^ 2 := by
      intro n
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hR : (Nat.nth Nat.Prime n : ℝ) ≤ (4 * ((n : ℝ) + 1)) ^ 2 := by
        exact_mod_cast NthPrime.nth_prime_quadratic_bound n
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad (by norm_num : (0 : ℝ) < 16) hquad 1 u
    exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
  have hval_sum : Summable (fun k : ℕ => PrimeNome.term NthPrime.series (PrimeNome.qRay u) k) := by
    have hC := hsum_prime.mul_left (t ^ 2)⁻¹
    have hshift : Summable (fun n : ℕ => PrimeNome.term NthPrime.series (PrimeNome.qRay u) (n + 1)) := by
      have hC_complex := (Complex.ofRealCLM.hasSum hC.hasSum).summable
      refine hC_complex.congr fun n => ?_
      have heq_real : (t ^ 2)⁻¹ * NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u =
          (Nat.nth Nat.Prime n : ℝ) * (Real.exp (-t)) ^ (n + 1) := by
        dsimp only [NthPrime.abelPolyTerm]
        rw [Polynomial.eval_one, mul_one]
        conv_rhs => rw [← Real.exp_nat_mul]
        have ht2 : t ^ 2 ≠ 0 := (pow_pos ht 2).ne'
        change (t ^ 2)⁻¹ * (t ^ 2 * (Nat.nth Nat.Prime n : ℝ) * Real.exp (-(t * ((n : ℝ) + 1)))) = _
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ht2, one_mul]
        congr 2; push_cast; ring
      change (((t ^ 2)⁻¹ * NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u : ℝ) : ℂ) = _
      rw [heq_real]
      simp only [PrimeNome.term, NthPrime.coeff_succ, PrimeNome.qRay, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_natCast]
      rfl
    exact (summable_nat_add_iff 1).mp hshift
  dsimp only [nthPrimeSmoothRay, PrimeNome.value]
  rw [hval_sum.tsum_eq_zero_add]
  have h0 : PrimeNome.term NthPrime.series (PrimeNome.qRay u) 0 = 0 := by
    simp [PrimeNome.term, NthPrime.coeff_zero]
  rw [h0, zero_add, ← tsum_mul_left]
  have hcs := (Complex.ofRealCLM.hasSum hsum_prime.hasSum).tsum_eq
  change _ = Complex.ofRealCLM _
  rw [← hcs]
  congr 1; ext n
  change PrimeNome.tRay u ^ 2 * (PowerSeries.coeff (n + 1) NthPrime.series * PrimeNome.qRay u ^ (n + 1)) =
    ((NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u : ℝ) : ℂ)
  simp only [PrimeNome.tRay, PrimeNome.qRay, NthPrime.coeff_succ, NthPrime.abelPolyTerm,
    Polynomial.eval_one, mul_one]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_nat_mul (-Real.exp (-u)) (n + 1)]
  have harg : ((n + 1 : ℕ) : ℝ) * -Real.exp (-u) = -(Real.exp (-u) * ((n : ℝ) + 1)) := by
    push_cast; ring
  rw [harg]; ring

/-- **Piece (A) for all jet orders `j` and inverse-power orders `N`** (from `Main.PNTAllOrders`):
`‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j (fun v => (S_invLi v : ℂ)) u‖ ≤ C / u ^ N`. -/
theorem nthPrimeSmoothRay_sub_S_invLi_allOrders (hpnt : Main.PNTAllOrders) (j N : ℕ) :
    ∃ C > 0, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u‖ ≤
        C / u ^ N := by
  let e : ℕ → ℝ := fun n => (Nat.nth Nat.Prime n : ℝ) - NthPrime.inverseLi (n + 1 : ℝ)
  have hdiff_fun : (fun u : ℝ => nthPrimeSmoothRay u - (S_invLi u : ℂ)) =
      fun u : ℝ => ((∑' n : ℕ, NthPrime.abelPolyTerm e 1 n u : ℝ) : ℂ) := by
    ext u
    rw [nthPrimeSmoothRay_eq_abelPolySum u]
    dsimp only [S_invLi]
    rw [← Complex.ofReal_sub]
    congr 1
    have hp_sum : Summable (fun n : ℕ => NthPrime.abelPolyTerm (fun k => (Nat.nth Nat.Prime k : ℝ)) 1 n u) := by
      have hquad : ∀ n : ℕ, |(Nat.nth Nat.Prime n : ℝ)| ≤ 16 * ((n : ℝ) + 2) ^ 2 := by
        intro n
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have hR : (Nat.nth Nat.Prime n : ℝ) ≤ (4 * ((n : ℝ) + 1)) ^ 2 := by
          exact_mod_cast NthPrime.nth_prime_quadratic_bound n
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad (by norm_num : (0 : ℝ) < 16) hquad 1 u
      exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
    have hi_sum : Summable (fun n : ℕ => NthPrime.abelPolyTerm invLiSeq 1 n u) := by
      obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad (by norm_num : (0 : ℝ) < 16) abs_invLiSeq_le 1 u
      exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
    rw [← hp_sum.tsum_sub hi_sum]
    congr 1; ext n
    dsimp only [NthPrime.abelPolyTerm, invLiSeq, e]
    ring
  obtain ⟨C, hC, hev⟩ := NthPrime.prime_inverseLi_abelSumJetError hpnt j N
  refine ⟨C, hC, hev.mono fun u hu => ?_⟩
  have hcd1 : ContDiffAt ℝ j nthPrimeSmoothRay u :=
    (nthPrimeSmoothRay_analytic u).contDiffAt.of_le le_top
  have hcd2 : ContDiffAt ℝ j (fun v : ℝ => (S_invLi v : ℂ)) u :=
    ((Complex.ofRealCLM.contDiff.of_le le_top).comp (contDiff_S_invLi j)).contDiffAt
  have hsub := iteratedDeriv_sub hcd1 hcd2
  change iteratedDeriv j (fun v => nthPrimeSmoothRay v - (S_invLi v : ℂ)) u = _ at hsub
  rw [← hsub, hdiff_fun, iteratedDeriv_ofReal_comp, Complex.norm_real, Real.norm_eq_abs]
  exact hu

/-! #### Assembly of Pieces (A)+(B)+(C)+(D) and Polynomial Jet Transfer (`hasymp_of_pnt`) -/

/-- **All-Orders Jet Equivalence `nthPrimeSmoothRay ↔ I_plus`** from `Main.PNTAllOrders`:
For every derivative order `j` and every inverse-power order `N`,
`‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j I_plus u‖ ≤ C / u ^ N` eventually. -/
theorem nthPrimeSmoothRay_sub_I_plus_allOrders (hpnt : Main.PNTAllOrders) (j N : ℕ) :
    ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j I_plus u‖ ≤ C / u ^ N := by
  obtain ⟨CA, hCA, hA⟩ := nthPrimeSmoothRay_sub_S_invLi_allOrders hpnt j N
  obtain ⟨UA, hUA⟩ := eventually_atTop.mp hA
  obtain ⟨CB0, hCB0, hB0⟩ := S_invLi_sub_J_invLi_jet_exp_decay j
  obtain ⟨CB, hCB, hB⟩ := mul_exp_neg_le_div_pow CB0 hCB0 N
  obtain ⟨CC0, hCC0, hC0⟩ := J_invLi_sub_T_jet_exp_decay j
  obtain ⟨CC, hCC, hC⟩ := mul_exp_neg_le_div_pow CC0 hCC0 N
  obtain ⟨CD0, hCD0, hD0⟩ := I_plus_sub_T_jet_exp_decay j
  obtain ⟨CD, hCD, hD⟩ := mul_exp_neg_le_div_pow CD0 hCD0 N
  refine ⟨CA + CB + CC + CD, by positivity, max 1 UA, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := (le_max_left 1 UA).trans hu
  have huA : UA ≤ u := (le_max_right 1 UA).trans hu
  have hcd_J : ContDiffAt ℝ j (fun v : ℝ => (J_invLi v : ℂ)) u :=
    ((Complex.ofRealCLM.contDiff.of_le le_top).comp (contDiff_J_invLi j)).contDiffAt
  have hcd_T : ContDiffAt ℝ j (fun v : ℝ => T_integral (Real.exp (-v))) u := by
    have han : AnalyticOnNhd ℂ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
      differentiableOn_T_exp_neg.analyticOnNhd isOpen_halfStrip
    have hcd_R : ContDiffOn ℝ ⊤ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
      (han.contDiffOn isOpen_halfStrip.uniqueDiffOn).restrict_scalars ℝ
    have hu_mem : (u : ℂ) ∈ halfStrip := by
      simp only [halfStrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
      exact ⟨by linarith, by norm_num⟩
    have hcomp : ContDiffAt ℝ ⊤ (fun v : ℝ => T_integral (Complex.exp (-(v : ℂ)))) u :=
      (hcd_R.contDiffAt (isOpen_halfStrip.mem_nhds hu_mem)).comp u Complex.ofRealCLM.contDiff.contDiffAt
    have heq : (fun v : ℝ => T_integral (Real.exp (-v))) = fun v : ℝ => T_integral (Complex.exp (-(v : ℂ))) := by
      ext v; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [heq]; exact hcomp.of_le le_top
  have hcd_I : ContDiffAt ℝ j I_plus u := contDiff_I_plus.contDiffAt.of_le le_top
  have hstepB : ‖iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u -
      iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u‖ ≤ CB / u ^ N := by
    rw [iteratedDeriv_ofReal_comp, iteratedDeriv_ofReal_comp, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact (hB0 u hu1).trans (hB u hu1)
  have hstepC : ‖iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u -
      iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u‖ ≤ CC / u ^ N := by
    have hsub := iteratedDeriv_sub hcd_J hcd_T
    change iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ) - T_integral (Real.exp (-v))) u = _ at hsub
    rw [← hsub]
    exact (hC0 u hu1).trans (hC u hu1)
  have hstepD : ‖iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u -
      iteratedDeriv j I_plus u‖ ≤ CD / u ^ N := by
    have hsub := iteratedDeriv_sub hcd_I hcd_T
    change iteratedDeriv j (fun v : ℝ => I_plus v - T_integral (Real.exp (-v))) u = _ at hsub
    rw [norm_sub_rev, ← hsub]
    exact (hD0 u hu1).trans (hD u hu1)
  have htri : ‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j I_plus u‖ ≤
      ‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u‖ +
      ‖iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u‖ +
      ‖iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u‖ +
      ‖iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u - iteratedDeriv j I_plus u‖ := by
    calc ‖iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j I_plus u‖
        = ‖(iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u) +
            ((iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u) +
            ((iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u) +
            (iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u - iteratedDeriv j I_plus u)))‖ := by
          congr 1; ring
      _ ≤ _ := by
          have h1 := norm_add_le
            (iteratedDeriv j nthPrimeSmoothRay u - iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u)
            ((iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u) +
            ((iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u) +
            (iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u - iteratedDeriv j I_plus u)))
          have h2 := norm_add_le
            (iteratedDeriv j (fun v : ℝ => (S_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u)
            ((iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u) +
            (iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u - iteratedDeriv j I_plus u))
          have h3 := norm_add_le
            (iteratedDeriv j (fun v : ℝ => (J_invLi v : ℂ)) u - iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u)
            (iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u - iteratedDeriv j I_plus u)
          linarith
  have hsum_div : CA / u ^ N + CB / u ^ N + CC / u ^ N + CD / u ^ N = (CA + CB + CC + CD) / u ^ N := by ring
  linarith [hUA u huA]

/-- **General Polynomial Jet-Difference Transfer (`eval_jet_diff_allOrders`)**:
If `g` has polynomially bounded jets and `f - g` has all-orders flat jets on `[U, ∞)`, then for
every multivariate polynomial `P`, `eval (jet f u) P - eval (jet g u) P` is `O(u^{-N})` for every `N`. -/
theorem eval_jet_diff_allOrders {r : ℕ} {f g : ℝ → ℂ}
    (hg_bound : ∃ CH > 0, ∃ A : ℕ, ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv (j : ℕ) g u‖ ≤ CH * u ^ A)
    (hdiff : ∀ j : Fin (r + 1), ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖iteratedDeriv (j : ℕ) f u - iteratedDeriv (j : ℕ) g u‖ ≤ C / u ^ N)
    (P : MvPolynomial (Fin (r + 1)) ℂ) :
    (∃ CP > 0, ∃ AP : ℕ, ∀ u : ℝ, 1 ≤ u →
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) P‖ ≤ CP * u ^ AP) ∧
    (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) P -
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) P‖ ≤ C / u ^ N) := by
  obtain ⟨CH, hCH, A, hgB⟩ := hg_bound
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨⟨‖c‖ + 1, by positivity, 0, fun u _ => by simp⟩, fun N => ⟨1, zero_lt_one, 1, fun u hu => ?_⟩⟩
    simp only [MvPolynomial.eval_C, sub_self, norm_zero]
    positivity
  | add p q ihp ihq =>
    obtain ⟨⟨Cp, hCp, Ap, hpb⟩, hpd⟩ := ihp
    obtain ⟨⟨Cq, hCq, Aq, hqb⟩, hqd⟩ := ihq
    refine ⟨⟨Cp + Cq, add_pos hCp hCq, max Ap Aq, fun u hu => ?_⟩, fun N => ?_⟩
    · rw [map_add]
      have h1 : u ^ Ap ≤ u ^ max Ap Aq := pow_le_pow_right₀ hu (le_max_left _ _)
      have h2 : u ^ Aq ≤ u ^ max Ap Aq := pow_le_pow_right₀ hu (le_max_right _ _)
      calc ‖MvPolynomial.eval _ p + MvPolynomial.eval _ q‖
          ≤ ‖MvPolynomial.eval _ p‖ + ‖MvPolynomial.eval _ q‖ := norm_add_le _ _
        _ ≤ Cp * u ^ Ap + Cq * u ^ Aq := add_le_add (hpb u hu) (hqb u hu)
        _ ≤ Cp * u ^ max Ap Aq + Cq * u ^ max Ap Aq :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hCp.le) (mul_le_mul_of_nonneg_left h2 hCq.le)
        _ = (Cp + Cq) * u ^ max Ap Aq := by ring
    · obtain ⟨C1, hC1, U1, h1⟩ := hpd N
      obtain ⟨C2, hC2, U2, h2⟩ := hqd N
      refine ⟨C1 + C2, add_pos hC1 hC2, max U1 U2, fun u hu => ?_⟩
      simp only [map_add]
      have hsub_eq : (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) p +
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) q) -
          (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p +
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) q) =
          (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) p -
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p) +
          (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) q -
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) q) := by ring
      rw [hsub_eq, add_div]
      exact (norm_add_le _ _).trans
        (add_le_add (h1 u ((le_max_left _ _).trans hu)) (h2 u ((le_max_right _ _).trans hu)))
  | mul_X p i ihp =>
    obtain ⟨⟨Cp, hCp, Ap, hpb⟩, hpd⟩ := ihp
    refine ⟨⟨Cp * CH, mul_pos hCp hCH, Ap + A, fun u hu => ?_⟩, fun N => ?_⟩
    · rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_add]
      calc ‖MvPolynomial.eval _ p‖ * ‖iteratedDeriv (i : ℕ) g u‖
          ≤ (Cp * u ^ Ap) * (CH * u ^ A) := mul_le_mul (hpb u hu) (hgB i u hu) (norm_nonneg _) (by positivity)
        _ = (Cp * CH) * (u ^ Ap * u ^ A) := by ring
    · obtain ⟨Cf0, hCf0, Uf0, hf0⟩ := hdiff i 0
      obtain ⟨C1, hC1, U1, h1⟩ := hpd (N + A)
      obtain ⟨C2, hC2, U2, h2⟩ := hdiff i (N + Ap)
      let Mf : ℝ := CH + Cf0
      refine ⟨C1 * Mf + Cp * C2, by positivity, max 1 (max Uf0 (max U1 U2)), fun u hu => ?_⟩
      have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
      have huf0 : Uf0 ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
      have hu1' : U1 ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hu))
      have hu2' : U2 ≤ u := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hu))
      have hf_bound : ‖iteratedDeriv (i : ℕ) f u‖ ≤ Mf * u ^ A := by
        have htri : ‖iteratedDeriv (i : ℕ) f u‖ ≤
            ‖iteratedDeriv (i : ℕ) f u - iteratedDeriv (i : ℕ) g u‖ + ‖iteratedDeriv (i : ℕ) g u‖ := by
          simpa using norm_add_le (iteratedDeriv (i : ℕ) f u - iteratedDeriv (i : ℕ) g u)
            (iteratedDeriv (i : ℕ) g u)
        have h1' : ‖iteratedDeriv (i : ℕ) f u - iteratedDeriv (i : ℕ) g u‖ ≤ Cf0 := by
          simpa using hf0 u huf0
        have huA : 1 ≤ u ^ A := one_le_pow₀ hu1
        dsimp only [Mf]; nlinarith [hgB i u hu1]
      simp only [map_mul, MvPolynomial.eval_X]
      have hid : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) p * iteratedDeriv (i : ℕ) f u -
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p * iteratedDeriv (i : ℕ) g u =
          (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) p -
            MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p) * iteratedDeriv (i : ℕ) f u +
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p *
            (iteratedDeriv (i : ℕ) f u - iteratedDeriv (i : ℕ) g u) := by ring
      rw [hid]
      have ht1 : ‖(MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) p -
            MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p) *
            iteratedDeriv (i : ℕ) f u‖ ≤ (C1 * Mf) / u ^ N := by
        rw [norm_mul]
        calc _ ≤ (C1 / u ^ (N + A)) * (Mf * u ^ A) :=
              mul_le_mul (h1 u hu1') hf_bound (norm_nonneg _) (by positivity)
          _ = (C1 * Mf) / u ^ N := by
              rw [pow_add]; field_simp [hu_pos.ne']
      have ht2 : ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) g u) p *
            (iteratedDeriv (i : ℕ) f u - iteratedDeriv (i : ℕ) g u)‖ ≤ (Cp * C2) / u ^ N := by
        rw [norm_mul]
        calc _ ≤ (Cp * u ^ Ap) * (C2 / u ^ (N + Ap)) :=
              mul_le_mul (hpb u hu1) (h2 u hu2') (norm_nonneg _) (by positivity)
          _ = (Cp * C2) / u ^ N := by
              rw [pow_add]; field_simp [hu_pos.ne']
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ (C1 * Mf) / u ^ N + (Cp * C2) / u ^ N := add_le_add ht1 ht2
        _ = (C1 * Mf + Cp * C2) / u ^ N := by ring

/-- **COMPLETE DISCHARGE OF HYPOTHESIS 2 (`hasymp`) FROM `Main.PNTAllOrders`**:
If a multivariate polynomial `P` vanishes eventually on the jets of `nthPrimeSmoothRay`, then
`‖eval (jet I_plus u) P‖ ≤ C / u ^ N` for every `N : ℕ`. -/
theorem hasymp_of_pnt (hpnt : Main.PNTAllOrders) (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) nthPrimeSmoothRay u) P = 0) :
    ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) P‖ ≤ C / u ^ N := by
  have hdiff := (eval_jet_diff_allOrders (I_plus_poly_jet_bound r)
    (fun j N => nthPrimeSmoothRay_sub_I_plus_allOrders hpnt (j : ℕ) N) P).2
  obtain ⟨U0, hU0⟩ := eventually_atTop.mp hP
  intro N
  obtain ⟨C, hC, U1, h1⟩ := hdiff N
  refine ⟨C, hC, max U0 U1, fun u hu => ?_⟩
  have h0 := hU0 u ((le_max_left _ _).trans hu)
  have h1' := h1 u ((le_max_right _ _).trans hu)
  rw [h0, zero_sub, norm_neg] at h1'
  exact h1'

/-! ### 3. Watson / Phragmén–Lindelöf Uniqueness on a Sector of Opening `> π` & `hbridge` Reduction -/

/-! #### 3a. Pure Complex-Analytic Watson Uniqueness Theorems -/

/-- Closed symmetric sector `{z : ℂ | R ≤ ‖z‖ ∧ |arg z| ≤ α}`. -/
@[expose] def closedSector (α R : ℝ) : Set ℂ :=
  {z : ℂ | R ≤ ‖z‖ ∧ |Complex.arg z| ≤ α}

/-- Open symmetric sector `{z : ℂ | R < ‖z‖ ∧ |arg z| < α}`. -/
@[expose] def openSector (α R : ℝ) : Set ℂ :=
  {z : ℂ | R < ‖z‖ ∧ |Complex.arg z| < α}

/-- Rotated closed sector `{z : ℂ | R ≤ ‖z‖ ∧ |arg (exp (-i θ₀) z)| ≤ (θ₂ - θ₁) / 2}`
corresponding to `θ₁ ≤ arg z ≤ θ₂` with center `θ₀ = (θ₁ + θ₂) / 2`. -/
@[expose] def rotatedClosedSector (θ₁ θ₂ R : ℝ) : Set ℂ :=
  {z : ℂ | R ≤ ‖z‖ ∧
    |Complex.arg (Complex.exp (-(((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I) * z)| ≤ (θ₂ - θ₁) / 2}

lemma abs_arg_le_iff_mul_cos_le_re {z : ℂ} (hz : z ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi) :
    |Complex.arg z| ≤ α ↔ ‖z‖ * Real.cos α ≤ z.re := by
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcos_arg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  have harg_le_pi : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
  have hmem1 : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi := ⟨abs_nonneg _, harg_le_pi⟩
  have hmem2 : α ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hα0, hαpi⟩
  rw [← Real.strictAntiOn_cos.le_iff_ge hmem2 hmem1, hcos_arg, le_div_iff₀ hnorm_pos, mul_comm]

lemma abs_arg_lt_iff_mul_cos_lt_re {z : ℂ} (hz : z ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi) :
    |Complex.arg z| < α ↔ ‖z‖ * Real.cos α < z.re := by
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcos_arg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  have harg_le_pi : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
  have hmem1 : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi := ⟨abs_nonneg _, harg_le_pi⟩
  have hmem2 : α ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hα0, hαpi⟩
  rw [← Real.strictAntiOn_cos.lt_iff_gt hmem2 hmem1, hcos_arg, lt_div_iff₀ hnorm_pos, mul_comm]

lemma arg_cexp_eq_im {w : ℂ} (hlo : -Real.pi < w.im) (hhi : w.im ≤ Real.pi) :
    Complex.arg (Complex.exp w) = w.im := by
  have heq : Complex.exp w = (Real.exp w.re : ℂ) * (Complex.cos (w.im : ℂ) + Complex.sin (w.im : ℂ) * I) := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos, Complex.ofReal_exp]
  rw [heq, Complex.arg_real_mul _ (Real.exp_pos w.re)]
  exact Complex.arg_cos_add_sin_mul_I ⟨hlo, hhi⟩

lemma mem_slitPlane_of_mem_closedSector {α R : ℝ} (hαpi : α < Real.pi) (hR : 0 < R)
    {z : ℂ} (hz : z ∈ closedSector α R) : z ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hz.1)
  by_contra hnot
  rw [Complex.mem_slitPlane_iff] at hnot
  push Not at hnot
  have hneg : z.re < 0 := lt_of_le_of_ne hnot.1 fun h0 => hz0 (Complex.ext h0 hnot.2)
  have harg : Complex.arg z = Real.pi := by
    have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hnot.2)
    rw [hz_eq, Complex.arg_ofReal_of_neg hneg]
  have habs : |Complex.arg z| = Real.pi := by rw [harg, abs_of_pos Real.pi_pos]
  linarith [hz.2]

lemma isOpen_openSector {α R : ℝ} (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi) (hR : 0 ≤ R) :
    IsOpen (openSector α R) := by
  have heq : openSector α R = {z : ℂ | R < ‖z‖ ∧ ‖z‖ * Real.cos α < z.re} := by
    ext z
    simp only [openSector, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR h1)
      exact ⟨h1, (abs_arg_lt_iff_mul_cos_lt_re hz0 hα0 hαpi).mp h2⟩
    · rintro ⟨h1, h2⟩
      have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR h1)
      exact ⟨h1, (abs_arg_lt_iff_mul_cos_lt_re hz0 hα0 hαpi).mpr h2⟩
  rw [heq]
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt (continuous_norm.mul continuous_const) Complex.continuous_re)

lemma isPreconnected_openSector {α R : ℝ} (_hα0 : 0 < α) (hαpi : α < Real.pi) (hR : 0 < R) :
    IsPreconnected (openSector α R) := by
  let S : Set ℂ := {w : ℂ | Real.log R < w.re ∧ |w.im| < α}
  have hconv : Convex ℝ S := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    simp only [S, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero]
    have hcomb_lt : ∀ x y c : ℝ, c < x → c < y → c < a * x + b * y := by
      intro x y c hx hy
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1]; linarith
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have h1 : a * c < a * x := mul_lt_mul_of_pos_left hx ha_pos
        have h2 : b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
        have h3 : a * c + b * c = c := by linear_combination c * hab
        linarith
    have hcomb_gt : ∀ x y c : ℝ, x < c → y < c → a * x + b * y < c := by
      intro x y c hx hy
      have := hcomb_lt (-x) (-y) (-c) (by linarith) (by linarith)
      linarith
    refine ⟨hcomb_lt w₁.re w₂.re (Real.log R) hw₁.1 hw₂.1, ?_⟩
    have h1 := abs_lt.mp hw₁.2
    have h2 := abs_lt.mp hw₂.2
    rw [abs_lt]
    exact ⟨hcomb_lt w₁.im w₂.im (-α) h1.1 h2.1, hcomb_gt w₁.im w₂.im α h1.2 h2.2⟩
  have himg : Complex.exp '' S = openSector α R := by
    ext z
    simp only [Set.mem_image, S, openSector, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have hnorm : R < ‖Complex.exp w‖ := by
        rw [Complex.norm_exp]
        exact (Real.log_lt_iff_lt_exp hR).mp hw1
      have harg : Complex.arg (Complex.exp w) = w.im := by
        have h := abs_lt.mp hw2
        exact arg_cexp_eq_im (by linarith) (by linarith)
      rw [harg]
      exact ⟨hnorm, hw2⟩
    · rintro ⟨h1, h2⟩
      have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hR h1)
      refine ⟨Complex.log z, ⟨?_, ?_⟩, Complex.exp_log hz0⟩
      · rw [Complex.log_re]
        exact Real.log_lt_log hR h1
      · rwa [Complex.log_im]
  rw [← himg]
  exact hconv.isPreconnected.image Complex.exp Complex.continuous_exp.continuousOn

/-- Real part of `z ^ (β : ℂ)` in polar coordinates for `z ≠ 0` and real `β`. -/
lemma cpow_ofReal_re {z : ℂ} (hz : z ≠ 0) (β : ℝ) :
    (z ^ (β : ℂ)).re = ‖z‖ ^ β * Real.cos (β * Complex.arg z) := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  have hre : (Complex.log z * (β : ℂ)).re = Real.log ‖z‖ * β := by
    simp [Complex.mul_re, Complex.log_re]
  have him : (Complex.log z * (β : ℂ)).im = β * Complex.arg z := by
    simp [Complex.mul_im, Complex.log_im, mul_comm]
  rw [hre, him, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- **WATSON'S UNIQUENESS THEOREM ON A SECTOR OF OPENING `> π`** (`watson_uniqueness_sector`):
If `f : ℂ → ℂ` is holomorphic on an open set `U` containing the closed sector
`closedSector α R = {z | R ≤ ‖z‖ ∧ |arg z| ≤ α}` with `π / 2 < α < π` and `R > 0`,
and satisfies exponential decay `‖f z‖ ≤ M * exp (-c * ‖z‖)` on `closedSector α R`
for some `M > 0, c > 0`, then `f z = 0` for EVERY `z ∈ closedSector α R`! -/
theorem watson_uniqueness_sector {α R M c : ℝ} (hα_lo : Real.pi / 2 < α) (hα_hi : α < Real.pi)
    (hR : 0 < R) (hM : 0 < M) (hc : 0 < c) {U : Set ℂ} (hU : IsOpen U)
    (hsub : closedSector α R ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hdecay : ∀ z ∈ closedSector α R, ‖f z‖ ≤ M * Real.exp (-c * ‖z‖)) :
    ∀ z ∈ closedSector α R, f z = 0 := by
  have hα0 : 0 < α := lt_trans (by positivity) hα_lo
  -- Choose `β ∈ (π / (2α), 1)` so `π / 2 < β * α < π` and `cos (β * α) < 0`
  let β : ℝ := (Real.pi / (2 * α) + 1) / 2
  have hratio_lt1 : Real.pi / (2 * α) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hratio_pos : 0 < Real.pi / (2 * α) := by positivity
  have hβ_pos : 0 < β := by dsimp [β]; linarith
  have hβ_lt1 : β < 1 := by dsimp [β]; linarith
  have hβα_lo : Real.pi / 2 < β * α := by
    have h1 : Real.pi / (2 * α) < β := by dsimp [β]; linarith
    have h2 : Real.pi / (2 * α) * α = Real.pi / 2 := by field_simp [hα0.ne']
    nlinarith
  have hβα_hi : β * α < Real.pi := by nlinarith
  have hcos_neg : Real.cos (β * α) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hβα_lo (by linarith [Real.pi_pos])
  -- Step 1: Show `f (x : ℂ) = 0` for every real `x > R` via Maximum Modulus Principle on bounded wedges
  have hreal_zero : ∀ x : ℝ, R < x → f (x : ℂ) = 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hR hx
    have hpow_lt : R ^ β < x ^ β := Real.rpow_lt_rpow hR.le hx hβ_pos
    have hbound_A : ∀ A : ℝ, 0 < A → ‖f (x : ℂ)‖ ≤ M * Real.exp (-A * (x ^ β - R ^ β)) := by
      intro A hA
      -- Choose outer radius `ρ` large enough that `x < ρ` and `A * ρ ^ β ≤ c * ρ`
      let ρ : ℝ := max (x + 1) (max 1 ((A / c + 1) ^ (1 / (1 - β))))
      have hρ_gt_x : x < ρ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hρ_gt_R : R < ρ := lt_trans hx hρ_gt_x
      have hρ_ge1 : 1 ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
      have hρ_pos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ_ge1
      have h1mβ : 0 < 1 - β := sub_pos.mpr hβ_lt1
      have hρ_outer : A * ρ ^ β ≤ c * ρ := by
        have hbase_pos : 0 < A / c + 1 := by positivity
        have hle : (A / c + 1) ^ (1 / (1 - β)) ≤ ρ := (le_max_right _ _).trans (le_max_right _ _)
        have hpow : A / c + 1 ≤ ρ ^ (1 - β) := by
          have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hbase_pos.le _) hle h1mβ.le
          rw [← Real.rpow_mul hbase_pos.le, one_div_mul_cancel h1mβ.ne', Real.rpow_one] at h1
          exact h1
        have hdiv : A / c ≤ ρ ^ (1 - β) := by linarith
        have hmul : A ≤ c * ρ ^ (1 - β) := by
          have := (div_le_iff₀ hc).mp hdiv
          linarith
        have hsplit : ρ ^ (1 - β) * ρ ^ β = ρ := by
          rw [← Real.rpow_add hρ_pos, sub_add_cancel, Real.rpow_one]
        calc A * ρ ^ β ≤ (c * ρ ^ (1 - β)) * ρ ^ β :=
              mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hρ_pos.le _)
          _ = c * (ρ ^ (1 - β) * ρ ^ β) := by ring
          _ = c * ρ := by rw [hsplit]
      let W : Set ℂ := {z : ℂ | R < ‖z‖ ∧ ‖z‖ < ρ ∧ ‖z‖ * Real.cos α < z.re}
      let K : Set ℂ := {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ ρ ∧ ‖z‖ * Real.cos α ≤ z.re}
      have hW_open : IsOpen W :=
        (isOpen_lt continuous_const continuous_norm).inter
          ((isOpen_lt continuous_norm continuous_const).inter
            (isOpen_lt (continuous_norm.mul continuous_const) Complex.continuous_re))
      have hK_closed : IsClosed K :=
        (isClosed_le continuous_const continuous_norm).inter
          ((isClosed_le continuous_norm continuous_const).inter
            (isClosed_le (continuous_norm.mul continuous_const) Complex.continuous_re))
      have hW_sub_K : W ⊆ K := fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
      have hcl_sub_K : closure W ⊆ K := closure_minimal hW_sub_K hK_closed
      have hK_sub_sec : K ⊆ closedSector α R := fun z hz => by
        have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hz.1)
        exact ⟨hz.1, (abs_arg_le_iff_mul_cos_le_re hz0 hα0.le hα_hi.le).mpr hz.2.2⟩
      have hW_bdd : Bornology.IsBounded W :=
        (Metric.isBounded_ball (x := (0 : ℂ)) (r := ρ)).subset fun z hz => by
          simpa [Metric.mem_ball, dist_zero_right] using hz.2.1
      let h : ℂ → ℂ := fun z => Complex.exp ((A : ℂ) * z ^ (β : ℂ)) * f z
      have hh_diff : DifferentiableOn ℂ h K := by
        intro z hz
        have hsec : z ∈ closedSector α R := hK_sub_sec hz
        have hslit : z ∈ Complex.slitPlane := mem_slitPlane_of_mem_closedSector hα_hi hR hsec
        have hcpow : DifferentiableAt ℂ (fun w : ℂ => w ^ (β : ℂ)) z :=
          DifferentiableAt.cpow differentiableAt_id (differentiableAt_const _) hslit
        have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((A : ℂ) * w ^ (β : ℂ))) z :=
          Complex.differentiable_exp.differentiableAt.comp _ (hcpow.const_mul (A : ℂ))
        have hf_at : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds (hsub hsec))
        exact (hexp.mul hf_at).differentiableWithinAt
      have hh_dcc : DiffContOnCl ℂ h W :=
        ⟨hh_diff.mono hW_sub_K, hh_diff.continuousOn.mono hcl_sub_K⟩
      -- Frontier bound `‖h z‖ ≤ M * exp (A * R ^ β)`
      have hfront : ∀ z ∈ frontier W, ‖h z‖ ≤ M * Real.exp (A * R ^ β) := by
        intro z hz
        have hzK : z ∈ K := hcl_sub_K hz.1
        have hz_notW : z ∉ W := by
          have hmem : z ∈ closure W \ interior W := hz
          rw [hW_open.interior_eq] at hmem
          exact hmem.2
        have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hzK.1)
        have hz_sec : z ∈ closedSector α R := hK_sub_sec hzK
        have hnorm_h : ‖h z‖ = Real.exp (A * ‖z‖ ^ β * Real.cos (β * Complex.arg z)) * ‖f z‖ := by
          dsimp only [h]
          rw [norm_mul, Complex.norm_exp]
          congr 2
          have hre : ((A : ℂ) * z ^ (β : ℂ)).re = A * (z ^ (β : ℂ)).re := by simp
          rw [hre, cpow_ofReal_re hz0 β]
          ring
        have hM_le : M ≤ M * Real.exp (A * R ^ β) :=
          le_mul_of_one_le_right hM.le (Real.one_le_exp (by positivity))
        have hf_dec : ‖f z‖ ≤ M * Real.exp (-c * ‖z‖) := hdecay z hz_sec
        have hf_M : ‖f z‖ ≤ M :=
          hf_dec.trans (mul_le_of_le_one_right hM.le (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])))
        -- On `K \ W`, at least one of the 3 inequalities is an equality!
        have hcases : ‖z‖ = R ∨ ‖z‖ = ρ ∨ ‖z‖ * Real.cos α = z.re := by
          by_contra hnone
          push Not at hnone
          apply hz_notW
          exact ⟨lt_of_le_of_ne hzK.1 (Ne.symm hnone.1),
            lt_of_le_of_ne hzK.2.1 hnone.2.1,
            lt_of_le_of_ne hzK.2.2 hnone.2.2⟩
        rcases hcases with hEqR | hEqρ | hEqArg
        · rw [hnorm_h, hEqR]
          have hcos1 : Real.cos (β * Complex.arg z) ≤ 1 := Real.cos_le_one _
          have hexp_le : Real.exp (A * R ^ β * Real.cos (β * Complex.arg z)) ≤ Real.exp (A * R ^ β) :=
            Real.exp_le_exp.mpr (by
              have hAR : 0 < A * R ^ β := mul_pos hA (Real.rpow_pos_of_pos hR β)
              nlinarith)
          calc Real.exp (A * R ^ β * Real.cos (β * Complex.arg z)) * ‖f z‖
              ≤ Real.exp (A * R ^ β) * M :=
                mul_le_mul hexp_le hf_M (norm_nonneg _) (Real.exp_pos _).le
            _ = M * Real.exp (A * R ^ β) := mul_comm _ _
        · rw [hnorm_h, hEqρ]
          have hcos1 : Real.cos (β * Complex.arg z) ≤ 1 := Real.cos_le_one _
          have hexp_le : Real.exp (A * ρ ^ β * Real.cos (β * Complex.arg z)) ≤ Real.exp (A * ρ ^ β) :=
            Real.exp_le_exp.mpr (by
              have hAρ : 0 < A * ρ ^ β := mul_pos hA (Real.rpow_pos_of_pos hρ_pos β)
              nlinarith)
          rw [hEqρ] at hf_dec
          calc Real.exp (A * ρ ^ β * Real.cos (β * Complex.arg z)) * ‖f z‖
              ≤ Real.exp (A * ρ ^ β) * (M * Real.exp (-c * ρ)) :=
                mul_le_mul hexp_le hf_dec (norm_nonneg _) (Real.exp_pos _).le
            _ = M * Real.exp (A * ρ ^ β + -c * ρ) := by rw [Real.exp_add]; ring
            _ ≤ M * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) hM.le
            _ = M := mul_one _
            _ ≤ M * Real.exp (A * R ^ β) := hM_le
        · have harg_eq : |Complex.arg z| = α := by
            have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
            have hcos_eq : Real.cos |Complex.arg z| = Real.cos α := by
              rw [Real.cos_abs, Complex.cos_arg hz0, ← hEqArg, mul_div_cancel_left₀ _ hnorm_pos.ne']
            exact Real.strictAntiOn_cos.injOn ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩ ⟨hα0.le, hα_hi.le⟩ hcos_eq
          have hcos_eq : Real.cos (β * Complex.arg z) = Real.cos (β * α) := by
            rw [← Real.cos_abs (β * Complex.arg z), abs_mul, abs_of_pos hβ_pos, harg_eq]
          rw [hnorm_h, hcos_eq]
          have hexp_le1 : Real.exp (A * ‖z‖ ^ β * Real.cos (β * α)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by
              have hAz : 0 < A * ‖z‖ ^ β := mul_pos hA (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) β)
              nlinarith)
          calc Real.exp (A * ‖z‖ ^ β * Real.cos (β * α)) * ‖f z‖
              ≤ 1 * M := mul_le_mul hexp_le1 hf_M (norm_nonneg _) zero_le_one
            _ = M := one_mul _
            _ ≤ M * Real.exp (A * R ^ β) := hM_le
      -- Apply Maximum Modulus Principle at `(x : ℂ) ∈ W ⊆ closure W`
      have hx_mem : (x : ℂ) ∈ W := by
        refine ⟨by simpa [abs_of_pos hx_pos] using hx,
          by simpa [abs_of_pos hx_pos] using hρ_gt_x, ?_⟩
        simp only [Complex.norm_real, Real.norm_of_nonneg hx_pos.le, Complex.ofReal_re]
        have hcos_lt1 : Real.cos α < 1 := by
          have := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hα0.le, hα_hi.le⟩ hα0
          simpa [Real.cos_zero] using this
        nlinarith
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hW_bdd hh_dcc hfront
        (subset_closure hx_mem)
      have hx_ne0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
      have hx_arg : Complex.arg (x : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hx_pos.le
      have hnorm_hx : ‖h (x : ℂ)‖ = Real.exp (A * x ^ β) * ‖f (x : ℂ)‖ := by
        dsimp only [h]
        rw [norm_mul, Complex.norm_exp]
        congr 2
        have hre : ((A : ℂ) * (x : ℂ) ^ (β : ℂ)).re = A * ((x : ℂ) ^ (β : ℂ)).re := by simp
        rw [hre, cpow_ofReal_re hx_ne0 β, hx_arg, mul_zero, Real.cos_zero, mul_one,
          Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
      rw [hnorm_hx] at hmax
      have hexp_pos : 0 < Real.exp (A * x ^ β) := Real.exp_pos _
      calc ‖f (x : ℂ)‖ = Real.exp (-(A * x ^ β)) * (Real.exp (A * x ^ β) * ‖f (x : ℂ)‖) := by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (-(A * x ^ β)) * (M * Real.exp (A * R ^ β)) :=
            mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
        _ = M * Real.exp (-A * (x ^ β - R ^ β)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    -- Let `A → +∞` to deduce `‖f (x : ℂ)‖ = 0`
    have hnorm0 : ‖f (x : ℂ)‖ ≤ 0 := by
      have htend : Tendsto (fun A : ℝ => M * Real.exp (-A * (x ^ β - R ^ β))) atTop (𝓝 0) := by
        have hlin : Tendsto (fun A : ℝ => -A * (x ^ β - R ^ β)) atTop atBot := by
          have hsub : 0 < x ^ β - R ^ β := sub_pos.mpr hpow_lt
          have h1 : Tendsto (fun A : ℝ => -(A * (x ^ β - R ^ β))) atTop atBot :=
            tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hsub)
          exact h1.congr fun A => by ring
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul M
      exact ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, fun A hA => hbound_A A (by linarith)⟩)
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  -- Step 2: Identity theorem on `openSector α R`
  have hopen_sub : openSector α R ⊆ closedSector α R := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have han : AnalyticOnNhd ℂ f (openSector α R) :=
    (hf.mono (hopen_sub.trans hsub)).analyticOnNhd (isOpen_openSector hα0.le hα_hi.le hR.le)
  have hz0_mem : ((R + 1 : ℝ) : ℂ) ∈ openSector α R := by
    simp only [openSector, Set.mem_ofPred_eq, Complex.norm_real,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ R + 1 by linarith),
      Complex.arg_ofReal_of_nonneg (show (0 : ℝ) ≤ R + 1 by linarith), abs_zero]
    exact ⟨by linarith, hα0⟩
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] ((R + 1 : ℝ) : ℂ), f z = 0 := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨δ, hδ, hball⟩ := hs
    let x : ℝ := R + 1 + min (δ / 2) 1
    have hx_gt : R < x := by
      have : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) zero_lt_one
      dsimp [x]; linarith
    have hx_mem : (x : ℂ) ∈ Metric.ball ((R + 1 : ℝ) : ℂ) δ ∩ {((R + 1 : ℝ) : ℂ)}ᶜ := by
      have hmin_pos : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) zero_lt_one
      have hmin_le : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
      constructor
      · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have : x - (R + 1) = min (δ / 2) 1 := by dsimp [x]; ring
        rw [this, abs_of_pos hmin_pos]
        linarith
      · intro heq
        have hre := congr_arg Complex.re heq
        simp only [Complex.ofReal_re] at hre
        dsimp [x] at hre; linarith
    exact ⟨(x : ℂ), hball hx_mem, hreal_zero x hx_gt⟩
  have hopen_zero : Set.EqOn f 0 (openSector α R) :=
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_openSector hα0 hα_hi hR) hz0_mem hfreq
  -- Step 3: Extend from `openSector α R` to `closedSector α R` by continuity
  intro z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hz.1)
  have hf_cont : ContinuousAt f z := (hf.differentiableAt (hU.mem_nhds (hsub hz))).continuousAt
  let seq : ℕ → ℂ := fun n =>
    Complex.exp (((Real.log ‖z‖ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) +
      I * (((1 - 1 / ((n : ℝ) + 2)) * Complex.arg z : ℝ) : ℂ))
  have hseq_mem : ∀ n : ℕ, seq n ∈ openSector α R := by
    intro n
    have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hfac_pos : 0 < 1 - 1 / ((n : ℝ) + 2) := by
      have : 1 / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
      linarith
    have hfac_lt1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    have harg_lt : |(1 - 1 / ((n : ℝ) + 2)) * Complex.arg z| < α := by
      rw [abs_mul, abs_of_pos hfac_pos]
      by_cases h0 : Complex.arg z = 0
      · simp [h0, hα0]
      · have habs_pos : 0 < |Complex.arg z| := abs_pos.mpr h0
        calc (1 - 1 / ((n : ℝ) + 2)) * |Complex.arg z| < 1 * |Complex.arg z| :=
              mul_lt_mul_of_pos_right hfac_lt1 habs_pos
          _ = |Complex.arg z| := one_mul _
          _ ≤ α := hz.2
    let w : ℂ := ((Real.log ‖z‖ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) +
      I * (((1 - 1 / ((n : ℝ) + 2)) * Complex.arg z : ℝ) : ℂ)
    have hre_eq : w.re = Real.log ‖z‖ + 1 / ((n : ℝ) + 1) := by
      dsimp only [w]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him_eq : w.im = (1 - 1 / ((n : ℝ) + 2)) * Complex.arg z := by
      dsimp only [w]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
    refine ⟨?_, ?_⟩
    · change R < ‖Complex.exp w‖
      rw [Complex.norm_exp, hre_eq, Real.exp_add, Real.exp_log (norm_pos_iff.mpr hz0)]
      have hexp1 : 1 < Real.exp (1 / ((n : ℝ) + 1)) := Real.one_lt_exp_iff.mpr hn1
      nlinarith [hz.1]
    · change |Complex.arg (Complex.exp w)| < α
      have harg_eq : Complex.arg (Complex.exp w) = w.im := by
        have h := abs_lt.mp harg_lt
        exact arg_cexp_eq_im (by rw [him_eq]; linarith) (by rw [him_eq]; linarith)
      rw [harg_eq, him_eq]
      exact harg_lt
  have hseq_lim : Tendsto seq atTop (𝓝 z) := by
    have hinv1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hinv2 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring_nf
    have hre_lim : Tendsto (fun n : ℕ => Real.log ‖z‖ + 1 / ((n : ℝ) + 1)) atTop (𝓝 (Real.log ‖z‖)) := by
      simpa using tendsto_const_nhds.add hinv1
    have him_lim : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2)) * Complex.arg z) atTop (𝓝 (Complex.arg z)) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 ((1 : ℝ) - 0)) :=
        tendsto_const_nhds.sub hinv2
      rw [sub_zero] at h1
      simpa using h1.mul_const (Complex.arg z)
    have harg_lim : Tendsto (fun n : ℕ =>
        ((Real.log ‖z‖ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) +
          I * (((1 - 1 / ((n : ℝ) + 2)) * Complex.arg z : ℝ) : ℂ))
        atTop (𝓝 (Complex.log z)) := by
      have h1 := Complex.continuous_ofReal.continuousAt.tendsto.comp hre_lim
      have h2 := (Complex.continuous_ofReal.continuousAt.tendsto.comp him_lim).const_mul I
      have htot := h1.add h2
      have hlog_eq : (Real.log ‖z‖ : ℂ) + I * (Complex.arg z : ℂ) = Complex.log z := by
        rw [Complex.log]; ring
      rwa [hlog_eq] at htot
    have hexp_lim := Complex.continuous_exp.continuousAt.tendsto.comp harg_lim
    rwa [Complex.exp_log hz0] at hexp_lim
  have hf_lim : Tendsto (fun n : ℕ => f (seq n)) atTop (𝓝 (f z)) := hf_cont.tendsto.comp hseq_lim
  have hf_zero : Tendsto (fun n : ℕ => f (seq n)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hopen_zero (hseq_mem n)).symm
  exact tendsto_nhds_unique hf_lim hf_zero

/-- Elementary factorial bound `N! ≤ N ^ N` for all `N : ℕ`. -/
lemma factorial_le_pow_self (N : ℕ) : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
  have hnat : N.factorial ≤ N ^ N := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Nat.factorial_succ, pow_succ']
      exact Nat.mul_le_mul_left (n + 1)
        (ih.trans (Nat.pow_le_pow_left (Nat.le_succ n) n))
  exact_mod_cast hnat

/-- **GEVREY-1 WATSON UNIQUENESS THEOREM ON A SECTOR OF OPENING `> π`** (`watson_uniqueness_gevrey1`):
If `f` is holomorphic on an open set containing `closedSector α R` (`π/2 < α < π`, `R > 0`) and
satisfies Gevrey-1 factorial flatness `∀ N : ℕ, ∀ z ∈ closedSector α R, ‖f z‖ ≤ C * A ^ N * N! / ‖z‖ ^ N`
for some `C > 0, A > 0`, then `f z = 0` for all `z ∈ closedSector α R`! -/
theorem watson_uniqueness_gevrey1 {α R C A : ℝ} (hα_lo : Real.pi / 2 < α) (hα_hi : α < Real.pi)
    (hR : 0 < R) (hC : 0 < C) (hA : 0 < A) {U : Set ℂ} (hU : IsOpen U)
    (hsub : closedSector α R ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hgev : ∀ N : ℕ, ∀ z ∈ closedSector α R,
      ‖f z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) :
    ∀ z ∈ closedSector α R, f z = 0 := by
  let c : ℝ := 1 / (Real.exp 1 * A)
  have hc : 0 < c := by dsimp [c]; positivity
  refine watson_uniqueness_sector hα_lo hα_hi hR (show 0 < C * Real.exp 1 by positivity) hc
    hU hsub hf fun z hz => ?_
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hR hz.1
  let N : ℕ := ⌊c * ‖z‖⌋₊
  have hN_le : (N : ℝ) ≤ c * ‖z‖ := Nat.floor_le (by positivity)
  have hN_gt : c * ‖z‖ - 1 < (N : ℝ) := by linarith [Nat.lt_floor_add_one (c * ‖z‖)]
  have hratio : A * (N : ℝ) / ‖z‖ ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hz_pos, Real.exp_neg]
    calc A * (N : ℝ) ≤ A * (c * ‖z‖) := mul_le_mul_of_nonneg_left hN_le hA.le
      _ = (Real.exp 1)⁻¹ * ‖z‖ := by dsimp [c]; field_simp [hA.ne', (Real.exp_pos 1).ne']
  have h1 := hgev N z hz
  have hfact := factorial_le_pow_self N
  have hpow_le : A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N ≤ Real.exp (-(N : ℝ)) := by
    calc A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N
        ≤ A ^ N * (N : ℝ) ^ N / ‖z‖ ^ N := by
          gcongr
      _ = (A * (N : ℝ) / ‖z‖) ^ N := by rw [div_pow, mul_pow]
      _ ≤ (Real.exp (-1)) ^ N := pow_le_pow_left₀ (by positivity) hratio N
      _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp_le : Real.exp (-(N : ℝ)) ≤ Real.exp 1 * Real.exp (-c * ‖z‖) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc ‖f z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := h1
    _ = C * (A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) := by ring
    _ ≤ C * Real.exp (-(N : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hC.le
    _ ≤ C * (Real.exp 1 * Real.exp (-c * ‖z‖)) := mul_le_mul_of_nonneg_left hexp_le hC.le
    _ = (C * Real.exp 1) * Real.exp (-c * ‖z‖) := by ring

/-- **ROTATED SECTOR WATSON UNIQUENESS** (`watson_uniqueness_rotated_sector`):
Works on ANY rotated sector `rotatedClosedSector θ₁ θ₂ R` with `π < θ₂ - θ₁ < 2π`
(in particular Codex's repaired bounded-angle sector `θ₁ = -3π/4`, `θ₂ = π/3`, width `13π/12 > π`!). -/
theorem watson_uniqueness_rotated_sector {θ₁ θ₂ R M c : ℝ}
    (hwidth_lo : Real.pi < θ₂ - θ₁) (hwidth_hi : θ₂ - θ₁ < 2 * Real.pi)
    (hR : 0 < R) (hM : 0 < M) (hc : 0 < c) {U : Set ℂ} (hU : IsOpen U)
    (hsub : rotatedClosedSector θ₁ θ₂ R ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hdecay : ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖f z‖ ≤ M * Real.exp (-c * ‖z‖)) :
    ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, f z = 0 := by
  let θ₀ : ℝ := (θ₁ + θ₂) / 2
  let α : ℝ := (θ₂ - θ₁) / 2
  let rot : ℂ := Complex.exp ((θ₀ : ℂ) * I)
  let invRot : ℂ := Complex.exp (-(θ₀ : ℂ) * I)
  have hrot_inv : invRot * rot = 1 := by
    dsimp [rot, invRot]; rw [← Complex.exp_add]; simp
  have hrot_inv' : rot * invRot = 1 := by
    dsimp [rot, invRot]; rw [← Complex.exp_add]; simp
  have hrot_norm : ‖rot‖ = 1 := by
    dsimp [rot]; rw [Complex.norm_exp]; simp
  have hinvRot_norm : ‖invRot‖ = 1 := by
    dsimp [invRot]; rw [Complex.norm_exp]; simp
  let g : ℂ → ℂ := fun w => f (rot * w)
  let V : Set ℂ := (fun w : ℂ => rot * w) ⁻¹' U
  have hV_open : IsOpen V := hU.preimage (continuous_const.mul continuous_id)
  have hV_sub : closedSector α R ⊆ V := by
    intro w hw
    apply hsub
    refine ⟨?_, ?_⟩
    · rw [norm_mul, hrot_norm, one_mul]; exact hw.1
    · change |Complex.arg (invRot * (rot * w))| ≤ α
      rw [← mul_assoc, hrot_inv, one_mul]
      exact hw.2
  have hg_diff : DifferentiableOn ℂ g V := by
    intro w hw
    have hf_at : DifferentiableAt ℂ f (rot * w) := hf.differentiableAt (hU.mem_nhds hw)
    have hmul : DifferentiableAt ℂ (fun x : ℂ => rot * x) w := differentiableAt_id.const_mul rot
    exact (show DifferentiableAt ℂ (f ∘ fun x : ℂ => rot * x) w from hf_at.comp w hmul).differentiableWithinAt
  have hg_decay : ∀ w ∈ closedSector α R, ‖g w‖ ≤ M * Real.exp (-c * ‖w‖) := by
    intro w hw
    have hmem : rot * w ∈ rotatedClosedSector θ₁ θ₂ R := by
      refine ⟨by rw [norm_mul, hrot_norm, one_mul]; exact hw.1, ?_⟩
      change |Complex.arg (invRot * (rot * w))| ≤ α
      rw [← mul_assoc, hrot_inv, one_mul]
      exact hw.2
    have h1 := hdecay (rot * w) hmem
    rwa [norm_mul, hrot_norm, one_mul] at h1
  have hg0 := watson_uniqueness_sector (α := α) (R := R) (by dsimp [α]; linarith) (by dsimp [α]; linarith)
    hR hM hc hV_open hV_sub hg_diff hg_decay
  intro z hz
  have hw_mem : invRot * z ∈ closedSector α R := by
    refine ⟨by rw [norm_mul, hinvRot_norm, one_mul]; exact hz.1, hz.2⟩
  have hgz := hg0 (invRot * z) hw_mem
  dsimp only [g] at hgz
  rwa [← mul_assoc, hrot_inv', one_mul] at hgz

/-- **ROTATED SECTOR GEVREY-1 WATSON UNIQUENESS**:
Same as `watson_uniqueness_rotated_sector` with Gevrey-1 factorial flatness. -/
theorem watson_uniqueness_rotated_gevrey1 {θ₁ θ₂ R C A : ℝ}
    (hwidth_lo : Real.pi < θ₂ - θ₁) (hwidth_hi : θ₂ - θ₁ < 2 * Real.pi)
    (hR : 0 < R) (hC : 0 < C) (hA : 0 < A) {U : Set ℂ} (hU : IsOpen U)
    (hsub : rotatedClosedSector θ₁ θ₂ R ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hgev : ∀ N : ℕ, ∀ z ∈ rotatedClosedSector θ₁ θ₂ R,
      ‖f z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) :
    ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, f z = 0 := by
  let c : ℝ := 1 / (Real.exp 1 * A)
  have hc : 0 < c := by dsimp [c]; positivity
  refine watson_uniqueness_rotated_sector hwidth_lo hwidth_hi hR (show 0 < C * Real.exp 1 by positivity) hc
    hU hsub hf fun z hz => ?_
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hR hz.1
  let N : ℕ := ⌊c * ‖z‖⌋₊
  have hN_le : (N : ℝ) ≤ c * ‖z‖ := Nat.floor_le (by positivity)
  have hN_gt : c * ‖z‖ - 1 < (N : ℝ) := by linarith [Nat.lt_floor_add_one (c * ‖z‖)]
  have hratio : A * (N : ℝ) / ‖z‖ ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hz_pos, Real.exp_neg]
    calc A * (N : ℝ) ≤ A * (c * ‖z‖) := mul_le_mul_of_nonneg_left hN_le hA.le
      _ = (Real.exp 1)⁻¹ * ‖z‖ := by dsimp [c]; field_simp [hA.ne', (Real.exp_pos 1).ne']
  have h1 := hgev N z hz
  have hfact := factorial_le_pow_self N
  have hpow_le : A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N ≤ Real.exp (-(N : ℝ)) := by
    calc A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N
        ≤ A ^ N * (N : ℝ) ^ N / ‖z‖ ^ N := by gcongr
      _ = (A * (N : ℝ) / ‖z‖) ^ N := by rw [div_pow, mul_pow]
      _ ≤ (Real.exp (-1)) ^ N := pow_le_pow_left₀ (by positivity) hratio N
      _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp_le : Real.exp (-(N : ℝ)) ≤ Real.exp 1 * Real.exp (-c * ‖z‖) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc ‖f z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := h1
    _ = C * (A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) := by ring
    _ ≤ C * Real.exp (-(N : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hC.le
    _ ≤ C * (Real.exp 1 * Real.exp (-c * ‖z‖)) := mul_le_mul_of_nonneg_left hexp_le hC.le
    _ = (C * Real.exp 1) * Real.exp (-c * ‖z‖) := by ring

/-- Positive real ray `[R, ∞)` lies inside `rotatedClosedSector θ₁ θ₂ R` whenever `θ₁ ≤ 0 ≤ θ₂`
and `θ₂ - θ₁ < 2π`. -/
lemma ofReal_mem_rotatedClosedSector {θ₁ θ₂ R x : ℝ} (hθ₁ : θ₁ ≤ 0) (hθ₂ : 0 ≤ θ₂)
    (hwidth : θ₂ - θ₁ < 2 * Real.pi) (hR : 0 < R) (hx : R ≤ x) :
    (x : ℂ) ∈ rotatedClosedSector θ₁ θ₂ R := by
  have hx_pos : 0 < x := lt_of_lt_of_le hR hx
  refine ⟨by simpa [Complex.norm_real, Real.norm_of_nonneg hx_pos.le] using hx, ?_⟩
  have hprod : Complex.exp (-(((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I) * (x : ℂ) =
      Complex.exp ((Real.log x : ℂ) + (-((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx_pos]
    ring
  rw [hprod]
  have him : ((Real.log x : ℂ) + (-((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I).im = -((θ₁ + θ₂) / 2) := by
    simp
  have harg : Complex.arg (Complex.exp ((Real.log x : ℂ) + (-((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I)) =
      -((θ₁ + θ₂) / 2) := by
    rw [arg_cexp_eq_im (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; linarith [Real.pi_pos]), him]
  rw [harg, abs_neg, abs_le]
  constructor <;> linarith

/-! #### 3b. Complex-Conjugation Symmetry `I_minus = star ∘ I_plus`, Real-Analyticity, and `hbridge` Reductions -/

/-- `R_integral (t : ℂ)` is purely real for `t < 1`. -/
lemma star_R_integral_ofReal {t : ℝ} (ht : t < 1) :
    star (PakNthPrimeEngine.R_integral (t : ℂ)) = PakNthPrimeEngine.R_integral (t : ℂ) := by
  have hreal : PakNthPrimeEngine.R_integral (t : ℂ) =
      ((t * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + t * PakNthPrimeEngine.E1 x) : ℝ) : ℂ) := by
    rw [R_integral_eq_mul_R_inner]
    dsimp only [R_inner]
    push_cast
    congr 1
    change ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(x : ℂ) + (t : ℂ) * (PakNthPrimeEngine.E1 x : ℂ)) =
      Complex.ofRealCLM (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x + t * PakNthPrimeEngine.E1 x))
    rw [← Complex.ofRealCLM.integral_comp_comm (integrableOn_exp_neg_add_mul_E1 ht)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp [Complex.ofReal_exp, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [hreal, Complex.star_def, Complex.conj_ofReal]

/-- `T_integral (t : ℂ)` is purely real for `0 < t < 1`. -/
lemma star_T_integral_ofReal {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    star (T_integral (t : ℂ)) = T_integral (t : ℂ) := by
  have hreal : T_integral (t : ℂ) =
      ((t * ∫ x in Set.Ioi (0 : ℝ), Real.exp (x - t * Ei_real x) : ℝ) : ℂ) := by
    rw [T_integral_eq_mul_T_inner]
    dsimp only [T_inner]
    push_cast
    congr 1
    change ∫ x in Set.Ioi (0 : ℝ), Complex.exp ((x : ℂ) - (t : ℂ) * (Ei_real x : ℂ)) =
      Complex.ofRealCLM (∫ x in Set.Ioi (0 : ℝ), Real.exp (x - t * Ei_real x))
    rw [← Complex.ofRealCLM.integral_comp_comm (integrableOn_exp_sub_mul_Ei_real ht0 ht1)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp [Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_mul]
  rw [hreal, Complex.star_def, Complex.conj_ofReal]

/-- **Exact Complex-Conjugation Symmetry**: `I_minus u = star (I_plus u)` for every `u > 0`. -/
theorem I_minus_eq_star_I_plus {u : ℝ} (hu : 0 < u) :
    I_minus u = star (I_plus u) := by
  set t : ℝ := Real.exp (-u)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [I_plus_eq_R_add_T hu, I_minus_eq_R_add_T hu]
  change PakNthPrimeEngine.R_integral (t : ℂ) + Complex.exp ((Real.pi : ℂ) * I * (t : ℂ)) * T_integral (t : ℂ) =
    star (PakNthPrimeEngine.R_integral (t : ℂ) + Complex.exp (-(Real.pi : ℂ) * I * (t : ℂ)) * T_integral (t : ℂ))
  rw [star_add, star_mul, star_R_integral_ofReal ht1, star_T_integral_ofReal ht0 ht1, mul_comm (T_integral (t : ℂ))]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]

/-- `iteratedDeriv` commutes with complex conjugation `star : ℂ → ℂ`. -/
lemma iteratedDeriv_star_comp (f : ℝ → ℂ) (k : ℕ) :
    iteratedDeriv k (fun u : ℝ => star (f u)) = fun u : ℝ => star (iteratedDeriv k f u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext u
    rw [iteratedDeriv_succ]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k f) u
    · have hc := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt u hd.hasDerivAt
      exact hc.deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun x : ℝ => star (iteratedDeriv k f x)) u := by
        intro h
        have hc := Complex.conjCLE.differentiableAt.comp u h
        have hfun : (⇑Complex.conjCLE ∘ fun x : ℝ => star (iteratedDeriv k f x)) = iteratedDeriv k f := by
          ext x; simp
        rw [hfun] at hc
        exact hd hc
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, star_zero]

/-- **Exponential Jet Proximity of `I_plus` and `I_minus`**:
For every `j, N : ℕ`, `‖iteratedDeriv j I_minus u - iteratedDeriv j I_plus u‖ ≤ C / u ^ N` eventually! -/
theorem I_minus_sub_I_plus_jet_allOrders (j N : ℕ) :
    ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖iteratedDeriv j I_minus u - iteratedDeriv j I_plus u‖ ≤ C / u ^ N := by
  obtain ⟨CD0, hCD0, hD0⟩ := I_plus_sub_T_jet_exp_decay j
  obtain ⟨CD, hCD, hD⟩ := mul_exp_neg_le_div_pow (2 * CD0) (by positivity) N
  refine ⟨CD, hCD, 1, fun u hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hloc_Im : I_minus =ᶠ[𝓝 u] (fun v : ℝ => star (I_plus v)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
    exact I_minus_eq_star_I_plus hv
  have hloc_T : (fun v : ℝ => T_integral (Real.exp (-v))) =ᶠ[𝓝 u]
      (fun v : ℝ => star (T_integral (Real.exp (-v)))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
    have hv0 : 0 < v := hv
    exact (star_T_integral_ofReal (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by linarith))).symm
  have hIm_jet : iteratedDeriv j I_minus u = star (iteratedDeriv j I_plus u) := by
    rw [hloc_Im.iteratedDeriv_eq, iteratedDeriv_star_comp]
  have hT_jet : star (iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u) =
      iteratedDeriv j (fun v : ℝ => T_integral (Real.exp (-v))) u := by
    rw [← congrFun (iteratedDeriv_star_comp _ j) u, ← hloc_T.iteratedDeriv_eq]
  have hcd_I : ContDiffAt ℝ j I_plus u := contDiff_I_plus.contDiffAt.of_le le_top
  have hcd_T : ContDiffAt ℝ j (fun v : ℝ => T_integral (Real.exp (-v))) u := by
    have han : AnalyticOnNhd ℂ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
      differentiableOn_T_exp_neg.analyticOnNhd isOpen_halfStrip
    have hcd_R : ContDiffOn ℝ ⊤ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
      (han.contDiffOn isOpen_halfStrip.uniqueDiffOn).restrict_scalars ℝ
    have hu_mem : (u : ℂ) ∈ halfStrip := by
      simp only [halfStrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
      exact ⟨by linarith, by norm_num⟩
    have hcomp : ContDiffAt ℝ ⊤ (fun v : ℝ => T_integral (Complex.exp (-(v : ℂ)))) u :=
      (hcd_R.contDiffAt (isOpen_halfStrip.mem_nhds hu_mem)).comp u Complex.ofRealCLM.contDiff.contDiffAt
    have heq : (fun v : ℝ => T_integral (Real.exp (-v))) = fun v : ℝ => T_integral (Complex.exp (-(v : ℂ))) := by
      ext v; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [heq]; exact hcomp.of_le le_top
  have hsub := iteratedDeriv_sub hcd_I hcd_T
  change iteratedDeriv j (fun v : ℝ => I_plus v - T_integral (Real.exp (-v))) u = _ at hsub
  set d : ℂ := iteratedDeriv j (fun v : ℝ => I_plus v - T_integral (Real.exp (-v))) u
  have hdiff_eq : iteratedDeriv j I_minus u - iteratedDeriv j I_plus u = star d - d := by
    rw [hIm_jet, hsub, star_sub, hT_jet]; ring
  rw [hdiff_eq]
  have hnorm_d : ‖d‖ ≤ CD0 * u * Real.exp (-u) := hD0 u hu
  have hnorm_star : ‖star d‖ = ‖d‖ := by simp
  calc ‖star d - d‖ ≤ ‖star d‖ + ‖d‖ := norm_sub_le _ _
    _ = 2 * ‖d‖ := by rw [hnorm_star]; ring
    _ ≤ 2 * (CD0 * u * Real.exp (-u)) := by linarith
    _ = (2 * CD0) * u * Real.exp (-u) := by ring
    _ ≤ CD / u ^ N := hD u hu

/-- Real-analyticity of `I_plus` on all of `ℝ`. -/
theorem analyticOnNhd_I_plus : AnalyticOnNhd ℝ I_plus Set.univ := by
  have heq : I_plus = fun u : ℝ => J_valley (-1) (Real.exp (-u) : ℂ) (1 / 4) :=
    funext fun u => I_contour_eq_J_valley (σ := -1) (Or.inl rfl) u (by norm_num) (by norm_num)
  rw [heq]
  have han_C : AnalyticOnNhd ℂ (fun t : ℂ => J_valley (-1) t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    (differentiableOn_J_valley_quarter (Or.inl rfl)).analyticOnNhd isOpen_sector_re_gt_abs_im
  intro u _
  have hmem : ((Real.exp (-u) : ℝ) : ℂ) ∈ {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨Real.exp_pos _, Real.exp_pos _⟩
  have han_R : AnalyticAt ℝ (fun t : ℂ => J_valley (-1) t (1 / 4)) ((Real.exp (-u) : ℝ) : ℂ) :=
    (han_C _ hmem).restrictScalars
  have hexp : AnalyticAt ℝ (fun v : ℝ => (Real.exp (-v) : ℂ)) u :=
    PrimeNome.tRay_analytic u
  exact han_R.comp_of_eq hexp rfl

/-- Real-analyticity of `I_minus` on all of `ℝ`. -/
theorem analyticOnNhd_I_minus : AnalyticOnNhd ℝ I_minus Set.univ := by
  have heq : I_minus = fun u : ℝ => J_valley 1 (Real.exp (-u) : ℂ) (1 / 4) :=
    funext fun u => I_contour_eq_J_valley (σ := 1) (Or.inr rfl) u (by norm_num) (by norm_num)
  rw [heq]
  have han_C : AnalyticOnNhd ℂ (fun t : ℂ => J_valley 1 t (1 / 4))
      {t : ℂ | 0 < t.re ∧ |t.im| < t.re} :=
    (differentiableOn_J_valley_quarter (Or.inr rfl)).analyticOnNhd isOpen_sector_re_gt_abs_im
  intro u _
  have hmem : ((Real.exp (-u) : ℝ) : ℂ) ∈ {t : ℂ | 0 < t.re ∧ |t.im| < t.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨Real.exp_pos _, Real.exp_pos _⟩
  have han_R : AnalyticAt ℝ (fun t : ℂ => J_valley 1 t (1 / 4)) ((Real.exp (-u) : ℝ) : ℂ) :=
    (han_C _ hmem).restrictScalars
  have hexp : AnalyticAt ℝ (fun v : ℝ => (Real.exp (-v) : ℂ)) u :=
    PrimeNome.tRay_analytic u
  exact han_R.comp_of_eq hexp rfl

/-- If `f : ℝ → ℂ` is globally real-analytic, then `u ↦ MvPolynomial.eval (jet f u) Q` is
globally real-analytic and vanishes everywhere on `ℝ` if it vanishes on any ray `[U₀, ∞)`. -/
theorem eval_jet_eq_zero_all_of_ray {r : ℕ} {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f Set.univ)
    (Q : MvPolynomial (Fin (r + 1)) ℂ) {U₀ : ℝ}
    (hray : ∀ u ≥ U₀, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) Q = 0) :
    ∀ u : ℝ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) Q = 0 := by
  have hjet_an : ∀ k : ℕ, AnalyticOnNhd ℝ (iteratedDeriv k f) Set.univ := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  have hQ_an_all : ∀ R : MvPolynomial (Fin (r + 1)) ℂ, AnalyticOnNhd ℝ
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) R)
      Set.univ := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C c =>
      intro u _; simp only [MvPolynomial.eval_C]; exact analyticAt_const
    | add p q ihp ihq =>
      intro u _
      have heq : (fun v : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f v) (p + q)) =
          (fun v : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f v) p +
            MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f v) q) := by
        ext v; simp [map_add]
      rw [heq]
      exact (ihp u trivial).add (ihq u trivial)
    | mul_X p i ihp =>
      intro u _
      have heq : (fun v : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f v) (p * MvPolynomial.X i)) =
          (fun v : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f v) p *
            iteratedDeriv (i : ℕ) f v) := by
        ext v; simp [map_mul]
      rw [heq]
      exact (ihp u trivial).mul (hjet_an (i : ℕ) u trivial)
  have hQ_an := hQ_an_all Q
  have hfreq : ∃ᶠ u : ℝ in 𝓝[≠] (U₀ + 1),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f u) Q = 0 := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨δ, hδ, hball⟩ := hs
    let x : ℝ := U₀ + 1 + min (δ / 2) 1
    have hmin_pos : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) zero_lt_one
    have hmin_le : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
    have hx_mem : x ∈ Metric.ball (U₀ + 1) δ ∩ {U₀ + 1}ᶜ := by
      refine ⟨?_, fun heq => by have h := Set.mem_singleton_iff.mp heq; dsimp [x] at h; linarith⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have : x - (U₀ + 1) = min (δ / 2) 1 := by dsimp [x]; ring
      rw [this, abs_of_pos hmin_pos]
      linarith
    exact ⟨x, hball hx_mem, hray x (by dsimp [x]; linarith)⟩
  have hzero := hQ_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ trivial hfreq
  intro u
  exact hzero trivial

/-- **Conjugation-Symmetry Reduction of `hbridge`** (`hbridge_of_one_sided_ray_bridge`):
Because `I_minus u = star (I_plus u)` on `(0, ∞)`, `I_minus - I_plus` has exponentially small jets,
and both `I_plus` and `I_minus` are globally real-analytic, the full two-sided global `hbridge`
follows unconditionally from a **one-sided ray bridge** on `I_plus` alone! -/
theorem hbridge_of_one_sided_ray_bridge
    (hbridge_plus : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ U₀ : ℝ, ∀ u ≥ U₀,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0) :
    ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0) := by
  intro r Q hQ_flat
  -- 1. `I_plus` vanishes on a ray, hence on all of `ℝ`
  obtain ⟨U₀, hray_plus⟩ := hbridge_plus r Q hQ_flat
  have hall_plus : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 :=
    eval_jet_eq_zero_all_of_ray analyticOnNhd_I_plus Q hray_plus
  -- 2. Conjugate polynomial `Qbar = Q.map (starRingEnd ℂ)` is flat on `I_plus`
  let Qbar : MvPolynomial (Fin (r + 1)) ℂ := MvPolynomial.map (starRingEnd ℂ) Q
  have hQbar_eq : ∀ u : ℝ, 0 < u →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Qbar =
        star (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q) := by
    intro u hu
    have hloc : I_minus =ᶠ[𝓝 u] (fun v : ℝ => star (I_plus v)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      exact I_minus_eq_star_I_plus hv
    have hjet : (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) =
        fun j : Fin (r + 1) => (starRingEnd ℂ) (iteratedDeriv (j : ℕ) I_minus u) := by
      ext j
      rw [hloc.iteratedDeriv_eq, iteratedDeriv_star_comp]
      simp
    dsimp only [Qbar]
    rw [hjet, MvPolynomial.eval_map]
    change MvPolynomial.eval₂ ((starRingEnd ℂ).comp (RingHom.id ℂ))
        ((starRingEnd ℂ) ∘ fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q =
      (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q)
    rw [MvPolynomial.hom_eval₂]
    rfl
  have hQ_minus_flat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q‖ ≤ C / u ^ N := by
    have hdiff := (eval_jet_diff_allOrders (I_plus_poly_jet_bound r)
      (fun j N => I_minus_sub_I_plus_jet_allOrders (j : ℕ) N) Q).2
    intro N
    obtain ⟨C, hC, U, hU⟩ := hdiff N
    refine ⟨C, hC, U, fun u hu => ?_⟩
    have h1 := hU u hu
    rw [hall_plus u, sub_zero] at h1
    exact h1
  have hQbar_flat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Qbar‖ ≤ C / u ^ N := by
    intro N
    obtain ⟨C, hC, U, hU⟩ := hQ_minus_flat N
    refine ⟨C, hC, max 1 U, fun u hu => ?_⟩
    have hu1 : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hu)
    rw [hQbar_eq u hu1]
    simpa [Complex.star_def] using hU u ((le_max_right _ _).trans hu)
  obtain ⟨U₁, hray_Qbar⟩ := hbridge_plus r Qbar hQbar_flat
  have hray_minus : ∀ u ≥ max 1 U₁,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0 := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hu)
    have h0 := hray_Qbar u ((le_max_right _ _).trans hu)
    rw [hQbar_eq u hu_pos] at h0
    exact star_eq_zero.mp h0
  have hall_minus : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0 :=
    eval_jet_eq_zero_all_of_ray analyticOnNhd_I_minus Q hray_minus
  exact fun u => ⟨hall_plus u, hall_minus u⟩

/-- **Sectorial Exponential-Decay Reduction of `hbridge`** (using `watson_uniqueness_rotated_sector`):
If every all-orders flat polynomial evaluation `u ↦ Q(J_r I_plus u)` admits a holomorphic extension
to a rotated sector of opening `> π` containing `[R, ∞)` (such as Codex's repaired `[-3π/4, π/3]`)
with exponential decay `‖F z‖ ≤ M * exp (-c * ‖z‖)`, then the full two-sided `hbridge` holds! -/
theorem hbridge_of_sectorial_exp_extension
    (hsector : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ (θ₁ θ₂ R M c : ℝ) (U : Set ℂ) (F : ℂ → ℂ),
        θ₁ ≤ 0 ∧ 0 ≤ θ₂ ∧ Real.pi < θ₂ - θ₁ ∧ θ₂ - θ₁ < 2 * Real.pi ∧
        0 < R ∧ 0 < M ∧ 0 < c ∧ IsOpen U ∧ rotatedClosedSector θ₁ θ₂ R ⊆ U ∧
        DifferentiableOn ℂ F U ∧
        (∀ u : ℝ, R ≤ u →
          F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q) ∧
        (∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖F z‖ ≤ M * Real.exp (-c * ‖z‖))) :
    ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0) := by
  refine hbridge_of_one_sided_ray_bridge fun r Q hflat => ?_
  obtain ⟨θ₁, θ₂, R, M, c, U, F, hθ₁, hθ₂, hw_lo, hw_hi, hR, hM, hc, hU, hsub, hFdiff, hFeq, hFdec⟩ :=
    hsector r Q hflat
  have hF0 := watson_uniqueness_rotated_sector hw_lo hw_hi hR hM hc hU hsub hFdiff hFdec
  refine ⟨R, fun u hu => ?_⟩
  rw [← hFeq u hu]
  exact hF0 (u : ℂ) (ofReal_mem_rotatedClosedSector hθ₁ hθ₂ hw_hi hR hu)

/-- **Sectorial Gevrey-1 Reduction of `hbridge`** (using `watson_uniqueness_rotated_gevrey1`):
Same as `hbridge_of_sectorial_exp_extension`, assuming Gevrey-1 factorial flatness
`‖F z‖ ≤ C * A ^ N * N! / ‖z‖ ^ N` on a rotated sector of opening `> π` containing `[R, ∞)`. -/
theorem hbridge_of_sectorial_gevrey1_extension
    (hsector : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ (θ₁ θ₂ R C A : ℝ) (U : Set ℂ) (F : ℂ → ℂ),
        θ₁ ≤ 0 ∧ 0 ≤ θ₂ ∧ Real.pi < θ₂ - θ₁ ∧ θ₂ - θ₁ < 2 * Real.pi ∧
        0 < R ∧ 0 < C ∧ 0 < A ∧ IsOpen U ∧ rotatedClosedSector θ₁ θ₂ R ⊆ U ∧
        DifferentiableOn ℂ F U ∧
        (∀ u : ℝ, R ≤ u →
          F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q) ∧
        (∀ N : ℕ, ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖F z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N)) :
    ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_minus u) Q = 0) := by
  refine hbridge_of_one_sided_ray_bridge fun r Q hflat => ?_
  obtain ⟨θ₁, θ₂, R, C, A, U, F, hθ₁, hθ₂, hw_lo, hw_hi, hR, hC, hA, hU, hsub, hFdiff, hFeq, hFgev⟩ :=
    hsector r Q hflat
  have hF0 := watson_uniqueness_rotated_gevrey1 hw_lo hw_hi hR hC hA hU hsub hFdiff hFgev
  refine ⟨R, fun u hu => ?_⟩
  rw [← hFeq u hu]
  exact hF0 (u : ℂ) (ofReal_mem_rotatedClosedSector hθ₁ hθ₂ hw_hi hR hu)

/-! ### 4. Master Export Theorems for Pak's Conjecture 2.5a (`∑ p_n q^n`) -/

/-- **MASTER EXPORT THEOREM 1 (`pak_2_5a_reduced`)**:
Directly wires our unconditional `I_plus_poly_jet_bound` (discharging `hI_bound`),
our `hasymp_of_pnt` (discharging `hasymp` from `Main.PNTAllOrders`), and our
conjugation-symmetry + real-analyticity reduction `hbridge_of_one_sided_ray_bridge`
into `PakNthPrimeStokes.pak_2_5a_of_stokes_bridge`.

Remaining hypotheses reduced from 3 (`hI_bound`, `hasymp`, `hbridge`) down to:
1. `hpnt : Main.PNTAllOrders` (the standard PNT hypothesis shared with Pak 2.5b), and
2. `hbridge_plus` (one-sided ray flatness-implies-vanishing for `I_plus` alone). -/
theorem pak_2_5a_reduced
    (hpnt : Main.PNTAllOrders)
    (hbridge_plus : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ U₀ : ℝ, ∀ u ≥ U₀,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q = 0) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series) :=
  pak_2_5a_of_stokes_bridge I_plus_poly_jet_bound (hasymp_of_pnt hpnt)
    (hbridge_of_one_sided_ray_bridge hbridge_plus)

/-- **MASTER EXPORT THEOREM 2 (`pak_2_5a_of_pnt_and_sectorial_exp_bridge`)**:
Pak's Conjecture 2.5a (`∑ p_n q^n` is differentially transcendental over `ℂ(q)`) assuming only
`Main.PNTAllOrders` and Codex's bounded-angle sectorial exponential-decay extension on any
sector of opening `> π` containing a positive real ray (such as `[-3π/4, π/3]`). -/
theorem pak_2_5a_of_pnt_and_sectorial_exp_bridge
    (hpnt : Main.PNTAllOrders)
    (hsector : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ (θ₁ θ₂ R M c : ℝ) (U : Set ℂ) (F : ℂ → ℂ),
        θ₁ ≤ 0 ∧ 0 ≤ θ₂ ∧ Real.pi < θ₂ - θ₁ ∧ θ₂ - θ₁ < 2 * Real.pi ∧
        0 < R ∧ 0 < M ∧ 0 < c ∧ IsOpen U ∧ rotatedClosedSector θ₁ θ₂ R ⊆ U ∧
        DifferentiableOn ℂ F U ∧
        (∀ u : ℝ, R ≤ u →
          F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q) ∧
        (∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖F z‖ ≤ M * Real.exp (-c * ‖z‖))) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series) :=
  pak_2_5a_of_stokes_bridge I_plus_poly_jet_bound (hasymp_of_pnt hpnt)
    (hbridge_of_sectorial_exp_extension hsector)

/-- **MASTER EXPORT THEOREM 3 (`pak_2_5a_of_pnt_and_sectorial_gevrey1_bridge`)**:
Pak's Conjecture 2.5a assuming only `Main.PNTAllOrders` and Gevrey-1 factorial flatness on a
rotated sector of opening `> π` containing a positive real ray. -/
theorem pak_2_5a_of_pnt_and_sectorial_gevrey1_bridge
    (hpnt : Main.PNTAllOrders)
    (hsector : ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ (θ₁ θ₂ R C A : ℝ) (U : Set ℂ) (F : ℂ → ℂ),
        θ₁ ≤ 0 ∧ 0 ≤ θ₂ ∧ Real.pi < θ₂ - θ₁ ∧ θ₂ - θ₁ < 2 * Real.pi ∧
        0 < R ∧ 0 < C ∧ 0 < A ∧ IsOpen U ∧ rotatedClosedSector θ₁ θ₂ R ⊆ U ∧
        DifferentiableOn ℂ F U ∧
        (∀ u : ℝ, R ≤ u →
          F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q) ∧
        (∀ N : ℕ, ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖F z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N)) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series) :=
  pak_2_5a_of_stokes_bridge I_plus_poly_jet_bound (hasymp_of_pnt hpnt)
    (hbridge_of_sectorial_gevrey1_extension hsector)

end
end PakPrimes.PakNthPrimeClosure
