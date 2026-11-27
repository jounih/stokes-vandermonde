module

public import PakStokes.AllD.SquaresPartitionAnalytic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import all PakStokes.AllD.SquaresPartitionAnalytic

/-! # Wave 11 (Module 2): 100% Unconditional Analytic Identity for the Physical 3D Ideal Bose–Einstein Condensate

Proves 100% unconditionally from Mathlib — with ZERO Bessel functions, ZERO contour integrals,
and ZERO Mellin transforms — the exact 1-term pure elementary identity for the internal energy
`F_BEC^{(3)}(e^{-1/X²}) = ∑_{n ∈ ℤ³ \ {0}} |n|² / (exp(|n|² / X²) - 1)` on `X > 0`:
```
∑'_{N : ℕ+} r_3(N) * N / (exp(N / X²) - 1)
  = bec3DConst * X^5 - X^2
    + X^4 * ∑'_{d : ℕ+} ∑'_{j : ℕ+} (r_3(d) * j / √d) *
        ((-2 π² I) * exp(-sqRay0 * √d * √j * X)
       + ( 2 π² I) * exp(-sqRay1 * √d * √j * X))
```
where `r_3(N) = #{(a, b, c) ∈ ℤ³ : a² + b² + c² = N}` and
`bec3DConst = (3 / 2) π^(3/2) ∑'_{k : ℕ+} k^(-5/2)`.

Proof architecture (100% elementary from Mathlib):
1. Exact elementary `K_{1/2}` Gaussian integral
   `∫_{0}^{∞} exp(-a² u² - w² / u²) du = (√π / (2 a)) exp(-2 a w)` for `a > 0`, `Re(w) > 0`,
   `Re(w²) ≥ 0` (via real ODE `F'(b) = -2 a F(b)` + Identity Theorem on the convex wedge
   `{|Im w| < Re w}` + Dominated Convergence to the boundary `Re(w²) = 0`).
2. 1D Poisson summation in `k` for the exact total derivative
   `h_p(x) = -d/dx (x^{-3/2} exp(-p / x)) · 1_{x > 0}` via Mathlib's `Real.fourier_deriv`.
3. Smooth radial kernel `φ(u) = (∫_0^1 exp(s u) ds)⁻¹` with all derivatives decaying as
   `O(exp(-u / 2))`, exact 3D Gaussian Fourier transform via 1D `fourier_gaussian_pi`, and
   3-step iterated 1D Mathlib Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`). -/

public section
namespace CubicTheta.AllD
open Complex Filter Set MeasureTheory
open scoped Topology FourierTransform
noncomputable section

/-- Leading bulk constant `(3 / 2) π^(3/2) ζ(5/2)` of the 3D ideal Bose–Einstein condensate
internal energy `F_BEC^{(3)}(e^{-1/X²})`. -/
def bec3DConst : ℂ :=
  ((3 / 2 * Real.pi ^ (3 / 2 : ℝ) * (∑' k : ℕ+, (k.val : ℝ) ^ (-(5 / 2 : ℝ))) : ℝ) : ℂ)

/-- Number of integer lattice vectors in `ℤ³` of squared Euclidean norm `N`:
`r_3(N) = #{(a, b, c) ∈ ℤ³ : a² + b² + c² = N}`. -/
def r3Count (N : ℕ) : ℕ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
    Finset.Icc (-(N : ℤ)) (N : ℤ))).filter
      (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (N : ℤ))).card

/-! ### 1. Elementary `K_{1/2}` Gaussian Integral `∫_0^∞ exp(-a² u² - w² / u²) du` -/

private lemma inv_sq_mul_exp_neg_div_sq_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    u ^ (-(2 : ℤ)) * Real.exp (-c / u ^ 2) ≤ c⁻¹ := by
  have h1 : c / u ^ 2 ≤ Real.exp (c / u ^ 2) := by
    linarith [Real.add_one_le_exp (c / u ^ 2)]
  have hpos : 0 < c / u ^ 2 := by positivity
  have hinv : Real.exp (-c / u ^ 2) ≤ (c / u ^ 2)⁻¹ := by
    rw [neg_div, Real.exp_neg]
    exact inv_anti₀ hpos h1
  calc u ^ (-(2 : ℤ)) * Real.exp (-c / u ^ 2)
      ≤ (u ^ 2)⁻¹ * (c / u ^ 2)⁻¹ := by
        rw [zpow_neg, zpow_two, ← sq]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = c⁻¹ := by field_simp [hc.ne', hu.ne']

private lemma integrableOn_rexp_neg_mul_sq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-c * u ^ 2)) (Ioi 0) :=
  (integrable_exp_neg_mul_sq hc).integrableOn

/-- Real case (`a > 0, b > 0`): `∫_{u > 0} exp(-a² u² - b² / u²) du = (√π / (2 a)) exp(-2 a b)`. -/
private theorem integral_rexp_neg_sq_sub_inv_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-a ^ 2 * u ^ 2 - b ^ 2 / u ^ 2)) =
      (Real.sqrt Real.pi / (2 * a)) * Real.exp (-2 * a * b) := by
  let F (x : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-a ^ 2 * u ^ 2 - x ^ 2 / u ^ 2)
  have hF_int (x : ℝ) : IntegrableOn (fun u : ℝ ↦ Real.exp (-a ^ 2 * u ^ 2 - x ^ 2 / u ^ 2)) (Ioi 0) := by
    refine (integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)).mono' ?_ ?_
    · have hc : ContinuousOn (fun u : ℝ ↦ Real.exp (-a ^ 2 * u ^ 2 - x ^ 2 / u ^ 2)) (Ioi 0) := by
        intro u hu
        have hu0 : u ^ 2 ≠ 0 := pow_ne_zero 2 (mem_Ioi.mp hu).ne'
        exact (((continuousAt_const.mul (continuousAt_id.pow 2)).sub
          (continuousAt_const.div (continuousAt_id.pow 2) hu0)).rexp).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [div_nonneg (sq_nonneg x) (sq_nonneg u)])
  have hF_deriv : ∀ x > 0, HasDerivAt F (-2 * a * F x) x := by
    intro x hx
    let s : Set ℝ := Ioo (x / 2) (2 * x)
    have hs : s ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
    let f (y u : ℝ) : ℝ := Real.exp (-a ^ 2 * u ^ 2 - y ^ 2 / u ^ 2)
    let f' (y u : ℝ) : ℝ := (-2 * y / u ^ 2) * Real.exp (-a ^ 2 * u ^ 2 - y ^ 2 / u ^ 2)
    let bound (u : ℝ) : ℝ := (16 / x) * Real.exp (-a ^ 2 * u ^ 2)
    have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (f y) (volume.restrict (Ioi 0)) :=
      Eventually.of_forall fun y ↦ (hF_int y).aestronglyMeasurable
    have hf'_meas : AEStronglyMeasurable (f' x) (volume.restrict (Ioi 0)) := by
      have hc : ContinuousOn (f' x) (Ioi 0) := by
        intro u hu
        have hu0 : u ≠ 0 := (mem_Ioi.mp hu).ne'
        exact (((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hu0)).mul
          ((continuousAt_const.mul (continuousAt_id.pow 2)).sub
            (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hu0))).rexp)).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    have hbound : ∀ᵐ u ∂volume.restrict (Ioi 0), ∀ y ∈ s, ‖f' y u‖ ≤ bound u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu y hy
      change 0 < u at hu
      have hy1 : x / 2 < y := hy.1
      have hy2 : y < 2 * x := hy.2
      have hy0 : 0 < y := lt_trans (half_pos hx) hy1
      dsimp only [f', bound]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_div,
          show |-2 * y| = 2 * y by rw [abs_mul, abs_neg, abs_of_pos zero_lt_two, abs_of_pos hy0],
          abs_of_pos (sq_pos_of_pos hu)]
      have hsplit : Real.exp (-a ^ 2 * u ^ 2 - y ^ 2 / u ^ 2) =
          Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-(y ^ 2) / u ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit]
      have hle_exp : Real.exp (-(y ^ 2) / u ^ 2) ≤ Real.exp (-(x ^ 2 / 4) / u ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hsq : x ^ 2 / 4 ≤ y ^ 2 := by nlinarith
        exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg u)
      have hinv := inv_sq_mul_exp_neg_div_sq_le (c := x ^ 2 / 4) (by positivity) hu
      rw [zpow_neg, zpow_two, ← sq] at hinv
      calc (2 * y / u ^ 2) * (Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-(y ^ 2) / u ^ 2))
          ≤ (4 * x / u ^ 2) * (Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-(x ^ 2 / 4) / u ^ 2)) := by
            have h1 : 2 * y / u ^ 2 ≤ 4 * x / u ^ 2 :=
              div_le_div_of_nonneg_right (by linarith) (sq_nonneg u)
            gcongr
        _ = 4 * x * ((u ^ 2)⁻¹ * Real.exp (-(x ^ 2 / 4) / u ^ 2)) * Real.exp (-a ^ 2 * u ^ 2) := by ring
        _ ≤ 4 * x * (x ^ 2 / 4)⁻¹ * Real.exp (-a ^ 2 * u ^ 2) := by gcongr
        _ = (16 / x) * Real.exp (-a ^ 2 * u ^ 2) := by field_simp [hx.ne']; ring
    have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0), ∀ y ∈ s, HasDerivAt (f · u) (f' y u) y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu y _
      have h1 : HasDerivAt (fun z : ℝ ↦ -a ^ 2 * u ^ 2 - z ^ 2 / u ^ 2) (-(2 * y / u ^ 2)) y := by
        have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
          simpa using hasDerivAt_pow 2 y
        exact (hsq.div_const (u ^ 2)).const_sub (-a ^ 2 * u ^ 2)
      convert h1.exp using 1; dsimp [f']; ring
    have hhd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas (hF_int x) hf'_meas hbound
      ((integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)).const_mul (16 / x)) hdiff).2
    -- Now evaluate `∫_{u > 0} (-2 x / u²) exp(-a² u² - x² / u²) du = -2 a F(x)`!
    have heval : (∫ u in Ioi (0 : ℝ), f' x u) = -2 * a * F x := by
      have hconst : (∫ u in Ioi (0 : ℝ), f' x u) =
          (-2 * x) * ∫ u in Ioi (0 : ℝ), (u ^ (-(2 : ℝ))) * Real.exp (-a ^ 2 * u ^ 2 - x ^ 2 / u ^ 2) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi; intro u hu
        dsimp only [f']
        have hpow : u ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := by
          rw [Real.rpow_neg (mem_Ioi.mp hu).le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hpow]; ring
      rw [hconst]
      -- Substitution `u = y⁻¹` via `integral_comp_rpow_Ioi` with `p = -1`!
      have hinv := integral_comp_rpow_Ioi
        (fun y : ℝ ↦ Real.exp (-x ^ 2 * y ^ 2 - a ^ 2 / y ^ 2)) (p := (-1 : ℝ)) (by norm_num)
      have hinv_eq : (∫ u in Ioi (0 : ℝ), (u ^ (-(2 : ℝ))) * Real.exp (-a ^ 2 * u ^ 2 - x ^ 2 / u ^ 2)) =
          ∫ y in Ioi (0 : ℝ), Real.exp (-x ^ 2 * y ^ 2 - a ^ 2 / y ^ 2) := by
        rw [← hinv]
        apply setIntegral_congr_fun measurableSet_Ioi; intro u hu
        have hu0 : 0 < u := mem_Ioi.mp hu
        simp only [abs_neg, abs_one, one_mul, smul_eq_mul,
          show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg_one]
        congr 2; field_simp [hu0.ne']; ring
      rw [hinv_eq]
      -- Scaling `y = (a / x) * v` on `Ioi 0`!
      have hsc := MeasureTheory.integral_comp_mul_left_Ioi
        (fun y : ℝ ↦ Real.exp (-x ^ 2 * y ^ 2 - a ^ 2 / y ^ 2)) (0 : ℝ) (show 0 < a / x by positivity)
      rw [mul_zero] at hsc
      have hsc_fun : (∫ v in Ioi (0 : ℝ), Real.exp (-x ^ 2 * ((a / x) * v) ^ 2 - a ^ 2 / ((a / x) * v) ^ 2)) =
          F x := by
        apply setIntegral_congr_fun measurableSet_Ioi; intro v hv
        have hv0 : (v : ℝ) ≠ 0 := (mem_Ioi.mp hv).ne'
        field_simp [ha.ne', hx.ne', hv0]
      rw [hsc_fun, smul_eq_mul] at hsc
      have hval_y : (∫ y in Ioi (0 : ℝ), Real.exp (-x ^ 2 * y ^ 2 - a ^ 2 / y ^ 2)) = (a / x) * F x := by
        have h1 := congrArg ((a / x) * ·) hsc
        field_simp [ha.ne', hx.ne'] at h1 ⊢
        linarith
      rw [hval_y]; field_simp [hx.ne']
    rwa [heval] at hhd
  -- Therefore `x ↦ exp(2 a x) * F x` has derivative 0 on `Ioi 0`, hence is constant!
  let G (x : ℝ) : ℝ := Real.exp (2 * a * x) * F x
  have hG_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt G 0 x := fun x hx ↦ by
    have h1 : HasDerivAt (fun y : ℝ ↦ Real.exp (2 * a * y)) (2 * a * Real.exp (2 * a * x)) x := by
      have hl : HasDerivAt (fun y : ℝ ↦ 2 * a * y) (2 * a) x := by simpa using (hasDerivAt_id x).const_mul (2 * a)
      simpa [mul_comm] using hl.exp
    convert h1.mul (hF_deriv x hx) using 1; ring
  have hG_const : ∀ x ∈ Ioi (0 : ℝ), G x = G b := fun x hx ↦
    (convex_Ioi (0 : ℝ)).is_const_of_fderivWithin_eq_zero
      (fun y hy ↦ (hG_deriv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ by
        rw [fderivWithin_of_isOpen isOpen_Ioi hy, (hG_deriv y hy).hasFDerivAt.fderiv]; simp)
      hx hb
  -- Limit as `n → ∞` along `x_n = 1 / (n + 1) → 0+` gives `G b = √π / (2 a)`!
  have hlim_F : Tendsto (fun n : ℕ ↦ F (1 / ((n : ℝ) + 1))) atTop (𝓝 (Real.sqrt Real.pi / (2 * a))) := by
    have hgauss : (∫ u in Ioi (0 : ℝ), Real.exp (-a ^ 2 * u ^ 2)) = Real.sqrt Real.pi / (2 * a) := by
      have h := integral_gaussian_Ioi (a ^ 2)
      rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq ha.le, div_div, mul_comm a 2] at h
      simpa only [neg_mul] using h
    rw [← hgauss]
    refine tendsto_integral_of_dominated_convergence (fun u : ℝ ↦ Real.exp (-a ^ 2 * u ^ 2))
      (fun n ↦ (hF_int _).aestronglyMeasurable) (integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha))
      (fun n ↦ ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [div_nonneg (sq_nonneg (1 / ((n : ℝ) + 1))) (sq_nonneg u)])
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have harg : Tendsto (fun n : ℕ ↦ -a ^ 2 * u ^ 2 - (1 / ((n : ℝ) + 1)) ^ 2 / u ^ 2) atTop
          (𝓝 (-a ^ 2 * u ^ 2 - 0 ^ 2 / u ^ 2)) :=
        tendsto_const_nhds.sub ((h0.pow 2).div_const (u ^ 2))
      simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp harg
  have hlim_G : Tendsto (fun n : ℕ ↦ G (1 / ((n : ℝ) + 1))) atTop (𝓝 (Real.sqrt Real.pi / (2 * a))) := by
    have he : Tendsto (fun n : ℕ ↦ Real.exp (2 * a * (1 / ((n : ℝ) + 1)))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * a))
    simpa only [one_mul] using he.mul hlim_F
  have hconst_seq : (fun n : ℕ ↦ G (1 / ((n : ℝ) + 1))) = fun _ ↦ G b := by
    funext n; exact hG_const _ (mem_Ioi.mpr (by positivity))
  rw [hconst_seq] at hlim_G
  have hGb : G b = Real.sqrt Real.pi / (2 * a) := tendsto_nhds_unique tendsto_const_nhds hlim_G
  have hmul := congrArg (Real.exp (-2 * a * b) * ·) hGb
  dsimp only [G] at hmul
  rw [← mul_assoc, ← Real.exp_add, show -2 * a * b + 2 * a * b = 0 by ring,
      Real.exp_zero, one_mul, mul_comm (Real.exp _)] at hmul
  exact hmul

/-- **Elementary Complex `K_{1/2}` Gaussian Integral**:
For EVERY `a > 0` and EVERY `w ∈ ℂ` with `0 < w.re` and `0 ≤ (w²).re`:
`∫_{u > 0} exp(-a² u² - w² / u²) du = (√π / (2 a)) exp(-2 a w)`!
(Proved via real ODE + Identity Theorem on the convex open wedge `{|Im w| < Re w}` + DCT!) -/
private theorem integral_cexp_neg_sq_sub_inv_sq {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw_re : 0 < w.re) (hw2_re : 0 ≤ (w ^ 2).re) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - w ^ 2 / ((u ^ 2 : ℝ) : ℂ))) =
      (((Real.sqrt Real.pi / (2 * a) : ℝ) : ℂ)) * Complex.exp (-2 * (a : ℂ) * w) := by
  let Ω : Set ℂ := {z : ℂ | -z.re < z.im ∧ z.im < z.re}
  have hΩ_open : IsOpen Ω :=
    (isOpen_lt Complex.continuous_re.neg Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im Complex.continuous_re)
  have hΩ_conv : Convex ℝ Ω := by
    intro x hx y hy s t hs ht hst
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
      have h1 := mul_le_mul_of_nonneg_left hx.1.le hs
      have h2 := mul_le_mul_of_nonneg_left hy.1.le ht
      rcases hs.eq_or_lt with rfl | hs'
      · have : t = 1 := by linarith
        subst this; linarith [hy.1]
      · have h1' := mul_lt_mul_of_pos_left hx.1 hs'
        linarith
    · simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
      have h2 := mul_le_mul_of_nonneg_left hy.2.le ht
      rcases hs.eq_or_lt with rfl | hs'
      · have : t = 1 := by linarith
        subst this; linarith [hy.2]
      · have h1' := mul_lt_mul_of_pos_left hx.2 hs'
        linarith
  have hΩ_re (z : ℂ) (hz : z ∈ Ω) : 0 < z.re := by linarith [hz.1, hz.2]
  have hΩ_sq_re (z : ℂ) (hz : z ∈ Ω) : 0 < (z ^ 2).re := by
    have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [sq, Complex.mul_re]; ring
    rw [hre]; nlinarith [hz.1, hz.2]
  let H1 (z : ℂ) : ℂ :=
    ∫ u in Ioi (0 : ℝ), Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ))
  let H2 (z : ℂ) : ℂ := (((Real.sqrt Real.pi / (2 * a) : ℝ) : ℂ)) * Complex.exp (-2 * (a : ℂ) * z)
  have hH1_int (z : ℂ) (hz : 0 ≤ (z ^ 2).re) :
      IntegrableOn (fun u : ℝ ↦ Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ)))
        (Ioi 0) := by
    refine (integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)).mono' ?_ ?_
    · have hc : ContinuousOn (fun u : ℝ ↦
          Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ))) (Ioi 0) := by
        intro u hu
        have hu0 : ((u ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (mem_Ioi.mp hu).ne')
        exact ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_id.pow 2))).neg.sub
          (continuousAt_const.div (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.pow 2)) hu0)).cexp.continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Complex.norm_exp]
      have hre : (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ)).re =
          -a ^ 2 * u ^ 2 - (z ^ 2).re / u ^ 2 := by
        rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofReal_re]; ring
      rw [hre]
      exact Real.exp_le_exp.mpr (by linarith [div_nonneg hz (sq_nonneg u)])
  have hH1_diff : DifferentiableOn ℂ H1 Ω := by
    intro z₀ hz₀
    have hc₀ : 0 < (z₀ ^ 2).re := hΩ_sq_re z₀ hz₀
    have hnhds1 : {z : ℂ | (z₀ ^ 2).re / 2 < (z ^ 2).re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.pow 2))).mem_nhds
        (show (z₀ ^ 2).re / 2 < (z₀ ^ 2).re by linarith)
    have hnhds2 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
    let s : Set ℂ := {z : ℂ | (z₀ ^ 2).re / 2 < (z ^ 2).re} ∩ Metric.ball z₀ 1
    have hs : s ∈ 𝓝 z₀ := Filter.inter_mem hnhds1 hnhds2
    let f (z : ℂ) (u : ℝ) : ℂ := Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ))
    let f' (z : ℂ) (u : ℝ) : ℂ :=
      (-2 * z / ((u ^ 2 : ℝ) : ℂ)) * Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ))
    let c0 : ℝ := (z₀ ^ 2).re / 2
    have hc0 : 0 < c0 := half_pos hc₀
    let B : ℝ := 2 * (‖z₀‖ + 1) / c0
    let bound (u : ℝ) : ℝ := B * Real.exp (-a ^ 2 * u ^ 2)
    have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (f z) (volume.restrict (Ioi 0)) :=
      Filter.Eventually.mono hnhds1 fun z hz ↦ (hH1_int z (by change c0 < (z ^ 2).re at hz; linarith)).aestronglyMeasurable
    have hf'_meas : AEStronglyMeasurable (f' z₀) (volume.restrict (Ioi 0)) := by
      have hc : ContinuousOn (f' z₀) (Ioi 0) := by
        intro u hu
        have hu0 : ((u ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (mem_Ioi.mp hu).ne')
        exact ((continuousAt_const.div (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.pow 2)) hu0).mul
          ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_id.pow 2))).neg.sub
            (continuousAt_const.div (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.pow 2)) hu0)).cexp).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    have hbound : ∀ᵐ u ∂volume.restrict (Ioi 0), ∀ z ∈ s, ‖f' z u‖ ≤ bound u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
      change 0 < u at hu
      have hz_re : c0 < (z ^ 2).re := hz.1
      have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have h1 : dist z z₀ < 1 := Metric.mem_ball.mp hz.2
        have h2 : ‖z‖ - ‖z₀‖ ≤ ‖z - z₀‖ := norm_sub_norm_le z z₀
        rw [dist_eq_norm] at h1; linarith
      dsimp only [f', bound]
      rw [norm_mul, norm_div, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hu), Complex.norm_exp]
      have hre : (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - z ^ 2 / ((u ^ 2 : ℝ) : ℂ)).re =
          -a ^ 2 * u ^ 2 - (z ^ 2).re / u ^ 2 := by
        rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofReal_re]; ring
      rw [hre]
      have hsplit : Real.exp (-a ^ 2 * u ^ 2 - (z ^ 2).re / u ^ 2) =
          Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-(z ^ 2).re / u ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit]
      have hle_exp : Real.exp (-(z ^ 2).re / u ^ 2) ≤ Real.exp (-c0 / u ^ 2) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) (sq_nonneg u))
      have hinv := inv_sq_mul_exp_neg_div_sq_le hc0 hu
      rw [zpow_neg, zpow_two, ← sq] at hinv
      calc (2 * ‖z‖ / u ^ 2) * (Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-(z ^ 2).re / u ^ 2))
          ≤ (2 * (‖z₀‖ + 1) / u ^ 2) * (Real.exp (-a ^ 2 * u ^ 2) * Real.exp (-c0 / u ^ 2)) := by
            gcongr
        _ = (2 * (‖z₀‖ + 1)) * ((u ^ 2)⁻¹ * Real.exp (-c0 / u ^ 2)) * Real.exp (-a ^ 2 * u ^ 2) := by ring
        _ ≤ (2 * (‖z₀‖ + 1)) * c0⁻¹ * Real.exp (-a ^ 2 * u ^ 2) := by gcongr
        _ = B * Real.exp (-a ^ 2 * u ^ 2) := by dsimp [B]; ring
    have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0), ∀ z ∈ s, HasDerivAt (f · u) (f' z u) z := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z _
      have h1 : HasDerivAt (fun ζ : ℂ ↦ -((a ^ 2 * u ^ 2 : ℝ) : ℂ) - ζ ^ 2 / ((u ^ 2 : ℝ) : ℂ))
          (-(2 * z / ((u ^ 2 : ℝ) : ℂ))) z := by
        have hsq : HasDerivAt (fun ζ : ℂ ↦ ζ ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
        exact (hsq.div_const ((u ^ 2 : ℝ) : ℂ)).const_sub (-((a ^ 2 * u ^ 2 : ℝ) : ℂ))
      convert h1.cexp using 1; dsimp [f']; ring
    have hhd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas (hH1_int z₀ hc₀.le)
      hf'_meas hbound ((integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)).const_mul B) hdiff).2
    exact hhd.differentiableAt.differentiableWithinAt
  have hH2_diff : DifferentiableOn ℂ H2 Ω := by
    intro z _; exact (((differentiableAt_id.const_mul (-2 * (a : ℂ))).cexp).const_mul _).differentiableWithinAt
  have hH1_an : AnalyticOnNhd ℂ H1 Ω := hH1_diff.analyticOnNhd hΩ_open
  have hH2_an : AnalyticOnNhd ℂ H2 Ω := hH2_diff.analyticOnNhd hΩ_open
  have hreal_eq : ∀ b : ℝ, 0 < b → H1 (b : ℂ) = H2 (b : ℂ) := fun b hb ↦ by
    dsimp only [H1, H2]
    have hfun : (fun u : ℝ ↦ Complex.exp (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - (b : ℂ) ^ 2 / ((u ^ 2 : ℝ) : ℂ))) =
        fun u : ℝ ↦ Complex.ofRealCLM (Real.exp (-a ^ 2 * u ^ 2 - b ^ 2 / u ^ 2)) := by
      funext u; change Complex.exp _ = ((Real.exp _ : ℝ) : ℂ); rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [hfun, Complex.ofRealCLM.integral_comp_comm
      ((integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)).mono'
        ((by
          intro u hu
          have hu0 : u ^ 2 ≠ 0 := pow_ne_zero 2 (mem_Ioi.mp hu).ne'
          exact (((continuousAt_const.mul (continuousAt_id.pow 2)).sub
            (continuousAt_const.div (continuousAt_id.pow 2) hu0)).rexp).continuousWithinAt :
            ContinuousOn (fun u : ℝ ↦ Real.exp (-a ^ 2 * u ^ 2 - b ^ 2 / u ^ 2)) (Ioi 0)).aestronglyMeasurable
          measurableSet_Ioi)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (by linarith [div_nonneg (sq_nonneg b) (sq_nonneg u)]))),
      integral_rexp_neg_sq_sub_inv_sq ha hb]
    change (((Real.sqrt Real.pi / (2 * a) * Real.exp (-2 * a * b) : ℝ) : ℂ)) = _
    push_cast; ring
  have h1_mem : (1 : ℂ) ∈ Ω := by simp [Ω]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), H1 z = H2 z := by
    rw [frequently_nhdsWithin_iff, Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    let b : ℝ := 1 + ε / 2
    refine ⟨(b : ℂ), ?_, hreal_eq b (by dsimp [b]; linarith), ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, show (b : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) by dsimp [b]; push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    · change (b : ℂ) ≠ 1
      intro h; have hre := congrArg Complex.re h; simp [b] at hre; linarith
  have hEqOn : EqOn H1 H2 Ω :=
    hH1_an.eqOn_of_preconnected_of_frequently_eq hH2_an hΩ_conv.isPreconnected h1_mem hfreq
  -- Boundary limit along `w_n = w + 1 / (n + 1) ∈ Ω`!
  let wn (n : ℕ) : ℂ := w + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hwn_mem (n : ℕ) : wn n ∈ Ω := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hre : (wn n).re = w.re + 1 / ((n : ℝ) + 1) := by
      dsimp only [wn]; rw [Complex.add_re, Complex.ofReal_re]
    have him : (wn n).im = w.im := by
      dsimp only [wn]; rw [Complex.add_im, Complex.ofReal_im, add_zero]
    have hsq : w.im ^ 2 ≤ w.re ^ 2 := by
      have h1 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by rw [sq, Complex.mul_re]; ring
      linarith
    have habs : |w.im| ≤ w.re := by
      have := sq_le_sq.mp hsq
      rwa [abs_of_pos hw_re] at this
    refine ⟨?_, ?_⟩
    · rw [hre, him]; linarith [(abs_le.mp habs).1]
    · rw [hre, him]; linarith [(abs_le.mp habs).2]
  have hwn_tendsto : Tendsto wn atTop (𝓝 w) := by
    have h0 : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using tendsto_const_nhds.add h0
  have hlim1 : Tendsto (fun n : ℕ ↦ H1 (wn n)) atTop (𝓝 (H1 w)) := by
    refine tendsto_integral_of_dominated_convergence (fun u : ℝ ↦ Real.exp (-a ^ 2 * u ^ 2))
      (fun n ↦ (hH1_int (wn n) (hΩ_sq_re _ (hwn_mem n)).le).aestronglyMeasurable)
      (integrableOn_rexp_neg_mul_sq_Ioi (sq_pos_of_pos ha)) (fun n ↦ ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      rw [Complex.norm_exp]
      have hre : (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - (wn n) ^ 2 / ((u ^ 2 : ℝ) : ℂ)).re =
          -a ^ 2 * u ^ 2 - ((wn n) ^ 2).re / u ^ 2 := by
        rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofReal_re]; ring
      rw [hre]
      exact Real.exp_le_exp.mpr (by linarith [div_nonneg (hΩ_sq_re _ (hwn_mem n)).le (sq_nonneg u)])
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      have harg : Tendsto (fun n : ℕ ↦ -((a ^ 2 * u ^ 2 : ℝ) : ℂ) - (wn n) ^ 2 / ((u ^ 2 : ℝ) : ℂ))
          atTop (𝓝 (-((a ^ 2 * u ^ 2 : ℝ) : ℂ) - w ^ 2 / ((u ^ 2 : ℝ) : ℂ))) :=
        tendsto_const_nhds.sub ((hwn_tendsto.pow 2).div_const _)
      exact Complex.continuous_exp.continuousAt.tendsto.comp harg
  have hlim2 : Tendsto (fun n : ℕ ↦ H2 (wn n)) atTop (𝓝 (H2 w)) :=
    ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul _).continuousAt.tendsto.comp
      hwn_tendsto
  have hseq_eq : (fun n : ℕ ↦ H1 (wn n)) = fun n ↦ H2 (wn n) := funext fun n ↦ hEqOn (hwn_mem n)
  rw [hseq_eq] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

/-- Substitution `x = u⁻²`: `∫_{x > 0} x^{-3/2} exp(-p/x - w² x) dx = √(π/p) exp(-2 √p w)`. -/
private theorem integral_rpow_neg_three_halves_cexp {p : ℝ} (hp : 0 < p) {w : ℂ}
    (hw_re : 0 < w.re) (hw2_re : 0 ≤ (w ^ 2).re) :
    (∫ x in Ioi (0 : ℝ), ((x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((p : ℂ) / (x : ℂ)) - w ^ 2 * (x : ℂ))) =
      (((Real.sqrt Real.pi / Real.sqrt p : ℝ) : ℂ)) * Complex.exp (-2 * (Real.sqrt p : ℂ) * w) := by
  have hsub := integral_comp_rpow_Ioi
    (fun x : ℝ ↦ ((x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((p : ℂ) / (x : ℂ)) - w ^ 2 * (x : ℂ)))
    (p := (-2 : ℝ)) (by norm_num)
  rw [← hsub]
  have ha : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hcongr : (∫ u in Ioi (0 : ℝ), (|(-2 : ℝ)| * u ^ ((-2 : ℝ) - 1)) •
      (((u ^ (-2 : ℝ)) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((p : ℂ) / ((u ^ (-2 : ℝ) : ℝ) : ℂ)) - w ^ 2 * ((u ^ (-2 : ℝ) : ℝ) : ℂ))) =
      (2 : ℂ) * ∫ u in Ioi (0 : ℝ),
        Complex.exp (-(((Real.sqrt p) ^ 2 * u ^ 2 : ℝ) : ℂ) - w ^ 2 / ((u ^ 2 : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi; intro u hu
    have hu0 : 0 < u := mem_Ioi.mp hu
    have hpow1 : (u ^ (-2 : ℝ)) ^ (-(3 / 2 : ℝ)) = u ^ (3 : ℝ) := by
      rw [← Real.rpow_mul hu0.le]; norm_num
    have hpow2 : u ^ ((-2 : ℝ) - 1) * u ^ (3 : ℝ) = 1 := by
      rw [← Real.rpow_add hu0]; norm_num
    have hpow3 : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
      rw [Real.rpow_neg hu0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    dsimp only
    rw [Complex.real_smul, abs_neg, abs_of_pos zero_lt_two, hpow1, hpow3, Real.sq_sqrt hp.le]
    push_cast
    have hpref : (2 : ℂ) * ((u ^ ((-2 : ℝ) - 1) : ℝ) : ℂ) * ((u ^ (3 : ℝ) : ℝ) : ℂ) = 2 := by
      rw [mul_assoc, ← Complex.ofReal_mul, hpow2, Complex.ofReal_one, mul_one]
    have hexp : -((p : ℂ) / ((u : ℂ) ^ 2)⁻¹) - w ^ 2 * ((u : ℂ) ^ 2)⁻¹ =
        -((p : ℂ) * (u : ℂ) ^ 2) - w ^ 2 / (u : ℂ) ^ 2 := by
      rw [div_inv_eq_mul, div_eq_mul_inv]
    rw [hpref, hexp]
  have hgoal : (∫ u in Ioi (0 : ℝ), (|(-2 : ℝ)| * u ^ ((-2 : ℝ) - 1)) •
      ((((u ^ (-2 : ℝ)) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((p : ℂ) / ((u ^ (-2 : ℝ) : ℝ) : ℂ)) - w ^ 2 * ((u ^ (-2 : ℝ) : ℝ) : ℂ)))) =
      (2 : ℂ) * ∫ u in Ioi (0 : ℝ),
        Complex.exp (-(((Real.sqrt p) ^ 2 * u ^ 2 : ℝ) : ℂ) - w ^ 2 / ((u ^ 2 : ℝ) : ℂ)) := by
    simpa only [smul_mul_assoc] using hcongr
  rw [hgoal, integral_cexp_neg_sq_sub_inv_sq ha hw_re hw2_re]
  push_cast; ring

/-! ### 2. 1D Poisson Summation in `k` for `h_p(x) = -d/dx (x^{-3/2} exp(-p/x)) · 1_{x > 0}` -/

private def becH (p : ℝ) (x : ℝ) : ℂ :=
  if 0 < x then -(((x ^ (-(3 / 2 : ℝ)) * Real.exp (-p / x) : ℝ) : ℂ)) else 0

private def bech (p : ℝ) (x : ℝ) : ℂ :=
  if 0 < x then
    ((((3 / 2 * x ^ (-(5 / 2 : ℝ)) - p * x ^ (-(7 / 2 : ℝ))) * Real.exp (-p / x) : ℝ) : ℂ))
  else 0

private lemma rpow_neg_mul_exp_neg_div_le {p x : ℝ} (hp : 0 < p) (hx : 0 < x) (r : ℝ)
    (n : ℕ) (_hn : r ≤ n) :
    x ^ (-r) * Real.exp (-p / x) ≤ ((n.factorial : ℝ) / p ^ n) * x ^ ((n : ℝ) - r) := by
  have hu : 0 ≤ p / x := by positivity
  have hexp : (p / x) ^ n / (n.factorial : ℝ) ≤ Real.exp (p / x) :=
    Real.pow_div_factorial_le_exp (p / x) hu n
  have hpos : 0 < (p / x) ^ n / (n.factorial : ℝ) := by positivity
  have hinv : Real.exp (-p / x) ≤ (n.factorial : ℝ) / (p / x) ^ n := by
    rw [neg_div, Real.exp_neg]
    exact (inv_anti₀ hpos hexp).trans_eq (inv_div _ _)
  have hxn : (p / x) ^ n = p ^ n / x ^ n := div_pow p x n
  rw [hxn, div_div_eq_mul_div] at hinv
  calc x ^ (-r) * Real.exp (-p / x)
      ≤ x ^ (-r) * ((n.factorial : ℝ) * x ^ n / p ^ n) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hx.le _)
    _ = ((n.factorial : ℝ) / p ^ n) * (x ^ (-r) * x ^ (n : ℝ)) := by
        rw [Real.rpow_natCast]; ring
    _ = ((n.factorial : ℝ) / p ^ n) * x ^ ((n : ℝ) - r) := by
        rw [← Real.rpow_add hx, show -r + (n : ℝ) = (n : ℝ) - r by ring]

private lemma becH_hasDerivAt {p : ℝ} (hp : 0 < p) (x : ℝ) : HasDerivAt (becH p) (bech p x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hnear : becH p =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) :=
      (gt_mem_nhds hx).mono fun y hy ↦ by simp [becH, not_lt.mpr hy.le]
    simpa [bech, not_lt.mpr hx.le] using (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hnear
  · simp only [bech, lt_irrefl, ↓reduceIte]
    rw [hasDerivAt_iff_tendsto_slope_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun t : ℝ ↦ ((3 : ℕ).factorial / p ^ 3) * |t| ^ (1 / 2 : ℝ))
        (𝓝[≠] 0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ |t| ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ ↦ |t| ^ (1 / 2 : ℝ)) :=
          continuous_abs.rpow_const fun _ ↦ Or.inr (by norm_num)
        simpa using (hc.continuousAt (x := 0)).tendsto
      simpa using (h1.mono_left nhdsWithin_le_nhds).const_mul ((3 : ℕ).factorial / p ^ 3)
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), zero_add,
        show becH p 0 = 0 by simp [becH], sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
    by_cases ht0 : 0 < t
    · simp only [becH, ht0, ↓reduceIte, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.exp_pos _)), abs_of_pos ht0]
      have hcomb : t⁻¹ * (t ^ (-(3 / 2 : ℝ)) * Real.exp (-p / t)) =
          t ^ (-(5 / 2 : ℝ)) * Real.exp (-p / t) := by
        rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
      rw [hcomb]
      have hbd := rpow_neg_mul_exp_neg_div_le hp ht0 (5 / 2 : ℝ) 3 (by norm_num)
      rw [show ((3 : ℕ) : ℝ) - 5 / 2 = 1 / 2 by norm_num] at hbd
      exact hbd
    · simp only [becH, ht0, ↓reduceIte, norm_zero, mul_zero]; positivity
  · have hnear : becH p =ᶠ[𝓝 x] fun y : ℝ ↦
        -(((y ^ (-(3 / 2 : ℝ)) * Real.exp (-p / y) : ℝ) : ℂ)) :=
      (lt_mem_nhds hx).mono fun y hy ↦ by simp [becH, hy]
    have h1 : HasDerivAt (fun y : ℝ ↦ y ^ (-(3 / 2 : ℝ))) (-(3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have h2 : HasDerivAt (fun y : ℝ ↦ Real.exp (-p / y))
        ((p / x ^ 2) * Real.exp (-p / x)) x := by
      have hi : HasDerivAt (fun y : ℝ ↦ -p / y) (p / x ^ 2) x := by
        have h := (hasDerivAt_inv hx.ne').const_mul (-p)
        convert h using 1
        · funext y; ring
        · ring
      simpa [mul_comm] using hi.exp
    have h3 : HasDerivAt (fun y : ℝ ↦ -(((y ^ (-(3 / 2 : ℝ)) * Real.exp (-p / y) : ℝ) : ℂ)))
        (-(((-(3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ) - 1) * Real.exp (-p / x) +
            x ^ (-(3 / 2 : ℝ)) * ((p / x ^ 2) * Real.exp (-p / x))) : ℝ) : ℂ)) x := by
      simpa only [Pi.neg_apply, Pi.mul_apply, Complex.ofReal_neg] using (h1.mul h2).neg.ofReal_comp
    refine h3.congr_of_eventuallyEq hnear |>.congr_deriv ?_
    simp only [bech, hx, ↓reduceIte, ← Complex.ofReal_neg]
    congr 1
    have h52 : x ^ (-(3 / 2 : ℝ) - 1) = x ^ (-(5 / 2 : ℝ)) := by congr 1; norm_num
    have h72 : x ^ (-(3 / 2 : ℝ)) * (p / x ^ 2) = p * x ^ (-(7 / 2 : ℝ)) := by
      rw [mul_div_assoc', ← Real.rpow_natCast x 2, div_eq_mul_inv, ← Real.rpow_neg hx.le,
          mul_right_comm, mul_comm (x ^ _ * _), ← Real.rpow_add hx]
      congr 2; norm_num
    rw [h52]
    linear_combination -(Real.exp (-p / x)) * h72

private lemma bech_continuous {p : ℝ} (hp : 0 < p) : Continuous (bech p) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hnear : bech p =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) :=
      (gt_mem_nhds hx).mono fun y hy ↦ by simp [bech, not_lt.mpr hy.le]
    exact continuousAt_const.congr hnear.symm
  · simp only [ContinuousAt, bech, lt_irrefl, ↓reduceIte]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let C : ℝ := 3 / 2 * ((3 : ℕ).factorial / p ^ 3) + p * ((4 : ℕ).factorial / p ^ 4)
    have hdom : Tendsto (fun y : ℝ ↦ C * |y| ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun y : ℝ ↦ |y| ^ (1 / 2 : ℝ)) :=
        continuous_abs.rpow_const fun _ ↦ Or.inr (by norm_num)
      simpa using (hc.continuousAt (x := 0)).tendsto.const_mul C
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    by_cases hy : 0 < y
    · simp only [bech, hy, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
      have h1 : y ^ (-(5 / 2 : ℝ)) * Real.exp (-p / y) ≤ ((3 : ℕ).factorial / p ^ 3) * y ^ (1 / 2 : ℝ) := by
        have h := rpow_neg_mul_exp_neg_div_le hp hy (5 / 2 : ℝ) 3 (by norm_num)
        rw [show ((3 : ℕ) : ℝ) - 5 / 2 = 1 / 2 by norm_num] at h; exact h
      have h2 : y ^ (-(7 / 2 : ℝ)) * Real.exp (-p / y) ≤ ((4 : ℕ).factorial / p ^ 4) * y ^ (1 / 2 : ℝ) := by
        have h := rpow_neg_mul_exp_neg_div_le hp hy (7 / 2 : ℝ) 4 (by norm_num)
        rw [show ((4 : ℕ) : ℝ) - 7 / 2 = 1 / 2 by norm_num] at h; exact h
      have htri : |(3 / 2 * y ^ (-(5 / 2 : ℝ)) - p * y ^ (-(7 / 2 : ℝ))) * Real.exp (-p / y)| ≤
          3 / 2 * (y ^ (-(5 / 2 : ℝ)) * Real.exp (-p / y)) +
          p * (y ^ (-(7 / 2 : ℝ)) * Real.exp (-p / y)) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hab : |3 / 2 * y ^ (-(5 / 2 : ℝ)) - p * y ^ (-(7 / 2 : ℝ))| ≤
            3 / 2 * y ^ (-(5 / 2 : ℝ)) + p * y ^ (-(7 / 2 : ℝ)) := by
          calc _ = |3 / 2 * y ^ (-(5 / 2 : ℝ)) + -(p * y ^ (-(7 / 2 : ℝ)))| := by rw [sub_eq_add_neg]
            _ ≤ |3 / 2 * y ^ (-(5 / 2 : ℝ))| + |-(p * y ^ (-(7 / 2 : ℝ)))| := abs_add_le _ _
            _ = 3 / 2 * y ^ (-(5 / 2 : ℝ)) + p * y ^ (-(7 / 2 : ℝ)) := by
                rw [abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
        nlinarith [Real.exp_pos (-p / y)]
      calc _ ≤ 3 / 2 * (((3 : ℕ).factorial / p ^ 3) * y ^ (1 / 2 : ℝ)) +
              p * (((4 : ℕ).factorial / p ^ 4) * y ^ (1 / 2 : ℝ)) := by nlinarith [h1, h2, htri]
        _ = C * y ^ (1 / 2 : ℝ) := by dsimp [C]; ring
    · simp only [bech, hy, ↓reduceIte, norm_zero]; positivity
  · have hnear : bech p =ᶠ[𝓝 x] fun y : ℝ ↦
        ((((3 / 2 * y ^ (-(5 / 2 : ℝ)) - p * y ^ (-(7 / 2 : ℝ))) * Real.exp (-p / y) : ℝ) : ℂ)) :=
      (lt_mem_nhds hx).mono fun y hy ↦ by simp [bech, hy]
    have hc : ContinuousAt (fun y : ℝ ↦
        ((((3 / 2 * y ^ (-(5 / 2 : ℝ)) - p * y ^ (-(7 / 2 : ℝ))) * Real.exp (-p / y) : ℝ) : ℂ))) x :=
      Complex.continuous_ofReal.continuousAt.comp
        (((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hx.ne'))).sub
          (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hx.ne')))).mul
          (continuousAt_const.div continuousAt_id hx.ne').rexp)
    exact hc.congr hnear.symm

private lemma becH_integrable {p : ℝ} (hp : 0 < p) : Integrable (becH p) := by
  have hcont : Continuous (becH p) :=
    continuous_iff_continuousAt.mpr fun x ↦ (becH_hasDerivAt hp x).continuousAt
  have h1 : IntegrableOn (becH p) (Iic 1) := by
    have h0 : IntegrableOn (becH p) (Iic 0) :=
      (integrableOn_zero (μ := volume) (s := Iic 0)).congr_fun
        (fun x hx ↦ by simp [becH, not_lt.mpr (mem_Iic.mp hx)]) measurableSet_Iic
    have h01 : IntegrableOn (becH p) (Ioc 0 1) :=
      hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← Iic_union_Ioc_eq_Iic zero_le_one]
    exact h0.union h01
  have h2 : IntegrableOn (becH p) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    simp only [becH, hx0, ↓reduceIte, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.exp_pos _))]
    have he : Real.exp (-p / x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx0.le _) he
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (1 : ℝ))]
  exact h1.union h2

private lemma bech_integrable {p : ℝ} (hp : 0 < p) : Integrable (bech p) := by
  have hcont := bech_continuous hp
  have h1 : IntegrableOn (bech p) (Iic 1) := by
    have h0 : IntegrableOn (bech p) (Iic 0) :=
      (integrableOn_zero (μ := volume) (s := Iic 0)).congr_fun
        (fun x hx ↦ by simp [bech, not_lt.mpr (mem_Iic.mp hx)]) measurableSet_Iic
    have h01 : IntegrableOn (bech p) (Ioc 0 1) :=
      hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← Iic_union_Ioc_eq_Iic zero_le_one]
    exact h0.union h01
  have h2 : IntegrableOn (bech p) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) zero_lt_one).const_mul
        (3 / 2 + p)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    simp only [bech, hx0, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    have he : Real.exp (-p / x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
    have hr : x ^ (-(7 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have htri : |3 / 2 * x ^ (-(5 / 2 : ℝ)) - p * x ^ (-(7 / 2 : ℝ))| ≤
        (3 / 2 + p) * x ^ (-(5 / 2 : ℝ)) := by
      have hab : |3 / 2 * x ^ (-(5 / 2 : ℝ)) - p * x ^ (-(7 / 2 : ℝ))| ≤
          3 / 2 * x ^ (-(5 / 2 : ℝ)) + p * x ^ (-(7 / 2 : ℝ)) := by
        calc _ = |3 / 2 * x ^ (-(5 / 2 : ℝ)) + -(p * x ^ (-(7 / 2 : ℝ)))| := by rw [sub_eq_add_neg]
          _ ≤ |3 / 2 * x ^ (-(5 / 2 : ℝ))| + |-(p * x ^ (-(7 / 2 : ℝ)))| := abs_add_le _ _
          _ = 3 / 2 * x ^ (-(5 / 2 : ℝ)) + p * x ^ (-(7 / 2 : ℝ)) := by
              rw [abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
      nlinarith
    calc _ ≤ ((3 / 2 + p) * x ^ (-(5 / 2 : ℝ))) * 1 :=
          mul_le_mul htri he (Real.exp_pos _).le (by positivity)
      _ = (3 / 2 + p) * x ^ (-(5 / 2 : ℝ)) := mul_one _
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (1 : ℝ))]
  exact h1.union h2

private lemma bech_isBigO {p : ℝ} (hp : 0 < p) :
    (bech p) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3 / 2 + p, Filter.hasBasis_cocompact.eventually_iff.mpr
    ⟨Metric.closedBall (0 : ℝ) 1, isCompact_closedBall 0 1, fun x hx ↦ ?_⟩⟩
  have hgt : 1 < |x| := by
    have hnot : ¬ dist x 0 ≤ 1 := fun h ↦ hx (Metric.mem_closedBall.mpr h)
    rw [Real.dist_eq, sub_zero] at hnot; linarith
  by_cases hx0 : 0 < x
  · have hx1 : 1 < x := by rwa [abs_of_pos hx0] at hgt
    simp only [bech, hx0, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    have he : Real.exp (-p / x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
    have hr1 : x ^ (-(7 / 2 : ℝ)) ≤ x ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have hr2 : x ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have htri : |3 / 2 * x ^ (-(5 / 2 : ℝ)) - p * x ^ (-(7 / 2 : ℝ))| ≤ (3 / 2 + p) * x ^ (-(2 : ℝ)) := by
      have hab : |3 / 2 * x ^ (-(5 / 2 : ℝ)) - p * x ^ (-(7 / 2 : ℝ))| ≤
          3 / 2 * x ^ (-(5 / 2 : ℝ)) + p * x ^ (-(7 / 2 : ℝ)) := by
        calc _ = |3 / 2 * x ^ (-(5 / 2 : ℝ)) + -(p * x ^ (-(7 / 2 : ℝ)))| := by rw [sub_eq_add_neg]
          _ ≤ |3 / 2 * x ^ (-(5 / 2 : ℝ))| + |-(p * x ^ (-(7 / 2 : ℝ)))| := abs_add_le _ _
          _ = 3 / 2 * x ^ (-(5 / 2 : ℝ)) + p * x ^ (-(7 / 2 : ℝ)) := by
              rw [abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
      nlinarith
    calc _ ≤ ((3 / 2 + p) * x ^ (-(2 : ℝ))) * 1 := mul_le_mul htri he (Real.exp_pos _).le (by positivity)
      _ = (3 / 2 + p) * x ^ (-(2 : ℝ)) := mul_one _
  · simp only [bech, hx0, ↓reduceIte, norm_zero]
    exact mul_nonneg (by positivity) (norm_nonneg _)

/-- Exact 1D Fourier transform of `bech p` via Mathlib's `Real.fourier_deriv` + `K_{1/2}` integral! -/
private theorem fourier_bech_eq {p : ℝ} (hp : 0 < p) (ξ : ℝ) :
    𝓕 (bech p) ξ =
      if ξ = 0 then 0
      else if 0 < ξ then
        (-2 * (Real.pi : ℂ) * I * (ξ : ℂ)) * (((Real.sqrt Real.pi / Real.sqrt p : ℝ) : ℂ)) *
          Complex.exp (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * ξ) : ℝ) : ℂ) * (1 + I)))
      else
        (-2 * (Real.pi : ℂ) * I * (ξ : ℂ)) * (((Real.sqrt Real.pi / Real.sqrt p : ℝ) : ℂ)) *
          Complex.exp (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (-ξ)) : ℝ) : ℂ) * (1 - I))) := by
  have hderiv_eq : deriv (becH p) = bech p := funext fun x ↦ (becH_hasDerivAt hp x).deriv
  have hF := congrFun (Real.fourier_deriv (becH_integrable hp)
    (fun x ↦ (becH_hasDerivAt hp x).differentiableAt) (by rw [hderiv_eq]; exact bech_integrable hp)) ξ
  rw [hderiv_eq] at hF
  rw [hF]
  by_cases hξ0 : ξ = 0
  · subst hξ0; simp
  · simp only [hξ0, ↓reduceIte, smul_eq_mul]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have hsplit := (integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (integrable_fourier_mul (becH_integrable hp) ξ)).symm
    have hle0 : (∫ x in (Ioi (0 : ℝ))ᶜ, Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * becH p x) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero; intro x hx
      have hx' : ¬ 0 < x := by simpa using hx
      simp [becH, hx']
    rw [hsplit, hle0, add_zero]
    have hpos_int : (∫ x in Ioi (0 : ℝ), Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * becH p x) =
        -∫ x in Ioi (0 : ℝ), ((x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-((p : ℂ) / (x : ℂ)) - (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) * (x : ℂ)) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi; intro x hx
      have hx0 : 0 < x := mem_Ioi.mp hx
      simp only [becH, hx0, ↓reduceIte, mul_neg, Complex.ofReal_mul, Complex.ofReal_exp]
      congr 1
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hpos_int]
    by_cases hξp : 0 < ξ
    · simp only [hξp, ↓reduceIte]
      let w : ℂ := ((Real.sqrt (Real.pi * ξ) : ℝ) : ℂ) * (1 + I)
      have hw_re : 0 < w.re := by
        simp [w, Complex.mul_re]; exact mul_pos Real.pi_pos hξp
      have hw2 : w ^ 2 = 2 * (Real.pi : ℂ) * I * (ξ : ℂ) := by
        dsimp only [w]
        rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (mul_pos Real.pi_pos hξp).le]
        push_cast; ring_nf; simp [Complex.I_sq]
      have hw2_re : 0 ≤ (w ^ 2).re := by rw [hw2]; simp [Complex.mul_re]
      have hint_eq := integral_rpow_neg_three_halves_cexp hp hw_re hw2_re
      rw [hw2] at hint_eq
      rw [hint_eq]; dsimp only [w]; ring
    · simp only [hξp, ↓reduceIte]
      have hξn : 0 < -ξ := by have : ξ < 0 := lt_of_le_of_ne (not_lt.mp hξp) hξ0; linarith
      let w : ℂ := ((Real.sqrt (Real.pi * (-ξ)) : ℝ) : ℂ) * (1 - I)
      have hw_re : 0 < w.re := by
        simp [w, Complex.mul_re]; nlinarith [Real.pi_pos, hξn]
      have hw2 : w ^ 2 = 2 * (Real.pi : ℂ) * I * (ξ : ℂ) := by
        dsimp only [w]
        rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (mul_pos Real.pi_pos hξn).le]
        push_cast; ring_nf; simp [Complex.I_sq]
      have hw2_re : 0 ≤ (w ^ 2).re := by rw [hw2]; simp [Complex.mul_re]
      have hint_eq := integral_rpow_neg_three_halves_cexp hp hw_re hw2_re
      rw [hw2] at hint_eq
      rw [hint_eq]; dsimp only [w]; ring

/-- **Exact 1D Poisson Summation in `k` for `bech p`**:
For EVERY `p > 0`:
`∑'_{k : ℕ+} bech p k = ∑'_{j : ℕ+} (𝓕 (bech p) j + 𝓕 (bech p) (-j))`! -/
private theorem tsum_bech_eq_tsum_pnat {p : ℝ} (hp : 0 < p) :
    (∑' k : ℕ+, bech p (k.val : ℝ)) =
      ∑' j : ℕ+, (2 * (Real.pi : ℂ) * I * (j.val : ℂ)) * (((Real.sqrt Real.pi / Real.sqrt p : ℝ) : ℂ)) *
        (-Complex.exp (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 + I))) +
          Complex.exp (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 - I)))) := by
  have hsum_pos : Summable (fun j : ℕ+ ↦ ‖𝓕 (bech p) (j.val : ℝ)‖) := by
    let c : ℝ := 2 * Real.sqrt p * Real.sqrt Real.pi
    have hc : 0 < c := by positivity
    let C : ℝ := 2 * Real.pi * (Real.sqrt Real.pi / Real.sqrt p)
    have hdom := (summable_pow_mul_exp_neg_sqrt hc 1).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_) hdom
    have hj : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast j.pos
    rw [fourier_bech_eq hp (j.val : ℝ)]
    simp only [hj.ne', ↓reduceIte, hj, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hj,
      abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / Real.sqrt p), Complex.norm_exp]
    have hre : (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 + I))).re =
        -c * Real.sqrt (j.val : ℝ) := by
      simp [c, Complex.mul_re, Real.sqrt_mul Real.pi_pos.le]; ring
    rw [hre]; dsimp [C]; rw [pow_one]; ring_nf; exact le_rfl
  have hsum_neg : Summable (fun j : ℕ+ ↦ ‖𝓕 (bech p) (-(j.val : ℝ))‖) := by
    let c : ℝ := 2 * Real.sqrt p * Real.sqrt Real.pi
    have hc : 0 < c := by positivity
    let C : ℝ := 2 * Real.pi * (Real.sqrt Real.pi / Real.sqrt p)
    have hdom := (summable_pow_mul_exp_neg_sqrt hc 1).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_) hdom
    have hj : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast j.pos
    have hnj : ¬ (0 : ℝ) < -(j.val : ℝ) := by linarith
    rw [fourier_bech_eq hp (-(j.val : ℝ))]
    simp only [neg_ne_zero.mpr hj.ne', ↓reduceIte, hnj, neg_neg, norm_mul, norm_neg,
      Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hj,
      abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / Real.sqrt p), Complex.norm_exp]
    have hre : (-2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 - I))).re =
        -c * Real.sqrt (j.val : ℝ) := by
      simp [c, Complex.mul_re, Real.sqrt_mul Real.pi_pos.le]; ring
    rw [hre]; dsimp [C]; rw [pow_one]; ring_nf; exact le_rfl
  have hsum_int : Summable (fun j : ℤ ↦ 𝓕 (bech p) (j : ℝ)) := by
    have hnat : Summable (fun n : ℕ ↦ 𝓕 (bech p) ((n : ℤ) : ℝ)) := by
      rw [← summable_nat_add_iff 1]
      exact (Equiv.pnatEquivNat.symm.summable_iff.mpr hsum_pos.of_norm).congr fun n ↦ by
        simp [Equiv.pnatEquivNat]
    have hneg : Summable (fun n : ℕ ↦ 𝓕 (bech p) (((-(n : ℤ) : ℤ) : ℝ))) := by
      rw [← summable_nat_add_iff 1]
      exact (Equiv.pnatEquivNat.symm.summable_iff.mpr hsum_neg.of_norm).congr fun n ↦ by
        simp [Equiv.pnatEquivNat]
    exact summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, hneg⟩
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (bech_continuous hp) one_lt_two (bech_isBigO hp) hsum_int 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hpois
  have hsum_h_int : Summable (fun k : ℤ ↦ bech p (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((bech_isBigO hp).comp_tendsto Int.tendsto_coe_cofinite)
  have htsum_int_split (F : ℤ → ℂ) (hF : Summable F) :
      (∑' k : ℤ, F k) = F 0 + ∑' j : ℕ+, F (j.val : ℤ) + ∑' j : ℕ+, F (-(j.val : ℤ)) := by
    have hnat : Summable (fun n : ℕ ↦ F (n : ℤ)) := hF.comp_injective Int.ofNat_injective
    have hneg : Summable (fun n : ℕ ↦ F (-(n + 1 : ℤ))) :=
      hF.comp_injective fun a b h ↦ by omega
    rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add]
    have h1 : (∑' n : ℕ, F ((n + 1 : ℕ) : ℤ)) = ∑' j : ℕ+, F (j.val : ℤ) :=
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ F (n : ℤ))).symm
    have h2 : (∑' n : ℕ, F (-(n + 1 : ℤ))) = ∑' j : ℕ+, F (-(j.val : ℤ)) := by
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ F (-(n : ℤ)))]
      apply tsum_congr; intro n; congr 1
    simp only [Nat.cast_zero]
    rw [h1, h2]
  have hlhs : (∑' k : ℤ, bech p (k : ℝ)) = ∑' k : ℕ+, bech p (k.val : ℝ) := by
    rw [htsum_int_split (fun k : ℤ ↦ bech p (k : ℝ)) hsum_h_int]
    simp only [Int.cast_zero, Int.cast_natCast, Int.cast_neg]
    have h0 : bech p (0 : ℝ) = 0 := by simp [bech]
    have hneg0 : (∑' j : ℕ+, bech p (-(j.val : ℝ))) = 0 := by
      have hz : ∀ j : ℕ+, bech p (-(j.val : ℝ)) = 0 := fun j ↦ by
        have hle : ¬ (0 : ℝ) < -(j.val : ℝ) := by
          have : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast j.pos
          linarith
        simp [bech, hle]
      simp [hz]
    rw [h0, hneg0, zero_add, add_zero]
  have hrhs : (∑' j : ℤ, 𝓕 (bech p) (j : ℝ)) =
      ∑' j : ℕ+, (𝓕 (bech p) (j.val : ℝ) + 𝓕 (bech p) (-(j.val : ℝ))) := by
    rw [htsum_int_split (fun j : ℤ ↦ 𝓕 (bech p) (j : ℝ)) hsum_int]
    have h0 : 𝓕 (bech p) ((0 : ℤ) : ℝ) = 0 := by simp [fourier_bech_eq hp]
    rw [h0, zero_add]
    simp only [Int.cast_natCast, Int.cast_neg]
    exact (hsum_pos.of_norm.tsum_add hsum_neg.of_norm).symm
  rw [hlhs, hrhs] at hpois
  rw [hpois]
  apply tsum_congr; intro j
  have hj : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast j.pos
  have hnj : ¬ (0 : ℝ) < -(j.val : ℝ) := by linarith
  rw [fourier_bech_eq hp (j.val : ℝ), fourier_bech_eq hp (-(j.val : ℝ))]
  simp only [hj.ne', ↓reduceIte, hj, neg_ne_zero.mpr hj.ne', hnj, neg_neg]
  push_cast; ring

/-! ### 3. Smooth Radial Kernel `φ(u) = (∫_0^1 exp(s u) ds)⁻¹` & Rapid Decay of All Derivatives -/

private def phiDenom (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.exp (s * u)

private def phiKernel (u : ℝ) : ℝ := (phiDenom u)⁻¹

private lemma phiDenom_zero : phiDenom 0 = 1 := by simp [phiDenom]

private lemma phiDenom_ne_zero_eq {u : ℝ} (hu : u ≠ 0) :
    phiDenom u = (Real.exp u - 1) / u := by
  unfold phiDenom
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ ↦ Real.exp (r * u) / u) (Real.exp (s * u)) s := by
    intro s _
    have h1 : HasDerivAt (fun r : ℝ ↦ r * u) u s := by simpa using (hasDerivAt_id s).mul_const u
    convert (h1.exp).div_const u using 1
    field_simp [hu]
  have hint : IntervalIntegrable (fun s : ℝ ↦ Real.exp (s * u)) volume 0 1 :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp [sub_div]

private lemma phiDenom_pos (u : ℝ) : 0 < phiDenom u := by
  by_cases hu : u = 0
  · subst hu; rw [phiDenom_zero]; exact zero_lt_one
  · rw [phiDenom_ne_zero_eq hu]
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · exact div_pos_of_neg_of_neg (by linarith [Real.exp_lt_one_iff.mpr hlt]) hlt
    · exact div_pos (by linarith [Real.one_lt_exp_iff.mpr hgt]) hgt

private lemma phiKernel_zero : phiKernel 0 = 1 := by simp [phiKernel, phiDenom_zero]

private lemma phiKernel_ne_zero_eq {u : ℝ} (hu : u ≠ 0) :
    phiKernel u = u / (Real.exp u - 1) := by
  rw [phiKernel, phiDenom_ne_zero_eq hu, inv_div]

private lemma phiDenom_moment_hasDerivAt (m : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ s in (0 : ℝ)..1, s ^ m * Real.exp (s * x))
      (∫ s in (0 : ℝ)..1, s ^ (m + 1) * Real.exp (s * u)) u := by
  let F' (x s : ℝ) : ℝ := s ^ (m + 1) * Real.exp (s * x)
  have hbound : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball u 1,
      ‖F' x s‖ ≤ Real.exp (|u| + 1) := by
    filter_upwards with s hs x hx
    rw [uIoc_of_le zero_le_one] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have hxm : x ≤ |u| + 1 := by
      have h1 : |x - u| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hx
      linarith [(abs_le.mp h1.le).2, le_abs_self u]
    dsimp only [F']
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs0 _), abs_of_pos (Real.exp_pos _)]
    have hp : s ^ (m + 1) ≤ 1 := pow_le_one₀ hs0 hs1
    have he : Real.exp (s * x) ≤ Real.exp (|u| + 1) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg u]
    calc s ^ (m + 1) * Real.exp (s * x) ≤ 1 * Real.exp (|u| + 1) :=
          mul_le_mul hp he (Real.exp_pos _).le zero_le_one
      _ = Real.exp (|u| + 1) := one_mul _
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u zero_lt_one)
    (Eventually.of_forall fun x ↦ ((continuous_pow m).mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    (((continuous_pow m).mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1)
    (((continuous_pow (m + 1)).mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    hbound intervalIntegrable_const (Eventually.of_forall fun s _ x _ ↦ by
      have hl : HasDerivAt (fun y : ℝ ↦ s * y) s x := by simpa using (hasDerivAt_id x).const_mul s
      exact ((hl.exp).const_mul (s ^ m)).congr_deriv (by dsimp [F']; rw [pow_succ]; ring))).2

private lemma phiKernel_contDiff (N : ℕ) : ContDiff ℝ N phiKernel := by
  have hmom : ∀ n m : ℕ, ContDiff ℝ (n : ℕ) (fun x : ℝ ↦ ∫ s in (0 : ℝ)..1, s ^ m * Real.exp (s * x)) := by
    intro n
    induction n with
    | zero =>
      intro m
      rw [Nat.cast_zero, contDiff_zero]
      exact Differentiable.continuous fun x ↦ (phiDenom_moment_hasDerivAt m x).differentiableAt
    | succ n ih =>
      intro m
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x ↦ (phiDenom_moment_hasDerivAt m x).differentiableAt, by simp, ?_⟩
      have hd : deriv (fun x : ℝ ↦ ∫ s in (0 : ℝ)..1, s ^ m * Real.exp (s * x)) =
          fun u : ℝ ↦ ∫ s in (0 : ℝ)..1, s ^ (m + 1) * Real.exp (s * u) :=
        funext fun u ↦ (phiDenom_moment_hasDerivAt m u).deriv
      rw [hd]
      exact ih (m + 1)
  have hden : ContDiff ℝ N phiDenom := by
    have h0 := hmom N 0
    convert h0 using 1
    ext u; simp [phiDenom]
  exact hden.inv fun u ↦ (phiDenom_pos u).ne'

/-- Building block `u^a * exp(-b u) * (1 - exp(-u))^{-m}` on `u > 0`. -/
private def ebTerm (a b m : ℕ) (u : ℝ) : ℝ :=
  u ^ a * Real.exp (-(b : ℝ) * u) * ((1 - Real.exp (-u))⁻¹) ^ m

private lemma ebTerm_hasDerivAt (a b m : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (ebTerm a b m)
      ((a : ℝ) * ebTerm (a - 1) b m u - (b : ℝ) * ebTerm a b m u -
        (m : ℝ) * ebTerm a (b + 1) (m + 1) u) u := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ a) ((a : ℝ) * u ^ (a - 1)) u := hasDerivAt_pow a u
  have h2 : HasDerivAt (fun x : ℝ ↦ Real.exp (-(b : ℝ) * x)) (-(b : ℝ) * Real.exp (-(b : ℝ) * u)) u := by
    have hl : HasDerivAt (fun x : ℝ ↦ -(b : ℝ) * x) (-(b : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(b : ℝ))
    simpa [mul_comm] using hl.exp
  have hden : 1 - Real.exp (-u) ≠ 0 := by linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)]
  have h3 : HasDerivAt (fun x : ℝ ↦ ((1 - Real.exp (-x))⁻¹) ^ m)
      (-(m : ℝ) * Real.exp (-u) * ((1 - Real.exp (-u))⁻¹) ^ (m + 1)) u := by
    have he : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-x)) (Real.exp (-u)) u := by
      have hn : HasDerivAt (fun x : ℝ ↦ -x) (-1) u := (hasDerivAt_id u).neg
      have hne := hn.exp
      simpa using hne.const_sub 1
    have hinv : HasDerivAt (fun x : ℝ ↦ (1 - Real.exp (-x))⁻¹)
        (-Real.exp (-u) / (1 - Real.exp (-u)) ^ 2) u := he.inv hden
    exact (hinv.pow m).congr_deriv (by
      cases m with
      | zero => simp
      | succ m' =>
        rw [Nat.add_sub_cancel, inv_pow, inv_pow, pow_succ, pow_succ]
        field_simp [hden]
        ring)
  have hprod : HasDerivAt (ebTerm a b m)
      (((a : ℝ) * u ^ (a - 1) * Real.exp (-(b : ℝ) * u) +
        u ^ a * (-(b : ℝ) * Real.exp (-(b : ℝ) * u))) * ((1 - Real.exp (-u))⁻¹) ^ m +
       (u ^ a * Real.exp (-(b : ℝ) * u)) *
        (-(m : ℝ) * Real.exp (-u) * ((1 - Real.exp (-u))⁻¹) ^ (m + 1))) u :=
    (h1.mul h2).mul h3
  refine hprod.congr_deriv ?_
  dsimp only [ebTerm]
  have hexp_add : Real.exp (-(b + 1 : ℕ) * u) = Real.exp (-(b : ℝ) * u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hexp_add]; ring

private def InExpClass (g : ℝ → ℝ) : Prop :=
  ∃ L : List (ℝ × ℕ × ℕ × ℕ), (∀ p ∈ L, 1 ≤ p.2.2.1) ∧
    ∀ u > 0, g u = (L.map fun p ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 u).sum

private lemma phiKernel_inExpClass : InExpClass phiKernel := by
  refine ⟨[(1, 1, 1, 1)], fun p hp ↦ by simp at hp; rw [hp], fun u hu ↦ ?_⟩
  rw [phiKernel_ne_zero_eq hu.ne']
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
    ebTerm, pow_one, Nat.cast_one, neg_mul, one_mul]
  have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  have h1 : Real.exp u - 1 ≠ 0 := by linarith [Real.one_lt_exp_iff.mpr hu]
  have h2 : 1 - Real.exp (-u) ≠ 0 := by linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)]
  rw [Real.exp_neg]
  field_simp [he, h1, h2]

private lemma inExpClass_deriv {g : ℝ → ℝ} (hg : InExpClass g) : InExpClass (deriv g) := by
  rcases hg with ⟨L, hLb, hLeq⟩
  let step (p : ℝ × ℕ × ℕ × ℕ) : List (ℝ × ℕ × ℕ × ℕ) :=
    [(p.1 * (p.2.1 : ℝ), p.2.1 - 1, p.2.2.1, p.2.2.2),
     (-(p.1 * (p.2.2.1 : ℝ)), p.2.1, p.2.2.1, p.2.2.2),
     (-(p.1 * (p.2.2.2 : ℝ)), p.2.1, p.2.2.1 + 1, p.2.2.2 + 1)]
  refine ⟨L.flatMap step, ?_, ?_⟩
  · intro q hq
    rw [List.mem_flatMap] at hq
    rcases hq with ⟨p, hpL, hqp⟩
    have hpb := hLb p hpL
    simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hqp
    rcases hqp with rfl | rfl | rfl <;> dsimp <;> omega
  · intro u hu
    have hnear : g =ᶠ[𝓝 u] fun x ↦ (L.map fun p ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 x).sum :=
      (lt_mem_nhds hu).mono fun x hx ↦ hLeq x hx
    rw [hnear.deriv_eq]
    have hd_list : ∀ M : List (ℝ × ℕ × ℕ × ℕ),
        HasDerivAt (fun x ↦ (M.map fun p ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 x).sum)
          (((M.flatMap step).map fun p ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 u).sum) u := by
      intro M
      induction M with
      | nil => simpa using hasDerivAt_const u (0 : ℝ)
      | cons p M ih =>
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
        have hp : HasDerivAt (fun x ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 x)
            (((step p).map fun q ↦ q.1 * ebTerm q.2.1 q.2.2.1 q.2.2.2 u).sum) u := by
          convert (ebTerm_hasDerivAt p.2.1 p.2.2.1 p.2.2.2 hu).const_mul p.1 using 1
          simp only [step, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          ring
        exact hp.add ih
    exact (hd_list L).deriv

private lemma phiKernel_iteratedDeriv_inExpClass (k : ℕ) : InExpClass (iteratedDeriv k phiKernel) := by
  induction k with
  | zero => simpa using phiKernel_inExpClass
  | succ k ih => rw [iteratedDeriv_succ]; exact inExpClass_deriv ih

private lemma ebTerm_exp_decay (a b m : ℕ) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ≥ 1, |ebTerm a b m u| ≤ C * Real.exp (-u / 2) := by
  let K : ℝ := (2 : ℝ) ^ a * (a.factorial : ℝ) * ((1 - Real.exp (-1))⁻¹) ^ m
  refine ⟨K, by
    have h1 : 0 < 1 - Real.exp (-1) := by linarith [Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)]
    positivity, fun u hu ↦ ?_⟩
  have hu0 : 0 < u := by linarith
  have hden_pos : 0 < 1 - Real.exp (-u) := by linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu0)]
  have hden_ge : 1 - Real.exp (-1) ≤ 1 - Real.exp (-u) := by
    linarith [Real.exp_le_exp.mpr (show -u ≤ -1 by linarith)]
  have hden1_pos : 0 < 1 - Real.exp (-1) := by
    linarith [Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)]
  have hinv_le : ((1 - Real.exp (-u))⁻¹) ^ m ≤ ((1 - Real.exp (-1))⁻¹) ^ m :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ hden1_pos hden_ge) m
  have hb_le : Real.exp (-(b : ℝ) * u) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith
  have hua : u ^ a * Real.exp (-u / 2) ≤ (2 : ℝ) ^ a * (a.factorial : ℝ) := by
    have hexp := Real.pow_div_factorial_le_exp (u / 2) (by positivity) a
    have hsplit : u ^ a = (2 : ℝ) ^ a * (u / 2) ^ a := by rw [← mul_pow]; congr 1; ring
    rw [hsplit]
    have hmul : (u / 2) ^ a * Real.exp (-u / 2) ≤ (a.factorial : ℝ) := by
      have h1 : (u / 2) ^ a ≤ (a.factorial : ℝ) * Real.exp (u / 2) :=
        (div_le_iff₀' (by positivity)).mp hexp
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-u / 2)).le
      rw [mul_assoc, ← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero, mul_one] at h2
      exact h2
    calc (2 : ℝ) ^ a * (u / 2) ^ a * Real.exp (-u / 2)
        = (2 : ℝ) ^ a * ((u / 2) ^ a * Real.exp (-u / 2)) := by ring
      _ ≤ (2 : ℝ) ^ a * (a.factorial : ℝ) := mul_le_mul_of_nonneg_left hmul (by positivity)
  dsimp only [ebTerm]
  rw [abs_of_pos (by positivity)]
  have he_split : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc u ^ a * Real.exp (-(b : ℝ) * u) * ((1 - Real.exp (-u))⁻¹) ^ m
      ≤ u ^ a * Real.exp (-u) * ((1 - Real.exp (-1))⁻¹) ^ m := by gcongr
    _ = (u ^ a * Real.exp (-u / 2)) * ((1 - Real.exp (-1))⁻¹) ^ m * Real.exp (-u / 2) := by
        rw [he_split]; ring
    _ ≤ ((2 : ℝ) ^ a * (a.factorial : ℝ)) * ((1 - Real.exp (-1))⁻¹) ^ m * Real.exp (-u / 2) := by
        gcongr
    _ = K * Real.exp (-u / 2) := by rfl

private lemma phiKernel_iteratedDeriv_exp_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ≥ 0, |iteratedDeriv k phiKernel u| ≤ C * Real.exp (-u / 2) := by
  obtain ⟨L, hLb, hLeq⟩ := phiKernel_iteratedDeriv_inExpClass k
  have htail : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ u ≥ 1, |iteratedDeriv k phiKernel u| ≤ C1 * Real.exp (-u / 2) := by
    have hlist : ∀ M : List (ℝ × ℕ × ℕ × ℕ), (∀ p ∈ M, 1 ≤ p.2.2.1) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u ≥ 1, |(M.map fun p ↦ p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 u).sum| ≤
          C * Real.exp (-u / 2) := by
      intro M
      induction M with
      | nil => intro _; exact ⟨0, le_rfl, fun u _ ↦ by simp⟩
      | cons p M ih =>
        intro hM
        obtain ⟨Cp, hCp, hbp⟩ := ebTerm_exp_decay p.2.1 p.2.2.1 p.2.2.2 (hM p (by simp))
        obtain ⟨CM, hCM, hbM⟩ := ih (fun q hq ↦ hM q (List.mem_cons_of_mem p hq))
        refine ⟨|p.1| * Cp + CM, by positivity, fun u hu ↦ ?_⟩
        simp only [List.map_cons, List.sum_cons]
        calc _ ≤ |p.1 * ebTerm p.2.1 p.2.2.1 p.2.2.2 u| +
                |(M.map fun q ↦ q.1 * ebTerm q.2.1 q.2.2.1 q.2.2.2 u).sum| := abs_add_le _ _
          _ ≤ |p.1| * (Cp * Real.exp (-u / 2)) + CM * Real.exp (-u / 2) := by
              rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (hbp u hu) (abs_nonneg _)) (hbM u hu)
          _ = (|p.1| * Cp + CM) * Real.exp (-u / 2) := by ring
    obtain ⟨C1, hC1, hb1⟩ := hlist L hLb
    exact ⟨C1, hC1, fun u hu ↦ by rw [hLeq u (by linarith)]; exact hb1 u hu⟩
  obtain ⟨C1, hC1, hb1⟩ := htail
  have hcont : Continuous (iteratedDeriv k phiKernel) :=
    (phiKernel_contDiff k).continuous_iteratedDeriv k le_rfl
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hcont.continuousOn
  let C0 : ℝ := max (|M0| * Real.exp (1 / 2)) 0
  refine ⟨max C0 C1, le_trans (le_max_right _ _) (le_max_left _ _), fun u hu ↦ ?_⟩
  by_cases hu1 : u ≤ 1
  · have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu, hu1⟩
    have hnorm : |iteratedDeriv k phiKernel u| ≤ |M0| := by
      have := hM0 u hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self M0)
    have hexp : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-u / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    calc |iteratedDeriv k phiKernel u| ≤ |M0| := hnorm
      _ = |M0| * Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ C0 * Real.exp (-u / 2) :=
          mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le (le_max_right _ _)
      _ ≤ max C0 C1 * Real.exp (-u / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · push Not at hu1
    exact (hb1 u hu1.le).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-! ### 4. 1D Gaussian Fourier Transforms (Order 0 & Order 2) and Exact 3D Kernel Fourier Transform -/

private lemma fourier_gauss0 {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))) ξ =
      (((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) * Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ))) := by
  have hb : 0 < ((a / Real.pi : ℝ) : ℂ).re := by simp; positivity
  have h := congrFun (fourier_gaussian_pi hb) ξ
  have hfun : (fun x : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * ((a / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2)) =
      fun x : ℝ ↦ Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2)) := by
    funext x; congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast; field_simp [hpi]
  rw [hfun] at h
  rw [h]
  have hcpow : ((a / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (a / Real.pi) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]; norm_num
  rw [hcpow]
  congr 1
  · have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have ha' : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    rw [Real.sqrt_div ha.le, Real.sqrt_div Real.pi_pos.le]
    push_cast; field_simp [hpi, ha']
  · congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    push_cast; field_simp [hpi, haC]

private lemma fourier_gauss2 {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ ((x : ℂ) ^ 2) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))) ξ =
      (((Real.sqrt (Real.pi / a) * (1 / (2 * a) - Real.pi ^ 2 * ξ ^ 2 / a ^ 2) : ℝ) : ℂ)) *
        Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ))) := by
  let g (x : ℝ) : ℂ := Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))
  have hg_mom : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (fun x : ℝ ↦ x ^ n • g x) := by
    intro n _
    refine ((integrable_exp_neg_mul_sq (half_pos ha)).const_mul
        ((2 / a) ^ n * (n.factorial : ℝ) + 1)).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact ((continuous_pow n).aestronglyMeasurable.smul (by fun_prop))
    · rw [norm_smul, Real.norm_eq_abs, abs_pow, Complex.norm_exp]
      have hre : (-((a : ℂ) * (x : ℂ) ^ 2)).re = -a * x ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re, neg_mul]
      rw [hre]
      have hbd : |x| ^ n * Real.exp (-(a / 2) * x ^ 2) ≤ (2 / a) ^ n * (n.factorial : ℝ) + 1 := by
        by_cases hx1 : |x| ≤ 1
        · calc |x| ^ n * Real.exp (-(a / 2) * x ^ 2) ≤ 1 * 1 :=
                mul_le_mul (pow_le_one₀ (abs_nonneg x) hx1)
                  (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])) (Real.exp_pos _).le zero_le_one
            _ ≤ _ := by linarith [show 0 ≤ (2 / a) ^ n * (n.factorial : ℝ) by positivity]
        · push Not at hx1
          have hx2 : |x| ≤ x ^ 2 := by rw [← sq_abs]; nlinarith
          have hu : (a / 2) * |x| ≤ (a / 2) * x ^ 2 := by nlinarith
          have hexp := Real.pow_div_factorial_le_exp ((a / 2) * |x|) (by positivity) n
          have h1 : |x| ^ n * Real.exp (-(a / 2) * |x|) ≤ (2 / a) ^ n * (n.factorial : ℝ) := by
            have hle : ((a / 2) * |x|) ^ n ≤ (n.factorial : ℝ) * Real.exp ((a / 2) * |x|) :=
              (div_le_iff₀' (by positivity)).mp hexp
            rw [mul_pow] at hle
            have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-(a / 2) * |x|)).le
            rw [mul_assoc (n.factorial : ℝ), ← Real.exp_add, show (a / 2) * |x| + -(a / 2) * |x| = 0 by ring,
                Real.exp_zero, mul_one] at hmul
            have hinv := mul_le_mul_of_nonneg_left hmul (show 0 ≤ (2 / a) ^ n by positivity)
            have hcan : (2 / a) ^ n * ((a / 2) ^ n * |x| ^ n * Real.exp (-(a / 2) * |x|)) =
                |x| ^ n * Real.exp (-(a / 2) * |x|) := by
              rw [← mul_assoc, ← mul_assoc, ← mul_pow, show (2 / a) * (a / 2) = 1 by field_simp [ha.ne'],
                  one_pow, one_mul]
            rw [hcan] at hinv
            exact hinv
          calc |x| ^ n * Real.exp (-(a / 2) * x ^ 2)
              ≤ |x| ^ n * Real.exp (-(a / 2) * |x|) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
            _ ≤ (2 / a) ^ n * (n.factorial : ℝ) := h1
            _ ≤ _ := by linarith
      have he_split : Real.exp (-a * x ^ 2) = Real.exp (-(a / 2) * x ^ 2) * Real.exp (-(a / 2) * x ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he_split, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
  have hd2 := congrFun (Real.iteratedDeriv_fourier hg_mom le_rfl) ξ
  have hFg : 𝓕 g = fun y : ℝ ↦ (((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) *
      Complex.exp (-(((Real.pi ^ 2 / a : ℝ) : ℂ)) * (y : ℂ) ^ 2) := by
    funext y; rw [fourier_gauss0 ha y]; congr 2; push_cast; ring
  have hd2_lhs : iteratedDeriv 2 (𝓕 g) ξ =
      (((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) *
        ((-2 * ((Real.pi ^ 2 / a : ℝ) : ℂ) + 4 * ((Real.pi ^ 2 / a : ℝ) : ℂ) ^ 2 * (ξ : ℂ) ^ 2) *
          Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ)))) := by
    rw [hFg, iteratedDeriv_const_mul_field]
    congr 1
    let c : ℂ := ((Real.pi ^ 2 / a : ℝ) : ℂ)
    have h1 (y : ℝ) : HasDerivAt (fun z : ℝ ↦ Complex.exp (-c * (z : ℂ) ^ 2))
        ((-2 * c * (y : ℂ)) * Complex.exp (-c * (y : ℂ) ^ 2)) y := by
      have ha1 : HasDerivAt (fun z : ℝ ↦ -c * (z : ℂ) ^ 2) (-2 * c * (y : ℂ)) y := by
        have hof : HasDerivAt (fun z : ℝ ↦ (z : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
        have hp := (hof.pow 2).const_mul (-c)
        refine hp.congr_deriv ?_; ring
      simpa [mul_comm] using ha1.cexp
    have hd1 : deriv (fun z : ℝ ↦ Complex.exp (-c * (z : ℂ) ^ 2)) =
        fun y : ℝ ↦ (-2 * c * (y : ℂ)) * Complex.exp (-c * (y : ℂ) ^ 2) := funext fun y ↦ (h1 y).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]
    have h2 : HasDerivAt (fun y : ℝ ↦ (-2 * c * (y : ℂ)) * Complex.exp (-c * (y : ℂ) ^ 2))
        ((-2 * c + 4 * c ^ 2 * (ξ : ℂ) ^ 2) * Complex.exp (-c * (ξ : ℂ) ^ 2)) ξ := by
      have hl : HasDerivAt (fun y : ℝ ↦ -2 * c * (y : ℂ)) (-2 * c) ξ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := ξ)).const_mul (-2 * c)
      convert hl.mul (h1 ξ) using 1; ring
    rw [h2.deriv]; congr 2; dsimp [c]; push_cast; ring
  have hd2_rhs : 𝓕 (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • g x) ξ =
      -((2 * Real.pi : ℂ) ^ 2) * 𝓕 (fun x : ℝ ↦ ((x : ℂ) ^ 2) * g x) ξ := by
    have hfun : (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • g x) =
        fun x : ℝ ↦ -((2 * Real.pi : ℂ) ^ 2) * (((x : ℂ) ^ 2) * g x) := by
      funext x; rw [smul_eq_mul]
      calc (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 * g x
          = ((2 * (Real.pi : ℂ)) ^ 2 * I ^ 2) * ((x : ℂ) ^ 2 * g x) := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    rw [hfun, fourier_const_mul]
  rw [hd2_lhs, hd2_rhs] at hd2
  have h2pi2 : (2 * (Real.pi : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  apply mul_left_cancel₀ h2pi2
  have hgoal_eq : (2 * (Real.pi : ℂ)) ^ 2 *
      (((Real.sqrt (Real.pi / a) * (1 / (2 * a) - Real.pi ^ 2 * ξ ^ 2 / a ^ 2) : ℝ) : ℂ) *
        Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ)))) =
      -(((Real.sqrt (Real.pi / a) : ℝ) : ℂ) *
        ((-2 * ((Real.pi ^ 2 / a : ℝ) : ℂ) + 4 * ((Real.pi ^ 2 / a : ℝ) : ℂ) ^ 2 * (ξ : ℂ) ^ 2) *
          Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ))))) := by
    push_cast; field_simp [haC]; ring
  rw [hgoal_eq]
  dsimp only [g] at hd2
  linear_combination hd2

/-! ### 5. 3D Radial Kernel `becF t`, Partial Fourier Transforms `g₁, g₂, g₃`, and Iterated 1D Poisson -/

private def becF (t : ℝ) (x₁ x₂ x₃ : ℝ) : ℂ :=
  (((t⁻¹ * phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ))

private def becG1 (t : ℝ) (m₁ : ℝ) (x₂ x₃ : ℝ) : ℂ :=
  𝓕 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) m₁

private def becG2 (t : ℝ) (m₁ m₂ : ℝ) (x₃ : ℝ) : ℂ :=
  𝓕 (fun x₂ : ℝ ↦ becG1 t m₁ x₂ x₃) m₂

private def becG3 (t : ℝ) (m₁ m₂ m₃ : ℝ) : ℂ :=
  𝓕 (fun x₃ : ℝ ↦ becG2 t m₁ m₂ x₃) m₃

private lemma becF_eq_of_ne_zero {t : ℝ} (ht : 0 < t) {x₁ x₂ x₃ : ℝ}
    (h : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 ≠ 0) :
    becF t x₁ x₂ x₃ =
      ((((x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) / (Real.exp (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) - 1) : ℝ) : ℂ)) := by
  unfold becF
  rw [phiKernel_ne_zero_eq (mul_ne_zero ht.ne' h)]
  congr 1; field_simp [ht.ne']

private lemma becF_zero (t : ℝ) : becF t 0 0 0 = ((t⁻¹ : ℝ) : ℂ) := by
  simp [becF, phiKernel_zero]

private lemma becF_exp_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₁ x₂ x₃ : ℝ,
      ‖becF t x₁ x₂ x₃‖ ≤ C * Real.exp (-(t / 2) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
  obtain ⟨C0, hC0, hb0⟩ := phiKernel_iteratedDeriv_exp_bound 0
  refine ⟨t⁻¹ * C0, by positivity, fun x₁ x₂ x₃ ↦ ?_⟩
  simp only [becF, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht]
  have hr : 0 ≤ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by positivity
  have h1 := hb0 _ hr
  rw [iteratedDeriv_zero] at h1
  calc t⁻¹ * |phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
      ≤ t⁻¹ * (C0 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (t⁻¹ * C0) * Real.exp (-(t / 2) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
        rw [mul_assoc]; congr 2; ring

private lemma poly_mul_exp_quarter_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, (x ^ 2) ^ k * Real.exp (-(t / 4) * x ^ 2) ≤ B := by
  refine ⟨(4 / t) ^ k * (k.factorial : ℝ), by positivity, fun x ↦ ?_⟩
  have hu : 0 ≤ (t / 4) * x ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp ((t / 4) * x ^ 2) hu k
  have h1 : ((t / 4) * x ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp ((t / 4) * x ^ 2) :=
    (div_le_iff₀' (by positivity)).mp hexp
  rw [mul_pow] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(t / 4) * x ^ 2)).le
  rw [mul_assoc (k.factorial : ℝ), ← Real.exp_add, show (t / 4) * x ^ 2 + -(t / 4) * x ^ 2 = 0 by ring,
      Real.exp_zero, mul_one] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (4 / t) ^ k by positivity)
  have hcan : (4 / t) ^ k * ((t / 4) ^ k * (x ^ 2) ^ k * Real.exp (-(t / 4) * x ^ 2)) =
      (x ^ 2) ^ k * Real.exp (-(t / 4) * x ^ 2) := by
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, show (4 / t) * (t / 4) = 1 by field_simp [ht.ne'],
        one_pow, one_mul]
  rwa [hcan] at h3

/-- Exact explicit 2nd derivative in `x₁` of `becF t` and its factorized Gaussian bound! -/
private def becF_d11 (t : ℝ) (x₁ x₂ x₃ : ℝ) : ℂ :=
  let r := t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)
  (((2 * iteratedDeriv 1 phiKernel r + 4 * t * x₁ ^ 2 * iteratedDeriv 2 phiKernel r : ℝ) : ℂ))

private def becF_d1122 (t : ℝ) (x₁ x₂ x₃ : ℝ) : ℂ :=
  let r := t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)
  (((4 * t * iteratedDeriv 2 phiKernel r +
     8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * iteratedDeriv 3 phiKernel r +
     16 * t ^ 3 * x₁ ^ 2 * x₂ ^ 2 * iteratedDeriv 4 phiKernel r : ℝ) : ℂ))

private lemma becF_iteratedDeriv_x1 {t : ℝ} (ht : 0 < t) (x₁ x₂ x₃ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ becF t y x₂ x₃) x₁ = becF_d11 t x₁ x₂ x₃ := by
  have hd_phi (k : ℕ) (u : ℝ) :
      HasDerivAt (iteratedDeriv k phiKernel) (iteratedDeriv (k + 1) phiKernel u) u := by
    rw [iteratedDeriv_succ]
    exact ((phiKernel_contDiff (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k) u).hasDerivAt
  have hd_comp (k : ℕ) (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ iteratedDeriv k phiKernel (t * (z ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
        (2 * t * y * iteratedDeriv (k + 1) phiKernel (t * (y ^ 2 + x₂ ^ 2 + x₃ ^ 2))) y := by
    have hin : HasDerivAt (fun z : ℝ ↦ t * (z ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (2 * t * y) y := by
      have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
      convert (((hsq.add_const (x₂ ^ 2)).add_const (x₃ ^ 2)).const_mul t) using 1; ring
    exact ((hd_phi k _).comp y hin).congr_deriv (by ring)
  have hd1 (y : ℝ) : HasDerivAt (fun z : ℝ ↦ becF t z x₂ x₃)
      (((2 * y * iteratedDeriv 1 phiKernel (t * (y ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) y := by
    have h0 := (hd_comp 0 y).const_mul t⁻¹
    rw [iteratedDeriv_zero] at h0
    have h1 := h0.ofReal_comp
    convert h1 using 1
    congr 1; field_simp [ht.ne']
  rw [iteratedDeriv_succ, iteratedDeriv_one, show deriv (fun z : ℝ ↦ becF t z x₂ x₃) =
      fun y : ℝ ↦ (((2 * y * iteratedDeriv 1 phiKernel (t * (y ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) from
        funext fun y ↦ (hd1 y).deriv]
  have hd2 : HasDerivAt (fun y : ℝ ↦ 2 * y * iteratedDeriv 1 phiKernel (t * (y ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
      (2 * iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
        4 * t * x₁ ^ 2 * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))) x₁ := by
    have hl : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x₁ := by simpa using (hasDerivAt_id x₁).const_mul 2
    convert hl.mul (hd_comp 1 x₁) using 1; ring
  exact hd2.ofReal_comp.deriv

private lemma becF_d11_iteratedDeriv_x2 {t : ℝ} (x₁ x₂ x₃ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ becF_d11 t x₁ y x₃) x₂ = becF_d1122 t x₁ x₂ x₃ := by
  have hd_phi (k : ℕ) (u : ℝ) :
      HasDerivAt (iteratedDeriv k phiKernel) (iteratedDeriv (k + 1) phiKernel u) u := by
    rw [iteratedDeriv_succ]
    exact ((phiKernel_contDiff (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k) u).hasDerivAt
  have hd_comp (k : ℕ) (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ iteratedDeriv k phiKernel (t * (x₁ ^ 2 + z ^ 2 + x₃ ^ 2)))
        (2 * t * y * iteratedDeriv (k + 1) phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2))) y := by
    have hin : HasDerivAt (fun z : ℝ ↦ t * (x₁ ^ 2 + z ^ 2 + x₃ ^ 2)) (2 * t * y) y := by
      have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
      convert (((hsq.const_add (x₁ ^ 2)).add_const (x₃ ^ 2)).const_mul t) using 1; ring
    exact ((hd_phi k _).comp y hin).congr_deriv (by ring)
  have hd1 (y : ℝ) : HasDerivAt (fun z : ℝ ↦ becF_d11 t x₁ z x₃)
      (((4 * t * y * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)) +
         8 * t ^ 2 * x₁ ^ 2 * y * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) y := by
    have ha := ((hd_comp 1 y).const_mul 2).add ((hd_comp 2 y).const_mul (4 * t * x₁ ^ 2))
    convert ha.ofReal_comp using 1; congr 1; ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, show deriv (fun z : ℝ ↦ becF_d11 t x₁ z x₃) =
      fun y : ℝ ↦ (((4 * t * y * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)) +
         8 * t ^ 2 * x₁ ^ 2 * y * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) from
        funext fun y ↦ (hd1 y).deriv]
  have hd2 : HasDerivAt (fun y : ℝ ↦
      4 * t * y * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)) +
      8 * t ^ 2 * x₁ ^ 2 * y * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + y ^ 2 + x₃ ^ 2)))
      (4 * t * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
       8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
       16 * t ^ 3 * x₁ ^ 2 * x₂ ^ 2 * iteratedDeriv 4 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))) x₂ := by
    have hl1 : HasDerivAt (fun y : ℝ ↦ 4 * t * y) (4 * t) x₂ := by simpa using (hasDerivAt_id x₂).const_mul (4 * t)
    have hl2 : HasDerivAt (fun y : ℝ ↦ 8 * t ^ 2 * x₁ ^ 2 * y) (8 * t ^ 2 * x₁ ^ 2) x₂ := by
      simpa using (hasDerivAt_id x₂).const_mul (8 * t ^ 2 * x₁ ^ 2)
    convert (hl1.mul (hd_comp 2 x₂)).add (hl2.mul (hd_comp 3 x₂)) using 1; ring
  exact hd2.ofReal_comp.deriv

private lemma becF_d11_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₁ x₂ x₃ : ℝ,
      ‖becF_d11 t x₁ x₂ x₃‖ ≤ C * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
  obtain ⟨C1, hC1, hb1⟩ := phiKernel_iteratedDeriv_exp_bound 1
  obtain ⟨C2, hC2, hb2⟩ := phiKernel_iteratedDeriv_exp_bound 2
  obtain ⟨B1, hB1, hp1⟩ := poly_mul_exp_quarter_le ht 1
  refine ⟨2 * C1 + 4 * t * C2 * B1, by positivity, fun x₁ x₂ x₃ ↦ ?_⟩
  simp only [becF_d11, Complex.norm_real, Real.norm_eq_abs]
  have hr : 0 ≤ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by positivity
  have h1 := hb1 _ hr
  have h2 := hb2 _ hr
  have he_split : Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2) =
      Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
      Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
  have he_le1 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃])
  have he_x1 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ Real.exp (-(t / 4) * x₁ ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₂, sq_nonneg x₃])
  have hx1_bd : x₁ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ B1 := by
    calc x₁ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))
        ≤ x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2) := mul_le_mul_of_nonneg_left he_x1 (sq_nonneg _)
      _ ≤ B1 := by simpa using hp1 x₁
  calc _ ≤ |2 * iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| +
          |4 * t * x₁ ^ 2 * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| := abs_add_le _ _
    _ ≤ 2 * (C1 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) +
        4 * t * x₁ ^ 2 * (C2 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) := by
        rw [abs_mul, abs_of_pos zero_lt_two, abs_mul, abs_of_nonneg (show 0 ≤ 4 * t * x₁ ^ 2 by positivity)]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 zero_le_two)
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = 2 * C1 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
          Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
        4 * t * C2 * (x₁ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))) *
          Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [he_split]; ring
    _ ≤ 2 * C1 * 1 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
        4 * t * C2 * B1 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by gcongr
    _ = (2 * C1 + 4 * t * C2 * B1) * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by ring

private lemma becF_d1122_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₁ x₂ x₃ : ℝ,
      ‖becF_d1122 t x₁ x₂ x₃‖ ≤ C * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
  obtain ⟨C2, hC2, hb2⟩ := phiKernel_iteratedDeriv_exp_bound 2
  obtain ⟨C3, hC3, hb3⟩ := phiKernel_iteratedDeriv_exp_bound 3
  obtain ⟨C4, hC4, hb4⟩ := phiKernel_iteratedDeriv_exp_bound 4
  obtain ⟨B1, hB1, hp1⟩ := poly_mul_exp_quarter_le ht 1
  refine ⟨4 * t * C2 + 16 * t ^ 2 * C3 * B1 + 16 * t ^ 3 * C4 * B1 ^ 2, by positivity, fun x₁ x₂ x₃ ↦ ?_⟩
  simp only [becF_d1122, Complex.norm_real, Real.norm_eq_abs]
  have hr : 0 ≤ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by positivity
  have h2 := hb2 _ hr; have h3 := hb3 _ hr; have h4 := hb4 _ hr
  have he_split : Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2) =
      Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
      Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
  have he_le1 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃])
  have hx1_bd : x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2) ≤ B1 := by simpa using hp1 x₁
  have hx2_bd : x₂ ^ 2 * Real.exp (-(t / 4) * x₂ ^ 2) ≤ B1 := by simpa using hp1 x₂
  have hx12_bd : x₁ ^ 2 * x₂ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ B1 ^ 2 := by
    have he12 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤
        Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg x₃]
    calc x₁ ^ 2 * x₂ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))
        ≤ x₁ ^ 2 * x₂ ^ 2 * (Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2)) :=
          mul_le_mul_of_nonneg_left he12 (by positivity)
      _ = (x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2)) * (x₂ ^ 2 * Real.exp (-(t / 4) * x₂ ^ 2)) := by ring
      _ ≤ B1 * B1 := mul_le_mul hx1_bd hx2_bd (by positivity) hB1
      _ = B1 ^ 2 := by ring
  have hxsum_bd : (x₁ ^ 2 + x₂ ^ 2) * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ 2 * B1 := by
    have he1 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ Real.exp (-(t / 4) * x₁ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₂, sq_nonneg x₃])
    have he2 : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤ Real.exp (-(t / 4) * x₂ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg x₃])
    rw [add_mul]
    linarith [mul_le_mul_of_nonneg_left he1 (sq_nonneg x₁), mul_le_mul_of_nonneg_left he2 (sq_nonneg x₂)]
  have htri1 := abs_add_le
    (4 * t * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
      8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
    (16 * t ^ 3 * x₁ ^ 2 * x₂ ^ 2 * iteratedDeriv 4 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
  have htri2 := abs_add_le
    (4 * t * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
    (8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
  have habs1 : |4 * t * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| ≤
      4 * t * C2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 4 * t * |iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
        ≤ 4 * t * (C2 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * t * C2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
            Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [he_split]; ring
      _ ≤ 4 * t * C2 * 1 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by gcongr
      _ = _ := by ring
  have habs2 : |8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| ≤
      16 * t ^ 2 * C3 * B1 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc _ ≤ 8 * t ^ 2 * (x₁ ^ 2 + x₂ ^ 2) * (C3 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 8 * t ^ 2 * C3 * ((x₁ ^ 2 + x₂ ^ 2) * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))) *
            Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [he_split]; ring
      _ ≤ 8 * t ^ 2 * C3 * (2 * B1) * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by gcongr
      _ = _ := by ring
  have habs3 : |16 * t ^ 3 * x₁ ^ 2 * x₂ ^ 2 * iteratedDeriv 4 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| ≤
      16 * t ^ 3 * C4 * B1 ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc _ ≤ 16 * t ^ 3 * x₁ ^ 2 * x₂ ^ 2 * (C4 * Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 16 * t ^ 3 * C4 * (x₁ ^ 2 * x₂ ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))) *
            Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by rw [he_split]; ring
      _ ≤ 16 * t ^ 3 * C4 * B1 ^ 2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by gcongr
  linarith

/-- Decay of `becG1 t m₁ x₂ x₃` in `(m₁, x₂, x₃)` via order-2 `Real.fourier_iteratedDeriv`! -/
private lemma becG1_bound {t : ℝ} (ht : 0 < t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m₁ x₂ x₃ : ℝ,
      ‖becG1 t m₁ x₂ x₃‖ ≤ (K / (1 + m₁ ^ 2)) * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by
  obtain ⟨C0, hC0, hb0⟩ := becF_exp_bound ht
  obtain ⟨C2, hC2, hb2⟩ := becF_d11_bound ht
  let I0 : ℝ := ∫ x : ℝ, Real.exp (-(t / 4) * x ^ 2)
  have hI0_nn : 0 ≤ I0 := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hG_int : Integrable (fun x : ℝ ↦ Real.exp (-(t / 4) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  let K : ℝ := (C0 + C2 / (4 * Real.pi ^ 2)) * I0
  refine ⟨K, by positivity, fun m₁ x₂ x₃ ↦ ?_⟩
  have hbd0 : ‖becG1 t m₁ x₂ x₃‖ ≤ C0 * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by
    rw [becG1, Real.fourier_real_eq_integral_exp_smul]
    calc ‖∫ x₁ : ℝ, Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) • becF t x₁ x₂ x₃‖
        ≤ ∫ x₁ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) • becF t x₁ x₂ x₃‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x₁ : ℝ, (C0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2))) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hG_int.const_mul _) (Eventually.of_forall fun x₁ ↦ ?_)
          dsimp only
          rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
          have h1 := hb0 x₁ x₂ x₃
          have he : Real.exp (-(t / 2) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤
              Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
          exact h1.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he hC0)
      _ = C0 * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by rw [integral_const_mul]; dsimp [I0]; ring
  have hbd2 : (4 * Real.pi ^ 2 * m₁ ^ 2) * ‖becG1 t m₁ x₂ x₃‖ ≤
      C2 * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by
    have hcd : ContDiff ℝ (2 : ℕ∞) (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) := by
      unfold becF
      have hr : ContDiff ℝ 2 (fun x₁ : ℝ ↦ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by fun_prop
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ((phiKernel_contDiff 2).comp hr))
    have hint_n : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃)) := by
      intro n hn
      have hn2 : n ≤ 2 := by exact_mod_cast hn
      interval_cases n
      · refine (hG_int.const_mul (C0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)))).mono'
            (hcd.continuous.aestronglyMeasurable) (Eventually.of_forall fun x₁ ↦ ?_)
        rw [iteratedDeriv_zero]
        have he : Real.exp (-(t / 2) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤
            Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
        exact (hb0 x₁ x₂ x₃).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he hC0)
      · obtain ⟨C1, hC1, hb1⟩ := phiKernel_iteratedDeriv_exp_bound 1
        obtain ⟨B1, hB1, hp1⟩ := poly_mul_exp_quarter_le ht 1
        have hd1 : iteratedDeriv 1 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) = fun x₁ : ℝ ↦
            (((2 * x₁ * iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) := by
          funext x₁; rw [iteratedDeriv_one]
          have hd_phi : HasDerivAt phiKernel (iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
              (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
            rw [iteratedDeriv_one]
            exact ((phiKernel_contDiff 1).differentiable one_ne_zero _).hasDerivAt
          have hin : HasDerivAt (fun z : ℝ ↦ t * (z ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (2 * t * x₁) x₁ := by
            have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * x₁) x₁ := by simpa using hasDerivAt_pow 2 x₁
            convert (((hsq.add_const (x₂ ^ 2)).add_const (x₃ ^ 2)).const_mul t) using 1; ring
          have h0 := ((hd_phi.comp x₁ hin).const_mul t⁻¹).ofReal_comp
          convert h0.deriv using 1; congr 1; field_simp [ht.ne']
        rw [hd1]
        refine (hG_int.const_mul (2 * C1 * (1 + B1))).mono'
            ((hcd.continuous_iteratedDeriv 1 (by norm_num)).congr (congrFun hd1)).aestronglyMeasurable
            (Eventually.of_forall fun x₁ ↦ ?_)
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (zero_lt_two (α := ℝ))]
        have hr : 0 ≤ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by positivity
        have h1 := hb1 (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) hr
        have hx1_le : |x₁| ≤ 1 + x₁ ^ 2 := by nlinarith [sq_abs x₁, sq_nonneg (|x₁| - 1)]
        have he_split : Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2) ≤
            Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg x₂, sq_nonneg x₃]
        have he_le1 : Real.exp (-(t / 4) * x₁ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x₁])
        have hx2_bd : x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2) ≤ B1 := by simpa using hp1 x₁
        calc 2 * |x₁| * |iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
            ≤ 2 * (1 + x₁ ^ 2) * (C1 * (Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hx1_le zero_le_two)
                (h1.trans (mul_le_mul_of_nonneg_left he_split hC1)) (abs_nonneg _) (by positivity)
          _ = 2 * C1 * (Real.exp (-(t / 4) * x₁ ^ 2) + x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2)) *
                Real.exp (-(t / 4) * x₁ ^ 2) := by ring
          _ ≤ 2 * C1 * (1 + B1) * Real.exp (-(t / 4) * x₁ ^ 2) := by gcongr
      · have hd2 : iteratedDeriv 2 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) = fun x₁ ↦ becF_d11 t x₁ x₂ x₃ :=
          funext fun x₁ ↦ becF_iteratedDeriv_x1 ht x₁ x₂ x₃
        rw [hd2]
        refine (hG_int.const_mul (C2 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)))).mono'
            ((hcd.continuous_iteratedDeriv 2 le_rfl).congr (congrFun hd2)).aestronglyMeasurable
            (Eventually.of_forall fun x₁ ↦ ?_)
        have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
            Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        exact (hb2 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
    have hF2 := congrFun (Real.fourier_iteratedDeriv hcd hint_n le_rfl) m₁
    have hnorm_lhs : ‖(2 * (Real.pi : ℂ) * I * (m₁ : ℂ)) ^ 2 • becG1 t m₁ x₂ x₃‖ =
        (4 * Real.pi ^ 2 * m₁ ^ 2) * ‖becG1 t m₁ x₂ x₃‖ := by
      rw [smul_eq_mul, norm_mul, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
          Complex.norm_real, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, mul_one]
      rw [mul_pow, mul_pow, sq_abs]; ring
    rw [← hnorm_lhs, becG1, ← hF2]
    have hd2 : iteratedDeriv 2 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) = fun x₁ ↦ becF_d11 t x₁ x₂ x₃ :=
      funext fun x₁ ↦ becF_iteratedDeriv_x1 ht x₁ x₂ x₃
    rw [hd2, Real.fourier_real_eq_integral_exp_smul]
    calc ‖∫ x₁ : ℝ, Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) • becF_d11 t x₁ x₂ x₃‖
        ≤ ∫ x₁ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) • becF_d11 t x₁ x₂ x₃‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x₁ : ℝ, (C2 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2))) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hG_int.const_mul _) (Eventually.of_forall fun x₁ ↦ ?_)
          dsimp only
          rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
          have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
              Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
          exact (hb2 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
      _ = C2 * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by rw [integral_const_mul]; dsimp [I0]; ring
  have hdiv : m₁ ^ 2 * ‖becG1 t m₁ x₂ x₃‖ ≤ (C2 / (4 * Real.pi ^ 2)) * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by
    have h4pi : 0 < 4 * Real.pi ^ 2 := by positivity
    rw [show (C2 / (4 * Real.pi ^ 2)) * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) =
        (C2 * I0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2))) / (4 * Real.pi ^ 2) by ring,
        le_div_iff₀' h4pi]
    linarith
  have hadd : (1 + m₁ ^ 2) * ‖becG1 t m₁ x₂ x₃‖ ≤ K * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) := by
    dsimp only [K]; linarith
  rw [div_mul_eq_mul_div, le_div_iff₀' (by positivity : 0 < 1 + m₁ ^ 2)]
  exact hadd

/-- Decay of `becG2 t m₁ m₂ x₃` in `(m₁, m₂, x₃)` via Fubini + order-2 `Real.fourier_iteratedDeriv`! -/
private lemma becG2_bound {t : ℝ} (ht : 0 < t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m₁ m₂ x₃ : ℝ,
      ‖becG2 t m₁ m₂ x₃‖ ≤ (K / ((1 + m₁ ^ 2) * (1 + m₂ ^ 2))) * Real.exp (-(t / 4) * x₃ ^ 2) := by
  obtain ⟨C0, hC0, hb0⟩ := becF_exp_bound ht
  obtain ⟨C2, hC2, hb2⟩ := becF_d11_bound ht
  obtain ⟨C4, hC4, hb4⟩ := becF_d1122_bound ht
  let I0 : ℝ := ∫ x : ℝ, Real.exp (-(t / 4) * x ^ 2)
  have hI0_nn : 0 ≤ I0 := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hG_int : Integrable (fun x : ℝ ↦ Real.exp (-(t / 4) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hF_symm (x₁ x₂ x₃ : ℝ) : becF t x₁ x₂ x₃ = becF t x₂ x₁ x₃ := by
    simp only [becF]; congr 3; ring
  have hG2_swap (m₁ m₂ x₃ : ℝ) : becG2 t m₁ m₂ x₃ = becG2 t m₂ m₁ x₃ := by
    simp only [becG2, becG1, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    have hmul_in (a b : ℝ) (f : ℝ → ℝ → ℂ) :
        (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * b) * I) *
          ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * a) * I) * f x y) =
        ∫ y : ℝ, ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * y * b) * I) *
          (Complex.exp (↑(-2 * Real.pi * x * a) * I) * f x y) := by
      congr 1; funext y; rw [← integral_const_mul]
    rw [hmul_in m₁ m₂ (fun x y ↦ becF t x y x₃), hmul_in m₂ m₁ (fun x y ↦ becF t x y x₃)]
    have hprod_int : Integrable (fun p : ℝ × ℝ ↦
        Complex.exp (↑(-2 * Real.pi * p.1 * m₂) * I) *
          (Complex.exp (↑(-2 * Real.pi * p.2 * m₁) * I) * becF t p.2 p.1 x₃))
        (volume.prod volume) := by
      have hdom : Integrable (fun p : ℝ × ℝ ↦
          (C0 * Real.exp (-(t / 4) * x₃ ^ 2)) *
            (Real.exp (-(t / 4) * p.1 ^ 2) * Real.exp (-(t / 4) * p.2 ^ 2))) (volume.prod volume) :=
        (hG_int.mul_prod hG_int).const_mul _
      refine hdom.mono' ?_ (Eventually.of_forall fun p ↦ ?_)
      · have hcont : Continuous (fun p : ℝ × ℝ ↦ becF t p.2 p.1 x₃) := by
          unfold becF
          have hphi : Continuous phiKernel := (phiKernel_contDiff 0).continuous
          exact Complex.continuous_ofReal.comp (continuous_const.mul (hphi.comp (by fun_prop)))
        exact (((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (↑(-2 * Real.pi * p.1 * m₂) * I)).mul
          ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (↑(-2 * Real.pi * p.2 * m₁) * I)).mul
            hcont))).aestronglyMeasurable
      · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
            one_mul, one_mul]
        have he : Real.exp (-(t / 2) * (p.2 ^ 2 + p.1 ^ 2 + x₃ ^ 2)) ≤
            Real.exp (-(t / 4) * x₃ ^ 2) * (Real.exp (-(t / 4) * p.1 ^ 2) * Real.exp (-(t / 4) * p.2 ^ 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_nonneg x₃]
        exact (hb0 p.2 p.1 x₃).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he hC0)
    rw [integral_integral_swap hprod_int]
    congr 1; funext x; congr 1; funext y
    rw [hF_symm x y x₃]; ring
  -- Bound the four terms `1`, `m₁²`, `m₂²`, `m₁² m₂²` multiplying `‖becG2 t m₁ m₂ x₃‖`!
  obtain ⟨K1, hK1, hbG1⟩ := becG1_bound ht
  let K : ℝ := K1 * I0 + K1 * I0 + (C4 / (16 * Real.pi ^ 4)) * I0 ^ 2
  refine ⟨K, by positivity, fun m₁ m₂ x₃ ↦ ?_⟩
  have h1m1 : (1 + m₁ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ ≤ K1 * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
    have hnorm_g2 : ‖becG2 t m₁ m₂ x₃‖ ≤ (K1 / (1 + m₁ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
      rw [becG2, Real.fourier_real_eq_integral_exp_smul]
      calc ‖∫ x₂ : ℝ, Complex.exp (↑(-2 * Real.pi * x₂ * m₂) * I) • becG1 t m₁ x₂ x₃‖
          ≤ ∫ x₂ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₂ * m₂) * I) • becG1 t m₁ x₂ x₃‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x₂ : ℝ, ((K1 / (1 + m₁ ^ 2)) * Real.exp (-(t / 4) * x₃ ^ 2)) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
              (hG_int.const_mul _) (Eventually.of_forall fun x₂ ↦ ?_)
            dsimp only
            rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
            have he : Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) =
                Real.exp (-(t / 4) * x₃ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2) := by
              rw [← Real.exp_add]; congr 1; ring
            exact (hbG1 m₁ x₂ x₃).trans_eq (by rw [he]; ring)
        _ = (K1 / (1 + m₁ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
            rw [integral_const_mul]; dsimp [I0]; ring
    have hpos : 0 < 1 + m₁ ^ 2 := by positivity
    calc (1 + m₁ ^ 2) * ‖becG2 t m₁ m₂ x₃‖
        ≤ (1 + m₁ ^ 2) * ((K1 / (1 + m₁ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2)) :=
          mul_le_mul_of_nonneg_left hnorm_g2 hpos.le
      _ = K1 * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by field_simp [hpos.ne']
  have h1m2 : (1 + m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ ≤ K1 * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
    rw [hG2_swap m₁ m₂ x₃]
    have hnorm_g2 : ‖becG2 t m₂ m₁ x₃‖ ≤ (K1 / (1 + m₂ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
      rw [becG2, Real.fourier_real_eq_integral_exp_smul]
      calc ‖∫ x₂ : ℝ, Complex.exp (↑(-2 * Real.pi * x₂ * m₁) * I) • becG1 t m₂ x₂ x₃‖
          ≤ ∫ x₂ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₂ * m₁) * I) • becG1 t m₂ x₂ x₃‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x₂ : ℝ, ((K1 / (1 + m₂ ^ 2)) * Real.exp (-(t / 4) * x₃ ^ 2)) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
              (hG_int.const_mul _) (Eventually.of_forall fun x₂ ↦ ?_)
            dsimp only
            rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
            have he : Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) =
                Real.exp (-(t / 4) * x₃ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2) := by
              rw [← Real.exp_add]; congr 1; ring
            exact (hbG1 m₂ x₂ x₃).trans_eq (by rw [he]; ring)
        _ = (K1 / (1 + m₂ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by
            rw [integral_const_mul]; dsimp [I0]; ring
    have hpos : 0 < 1 + m₂ ^ 2 := by positivity
    calc (1 + m₂ ^ 2) * ‖becG2 t m₂ m₁ x₃‖
        ≤ (1 + m₂ ^ 2) * ((K1 / (1 + m₂ ^ 2)) * I0 * Real.exp (-(t / 4) * x₃ ^ 2)) :=
          mul_le_mul_of_nonneg_left hnorm_g2 hpos.le
      _ = K1 * I0 * Real.exp (-(t / 4) * x₃ ^ 2) := by field_simp [hpos.ne']
  -- Mixed `(2πi m₁)² (2πi m₂)² becG2 = ∬ e^{-2πi(m₁x₁+m₂x₂)} becF_d1122 dx₂ dx₁`!
  have hm12 : (16 * Real.pi ^ 4 * m₁ ^ 2 * m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ ≤
      C4 * I0 ^ 2 * Real.exp (-(t / 4) * x₃ ^ 2) := by
    have hstep1 (x₂ : ℝ) : (2 * (Real.pi : ℂ) * I * (m₁ : ℂ)) ^ 2 * becG1 t m₁ x₂ x₃ =
        𝓕 (fun x₁ : ℝ ↦ becF_d11 t x₁ x₂ x₃) m₁ := by
      have hcd : ContDiff ℝ (2 : ℕ∞) (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) := by
        unfold becF
        have hr : ContDiff ℝ 2 (fun x₁ : ℝ ↦ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by fun_prop
        exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ((phiKernel_contDiff 2).comp hr))
      have hint_n : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃)) := by
        intro n hn; have hn2 : n ≤ 2 := by exact_mod_cast hn
        interval_cases n
        · refine (hG_int.const_mul (C0 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)))).mono'
              hcd.continuous.aestronglyMeasurable (Eventually.of_forall fun x₁ ↦ ?_)
          rw [iteratedDeriv_zero]
          have he : Real.exp (-(t / 2) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) ≤
              Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
          exact (hb0 x₁ x₂ x₃).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he hC0)
        · obtain ⟨C1, hC1, hb1⟩ := phiKernel_iteratedDeriv_exp_bound 1
          obtain ⟨B1, hB1, hp1⟩ := poly_mul_exp_quarter_le ht 1
          have hd1 : iteratedDeriv 1 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) = fun x₁ : ℝ ↦
              (((2 * x₁ * iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) := by
            funext x₁; rw [iteratedDeriv_one]
            have hd_phi : HasDerivAt phiKernel (iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
                (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
              rw [iteratedDeriv_one]; exact ((phiKernel_contDiff 1).differentiable one_ne_zero _).hasDerivAt
            have hin : HasDerivAt (fun z : ℝ ↦ t * (z ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (2 * t * x₁) x₁ := by
              have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * x₁) x₁ := by simpa using hasDerivAt_pow 2 x₁
              convert (((hsq.add_const (x₂ ^ 2)).add_const (x₃ ^ 2)).const_mul t) using 1; ring
            convert ((hd_phi.comp x₁ hin).const_mul t⁻¹).ofReal_comp.deriv using 1; congr 1; field_simp [ht.ne']
          rw [hd1]
          refine (hG_int.const_mul (2 * C1 * (1 + B1))).mono'
              ((hcd.continuous_iteratedDeriv 1 (by norm_num)).congr (congrFun hd1)).aestronglyMeasurable
              (Eventually.of_forall fun x₁ ↦ ?_)
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (zero_lt_two (α := ℝ))]
          have h1 := hb1 (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (by positivity)
          have hx1_le : |x₁| ≤ 1 + x₁ ^ 2 := by nlinarith [sq_abs x₁, sq_nonneg (|x₁| - 1)]
          have he_split : Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2) ≤
              Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg x₂, sq_nonneg x₃]
          have he_le1 : Real.exp (-(t / 4) * x₁ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x₁])
          have hx2_bd : x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2) ≤ B1 := by simpa using hp1 x₁
          calc 2 * |x₁| * |iteratedDeriv 1 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
              ≤ 2 * (1 + x₁ ^ 2) * (C1 * (Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2))) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hx1_le zero_le_two)
                  (h1.trans (mul_le_mul_of_nonneg_left he_split hC1)) (abs_nonneg _) (by positivity)
            _ = 2 * C1 * (Real.exp (-(t / 4) * x₁ ^ 2) + x₁ ^ 2 * Real.exp (-(t / 4) * x₁ ^ 2)) *
                  Real.exp (-(t / 4) * x₁ ^ 2) := by ring
            _ ≤ 2 * C1 * (1 + B1) * Real.exp (-(t / 4) * x₁ ^ 2) := by gcongr
        · have hd2 : iteratedDeriv 2 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) = fun x₁ ↦ becF_d11 t x₁ x₂ x₃ :=
            funext fun x₁ ↦ becF_iteratedDeriv_x1 ht x₁ x₂ x₃
          rw [hd2]
          refine (hG_int.const_mul (C2 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)))).mono'
              ((hcd.continuous_iteratedDeriv 2 le_rfl).congr (congrFun hd2)).aestronglyMeasurable
              (Eventually.of_forall fun x₁ ↦ ?_)
          have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
              Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
          exact (hb2 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
      have hF2 := (congrFun (Real.fourier_iteratedDeriv hcd hint_n le_rfl) m₁).symm
      simpa only [smul_eq_mul, becG1, show iteratedDeriv 2 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) =
        fun x₁ ↦ becF_d11 t x₁ x₂ x₃ from funext fun x₁ ↦ becF_iteratedDeriv_x1 ht x₁ x₂ x₃] using hF2
    have hstep2 (x₁ : ℝ) : (2 * (Real.pi : ℂ) * I * (m₂ : ℂ)) ^ 2 *
        𝓕 (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃) m₂ =
        𝓕 (fun x₂ : ℝ ↦ becF_d1122 t x₁ x₂ x₃) m₂ := by
      have hcd : ContDiff ℝ (2 : ℕ∞) (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃) := by
        unfold becF_d11
        have hr : ContDiff ℝ 2 (fun x₂ : ℝ ↦ t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by fun_prop
        have hc1 : ContDiff ℝ 2 (iteratedDeriv 1 phiKernel) :=
          (contDiff_succ_iff_deriv.mp (phiKernel_contDiff 3)).2.2 |> fun h ↦ by
            simpa only [iteratedDeriv_one] using h
        have hc2 : ContDiff ℝ 2 (iteratedDeriv 2 phiKernel) := by
          have hc1' : ContDiff ℝ 3 (deriv phiKernel) := (contDiff_succ_iff_deriv.mp (phiKernel_contDiff 4)).2.2
          rw [show iteratedDeriv 2 phiKernel = deriv (deriv phiKernel) by ext u; simp [iteratedDeriv_succ]]
          exact (contDiff_succ_iff_deriv.mp hc1').2.2
        exact Complex.ofRealCLM.contDiff.comp
          ((contDiff_const.mul (hc1.comp hr)).add (contDiff_const.mul (hc2.comp hr)))
      have hint_n : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃)) := by
        intro n hn; have hn2 : n ≤ 2 := by exact_mod_cast hn
        interval_cases n
        · refine (hG_int.const_mul (C2 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₃ ^ 2)))).mono'
              hcd.continuous.aestronglyMeasurable (Eventually.of_forall fun x₂ ↦ ?_)
          rw [iteratedDeriv_zero]
          have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
              Real.exp (-(t / 4) * (x₁ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
          exact (hb2 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
        · obtain ⟨C2', hC2', hb2'⟩ := phiKernel_iteratedDeriv_exp_bound 2
          obtain ⟨C3', hC3', hb3'⟩ := phiKernel_iteratedDeriv_exp_bound 3
          obtain ⟨B1, hB1, hp1⟩ := poly_mul_exp_quarter_le ht 1
          have hd1 : iteratedDeriv 1 (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃) = fun x₂ : ℝ ↦
              (((4 * t * x₂ * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) +
                 8 * t ^ 2 * x₁ ^ 2 * x₂ * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) : ℝ) : ℂ)) := by
            funext x₂; rw [iteratedDeriv_one]
            have hd_phi (k : ℕ) (u : ℝ) : HasDerivAt (iteratedDeriv k phiKernel) (iteratedDeriv (k + 1) phiKernel u) u := by
              rw [iteratedDeriv_succ]
              exact ((phiKernel_contDiff (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k) u).hasDerivAt
            have hin : HasDerivAt (fun z : ℝ ↦ t * (x₁ ^ 2 + z ^ 2 + x₃ ^ 2)) (2 * t * x₂) x₂ := by
              have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * x₂) x₂ := by simpa using hasDerivAt_pow 2 x₂
              convert (((hsq.const_add (x₁ ^ 2)).add_const (x₃ ^ 2)).const_mul t) using 1; ring
            have ha := ((((hd_phi 1 _).comp x₂ hin).const_mul 2).add
              (((hd_phi 2 _).comp x₂ hin).const_mul (4 * t * x₁ ^ 2))).ofReal_comp
            exact ha.deriv.trans (by congr 1; ring)
          rw [hd1]
          refine (hG_int.const_mul ((4 * t * C2' + 8 * t ^ 2 * x₁ ^ 2 * C3') * (1 + B1))).mono'
              ((hcd.continuous_iteratedDeriv 1 (by norm_num)).congr (congrFun hd1)).aestronglyMeasurable
              (Eventually.of_forall fun x₂ ↦ ?_)
          simp only [Complex.norm_real, Real.norm_eq_abs]
          have h2' := hb2' (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (by positivity)
          have h3' := hb3' (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) (by positivity)
          have hx2_le : |x₂| ≤ 1 + x₂ ^ 2 := by nlinarith [sq_abs x₂, sq_nonneg (|x₂| - 1)]
          have he_split : Real.exp (-(t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) / 2) ≤
              Real.exp (-(t / 4) * x₂ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg x₁, sq_nonneg x₃]
          have he_le1 : Real.exp (-(t / 4) * x₂ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x₂])
          have hx2_bd : x₂ ^ 2 * Real.exp (-(t / 4) * x₂ ^ 2) ≤ B1 := by simpa using hp1 x₂
          have htri := abs_add_le
            (4 * t * x₂ * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
            (8 * t ^ 2 * x₁ ^ 2 * x₂ * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)))
          have ha1 : |4 * t * x₂ * iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| ≤
              4 * t * C2' * (1 + B1) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            rw [abs_mul, abs_mul, abs_of_pos (show 0 < 4 * t by positivity)]
            calc 4 * t * |x₂| * |iteratedDeriv 2 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
                ≤ 4 * t * (1 + x₂ ^ 2) * (C2' * (Real.exp (-(t / 4) * x₂ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2))) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hx2_le (by positivity))
                    (h2'.trans (mul_le_mul_of_nonneg_left he_split hC2')) (abs_nonneg _) (by positivity)
              _ = 4 * t * C2' * (Real.exp (-(t / 4) * x₂ ^ 2) + x₂ ^ 2 * Real.exp (-(t / 4) * x₂ ^ 2)) *
                    Real.exp (-(t / 4) * x₂ ^ 2) := by ring
              _ ≤ 4 * t * C2' * (1 + B1) * Real.exp (-(t / 4) * x₂ ^ 2) := by gcongr
          have ha2 : |8 * t ^ 2 * x₁ ^ 2 * x₂ * iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))| ≤
              8 * t ^ 2 * x₁ ^ 2 * C3' * (1 + B1) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ 8 * t ^ 2 * x₁ ^ 2 by positivity)]
            calc 8 * t ^ 2 * x₁ ^ 2 * |x₂| * |iteratedDeriv 3 phiKernel (t * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2))|
                ≤ 8 * t ^ 2 * x₁ ^ 2 * (1 + x₂ ^ 2) * (C3' * (Real.exp (-(t / 4) * x₂ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2))) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hx2_le (by positivity))
                    (h3'.trans (mul_le_mul_of_nonneg_left he_split hC3')) (abs_nonneg _) (by positivity)
              _ = 8 * t ^ 2 * x₁ ^ 2 * C3' * (Real.exp (-(t / 4) * x₂ ^ 2) + x₂ ^ 2 * Real.exp (-(t / 4) * x₂ ^ 2)) *
                    Real.exp (-(t / 4) * x₂ ^ 2) := by ring
              _ ≤ 8 * t ^ 2 * x₁ ^ 2 * C3' * (1 + B1) * Real.exp (-(t / 4) * x₂ ^ 2) := by gcongr
          linarith
        · have hd2 : iteratedDeriv 2 (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃) = fun x₂ ↦ becF_d1122 t x₁ x₂ x₃ :=
            funext fun x₂ ↦ becF_d11_iteratedDeriv_x2 x₁ x₂ x₃
          rw [hd2]
          refine (hG_int.const_mul (C4 * Real.exp (-(t / 4) * (x₁ ^ 2 + x₃ ^ 2)))).mono'
              ((hcd.continuous_iteratedDeriv 2 le_rfl).congr (congrFun hd2)).aestronglyMeasurable
              (Eventually.of_forall fun x₂ ↦ ?_)
          have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
              Real.exp (-(t / 4) * (x₁ ^ 2 + x₃ ^ 2)) * Real.exp (-(t / 4) * x₂ ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
          exact (hb4 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
      have hF2 := (congrFun (Real.fourier_iteratedDeriv hcd hint_n le_rfl) m₂).symm
      simpa only [smul_eq_mul, show iteratedDeriv 2 (fun x₂ : ℝ ↦ becF_d11 t x₁ x₂ x₃) =
        fun x₂ ↦ becF_d1122 t x₁ x₂ x₃ from funext fun x₂ ↦ becF_d11_iteratedDeriv_x2 x₁ x₂ x₃] using hF2
    have hprod_d11 : Integrable (fun p : ℝ × ℝ ↦
        Complex.exp (↑(-2 * Real.pi * p.1 * m₂) * I) *
          (Complex.exp (↑(-2 * Real.pi * p.2 * m₁) * I) * becF_d11 t p.2 p.1 x₃))
        (volume.prod volume) := by
      have hdom : Integrable (fun p : ℝ × ℝ ↦
          (C2 * Real.exp (-(t / 4) * x₃ ^ 2)) *
            (Real.exp (-(t / 4) * p.1 ^ 2) * Real.exp (-(t / 4) * p.2 ^ 2))) (volume.prod volume) :=
        (hG_int.mul_prod hG_int).const_mul _
      refine hdom.mono' ?_ (Eventually.of_forall fun p ↦ ?_)
      · have hcont : Continuous (fun p : ℝ × ℝ ↦ becF_d11 t p.2 p.1 x₃) := by
          unfold becF_d11
          have hc1 : Continuous (iteratedDeriv 1 phiKernel) := (phiKernel_contDiff 1).continuous_iteratedDeriv 1 le_rfl
          have hc2 : Continuous (iteratedDeriv 2 phiKernel) := (phiKernel_contDiff 2).continuous_iteratedDeriv 2 le_rfl
          exact Complex.continuous_ofReal.comp
            ((continuous_const.mul (hc1.comp (by fun_prop))).add
              ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ 4 * t * p.2 ^ 2).mul (hc2.comp (by fun_prop))))
        exact (((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (↑(-2 * Real.pi * p.1 * m₂) * I)).mul
          ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (↑(-2 * Real.pi * p.2 * m₁) * I)).mul
            hcont))).aestronglyMeasurable
      · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
            one_mul, one_mul]
        have he : Real.exp (-(t / 4) * (p.2 ^ 2 + p.1 ^ 2 + x₃ ^ 2)) =
            Real.exp (-(t / 4) * x₃ ^ 2) * (Real.exp (-(t / 4) * p.1 ^ 2) * Real.exp (-(t / 4) * p.2 ^ 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        exact (hb2 p.2 p.1 x₃).trans_eq (by rw [he]; ring)
    have hid : (2 * (Real.pi : ℂ) * I * (m₂ : ℂ)) ^ 2 * ((2 * (Real.pi : ℂ) * I * (m₁ : ℂ)) ^ 2 * becG2 t m₁ m₂ x₃) =
        ∫ x₁ : ℝ, Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) *
          𝓕 (fun x₂ : ℝ ↦ becF_d1122 t x₁ x₂ x₃) m₂ := by
      have h1 : (2 * (Real.pi : ℂ) * I * (m₁ : ℂ)) ^ 2 * becG2 t m₁ m₂ x₃ =
          ∫ x₂ : ℝ, ∫ x₁ : ℝ, Complex.exp (↑(-2 * Real.pi * x₂ * m₂) * I) *
            (Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) * becF_d11 t x₁ x₂ x₃) := by
        rw [becG2, ← fourier_const_mul]
        simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
        congr 1; funext x₂
        rw [hstep1 x₂, Real.fourier_real_eq_integral_exp_smul]
        simp only [smul_eq_mul, ← integral_const_mul]
      rw [h1, integral_integral_swap hprod_d11, ← integral_const_mul]
      congr 1; funext x₁
      rw [← hstep2 x₁, Real.fourier_real_eq_integral_exp_smul]
      simp only [smul_eq_mul, ← integral_const_mul]
      congr 1; funext x₂; ring
    have hnorm_lhs : ‖(2 * (Real.pi : ℂ) * I * (m₂ : ℂ)) ^ 2 * ((2 * (Real.pi : ℂ) * I * (m₁ : ℂ)) ^ 2 * becG2 t m₁ m₂ x₃)‖ =
        (16 * Real.pi ^ 4 * m₁ ^ 2 * m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow, sq_abs]
      ring
    rw [← hnorm_lhs, hid]
    calc ‖∫ x₁ : ℝ, Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) *
            𝓕 (fun x₂ : ℝ ↦ becF_d1122 t x₁ x₂ x₃) m₂‖
        ≤ ∫ x₁ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₁ * m₁) * I) *
            𝓕 (fun x₂ : ℝ ↦ becF_d1122 t x₁ x₂ x₃) m₂‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x₁ : ℝ, (C4 * I0 * Real.exp (-(t / 4) * x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hG_int.const_mul _) (Eventually.of_forall fun x₁ ↦ ?_)
          dsimp only
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Real.fourier_real_eq_integral_exp_smul]
          calc ‖∫ x₂ : ℝ, Complex.exp (↑(-2 * Real.pi * x₂ * m₂) * I) • becF_d1122 t x₁ x₂ x₃‖
              ≤ ∫ x₂ : ℝ, ‖Complex.exp (↑(-2 * Real.pi * x₂ * m₂) * I) • becF_d1122 t x₁ x₂ x₃‖ :=
                norm_integral_le_integral_norm _
            _ ≤ ∫ x₂ : ℝ, (C4 * Real.exp (-(t / 4) * x₃ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2)) *
                  Real.exp (-(t / 4) * x₂ ^ 2) := by
                apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
                  (hG_int.const_mul _) (Eventually.of_forall fun x₂ ↦ ?_)
                dsimp only
                rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
                have he : Real.exp (-(t / 4) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) =
                    Real.exp (-(t / 4) * x₃ ^ 2) * Real.exp (-(t / 4) * x₁ ^ 2) * Real.exp (-(t / 4) * x₂ ^ 2) := by
                  rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
                exact (hb4 x₁ x₂ x₃).trans_eq (by rw [he]; ring)
            _ = (C4 * I0 * Real.exp (-(t / 4) * x₃ ^ 2)) * Real.exp (-(t / 4) * x₁ ^ 2) := by
                rw [integral_const_mul]; dsimp [I0]; ring
      _ = C4 * I0 ^ 2 * Real.exp (-(t / 4) * x₃ ^ 2) := by rw [integral_const_mul]; dsimp [I0]; ring
  have hm12' : m₁ ^ 2 * m₂ ^ 2 * ‖becG2 t m₁ m₂ x₃‖ ≤
      (C4 / (16 * Real.pi ^ 4)) * I0 ^ 2 * Real.exp (-(t / 4) * x₃ ^ 2) := by
    have h16pi : 0 < 16 * Real.pi ^ 4 := by positivity
    rw [show (C4 / (16 * Real.pi ^ 4)) * I0 ^ 2 * Real.exp (-(t / 4) * x₃ ^ 2) =
        (C4 * I0 ^ 2 * Real.exp (-(t / 4) * x₃ ^ 2)) / (16 * Real.pi ^ 4) by ring,
        le_div_iff₀' h16pi]
    linarith
  have hprod_le : (1 + m₁ ^ 2) * (1 + m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ ≤ K * Real.exp (-(t / 4) * x₃ ^ 2) := by
    have hexp : (1 + m₁ ^ 2) * (1 + m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ ≤
        (1 + m₁ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ + (1 + m₂ ^ 2) * ‖becG2 t m₁ m₂ x₃‖ +
        m₁ ^ 2 * m₂ ^ 2 * ‖becG2 t m₁ m₂ x₃‖ := by nlinarith [norm_nonneg (becG2 t m₁ m₂ x₃)]
    dsimp only [K]; linarith
  rw [div_mul_eq_mul_div, le_div_iff₀' (by positivity : 0 < (1 + m₁ ^ 2) * (1 + m₂ ^ 2))]
  exact hprod_le

/-! ### 6. Exact Closed-Form Evaluation of `becG3 t m₁ m₂ m₃` via `k`-Expansion & `tsum_bech_eq_tsum_pnat` -/

private lemma becG3_eq_tsum_gauss {t : ℝ} (ht : 0 < t) (m₁ m₂ m₃ : ℝ) :
    becG3 t m₁ m₂ m₃ =
      ∑' k : ℕ+,
        (((Real.pi / (k.val * t)) ^ (3 / 2 : ℝ) *
          (3 / (2 * (k.val * t)) - Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / (k.val * t) ^ 2) *
          Real.exp (-Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / (k.val * t)) : ℝ) : ℂ) := by
  -- Use coordinate order `p = (x₃, (x₂, x₁)) : ℝ × (ℝ × ℝ)` so `integral_prod` unpacks
  -- directly to `∫ x₃, ∫ x₂, ∫ x₁` with ZERO Fubini swaps!
  let μ₃ : Measure (ℝ × ℝ × ℝ) := volume.prod (volume.prod volume)
  let e3D (p : ℝ × ℝ × ℝ) : ℂ :=
    Complex.exp (↑(-2 * Real.pi * p.1 * m₃) * I) *
    (Complex.exp (↑(-2 * Real.pi * p.2.1 * m₂) * I) *
      Complex.exp (↑(-2 * Real.pi * p.2.2 * m₁) * I))
  let g3D (k : ℕ+) (p : ℝ × ℝ × ℝ) : ℂ :=
    (((p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2) *
      Real.exp (-(k.val * t) * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) : ℝ) : ℂ)
  have he3_norm (p : ℝ × ℝ × ℝ) : ‖e3D p‖ = 1 := by
    dsimp only [e3D]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
  -- Step 1: Unpack `becG3` as a single 3D integral over `μ₃`!
  obtain ⟨C0, hC0, hb0⟩ := becF_exp_bound ht
  have hG_int : Integrable (fun x : ℝ ↦ Real.exp (-(t / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (half_pos ht)
  have hprod3_int : Integrable (fun p : ℝ × ℝ × ℝ ↦ e3D p * becF t p.2.2 p.2.1 p.1) μ₃ := by
    have hdom : Integrable (fun p : ℝ × ℝ × ℝ ↦
        C0 * (Real.exp (-(t / 2) * p.1 ^ 2) *
          (Real.exp (-(t / 2) * p.2.1 ^ 2) * Real.exp (-(t / 2) * p.2.2 ^ 2)))) μ₃ :=
      (hG_int.mul_prod (hG_int.mul_prod hG_int)).const_mul C0
    refine hdom.mono' ?_ (Eventually.of_forall fun p ↦ ?_)
    · have hcont : Continuous (fun p : ℝ × ℝ × ℝ ↦ becF t p.2.2 p.2.1 p.1) := by
        unfold becF
        exact Complex.continuous_ofReal.comp
          (continuous_const.mul ((phiKernel_contDiff 0).continuous.comp (by fun_prop)))
      exact ((by fun_prop : Continuous e3D).mul hcont).aestronglyMeasurable
    · rw [norm_mul, he3_norm, one_mul]
      have hsp : Real.exp (-(t / 2) * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) =
          Real.exp (-(t / 2) * p.1 ^ 2) *
            (Real.exp (-(t / 2) * p.2.1 ^ 2) * Real.exp (-(t / 2) * p.2.2 ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      exact (hb0 p.2.2 p.2.1 p.1).trans_eq (by rw [hsp])
  have hbecG3_eq : becG3 t m₁ m₂ m₃ = ∫ p : ℝ × ℝ × ℝ, e3D p * becF t p.2.2 p.2.1 p.1 ∂μ₃ := by
    rw [MeasureTheory.integral_prod _ hprod3_int]
    simp only [becG3, becG2, becG1, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    congr 1; funext x₃
    have hprod2_int : Integrable (fun q : ℝ × ℝ ↦ e3D (x₃, q) * becF t q.2 q.1 x₃) (volume.prod volume) := by
      have hdom : Integrable (fun q : ℝ × ℝ ↦
          (C0 * Real.exp (-(t / 2) * x₃ ^ 2)) *
            (Real.exp (-(t / 2) * q.1 ^ 2) * Real.exp (-(t / 2) * q.2 ^ 2))) (volume.prod volume) :=
        (hG_int.mul_prod hG_int).const_mul _
      refine hdom.mono' ?_ (Eventually.of_forall fun q ↦ ?_)
      · have hc : Continuous (fun q : ℝ × ℝ ↦ becF t q.2 q.1 x₃) := by
          unfold becF
          exact Complex.continuous_ofReal.comp
            (continuous_const.mul ((phiKernel_contDiff 0).continuous.comp (by fun_prop)))
        exact ((by fun_prop : Continuous fun q : ℝ × ℝ ↦ e3D (x₃, q)).mul hc).aestronglyMeasurable
      · rw [norm_mul, he3_norm, one_mul]
        have hsp : Real.exp (-(t / 2) * (q.2 ^ 2 + q.1 ^ 2 + x₃ ^ 2)) =
            Real.exp (-(t / 2) * x₃ ^ 2) * (Real.exp (-(t / 2) * q.1 ^ 2) * Real.exp (-(t / 2) * q.2 ^ 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        exact (hb0 q.2 q.1 x₃).trans_eq (by rw [hsp]; ring)
    rw [MeasureTheory.integral_prod _ hprod2_int, ← integral_const_mul]
    congr 1; funext x₂
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext x₁
    dsimp only [e3D]; ring
  -- Step 2: 1D Gaussian moments & integrability for each `k : ℕ+`!
  have h1D_gauss0 {a : ℝ} (ha : 0 < a) :
      (∫ x : ℝ, Real.exp (-a * x ^ 2)) = Real.sqrt (Real.pi / a) := by
    have h0 := fourier_gauss0 ha 0
    simp only [Real.fourier_real_eq_integral_exp_smul, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, zero_pow two_ne_zero, zero_div, neg_zero, mul_one] at h0
    have hfun : (fun x : ℝ ↦ Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))) =
        fun x : ℝ ↦ Complex.ofRealCLM (Real.exp (-a * x ^ 2)) := by
      funext x; change Complex.exp _ = ((Real.exp _ : ℝ) : ℂ); rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [hfun, Complex.ofRealCLM.integral_comp_comm (integrable_exp_neg_mul_sq ha)] at h0
    exact Complex.ofReal_injective h0
  have h1D_gauss2_int {a : ℝ} (ha : 0 < a) :
      Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (-a * x ^ 2)) := by
    obtain ⟨B, hB, hbd⟩ := poly_mul_exp_quarter_le (show 0 < 2 * a by positivity) 1
    refine ((integrable_exp_neg_mul_sq (half_pos ha)).const_mul B).mono' (by fun_prop)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsp : Real.exp (-a * x ^ 2) = Real.exp (-(2 * a / 4) * x ^ 2) * Real.exp (-(a / 2) * x ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsp, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by simpa using hbd x) (Real.exp_pos _).le
  have h1D_gauss2 {a : ℝ} (ha : 0 < a) :
      (∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2)) = Real.sqrt (Real.pi / a) * (1 / (2 * a)) := by
    have h0 := fourier_gauss2 ha 0
    simp only [Real.fourier_real_eq_integral_exp_smul, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, zero_pow two_ne_zero, zero_div, sub_zero, neg_zero, mul_one] at h0
    have hfun : (fun x : ℝ ↦ ((x : ℂ) ^ 2) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))) =
        fun x : ℝ ↦ Complex.ofRealCLM (x ^ 2 * Real.exp (-a * x ^ 2)) := by
      funext x
      change ((x : ℂ) ^ 2) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2)) =
        ((x ^ 2 * Real.exp (-a * x ^ 2) : ℝ) : ℂ)
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]; congr 2; push_cast; ring
    rw [hfun, Complex.ofRealCLM.integral_comp_comm (h1D_gauss2_int ha)] at h0
    exact Complex.ofReal_injective h0
  -- Helper: integrability & exact value of each 3D term `e3D p * g3D k p`!
  have hg3D_int (k : ℕ+) : Integrable (fun p : ℝ × ℝ × ℝ ↦ e3D p * g3D k p) μ₃ := by
    let a : ℝ := (k.val : ℝ) * t
    have ha : 0 < a := mul_pos (by exact_mod_cast k.pos) ht
    have h0 : Integrable (fun x : ℝ ↦ Real.exp (-a * x ^ 2)) := integrable_exp_neg_mul_sq ha
    have h2 : Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (-a * x ^ 2)) := h1D_gauss2_int ha
    have hterm1 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2)))) μ₃ :=
      h0.mul_prod (h0.mul_prod h2)
    have hterm2 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      h0.mul_prod (h2.mul_prod h0)
    have hterm3 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        (p.1 ^ 2 * Real.exp (-a * p.1 ^ 2)) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      h2.mul_prod (h0.mul_prod h0)
    have h12 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2))) +
        Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      hterm1.add hterm2
    have h123 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        (Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2))) +
         Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) +
        (p.1 ^ 2 * Real.exp (-a * p.1 ^ 2)) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      h12.add hterm3
    refine h123.mono' (by fun_prop) (Eventually.of_forall fun p ↦ ?_)
    rw [norm_mul, he3_norm, one_mul]
    dsimp only [g3D]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsp : Real.exp (-a * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) =
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    change (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2) * Real.exp (-a * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) ≤ _
    rw [hsp]; apply le_of_eq; ring
  have hg3D_norm_int (k : ℕ+) :
      (∫ p : ℝ × ℝ × ℝ, ‖e3D p * g3D k p‖ ∂μ₃) =
        (3 / 2) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(5 / 2 : ℝ)) * (k.val : ℝ) ^ (-(5 / 2 : ℝ)) := by
    let a : ℝ := (k.val : ℝ) * t
    have ha : 0 < a := mul_pos (by exact_mod_cast k.pos) ht
    have h0 : Integrable (fun x : ℝ ↦ Real.exp (-a * x ^ 2)) := integrable_exp_neg_mul_sq ha
    have h2 : Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (-a * x ^ 2)) := h1D_gauss2_int ha
    have hterm1 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2)))) μ₃ :=
      h0.mul_prod (h0.mul_prod h2)
    have hterm2 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      h0.mul_prod (h2.mul_prod h0)
    have hterm3 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        (p.1 ^ 2 * Real.exp (-a * p.1 ^ 2)) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      h2.mul_prod (h0.mul_prod h0)
    have h12 : Integrable (fun p : ℝ × ℝ × ℝ ↦
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2))) +
        Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) μ₃ :=
      hterm1.add hterm2
    have hfun : (fun p : ℝ × ℝ × ℝ ↦ ‖e3D p * g3D k p‖) = fun p ↦
        (Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2))) +
         Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2))) +
        (p.1 ^ 2 * Real.exp (-a * p.1 ^ 2)) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2)) := by
      funext p
      rw [norm_mul, he3_norm, one_mul]
      dsimp only [g3D]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsp : Real.exp (-a * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) =
          Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      change (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2) * Real.exp (-a * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) = _
      rw [hsp]; ring
    rw [hfun, integral_add h12 hterm3, integral_add hterm1 hterm2]
    have hint3R (f g h : ℝ → ℝ) :
        (∫ p : ℝ × ℝ × ℝ, f p.1 * (g p.2.1 * h p.2.2) ∂μ₃) =
          (∫ x : ℝ, f x) * ((∫ x : ℝ, g x) * (∫ x : ℝ, h x)) := by
      dsimp only [μ₃]
      rw [MeasureTheory.integral_prod_mul (f := f) (g := fun q : ℝ × ℝ ↦ g q.1 * h q.2),
          MeasureTheory.integral_prod_mul (f := g) (g := h)]
    have hi1 : (∫ p : ℝ × ℝ × ℝ,
        Real.exp (-a * p.1 ^ 2) * (Real.exp (-a * p.2.1 ^ 2) * (p.2.2 ^ 2 * Real.exp (-a * p.2.2 ^ 2))) ∂μ₃) =
        Real.sqrt (Real.pi / a) * (Real.sqrt (Real.pi / a) * (Real.sqrt (Real.pi / a) * (1 / (2 * a)))) := by
      rw [hint3R (fun x ↦ Real.exp (-a * x ^ 2)) (fun x ↦ Real.exp (-a * x ^ 2))
            (fun x ↦ x ^ 2 * Real.exp (-a * x ^ 2)), h1D_gauss0 ha, h1D_gauss2 ha]
    have hi2 : (∫ p : ℝ × ℝ × ℝ,
        Real.exp (-a * p.1 ^ 2) * ((p.2.1 ^ 2 * Real.exp (-a * p.2.1 ^ 2)) * Real.exp (-a * p.2.2 ^ 2)) ∂μ₃) =
        Real.sqrt (Real.pi / a) * ((Real.sqrt (Real.pi / a) * (1 / (2 * a))) * Real.sqrt (Real.pi / a)) := by
      rw [hint3R (fun x ↦ Real.exp (-a * x ^ 2)) (fun x ↦ x ^ 2 * Real.exp (-a * x ^ 2))
            (fun x ↦ Real.exp (-a * x ^ 2)), h1D_gauss0 ha, h1D_gauss2 ha]
    have hi3 : (∫ p : ℝ × ℝ × ℝ,
        (p.1 ^ 2 * Real.exp (-a * p.1 ^ 2)) * (Real.exp (-a * p.2.1 ^ 2) * Real.exp (-a * p.2.2 ^ 2)) ∂μ₃) =
        (Real.sqrt (Real.pi / a) * (1 / (2 * a))) * (Real.sqrt (Real.pi / a) * Real.sqrt (Real.pi / a)) := by
      rw [hint3R (fun x ↦ x ^ 2 * Real.exp (-a * x ^ 2)) (fun x ↦ Real.exp (-a * x ^ 2))
            (fun x ↦ Real.exp (-a * x ^ 2)), h1D_gauss0 ha, h1D_gauss2 ha]
    rw [hi1, hi2, hi3]
    have hsqrt3 : Real.sqrt (Real.pi / a) ^ 3 = Real.pi ^ (3 / 2 : ℝ) * a ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.div_rpow Real.pi_pos.le ha.le, div_eq_mul_inv, ← Real.rpow_neg ha.le]
    have hpow52 : a ^ (-(3 / 2 : ℝ)) * a⁻¹ = t ^ (-(5 / 2 : ℝ)) * (k.val : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ha]
      have hkn : (0 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.pos.le
      rw [show -(3 / 2 : ℝ) + -1 = -(5 / 2 : ℝ) by norm_num, Real.mul_rpow hkn ht.le, mul_comm]
    calc _ = (3 / 2) * Real.sqrt (Real.pi / a) ^ 3 * a⁻¹ := by ring
      _ = (3 / 2) * Real.pi ^ (3 / 2 : ℝ) * (a ^ (-(3 / 2 : ℝ)) * a⁻¹) := by rw [hsqrt3]; ring
      _ = (3 / 2) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(5 / 2 : ℝ)) * (k.val : ℝ) ^ (-(5 / 2 : ℝ)) := by
          rw [hpow52]; ring
  have hg3D_summable : Summable (fun k : ℕ+ ↦ ∫ p : ℝ × ℝ × ℝ, ‖e3D p * g3D k p‖ ∂μ₃) := by
    simp_rw [hg3D_norm_int]
    have hnat : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (5 / 2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hpnat : Summable (fun k : ℕ+ ↦ (k.val : ℝ) ^ (-(5 / 2 : ℝ))) := by
      refine (hnat.comp_injective PNat.coe_injective).congr fun k ↦ ?_
      have hk : (0 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.pos.le
      dsimp only [Function.comp_def]
      rw [Real.rpow_neg hk]
    exact hpnat.mul_left _
  -- Step 3: Pointwise `a.e.` identity `e3D p * becF = ∑'_{k : ℕ+} e3D p * g3D k p`!
  have hae_eq : (fun p : ℝ × ℝ × ℝ ↦ e3D p * becF t p.2.2 p.2.1 p.1) =ᵐ[μ₃]
      fun p : ℝ × ℝ × ℝ ↦ ∑' k : ℕ+, e3D p * g3D k p := by
    have hne0 : ∀ᵐ p : ℝ × ℝ × ℝ ∂μ₃, p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2 ≠ 0 := by
      rw [ae_iff]
      have hsub : {p : ℝ × ℝ × ℝ | ¬ p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2 ≠ 0} ⊆ {(0, (0, 0))} := by
        intro p hp
        simp only [mem_ofPred_eq, not_not, mem_singleton_iff] at hp ⊢
        have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.2.2, sq_nonneg p.2.1, sq_nonneg p.1]
        have h2 : p.2.1 = 0 := by nlinarith [sq_nonneg p.2.2, sq_nonneg p.2.1, sq_nonneg p.1]
        have h3 : p.2.2 = 0 := by nlinarith [sq_nonneg p.2.2, sq_nonneg p.2.1, sq_nonneg p.1]
        exact Prod.ext h1 (Prod.ext h2 h3)
      exact measure_mono_null hsub (measure_singleton _)
    filter_upwards [hne0] with p hp
    rw [tsum_mul_left]
    congr 1
    rw [becF_eq_of_ne_zero ht hp]
    set r : ℝ := p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2
    have hr : 0 < r := lt_of_le_of_ne (by positivity) hp.symm
    have hu : 0 < t * r := mul_pos ht hr
    have hgeom : (∑' k : ℕ+, Real.exp (-((k.val : ℝ) * (t * r)))) = (Real.exp (t * r) - 1)⁻¹ := by
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ Real.exp (-((n : ℝ) * (t * r))))]
      have hpow : (fun n : ℕ ↦ Real.exp (-(((n + 1 : ℕ) : ℝ) * (t * r)))) =
          fun n : ℕ ↦ Real.exp (-(t * r)) * (Real.exp (-(t * r))) ^ n := by
        funext n
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      rw [hpow, tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))]
      have he : Real.exp (t * r) ≠ 0 := (Real.exp_pos _).ne'
      have h1 : Real.exp (t * r) - 1 ≠ 0 := by linarith [Real.one_lt_exp_iff.mpr hu]
      have h2 : 1 - Real.exp (-(t * r)) ≠ 0 := by linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)]
      rw [Real.exp_neg]; field_simp [he, h1, h2]
    have hreal : (∑' k : ℕ+, r * Real.exp (-((k.val : ℝ) * t) * r)) = r / (Real.exp (t * r) - 1) := by
      have hrew : (fun k : ℕ+ ↦ r * Real.exp (-((k.val : ℝ) * t) * r)) =
          fun k : ℕ+ ↦ r * Real.exp (-((k.val : ℝ) * (t * r))) := by
        funext k; congr 2; ring
      rw [hrew, tsum_mul_left, hgeom, div_eq_mul_inv]
    rw [← hreal, Complex.ofReal_tsum]
  -- Step 4: Swap `∫` and `∑' k` via `integral_tsum_of_summable_integral_norm`, and evaluate each `k`-term!
  rw [hbecG3_eq, integral_congr_ae hae_eq, ← integral_tsum_of_summable_integral_norm hg3D_int hg3D_summable]
  apply tsum_congr; intro k
  let a : ℝ := (k.val : ℝ) * t
  have ha : 0 < a := mul_pos (by exact_mod_cast k.pos) ht
  have h0C (ξ : ℝ) : Integrable (fun x : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))) := by
    refine (integrable_exp_neg_mul_sq ha).mono' (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
    have hre : (-((a : ℂ) * (x : ℂ) ^ 2)).re = -a * x ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re, neg_mul]
    rw [hre]
  have h2C (ξ : ℝ) : Integrable (fun x : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * (((x : ℂ) ^ 2) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2)))) := by
    refine (h1D_gauss2_int ha).mono' (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, Complex.norm_exp]
    have hre : (-((a : ℂ) * (x : ℂ) ^ 2)).re = -a * x ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re, neg_mul]
    rw [hre]
  let f0 (ξ x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2))
  let f2 (ξ x : ℝ) : ℂ :=
    Complex.exp (↑(-2 * Real.pi * x * ξ) * I) * (((x : ℂ) ^ 2) * Complex.exp (-((a : ℂ) * (x : ℂ) ^ 2)))
  have hT1 : Integrable (fun p : ℝ × ℝ × ℝ ↦ f0 m₃ p.1 * (f0 m₂ p.2.1 * f2 m₁ p.2.2)) μ₃ :=
    (h0C m₃).mul_prod ((h0C m₂).mul_prod (h2C m₁))
  have hT2 : Integrable (fun p : ℝ × ℝ × ℝ ↦ f0 m₃ p.1 * (f2 m₂ p.2.1 * f0 m₁ p.2.2)) μ₃ :=
    (h0C m₃).mul_prod ((h2C m₂).mul_prod (h0C m₁))
  have hT3 : Integrable (fun p : ℝ × ℝ × ℝ ↦ f2 m₃ p.1 * (f0 m₂ p.2.1 * f0 m₁ p.2.2)) μ₃ :=
    (h2C m₃).mul_prod ((h0C m₂).mul_prod (h0C m₁))
  have hT12 : Integrable (fun p : ℝ × ℝ × ℝ ↦
      f0 m₃ p.1 * (f0 m₂ p.2.1 * f2 m₁ p.2.2) + f0 m₃ p.1 * (f2 m₂ p.2.1 * f0 m₁ p.2.2)) μ₃ :=
    hT1.add hT2
  have hsplit : (fun p : ℝ × ℝ × ℝ ↦ e3D p * g3D k p) = fun p ↦
      (f0 m₃ p.1 * (f0 m₂ p.2.1 * f2 m₁ p.2.2) + f0 m₃ p.1 * (f2 m₂ p.2.1 * f0 m₁ p.2.2)) +
      f2 m₃ p.1 * (f0 m₂ p.2.1 * f0 m₁ p.2.2) := by
    funext p
    dsimp only [e3D, g3D, f0, f2]
    have hsp : Complex.exp (-((a : ℂ) * ((p.2.2 : ℂ) ^ 2 + (p.2.1 : ℂ) ^ 2 + (p.1 : ℂ) ^ 2))) =
        Complex.exp (-((a : ℂ) * (p.1 : ℂ) ^ 2)) *
          (Complex.exp (-((a : ℂ) * (p.2.1 : ℂ) ^ 2)) * Complex.exp (-((a : ℂ) * (p.2.2 : ℂ) ^ 2))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have hg_eq : (((p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2) *
        Real.exp (-(k.val * t) * (p.2.2 ^ 2 + p.2.1 ^ 2 + p.1 ^ 2)) : ℝ) : ℂ) =
        ((p.2.2 : ℂ) ^ 2 + (p.2.1 : ℂ) ^ 2 + (p.1 : ℂ) ^ 2) *
          Complex.exp (-((a : ℂ) * ((p.2.2 : ℂ) ^ 2 + (p.2.1 : ℂ) ^ 2 + (p.1 : ℂ) ^ 2))) := by
      rw [Complex.ofReal_mul, Complex.ofReal_exp]; dsimp [a]; push_cast; congr 2; ring
    rw [hg_eq, hsp]; ring
  rw [hsplit, integral_add hT12 hT3, integral_add hT1 hT2]
  have hf0_val (ξ : ℝ) : (∫ x : ℝ, f0 ξ x) =
      (((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) * Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ))) := by
    simpa only [f0, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul] using fourier_gauss0 ha ξ
  have hf2_val (ξ : ℝ) : (∫ x : ℝ, f2 ξ x) =
      (((Real.sqrt (Real.pi / a) * (1 / (2 * a) - Real.pi ^ 2 * ξ ^ 2 / a ^ 2) : ℝ) : ℂ)) *
        Complex.exp (-(((Real.pi ^ 2 * ξ ^ 2 / a : ℝ) : ℂ))) := by
    simpa only [f2, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul] using fourier_gauss2 ha ξ
  have hint3C (f g h : ℝ → ℂ) :
      (∫ p : ℝ × ℝ × ℝ, f p.1 * (g p.2.1 * h p.2.2) ∂μ₃) =
        (∫ x : ℝ, f x) * ((∫ x : ℝ, g x) * (∫ x : ℝ, h x)) := by
    dsimp only [μ₃]
    rw [MeasureTheory.integral_prod_mul (f := f) (g := fun q : ℝ × ℝ ↦ g q.1 * h q.2),
        MeasureTheory.integral_prod_mul (f := g) (g := h)]
  rw [hint3C (f0 m₃) (f0 m₂) (f2 m₁), hint3C (f0 m₃) (f2 m₂) (f0 m₁),
      hint3C (f2 m₃) (f0 m₂) (f0 m₁),
      hf0_val, hf0_val, hf0_val, hf2_val, hf2_val, hf2_val]
  have hexp_prod :
      Complex.exp (-(((Real.pi ^ 2 * m₃ ^ 2 / a : ℝ) : ℂ))) *
      (Complex.exp (-(((Real.pi ^ 2 * m₂ ^ 2 / a : ℝ) : ℂ))) *
       Complex.exp (-(((Real.pi ^ 2 * m₁ ^ 2 / a : ℝ) : ℂ)))) =
      Complex.exp (-(((Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / a : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hsqrt3 : Real.sqrt (Real.pi / a) ^ 3 = (Real.pi / a) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hcomb :
      ((Real.sqrt (Real.pi / a) : ℂ) ^ 3 *
        ((1 / (2 * (a : ℂ)) - (Real.pi : ℂ) ^ 2 * (m₁ : ℂ) ^ 2 / (a : ℂ) ^ 2) +
         (1 / (2 * (a : ℂ)) - (Real.pi : ℂ) ^ 2 * (m₂ : ℂ) ^ 2 / (a : ℂ) ^ 2) +
         (1 / (2 * (a : ℂ)) - (Real.pi : ℂ) ^ 2 * (m₃ : ℂ) ^ 2 / (a : ℂ) ^ 2))) *
        Complex.exp (-(((Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / a : ℝ) : ℂ))) =
      (((Real.pi / a) ^ (3 / 2 : ℝ) *
        (3 / (2 * a) - Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / a ^ 2) *
        Real.exp (-Real.pi ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) / a) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hsqrt3, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 1
    · dsimp only [a]; push_cast; ring
    · congr 1; dsimp only [a]; push_cast; ring
  rw [← hcomb, ← hexp_prod]
  push_cast; ring

/-! ### 7. Iterated 3D Poisson Summation and Final Proof of `bec3D_analytic_identity` -/

private lemma isBigO_cocompact_of_exp_neg_sq {f : ℝ → ℂ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hbd : ∀ x : ℝ, ‖f x‖ ≤ C * Real.exp (-c * x ^ 2)) :
    f =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨C / c, Filter.hasBasis_cocompact.eventually_iff.mpr
    ⟨Metric.closedBall (0 : ℝ) 1, isCompact_closedBall 0 1, fun x hx ↦ ?_⟩⟩
  have hgt : 1 < |x| := by
    have hnot : ¬ dist x 0 ≤ 1 := fun h ↦ hx (Metric.mem_closedBall.mp h)
    rw [Real.dist_eq, sub_zero] at hnot; linarith
  have hx0 : 0 < |x| := zero_lt_one.trans hgt
  have hpow : |x| ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _), hpow]
  have hcx : c * x ^ 2 ≤ Real.exp (c * x ^ 2) := by linarith [Real.add_one_le_exp (c * x ^ 2)]
  have hpos : 0 < c * x ^ 2 := by
    have : 0 < x ^ 2 := by rw [← sq_abs]; positivity
    positivity
  have hinv : Real.exp (-c * x ^ 2) ≤ (c * x ^ 2)⁻¹ := by
    rw [neg_mul, Real.exp_neg]; exact inv_anti₀ hpos hcx
  calc ‖f x‖ ≤ C * Real.exp (-c * x ^ 2) := hbd x
    _ ≤ C * (c * x ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hC
    _ = C / c * (x ^ 2)⁻¹ := by rw [mul_inv, div_eq_mul_inv, mul_assoc]

private lemma summable_int_inv_one_add_sq :
    Summable (fun m : ℤ ↦ (1 + (m : ℝ) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ ↦ (1 + (n : ℝ) ^ 2)⁻¹) := by
    rw [← summable_nat_add_iff 1]
    have h2 : Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr one_lt_two).comp_injective Nat.succ_injective
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) h2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (by linarith)
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, ?_⟩
  exact hnat.congr fun n ↦ by simp

private lemma summable_int_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ ↦ Real.exp (-c * |(m : ℝ)|)) := by
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-c * |(n : ℝ)|)) := by
    have hg := summable_geometric_of_lt_one (Real.exp_pos (-c)).le
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
    refine hg.congr fun n ↦ ?_
    rw [← Real.exp_nat_mul, abs_of_nonneg (Nat.cast_nonneg n)]; congr 1; ring
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, ?_⟩
  exact hnat.congr fun n ↦ by simp

private lemma summable_int_exp_neg_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ ↦ Real.exp (-c * (m : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (fun m ↦ ?_) (summable_int_exp_neg_abs hc)
  apply Real.exp_le_exp.mpr
  have hle : |(m : ℝ)| ≤ (m : ℝ) ^ 2 := by
    rw [← sq_abs]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      nlinarith
  nlinarith

private lemma becG3_eval_nonzero {X : ℝ} (hX : 0 < X) {m₁ m₂ m₃ : ℝ}
    (hm : 0 < m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) :
    becG3 (X ^ 2)⁻¹ m₁ m₂ m₃ =
      (X : ℂ) ^ 4 * ∑' j : ℕ+,
        ((((j.val : ℝ) / Real.sqrt (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) : ℝ) : ℂ)) *
          ((-2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay0 * (((Real.sqrt (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
           (2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay1 * (((Real.sqrt (m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))) := by
  set t : ℝ := (X ^ 2)⁻¹
  have ht : 0 < t := by positivity
  set M2 : ℝ := m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2
  set p : ℝ := Real.pi ^ 2 * M2 * X ^ 2
  have hp : 0 < p := by positivity
  rw [becG3_eq_tsum_gauss ht m₁ m₂ m₃]
  have hterm_eq : ∀ k : ℕ+,
      (((Real.pi / (k.val * t)) ^ (3 / 2 : ℝ) *
        (3 / (2 * (k.val * t)) - Real.pi ^ 2 * M2 / (k.val * t) ^ 2) *
        Real.exp (-Real.pi ^ 2 * M2 / (k.val * t)) : ℝ) : ℂ) =
      (((Real.pi ^ (3 / 2 : ℝ) * X ^ 5 : ℝ) : ℂ)) * bech p (k.val : ℝ) := by
    intro k
    have hk : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast k.pos
    simp only [bech, hk, ↓reduceIte, ← Complex.ofReal_mul]
    congr 1
    have ht_inv : t⁻¹ = X ^ 2 := inv_inv (X ^ 2)
    have hdiv_t : Real.pi / (k.val * t) = Real.pi * X ^ 2 * (k.val : ℝ)⁻¹ := by
      dsimp [t]; field_simp [hk.ne', hX.ne']
    have hpow32 : (Real.pi / (k.val * t)) ^ (3 / 2 : ℝ) =
        Real.pi ^ (3 / 2 : ℝ) * X ^ 3 * (k.val : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [hdiv_t, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow Real.pi_pos.le (by positivity),
          show (X ^ 2) ^ (3 / 2 : ℝ) = X ^ 3 by
            rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX.le]; norm_num,
          Real.inv_rpow hk.le, ← Real.rpow_neg hk.le]
    have harg : -Real.pi ^ 2 * M2 / (k.val * t) = -p / (k.val : ℝ) := by
      dsimp [p, t]; field_simp [hk.ne', hX.ne']
    have h1 : (k.val : ℝ) ^ (-(3 / 2 : ℝ)) * (k.val : ℝ)⁻¹ = (k.val : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hk]; norm_num
    have h2 : (k.val : ℝ) ^ (-(3 / 2 : ℝ)) * ((k.val : ℝ) ^ 2)⁻¹ = (k.val : ℝ) ^ (-(7 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (k.val : ℝ) 2, ← Real.rpow_neg hk.le, ← Real.rpow_add hk]; norm_num
    rw [hpow32, harg]
    have hbrack : 3 / (2 * (k.val * t)) - Real.pi ^ 2 * M2 / (k.val * t) ^ 2 =
        X ^ 2 * (3 / 2 * (k.val : ℝ)⁻¹ - p * ((k.val : ℝ) ^ 2)⁻¹) := by
      dsimp [p, t]; field_simp [hk.ne', hX.ne']
    rw [hbrack]
    calc Real.pi ^ (3 / 2 : ℝ) * X ^ 3 * (k.val : ℝ) ^ (-(3 / 2 : ℝ)) *
          (X ^ 2 * (3 / 2 * (k.val : ℝ)⁻¹ - p * ((k.val : ℝ) ^ 2)⁻¹)) * Real.exp (-p / (k.val : ℝ))
        = Real.pi ^ (3 / 2 : ℝ) * X ^ 5 *
          ((3 / 2 * ((k.val : ℝ) ^ (-(3 / 2 : ℝ)) * (k.val : ℝ)⁻¹) -
            p * ((k.val : ℝ) ^ (-(3 / 2 : ℝ)) * ((k.val : ℝ) ^ 2)⁻¹)) * Real.exp (-p / (k.val : ℝ))) := by ring
      _ = _ := by rw [h1, h2]
  rw [show (∑' k : ℕ+,
      (((Real.pi / (k.val * t)) ^ (3 / 2 : ℝ) *
        (3 / (2 * (k.val * t)) - Real.pi ^ 2 * M2 / (k.val * t) ^ 2) *
        Real.exp (-Real.pi ^ 2 * M2 / (k.val * t)) : ℝ) : ℂ)) =
      ∑' k : ℕ+, (((Real.pi ^ (3 / 2 : ℝ) * X ^ 5 : ℝ) : ℂ)) * bech p (k.val : ℝ) from tsum_congr hterm_eq]
  rw [tsum_mul_left, tsum_bech_eq_tsum_pnat hp, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr; intro j
  have hj : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast j.pos
  have hsqrt_p : Real.sqrt p = Real.pi * Real.sqrt M2 * X := by
    dsimp [p]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq Real.pi_pos.le, Real.sqrt_sq hX.le]
  have hpi2 : Real.pi ^ (3 / 2 : ℝ) * Real.sqrt Real.pi = Real.pi ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]; norm_num
  have hray0 : -2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 + I)) =
      -sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)) := by
    rw [hsqrt_p, Real.sqrt_mul Real.pi_pos.le, sqRay0]
    have hpi32 : Real.pi * Real.sqrt Real.pi = Real.pi ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' Real.pi_pos.le (by norm_num)]; norm_num
    push_cast
    calc -2 * ((Real.pi : ℂ) * (Real.sqrt M2 : ℂ) * (X : ℂ)) * (((Real.sqrt Real.pi : ℂ) * (Real.sqrt (j.val : ℝ) : ℂ)) * (1 + I))
        = -(2 * ((Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ)) * (1 + I)) * ((Real.sqrt M2 : ℂ) * (Real.sqrt (j.val : ℝ) : ℂ) * (X : ℂ)) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, hpi32]
  have hray1 : -2 * (Real.sqrt p : ℂ) * (((Real.sqrt (Real.pi * (j.val : ℝ)) : ℝ) : ℂ) * (1 - I)) =
      -sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)) := by
    rw [hsqrt_p, Real.sqrt_mul Real.pi_pos.le, sqRay1]
    have hpi32 : Real.pi * Real.sqrt Real.pi = Real.pi ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' Real.pi_pos.le (by norm_num)]; norm_num
    push_cast
    calc -2 * ((Real.pi : ℂ) * (Real.sqrt M2 : ℂ) * (X : ℂ)) * (((Real.sqrt Real.pi : ℂ) * (Real.sqrt (j.val : ℝ) : ℂ)) * (1 - I))
        = -(2 * ((Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ)) * (1 - I)) * ((Real.sqrt M2 : ℂ) * (Real.sqrt (j.val : ℝ) : ℂ) * (X : ℂ)) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, hpi32]
  rw [hray0, hray1, hsqrt_p]
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hXC : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hMC : (Real.sqrt M2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne'
  have hpref : (((Real.pi ^ (3 / 2 : ℝ) * X ^ 5 : ℝ) : ℂ)) *
      ((2 * (Real.pi : ℂ) * I * (j.val : ℂ)) * (((Real.sqrt Real.pi / (Real.pi * Real.sqrt M2 * X) : ℝ) : ℂ))) =
      (X : ℂ) ^ 4 * ((((j.val : ℝ) / Real.sqrt M2 : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) ^ 2 * I) := by
    have hpi2C : ((Real.pi ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ 2 := by
      rw [← Complex.ofReal_mul, hpi2, Complex.ofReal_pow]
    calc (((Real.pi ^ (3 / 2 : ℝ) * X ^ 5 : ℝ) : ℂ)) *
          ((2 * (Real.pi : ℂ) * I * (j.val : ℂ)) * (((Real.sqrt Real.pi / (Real.pi * Real.sqrt M2 * X) : ℝ) : ℂ)))
        = (((Real.pi ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Real.sqrt Real.pi : ℂ)) *
            (2 * (Real.pi : ℂ) * I * (j.val : ℂ) * (X : ℂ) ^ 5) /
            ((Real.pi : ℂ) * (Real.sqrt M2 : ℂ) * (X : ℂ)) := by push_cast; ring
      _ = (Real.pi : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * I * (j.val : ℂ) * (X : ℂ) ^ 5) /
            ((Real.pi : ℂ) * (Real.sqrt M2 : ℂ) * (X : ℂ)) := by rw [hpi2C]
      _ = (X : ℂ) ^ 4 * ((((j.val : ℝ) / Real.sqrt M2 : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) ^ 2 * I) := by
            push_cast; field_simp [hpiC, hXC, hMC]
  calc _ = ((((Real.pi ^ (3 / 2 : ℝ) * X ^ 5 : ℝ) : ℂ)) *
            ((2 * (Real.pi : ℂ) * I * (j.val : ℂ)) * (((Real.sqrt Real.pi / (Real.pi * Real.sqrt M2 * X) : ℝ) : ℂ)))) *
            (-Complex.exp (-sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
              Complex.exp (-sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))) := by ring
    _ = _ := by rw [hpref]; ring

private lemma becG3_eval_zero {X : ℝ} (hX : 0 < X) :
    becG3 (X ^ 2)⁻¹ 0 0 0 = bec3DConst * (X : ℂ) ^ 5 := by
  have ht : 0 < (X ^ 2)⁻¹ := by positivity
  rw [becG3_eq_tsum_gauss ht 0 0 0]
  simp only [bec3DConst, zero_pow two_ne_zero, add_zero, mul_zero, zero_div, sub_zero,
    Real.exp_zero, mul_one, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_tsum]
  congr 1
  rw [show 3 / 2 * Real.pi ^ (3 / 2 : ℝ) * (∑' k : ℕ+, (k.val : ℝ) ^ (-(5 / 2 : ℝ))) * X ^ 5 =
      (3 / 2 * Real.pi ^ (3 / 2 : ℝ) * X ^ 5) * (∑' k : ℕ+, (k.val : ℝ) ^ (-(5 / 2 : ℝ))) by ring,
      ← tsum_mul_left]
  apply tsum_congr; intro k
  have hk : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast k.pos
  have h1 : Real.pi / ((k.val : ℝ) * (X ^ 2)⁻¹) = Real.pi * X ^ 2 * (k.val : ℝ)⁻¹ := by
    field_simp [hk.ne', hX.ne']
  rw [h1, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow Real.pi_pos.le (by positivity),
      show (X ^ 2) ^ (3 / 2 : ℝ) = X ^ 3 by
        rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX.le]; norm_num,
      Real.inv_rpow hk.le, ← Real.rpow_neg hk.le]
  have h2 : 3 / (2 * ((k.val : ℝ) * (X ^ 2)⁻¹)) = 3 / 2 * X ^ 2 * (k.val : ℝ)⁻¹ := by
    field_simp [hk.ne', hX.ne']
  rw [h2]
  have h52 : (k.val : ℝ) ^ (-(3 / 2 : ℝ)) * (k.val : ℝ)⁻¹ = (k.val : ℝ) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hk]; norm_num
  calc Real.pi ^ (3 / 2 : ℝ) * X ^ 3 * (k.val : ℝ) ^ (-(3 / 2 : ℝ)) * (3 / 2 * X ^ 2 * (k.val : ℝ)⁻¹)
      = 3 / 2 * Real.pi ^ (3 / 2 : ℝ) * X ^ 5 * ((k.val : ℝ) ^ (-(3 / 2 : ℝ)) * (k.val : ℝ)⁻¹) := by ring
    _ = _ := by rw [h52]

private lemma tsum_int3_radial (φ : ℕ → ℂ)
    (hsum : Summable (fun v : ℤ × ℤ × ℤ ↦ φ (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat)) :
    (∑' v : ℤ × ℤ × ℤ, φ (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat) =
      φ 0 + ∑' N : ℕ+, (r3Count N.val : ℂ) * φ N.val := by
  let normSq3 (v : ℤ × ℤ × ℤ) : ℕ := (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat
  have htoNat (v : ℤ × ℤ × ℤ) : ((normSq3 v : ℕ) : ℤ) = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 :=
    Int.toNat_of_nonneg (by positivity)
  have hsigma : Summable (fun p : (d : ℕ) × {v : ℤ × ℤ × ℤ // normSq3 v = d} ↦ φ (normSq3 p.2.val)) :=
    (Equiv.sigmaFiberEquiv normSq3).summable_iff.mpr hsum
  have hfib : (∑' v : ℤ × ℤ × ℤ, φ (normSq3 v)) =
      ∑' d : ℕ, ∑' x : {v : ℤ × ℤ × ℤ // normSq3 v = d}, φ (normSq3 x.val) := by
    rw [← (Equiv.sigmaFiberEquiv normSq3).tsum_eq]
    exact hsigma.tsum_sigma
  have hcard (d : ℕ) :
      (∑' x : {v : ℤ × ℤ × ℤ // normSq3 v = d}, φ (normSq3 x.val)) = (r3Count d : ℂ) * φ d := by
    let S : Finset (ℤ × ℤ × ℤ) :=
      (Finset.Icc (-(d : ℤ)) (d : ℤ) ×ˢ (Finset.Icc (-(d : ℤ)) (d : ℤ) ×ˢ
        Finset.Icc (-(d : ℤ)) (d : ℤ))).filter
        (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (d : ℤ))
    have hmem : ∀ v : ℤ × ℤ × ℤ, normSq3 v = d ↔ v ∈ S := by
      intro v
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · intro h
        have heq : v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (d : ℤ) := by
          rw [← htoNat v, h]
        have hle_sq (a : ℤ) : -(a ^ 2) ≤ a ∧ a ≤ a ^ 2 := by
          constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
        have h1 := hle_sq v.1; have h2 := hle_sq v.2.1; have h3 := hle_sq v.2.2
        refine ⟨⟨⟨by nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2],
                 by nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2]⟩,
                ⟨by nlinarith [sq_nonneg v.1, sq_nonneg v.2.2],
                 by nlinarith [sq_nonneg v.1, sq_nonneg v.2.2]⟩,
                ⟨by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1],
                 by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1]⟩⟩, heq⟩
      · intro h
        have h1 : ((normSq3 v : ℕ) : ℤ) = (d : ℤ) := by rw [htoNat v, h.2]
        exact_mod_cast h1
    have hcongr : (∑' x : {v : ℤ × ℤ × ℤ // normSq3 v = d}, φ (normSq3 x.val)) =
        ∑' _x : {v : ℤ × ℤ × ℤ // v ∈ S}, φ d := by
      have h1 : (∑' x : {v : ℤ × ℤ × ℤ // normSq3 v = d}, φ (normSq3 x.val)) =
          ∑' _x : {v : ℤ × ℤ × ℤ // normSq3 v = d}, φ d := by
        apply tsum_congr; intro x; rw [x.property]
      rw [h1]
      exact (Equiv.subtypeEquivRight hmem).tsum_eq (fun _ ↦ φ d)
    rw [hcongr, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rfl
  change (∑' v : ℤ × ℤ × ℤ, φ (normSq3 v)) = _
  rw [hfib]
  simp_rw [hcard]
  have hsum_d : Summable (fun d : ℕ ↦ (r3Count d : ℂ) * φ d) :=
    hsigma.sigma.congr fun d ↦ hcard d
  rw [hsum_d.tsum_eq_zero_add]
  have hr0 : r3Count 0 = 1 := by decide
  rw [hr0, Nat.cast_one, one_mul, tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ (r3Count d : ℂ) * φ d)]

private lemma bec3D_summable_F3 {X : ℝ} (hX : 0 < X) :
    Summable (fun v : ℤ × ℤ × ℤ ↦ becF (X ^ 2)⁻¹ (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) := by
  let t : ℝ := (X ^ 2)⁻¹
  have ht : 0 < t := by positivity
  obtain ⟨C0, hC0, hbF⟩ := becF_exp_bound ht
  have hs1 : Summable (fun n : ℤ ↦ Real.exp (-(t / 2) * (n : ℝ) ^ 2)) :=
    summable_int_exp_neg_sq (half_pos ht)
  have hdom : Summable (fun v : ℤ × ℤ × ℤ ↦
      C0 * (Real.exp (-(t / 2) * (v.1 : ℝ) ^ 2) *
        (Real.exp (-(t / 2) * (v.2.1 : ℝ) ^ 2) * Real.exp (-(t / 2) * (v.2.2 : ℝ) ^ 2)))) :=
    (hs1.mul_of_nonneg (hs1.mul_of_nonneg hs1 (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ (Real.exp_pos _).le)) (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ by positivity)).mul_left C0
  refine Summable.of_norm_bounded hdom fun v ↦ ?_
  have hsp : Real.exp (-(t / 2) * ((v.1 : ℝ) ^ 2 + (v.2.1 : ℝ) ^ 2 + (v.2.2 : ℝ) ^ 2)) =
      Real.exp (-(t / 2) * (v.1 : ℝ) ^ 2) *
        (Real.exp (-(t / 2) * (v.2.1 : ℝ) ^ 2) * Real.exp (-(t / 2) * (v.2.2 : ℝ) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact (hbF v.1 v.2.1 v.2.2).trans_eq (by rw [hsp])

private lemma bec3D_summable_G3 {X : ℝ} (hX : 0 < X) :
    Summable (fun m : ℤ × ℤ × ℤ ↦ becG3 (X ^ 2)⁻¹ (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ)) := by
  set t : ℝ := (X ^ 2)⁻¹
  let c : ℝ := 2 * Real.pi ^ (3 / 2 : ℝ) * X
  have hc : 0 < c := by positivity
  let S_j : ℝ := ∑' j : ℕ+, (j.val : ℝ) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ))
  have hsum_j : Summable (fun j : ℕ+ ↦ (j.val : ℝ) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ))) := by
    simpa only [pow_one] using summable_pow_mul_exp_neg_sqrt (half_pos hc) 1
  have hSj_nn : 0 ≤ S_j := tsum_nonneg fun _ ↦ by positivity
  let C3 : ℝ := ‖becG3 t 0 0 0‖ + 4 * Real.pi ^ 2 * X ^ 4 * S_j
  have hC3_nn : 0 ≤ C3 := by dsimp [C3]; positivity
  have hsum_exp : Summable (fun m : ℤ ↦ Real.exp (-(c / 6) * |(m : ℝ)|)) :=
    summable_int_exp_neg_abs (by positivity)
  have hdom : Summable (fun m : ℤ × ℤ × ℤ ↦
      C3 * (Real.exp (-(c / 6) * |(m.1 : ℝ)|) *
        (Real.exp (-(c / 6) * |(m.2.1 : ℝ)|) * Real.exp (-(c / 6) * |(m.2.2 : ℝ)|)))) :=
    (hsum_exp.mul_of_nonneg (hsum_exp.mul_of_nonneg hsum_exp (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ (Real.exp_pos _).le)) (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ by positivity)).mul_left C3
  refine Summable.of_norm_bounded hdom fun m ↦ ?_
  by_cases hm0 : m = (0, (0, 0))
  · subst hm0
    simp only [Int.cast_zero, abs_zero, mul_zero, Real.exp_zero, mul_one]
    dsimp [C3]; linarith [show 0 ≤ 4 * Real.pi ^ 2 * X ^ 4 * S_j by positivity]
  · have hM2_ge1 : (1 : ℝ) ≤ (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by
      have hint : (1 : ℤ) ≤ m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2 := by
        have hpos : m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2 ≠ 0 := by
          intro h
          have h1 : m.1 = 0 := by nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
          have h2 : m.2.1 = 0 := by nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
          have h3 : m.2.2 = 0 := by nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
          exact hm0 (Prod.ext h1 (Prod.ext h2 h3))
        have hnn : (0 : ℤ) ≤ m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2 := by positivity
        omega
      exact_mod_cast hint
    have hM2_pos : (0 : ℝ) < (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by linarith
    set M2 : ℝ := (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2
    have hsqrt_ge1 : 1 ≤ Real.sqrt M2 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM2_ge1
    have h3sqrt : |(m.1 : ℝ)| + |(m.2.1 : ℝ)| + |(m.2.2 : ℝ)| ≤ 3 * Real.sqrt M2 := by
      have ha1 : |(m.1 : ℝ)| ≤ Real.sqrt M2 := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m.2.1 : ℝ), sq_nonneg (m.2.2 : ℝ)])
      have ha2 : |(m.2.1 : ℝ)| ≤ Real.sqrt M2 := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.2 : ℝ)])
      have ha3 : |(m.2.2 : ℝ)| ≤ Real.sqrt M2 := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.1 : ℝ)])
      linarith
    rw [becG3_eval_nonzero hX hM2_pos, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hX]
    let term (j : ℕ+) : ℂ :=
      ((((j.val : ℝ) / Real.sqrt M2 : ℝ) : ℂ)) *
        ((-2 * (Real.pi : ℂ) ^ 2 * I) *
            Complex.exp (-sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
         (2 * (Real.pi : ℂ) ^ 2 * I) *
            Complex.exp (-sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))))
    have hterm_bd : ∀ j : ℕ+, ‖term j‖ ≤
        (4 * Real.pi ^ 2 * Real.exp (-(c / 2) * Real.sqrt M2)) *
          ((j.val : ℝ) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ))) := by
      intro j
      dsimp only [term]
      have hj1 : (1 : ℝ) ≤ Real.sqrt (j.val : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast j.pos)
      have hre0 : (-sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))).re =
          -c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ)) := by
        simp [sqRay0, c, Complex.mul_re]; ring
      have hre1 : (-sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))).re =
          -c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ)) := by
        simp [sqRay1, c, Complex.mul_re]; ring
      have hnorm_sum :
          ‖(-2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
           (2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))‖ ≤
          4 * Real.pi ^ 2 * Real.exp (-c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ))) := by
        calc _ ≤ ‖(-2 * (Real.pi : ℂ) ^ 2 * I) *
                  Complex.exp (-sqRay0 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))‖ +
                ‖(2 * (Real.pi : ℂ) ^ 2 * I) *
                  Complex.exp (-sqRay1 * (((Real.sqrt M2 * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))‖ :=
              norm_add_le _ _
          _ = 2 * Real.pi ^ 2 * Real.exp (-c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ))) +
              2 * Real.pi ^ 2 * Real.exp (-c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ))) := by
              simp only [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat, Complex.norm_real,
                Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one,
                Complex.norm_exp, hre0, hre1]
          _ = 4 * Real.pi ^ 2 * Real.exp (-c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ))) := by ring
      have hexp_split : Real.exp (-c * (Real.sqrt M2 * Real.sqrt (j.val : ℝ))) ≤
          Real.exp (-(c / 2) * Real.sqrt M2) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        have hmul_ge : Real.sqrt M2 + Real.sqrt (j.val : ℝ) ≤ 2 * (Real.sqrt M2 * Real.sqrt (j.val : ℝ)) := by
          nlinarith
        nlinarith
      have hinv_le : (Real.sqrt M2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt_ge1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc ((j.val : ℝ) / Real.sqrt M2) * _
          ≤ ((j.val : ℝ) * 1) * (4 * Real.pi ^ 2 *
              (Real.exp (-(c / 2) * Real.sqrt M2) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ)))) := by
            rw [div_eq_mul_inv]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hinv_le (by positivity))
              (hnorm_sum.trans (mul_le_mul_of_nonneg_left hexp_split (by positivity)))
              (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have htsum_bd : ‖∑' j : ℕ+, term j‖ ≤ (4 * Real.pi ^ 2 * Real.exp (-(c / 2) * Real.sqrt M2)) * S_j := by
      calc ‖∑' j : ℕ+, term j‖
          ≤ ∑' j : ℕ+, ‖term j‖ := norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
              hterm_bd (hsum_j.mul_left _))
        _ ≤ ∑' j : ℕ+, (4 * Real.pi ^ 2 * Real.exp (-(c / 2) * Real.sqrt M2)) *
              ((j.val : ℝ) * Real.exp (-(c / 2) * Real.sqrt (j.val : ℝ))) :=
            Summable.tsum_le_tsum hterm_bd (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
              hterm_bd (hsum_j.mul_left _)) (hsum_j.mul_left _)
        _ = (4 * Real.pi ^ 2 * Real.exp (-(c / 2) * Real.sqrt M2)) * S_j := tsum_mul_left
    have he_m : Real.exp (-(c / 2) * Real.sqrt M2) ≤
        Real.exp (-(c / 6) * |(m.1 : ℝ)|) *
          (Real.exp (-(c / 6) * |(m.2.1 : ℝ)|) * Real.exp (-(c / 6) * |(m.2.2 : ℝ)|)) := by
      rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    have hC3_le : 4 * Real.pi ^ 2 * X ^ 4 * S_j ≤ C3 := by
      dsimp [C3]; linarith [norm_nonneg (becG3 t 0 0 0)]
    change X ^ 4 * ‖∑' j : ℕ+, term j‖ ≤ _
    calc X ^ 4 * ‖∑' j : ℕ+, term j‖
        ≤ X ^ 4 * ((4 * Real.pi ^ 2 * Real.exp (-(c / 2) * Real.sqrt M2)) * S_j) :=
          mul_le_mul_of_nonneg_left htsum_bd (by positivity)
      _ = (4 * Real.pi ^ 2 * X ^ 4 * S_j) * Real.exp (-(c / 2) * Real.sqrt M2) := by ring
      _ ≤ C3 * (Real.exp (-(c / 6) * |(m.1 : ℝ)|) *
            (Real.exp (-(c / 6) * |(m.2.1 : ℝ)|) * Real.exp (-(c / 6) * |(m.2.2 : ℝ)|))) :=
          mul_le_mul hC3_le he_m (Real.exp_pos _).le hC3_nn

private lemma becF_continuous_x1 (t x₂ x₃ : ℝ) : Continuous (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) := by
  unfold becF
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    ((phiKernel_contDiff 0).continuous.comp
      (continuous_const.mul (((continuous_id.pow 2).add continuous_const).add continuous_const))))

private lemma becF_continuous_x2 (t x₁ x₃ : ℝ) : Continuous (fun x₂ : ℝ ↦ becF t x₁ x₂ x₃) := by
  unfold becF
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    ((phiKernel_contDiff 0).continuous.comp
      (continuous_const.mul ((continuous_const.add (continuous_id.pow 2)).add continuous_const))))

private lemma becF_continuous_x3 (t x₁ x₂ : ℝ) : Continuous (fun x₃ : ℝ ↦ becF t x₁ x₂ x₃) := by
  unfold becF
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    ((phiKernel_contDiff 0).continuous.comp
      (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))))

private lemma continuous_cexp_fourier (ξ : ℝ) :
    Continuous (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ξ) * I)) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul
      continuous_const)

private lemma becG1_continuous_x2 {t : ℝ} (ht : 0 < t) (m₁ x₃ : ℝ) :
    Continuous (fun x₂ : ℝ ↦ becG1 t m₁ x₂ x₃) := by
  obtain ⟨C0, hC0, hbF⟩ := becF_exp_bound ht
  simp only [becG1, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  refine continuous_of_dominated (bound := fun x₁ : ℝ ↦ C0 * Real.exp (-(t / 2) * x₁ ^ 2))
    (fun x₂ ↦ ((continuous_cexp_fourier m₁).mul (becF_continuous_x1 t x₂ x₃)).aestronglyMeasurable)
    (fun x₂ ↦ Eventually.of_forall fun x₁ ↦ ?_)
    ((integrable_exp_neg_mul_sq (half_pos ht)).const_mul C0)
    (Eventually.of_forall fun x₁ ↦ continuous_const.mul (becF_continuous_x2 t x₁ x₃))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (hbF x₁ x₂ x₃).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₂, sq_nonneg x₃])) hC0)

private lemma becG1_continuous_x3 {t : ℝ} (ht : 0 < t) (m₁ x₂ : ℝ) :
    Continuous (fun x₃ : ℝ ↦ becG1 t m₁ x₂ x₃) := by
  obtain ⟨C0, hC0, hbF⟩ := becF_exp_bound ht
  simp only [becG1, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  refine continuous_of_dominated (bound := fun x₁ : ℝ ↦ C0 * Real.exp (-(t / 2) * x₁ ^ 2))
    (fun x₃ ↦ ((continuous_cexp_fourier m₁).mul (becF_continuous_x1 t x₂ x₃)).aestronglyMeasurable)
    (fun x₃ ↦ Eventually.of_forall fun x₁ ↦ ?_)
    ((integrable_exp_neg_mul_sq (half_pos ht)).const_mul C0)
    (Eventually.of_forall fun x₁ ↦ continuous_const.mul (becF_continuous_x3 t x₁ x₂))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (hbF x₁ x₂ x₃).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₂, sq_nonneg x₃])) hC0)

private lemma becG2_continuous_x3 {t : ℝ} (ht : 0 < t) (m₁ m₂ : ℝ) :
    Continuous (fun x₃ : ℝ ↦ becG2 t m₁ m₂ x₃) := by
  obtain ⟨K1, hK1, hbG1⟩ := becG1_bound ht
  simp only [becG2, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  refine continuous_of_dominated (bound := fun x₂ : ℝ ↦ K1 * Real.exp (-(t / 4) * x₂ ^ 2))
    (fun x₃ ↦ ((continuous_cexp_fourier m₂).mul (becG1_continuous_x2 ht m₁ x₃)).aestronglyMeasurable)
    (fun x₃ ↦ Eventually.of_forall fun x₂ ↦ ?_)
    ((integrable_exp_neg_mul_sq (show 0 < t / 4 by positivity)).const_mul K1)
    (Eventually.of_forall fun x₂ ↦ continuous_const.mul (becG1_continuous_x3 ht m₁ x₂))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h1 : K1 / (1 + m₁ ^ 2) ≤ K1 := div_le_self hK1 (by nlinarith [sq_nonneg m₁])
  have h2 : Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) ≤ Real.exp (-(t / 4) * x₂ ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₃])
  exact (hbG1 m₁ x₂ x₃).trans (mul_le_mul h1 h2 (Real.exp_pos _).le hK1)

private lemma bec3D_iterated_poisson {X : ℝ} (hX : 0 < X) :
    (∑' v : ℤ × ℤ × ℤ, becF (X ^ 2)⁻¹ (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) =
      ∑' m : ℤ × ℤ × ℤ, becG3 (X ^ 2)⁻¹ (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ) := by
  set t : ℝ := (X ^ 2)⁻¹
  have ht : 0 < t := by positivity
  obtain ⟨C0, hC0, hbF⟩ := becF_exp_bound ht
  obtain ⟨K1, hK1, hbG1⟩ := becG1_bound ht
  obtain ⟨K2, hK2, hbG2⟩ := becG2_bound ht
  have hsum_F3 : Summable (fun v : ℤ × ℤ × ℤ ↦ becF t (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) :=
    bec3D_summable_F3 hX
  have hsum_G3 : Summable (fun m : ℤ × ℤ × ℤ ↦ becG3 t (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ)) :=
    bec3D_summable_G3 hX
  -- Three-step iterated 1D Poisson summation: `∑' v : ℤ³, becF t v = ∑' m : ℤ³, becG3 t m`!
  have hpois1 (x₂ x₃ : ℝ) : (∑' n₁ : ℤ, becF t (n₁ : ℝ) x₂ x₃) = ∑' m₁ : ℤ, becG1 t (m₁ : ℝ) x₂ x₃ := by
    have hbigO : (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) :=
      isBigO_cocompact_of_exp_neg_sq hC0 (half_pos ht) fun x₁ ↦
        (hbF x₁ x₂ x₃).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₂, sq_nonneg x₃])) hC0)
    have hsum_m1 : Summable (fun m₁ : ℤ ↦ 𝓕 (fun x₁ : ℝ ↦ becF t x₁ x₂ x₃) (m₁ : ℝ)) := by
      refine Summable.of_norm_bounded (summable_int_inv_one_add_sq.mul_left
          (K1 * Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)))) fun m₁ ↦ ?_
      exact (hbG1 m₁ x₂ x₃).trans_eq (by ring)
    have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      (becF_continuous_x1 t x₂ x₃) one_lt_two hbigO hsum_m1 0
    simpa only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one, becG1] using hp
  have hpois2 (m₁ : ℤ) (x₃ : ℝ) :
      (∑' n₂ : ℤ, becG1 t (m₁ : ℝ) (n₂ : ℝ) x₃) = ∑' m₂ : ℤ, becG2 t (m₁ : ℝ) (m₂ : ℝ) x₃ := by
    have hbigO : (fun x₂ : ℝ ↦ becG1 t (m₁ : ℝ) x₂ x₃) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) :=
      isBigO_cocompact_of_exp_neg_sq hK1 (show 0 < t / 4 by positivity) fun x₂ ↦ by
        have h1 : K1 / (1 + (m₁ : ℝ) ^ 2) ≤ K1 := div_le_self hK1 (by nlinarith [sq_nonneg (m₁ : ℝ)])
        have h2 : Real.exp (-(t / 4) * (x₂ ^ 2 + x₃ ^ 2)) ≤ Real.exp (-(t / 4) * x₂ ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₃])
        exact (hbG1 m₁ x₂ x₃).trans (mul_le_mul h1 h2 (Real.exp_pos _).le hK1)
    have hsum_m2 : Summable (fun m₂ : ℤ ↦ 𝓕 (fun x₂ : ℝ ↦ becG1 t (m₁ : ℝ) x₂ x₃) (m₂ : ℝ)) := by
      refine Summable.of_norm_bounded (summable_int_inv_one_add_sq.mul_left
          (K2 / (1 + (m₁ : ℝ) ^ 2) * Real.exp (-(t / 4) * x₃ ^ 2))) fun m₂ ↦ ?_
      exact (hbG2 m₁ m₂ x₃).trans_eq (by rw [div_eq_mul_inv, mul_inv]; ring)
    have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      (becG1_continuous_x2 ht m₁ x₃) one_lt_two hbigO hsum_m2 0
    simpa only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one, becG2] using hp
  have hpois3 (m₁ m₂ : ℤ) :
      (∑' n₃ : ℤ, becG2 t (m₁ : ℝ) (m₂ : ℝ) (n₃ : ℝ)) = ∑' m₃ : ℤ, becG3 t (m₁ : ℝ) (m₂ : ℝ) (m₃ : ℝ) := by
    have hbigO : (fun x₃ : ℝ ↦ becG2 t (m₁ : ℝ) (m₂ : ℝ) x₃) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) :=
      isBigO_cocompact_of_exp_neg_sq hK2 (show 0 < t / 4 by positivity) fun x₃ ↦ by
        have h1 : K2 / ((1 + (m₁ : ℝ) ^ 2) * (1 + (m₂ : ℝ) ^ 2)) ≤ K2 :=
          div_le_self hK2 (by nlinarith [sq_nonneg (m₁ : ℝ), sq_nonneg (m₂ : ℝ)])
        exact (hbG2 m₁ m₂ x₃).trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
    have hsum_m3 : Summable (fun m₃ : ℤ ↦ 𝓕 (fun x₃ : ℝ ↦ becG2 t (m₁ : ℝ) (m₂ : ℝ) x₃) (m₃ : ℝ)) :=
      (hsum_G3.prod_factor m₁).prod_factor m₂
    have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      (becG2_continuous_x3 ht m₁ m₂) one_lt_two hbigO hsum_m3 0
    simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hp
    exact hp
  have hsum_G1_pair (x₃ : ℝ) : Summable (fun p : ℤ × ℤ ↦ becG1 t (p.2 : ℝ) (p.1 : ℝ) x₃) := by
    have hs_inv := summable_int_inv_one_add_sq
    have hs_exp := summable_int_exp_neg_sq (show 0 < t / 4 by positivity)
    have hdom : Summable (fun p : ℤ × ℤ ↦
        (K1 * Real.exp (-(t / 4) * x₃ ^ 2)) *
          (Real.exp (-(t / 4) * (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :=
      (hs_exp.mul_of_nonneg hs_inv (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ by positivity)).mul_left _
    refine Summable.of_norm_bounded hdom fun p ↦ ?_
    have hsp : Real.exp (-(t / 4) * ((p.1 : ℝ) ^ 2 + x₃ ^ 2)) =
        Real.exp (-(t / 4) * x₃ ^ 2) * Real.exp (-(t / 4) * (p.1 : ℝ) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    exact (hbG1 p.2 p.1 x₃).trans_eq (by rw [hsp]; ring)
  have hsum_G2_triple : Summable (fun p : ℤ × ℤ × ℤ ↦ becG2 t (p.2.1 : ℝ) (p.2.2 : ℝ) (p.1 : ℝ)) := by
    have hs_inv := summable_int_inv_one_add_sq
    have hs_exp := summable_int_exp_neg_sq (show 0 < t / 4 by positivity)
    have hdom : Summable (fun p : ℤ × ℤ × ℤ ↦
        K2 * (Real.exp (-(t / 4) * (p.1 : ℝ) ^ 2) *
          ((1 + (p.2.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2.2 : ℝ) ^ 2)⁻¹))) :=
      (hs_exp.mul_of_nonneg (hs_inv.mul_of_nonneg hs_inv (fun _ ↦ by positivity) (fun _ ↦ by positivity))
        (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ by positivity)).mul_left K2
    refine Summable.of_norm_bounded hdom fun p ↦ ?_
    exact (hbG2 p.2.1 p.2.2 p.1).trans_eq (by rw [div_eq_mul_inv, mul_inv]; ring)
  let eRev : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) :=
    { toFun := fun v ↦ (v.2.2, (v.2.1, v.1))
      invFun := fun v ↦ (v.2.2, (v.2.1, v.1))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsum_F3_rev : Summable (fun p : ℤ × ℤ × ℤ ↦ becF t (p.2.2 : ℝ) (p.2.1 : ℝ) (p.1 : ℝ)) :=
    eRev.summable_iff.mpr hsum_F3
  have hLHS_iter : (∑' v : ℤ × ℤ × ℤ, becF t (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) =
      ∑' n₃ : ℤ, ∑' n₂ : ℤ, ∑' n₁ : ℤ, becF t (n₁ : ℝ) (n₂ : ℝ) (n₃ : ℝ) := by
    rw [← eRev.tsum_eq]
    change (∑' p : ℤ × ℤ × ℤ, becF t (p.2.2 : ℝ) (p.2.1 : ℝ) (p.1 : ℝ)) = _
    rw [hsum_F3_rev.tsum_prod]
    apply tsum_congr; intro n₃
    exact (hsum_F3_rev.prod_factor n₃).tsum_prod
  have hRHS_iter : (∑' m : ℤ × ℤ × ℤ, becG3 t (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ)) =
      ∑' m₁ : ℤ, ∑' m₂ : ℤ, ∑' m₃ : ℤ, becG3 t (m₁ : ℝ) (m₂ : ℝ) (m₃ : ℝ) := by
    rw [hsum_G3.tsum_prod]
    apply tsum_congr; intro m₁
    exact (hsum_G3.prod_factor m₁).tsum_prod
  rw [hLHS_iter, hRHS_iter]
  have hstep12 (n₃ : ℤ) :
      (∑' n₂ : ℤ, ∑' n₁ : ℤ, becF t (n₁ : ℝ) (n₂ : ℝ) (n₃ : ℝ)) =
      ∑' m : ℤ × ℤ, becG2 t (m.1 : ℝ) (m.2 : ℝ) (n₃ : ℝ) := by
    simp_rw [hpois1]
    rw [← Summable.tsum_comm (f := fun n₂ m₁ : ℤ ↦ becG1 t (m₁ : ℝ) (n₂ : ℝ) (n₃ : ℝ)) (hsum_G1_pair n₃)]
    simp_rw [hpois2]
    exact (hsum_G2_triple.prod_factor n₃).tsum_prod.symm
  simp_rw [hstep12]
  rw [← Summable.tsum_comm (f := fun (n₃ : ℤ) (m : ℤ × ℤ) ↦ becG2 t (m.1 : ℝ) (m.2 : ℝ) (n₃ : ℝ))
        hsum_G2_triple]
  have hG3_pair : Summable (fun q : ℤ × ℤ ↦ ∑' m₃ : ℤ, becG3 t (q.1 : ℝ) (q.2 : ℝ) (m₃ : ℝ)) := by
    have h1 : Summable (fun q : ℤ × ℤ ↦ ∑' n₃ : ℤ, becG2 t (q.1 : ℝ) (q.2 : ℝ) (n₃ : ℝ)) :=
      ((Equiv.prodComm (ℤ × ℤ) ℤ).summable_iff.mpr hsum_G2_triple).prod
    exact h1.congr fun q ↦ hpois3 q.1 q.2
  simp_rw [hpois3]
  exact hG3_pair.tsum_prod

/-- **100% Unconditional Analytic Identity for the Physical 3D Ideal Bose–Einstein Condensate**:
For EVERY `X > 0`:
```
∑'_{N : ℕ+} r_3(N) * N / (exp(N / X²) - 1)
  = bec3DConst * X^5 - X^2
    + X^4 * ∑'_{d : ℕ+} ∑'_{j : ℕ+} (r_3(d) * j / √d) *
        ((-2 π² I) * exp(-sqRay0 * √d * √j * X)
       + ( 2 π² I) * exp(-sqRay1 * √d * √j * X))
``` -/
theorem bec3D_analytic_identity {X : ℝ} (hX : 0 < X) :
    (∑' N : ℕ+, (((r3Count N.val : ℝ) * (N.val : ℝ) /
        (Real.exp ((N.val : ℝ) / X ^ 2) - 1) : ℝ) : ℂ)) =
      bec3DConst * (X : ℂ) ^ 5 - (X : ℂ) ^ 2 +
      (X : ℂ) ^ 4 * ∑' d : ℕ+, ∑' j : ℕ+,
        ((((r3Count d.val : ℝ) * (j.val : ℝ) / Real.sqrt (d.val : ℝ) : ℝ) : ℂ)) *
          ((-2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay0 * (((Real.sqrt (d.val : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
           (2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay1 * (((Real.sqrt (d.val : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))) := by
  set t : ℝ := (X ^ 2)⁻¹
  have ht : 0 < t := by positivity
  have hsum_F3 : Summable (fun v : ℤ × ℤ × ℤ ↦ becF t (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) :=
    bec3D_summable_F3 hX
  have hsum_G3 : Summable (fun m : ℤ × ℤ × ℤ ↦ becG3 t (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ)) :=
    bec3D_summable_G3 hX
  have h3D_poisson :
      (∑' v : ℤ × ℤ × ℤ, becF t (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) =
      ∑' m : ℤ × ℤ × ℤ, becG3 t (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ) :=
    bec3D_iterated_poisson hX
  -- 4. Group BOTH sides of `h3D_poisson` radially using `tsum_int3_radial`!
  let φL (d : ℕ) : ℂ :=
    if d = 0 then ((X ^ 2 : ℝ) : ℂ)
    else (((d : ℝ) / (Real.exp ((d : ℝ) / X ^ 2) - 1) : ℝ) : ℂ)
  have hφL_eq : (fun v : ℤ × ℤ × ℤ ↦ becF t (v.1 : ℝ) (v.2.1 : ℝ) (v.2.2 : ℝ)) =
      fun v : ℤ × ℤ × ℤ ↦ φL (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat := by
    funext v
    have hnn : (0 : ℤ) ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by positivity
    have hcast : (((v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat : ℕ) : ℝ) =
        (v.1 : ℝ) ^ 2 + (v.2.1 : ℝ) ^ 2 + (v.2.2 : ℝ) ^ 2 := by
      have hZ : (((v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat : ℕ) : ℤ) = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 :=
        Int.toNat_of_nonneg hnn
      exact_mod_cast hZ
    by_cases hd : (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2).toNat = 0
    · have h0 : (v.1 : ℝ) ^ 2 + (v.2.1 : ℝ) ^ 2 + (v.2.2 : ℝ) ^ 2 = 0 := by rw [← hcast, hd]; simp
      simp only [φL, hd, ↓reduceIte, becF, h0, mul_zero, phiKernel_zero, mul_one, t, inv_inv]
    · have hne : (v.1 : ℝ) ^ 2 + (v.2.1 : ℝ) ^ 2 + (v.2.2 : ℝ) ^ 2 ≠ 0 := by
        rw [← hcast]; exact Nat.cast_ne_zero.mpr hd
      simp only [φL, hd, ↓reduceIte]
      rw [becF_eq_of_ne_zero ht hne, ← hcast]
      congr 1; dsimp [t]; rw [inv_mul_eq_div]
  let φR (d : ℕ) : ℂ :=
    if d = 0 then bec3DConst * (X : ℂ) ^ 5
    else (X : ℂ) ^ 4 * ∑' j : ℕ+,
      ((((j.val : ℝ) / Real.sqrt (d : ℝ) : ℝ) : ℂ)) *
        ((-2 * (Real.pi : ℂ) ^ 2 * I) *
            Complex.exp (-sqRay0 * (((Real.sqrt (d : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
         (2 * (Real.pi : ℂ) ^ 2 * I) *
            Complex.exp (-sqRay1 * (((Real.sqrt (d : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))))
  have hφR_eq : (fun m : ℤ × ℤ × ℤ ↦ becG3 t (m.1 : ℝ) (m.2.1 : ℝ) (m.2.2 : ℝ)) =
      fun m : ℤ × ℤ × ℤ ↦ φR (m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2).toNat := by
    funext m
    have hnn : (0 : ℤ) ≤ m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2 := by positivity
    have hcast : (((m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2).toNat : ℕ) : ℝ) =
        (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by
      have hZ : (((m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2).toNat : ℕ) : ℤ) = m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2 :=
        Int.toNat_of_nonneg hnn
      exact_mod_cast hZ
    by_cases hd : (m.1 ^ 2 + m.2.1 ^ 2 + m.2.2 ^ 2).toNat = 0
    · have h0 : (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 = 0 := by rw [← hcast, hd]; simp
      have hm1 : m.1 = 0 := by
        have : (m.1 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.1 : ℝ), sq_nonneg (m.2.2 : ℝ)]
        exact_mod_cast this
      have hm2 : m.2.1 = 0 := by
        have : (m.2.1 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.1 : ℝ), sq_nonneg (m.2.2 : ℝ)]
        exact_mod_cast this
      have hm3 : m.2.2 = 0 := by
        have : (m.2.2 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.1 : ℝ), sq_nonneg (m.2.2 : ℝ)]
        exact_mod_cast this
      rw [hd]
      simp only [φR, ↓reduceIte, hm1, hm2, hm3, Int.cast_zero, t, becG3_eval_zero hX]
    · have hpos : (0 : ℝ) < (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by
        rw [← hcast]; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
      simp only [φR, hd, ↓reduceIte]
      rw [becG3_eval_nonzero hX hpos, ← hcast]
  rw [hφL_eq, hφR_eq] at h3D_poisson
  rw [tsum_int3_radial φL (hφL_eq ▸ hsum_F3), tsum_int3_radial φR (hφR_eq ▸ hsum_G3)] at h3D_poisson
  have hL_simpl : (∑' N : ℕ+, (r3Count N.val : ℂ) * φL N.val) =
      ∑' N : ℕ+, (((r3Count N.val : ℝ) * (N.val : ℝ) /
        (Real.exp ((N.val : ℝ) / X ^ 2) - 1) : ℝ) : ℂ) := by
    apply tsum_congr; intro N
    simp only [φL, N.ne_zero, ↓reduceIte, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    congr 1; ring
  have hR_simpl : (∑' d : ℕ+, (r3Count d.val : ℂ) * φR d.val) =
      (X : ℂ) ^ 4 * ∑' d : ℕ+, ∑' j : ℕ+,
        ((((r3Count d.val : ℝ) * (j.val : ℝ) / Real.sqrt (d.val : ℝ) : ℝ) : ℂ)) *
          ((-2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay0 * (((Real.sqrt (d.val : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ))) +
           (2 * (Real.pi : ℂ) ^ 2 * I) *
              Complex.exp (-sqRay1 * (((Real.sqrt (d.val : ℝ) * Real.sqrt (j.val : ℝ) * X : ℝ) : ℂ)))) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro d
    simp only [φR, d.ne_zero, ↓reduceIte]
    rw [mul_left_comm, ← tsum_mul_left]
    congr 1
    apply tsum_congr; intro j
    rw [← mul_assoc]; congr 1; push_cast; ring
  rw [hL_simpl, hR_simpl] at h3D_poisson
  have hφL0 : φL 0 = (X : ℂ) ^ 2 := by simp [φL]
  have hφR0 : φR 0 = bec3DConst * (X : ℂ) ^ 5 := by simp [φR]
  rw [hφL0, hφR0] at h3D_poisson
  linear_combination h3D_poisson

end
end CubicTheta.AllD
