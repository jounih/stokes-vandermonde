module

public import Laplace
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! A test-function version of the beta–gamma identity. It identifies an
ordinary ray sum of a scaled Euler kernel with a single Kummer integral. -/
public section
namespace CubicTheta
open Complex Filter Set MeasureTheory
open scoped Topology
noncomputable section

def betaAverage (a b : ℂ) (f : ℝ → ℂ) (r : ℝ) :=
  ∫ t in (0:ℝ)..1, (t:ℂ)^(a-1) * (1-(t:ℂ))^(b-1) * f (r*t)

private theorem beta_scale (a b : ℂ) (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ y in (0:ℝ)..r, (y:ℂ)^(a-1) * ((r:ℂ)-y)^(b-1) * f y) =
      (r:ℂ)^(a+b-1)*betaAverage a b f r := by
  have rn : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have factor : (r:ℂ)^(a+b-1) = r*((r:ℂ)^(a-1)*(r:ℂ)^(b-1)) := by
    rw [show a+b-1=1+(a-1)+(b-1) by ring,cpow_add _ _ rn,cpow_add _ _ rn,cpow_one,mul_assoc]
  rw [betaAverage,factor,mul_assoc,← intervalIntegral.integral_const_mul,← real_smul,
    ← zero_div r, ← div_self hr.ne', ← intervalIntegral.integral_comp_div _ hr.ne',zero_div]
  rw [intervalIntegral.integral_of_le hr.le,intervalIntegral.integral_of_le hr.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [mul_div_cancel₀ _ hr.ne']
  rw [← mul_assoc ((r:ℂ)^(a-1)*(r:ℂ)^(b-1)),mul_mul_mul_comm,
    ← mul_cpow_ofReal_nonneg hr.le (div_pos hx.1 hr).le, ofReal_div,mul_div_cancel₀ _ rn,
    (by push_cast; rfl : (1:ℂ)-(x:ℂ)/r=↑(1-x/r)),
    ← mul_cpow_ofReal_nonneg hr.le (sub_nonneg.mpr ((div_le_one hr).mpr hx.2))]
  push_cast; rw [mul_sub,mul_one,mul_div_cancel₀ _ rn]

/-- With a+b=1, exponential averaging of f(vt) under a beta weight
reduces to gamma averaging of f(y). The two sides use actual integrals. -/
theorem beta_gamma_transport {a b : ℂ} (hab : a+b=1) (hb : 0 < b.re)
    (f : ℝ → ℂ)
    (hf : IntegrableOn (fun y : ℝ ↦ (Real.exp (-y):ℂ)*(y:ℂ)^(a-1)*f y) (Ioi 0)) :
    (∫ v in Ioi (0:ℝ), (Real.exp (-v):ℂ)*betaAverage a b f v) =
    (∫ y in Ioi (0:ℝ), (Real.exp (-y):ℂ)*(y:ℂ)^(a-1)*f y) * Gamma b := by
  have hc := integral_posConvolution hf (GammaIntegral_convergent hb) (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at hc
  rw [Gamma_eq_integral hb,GammaIntegral,← hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have sc := beta_scale a b f hv
  rw [hab,sub_self,cpow_zero,one_mul] at sc
  dsimp only
  rw [← sc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  have ex : (Real.exp (-v):ℂ) = (Real.exp (-y):ℂ)*(Real.exp (-(v-y)):ℂ) := by
    rw [← ofReal_mul,← Real.exp_add]; congr 2; ring
  dsimp only; rw [ex]; push_cast; ring

/-- The shape 5/6 is attached to the test variable, and 1/6 to its
complement. Consequently the two upper hypergeometric parameters differ. -/
def cubicBetaKernel (c : ℂ) (u : ℝ) : ℂ :=
  (Gamma (5/6)*Gamma (1/6))⁻¹ *
    betaAverage (5/6) (1/6) (fun y ↦ (1+(y:ℂ)/(2*c))^(-(1/6:ℂ))) u

private theorem kummer_integrable {d : ℂ} (hd : 0 ≤ d.re) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-y):ℂ)*(y:ℂ)^((5/6:ℂ)-1)*
      (1+(y:ℂ)*d)^(-(1/6:ℂ))) (Ioi 0) := by
  have hg := GammaIntegral_convergent (s := (5/6:ℂ)) (by norm_num)
  have hpos (y : ℝ) (hy : y ∈ Ioi (0:ℝ)) : 1 ≤ (1+(y:ℂ)*d).re := by
    simp [Complex.add_re,Complex.mul_re,mul_nonneg (le_of_lt hy) hd]
  have cont : ContinuousOn (fun y : ℝ ↦ (1+(y:ℂ)*d)^(-(1/6:ℂ))) (Ioi 0) :=
    ContinuousOn.cpow (by fun_prop) continuousOn_const fun y hy ↦
      mem_slitPlane_iff.mpr (.inl (lt_of_lt_of_le zero_lt_one (hpos y hy)))
  apply hg.norm.mono'
  · exact hg.aestronglyMeasurable.mul (cont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  have hn := (hpos y hy).trans (le_refl _)
  have bound := hn.trans (Complex.re_le_norm _)
  rw [show -(1/6:ℂ) = ((-(1/6:ℝ):ℝ):ℂ) by norm_num,Complex.norm_cpow_real]
  exact Real.rpow_le_one_of_one_le_of_nonpos bound (by norm_num)

theorem cubicBeta_raySum {c : ℂ} (hc : 0 < c.re) {p : ℝ} (hp : 0 < p) :
    raySum (cubicBetaKernel c) p =
      (Gamma (5/6))⁻¹ * ∫ y in Ioi (0:ℝ), (Real.exp (-y):ℂ)*(y:ℂ)^((5/6:ℂ)-1)*
        (1+(y:ℂ)/(2*c*p))^(-(1/6:ℂ)) := by
  let f (y : ℝ) := (1+(y:ℂ)/(2*c*p))^(-(1/6:ℂ))
  have hd : 0 ≤ ((2*c*p)⁻¹).re := by
    rw [Complex.inv_re]; apply div_nonneg _ (Complex.normSq_nonneg _)
    simp [Complex.mul_re]; positivity
  have hf := kummer_integrable hd
  simp only [← div_eq_mul_inv] at hf
  have tr := beta_gamma_transport (a := 5/6) (b := 1/6) (by norm_num) (by norm_num) f hf
  have sc (v : ℝ) : cubicBetaKernel c (v/p) =
      (Gamma (5/6)*Gamma (1/6))⁻¹ * betaAverage (5/6) (1/6) f v := by
    unfold cubicBetaKernel betaAverage f
    congr 1
    apply intervalIntegral.integral_congr
    intro y _
    push_cast
    rw [show (v:ℂ)/p*y/(2*c) = v*y/(2*c*p) by ring]
  unfold raySum
  simp only [sc,Complex.real_smul]
  simp_rw [mul_left_comm (b := (Gamma (5/6)*Gamma (1/6))⁻¹)]
  rw [integral_const_mul,tr]
  have hn : Gamma (1/6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  dsimp [f]; field_simp

end
end CubicTheta
