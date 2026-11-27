module

public import PakStokes.BetaGammaTransport
import all PakStokes.BetaGammaTransport
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Analyticity and the common unit bound for the same Euler kernel whose
ray sum is the physical Kummer integral in BetaGammaTransport. -/
public section
namespace CubicTheta
open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section

private def weight (y : ℝ) : ℂ := (y:ℂ)^((5/6:ℂ)-1)*(1-(y:ℂ))^((1/6:ℂ)-1)
private abbrev μ := (volume : Measure ℝ).restrict (Ioc 0 1)
private def Z := Gamma (5/6)*Gamma (1/6)
private def avg (z : ℂ) := Z⁻¹ * ∫ y, weight y * (1+z*y)^(-(1/6:ℂ)) ∂μ
private def domain := {z : ℂ | -(1/2:ℝ) < z.re}

private theorem wInt : Integrable weight μ :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (betaIntegral_convergent (u := 5/6) (v := 1/6) (by norm_num) (by norm_num))

private theorem mass : ∫ y, weight y ∂μ = Z := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  change betaIntegral (5/6) (1/6) = _
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num),
    show (5/6:ℂ)+1/6 = 1 by norm_num,Gamma_one,div_one]; rfl

private theorem absMass : (∫ y, ‖weight y‖ ∂μ) = ‖Z‖ := by
  have eqmass : ((∫ y, ‖weight y‖ ∂μ : ℝ):ℂ) = Z := by
    rw [← integral_complex_ofReal,← mass]; apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
    have a (r : ℝ) (hr : 0 ≤ r) (d : ℝ) : ((r^d:ℝ):ℂ) = (r:ℂ)^(d:ℂ) :=
      Complex.ofReal_cpow hr d
    have we : weight y = ((y^((5/6:ℝ)-1)*(1-y)^((1/6:ℝ)-1):ℝ):ℂ) := by
      unfold weight; rw [ofReal_mul,a _ hy.1.le,a _ (sub_nonneg.mpr hy.2)]; push_cast; rfl
    rw [we,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hy.1.le _) (Real.rpow_nonneg (sub_nonneg.mpr hy.2) _))]
  rw [← eqmass,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]

private theorem base_re {z : ℂ} (hz : z ∈ domain) {y : ℝ} (hy : y ∈ Ioc (0:ℝ) 1) :
    1/2 ≤ (1+z*y).re := by
  change -(1/2:ℝ) < z.re at hz
  simp only [Complex.add_re,one_re,Complex.mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  nlinarith [mul_nonneg (show 0 ≤ z.re+1/2 by linarith) hy.1.le,hy.2]

private theorem avgAnalytic : AnalyticOnNhd ℂ avg domain := by
  have op : IsOpen domain := isOpen_lt continuous_const continuous_re
  apply DifferentiableOn.analyticOnNhd _ op
  intro z hz
  let p : ℂ := -(1/6)
  let f (u : ℂ) (y : ℝ) := weight y*(1+u*y)^p
  let df (u : ℂ) (y : ℝ) := weight y*((y:ℂ)*p*(1+u*y)^(p-1))
  have slit (u) (hu : u ∈ domain) (y) (hy : y ∈ Ioc (0:ℝ) 1) : 1+u*y ∈ slitPlane :=
    mem_slitPlane_iff.mpr (.inl (lt_of_lt_of_le (by norm_num) (base_re hu hy)))
  have cc (u) (hu : u ∈ domain) (e : ℂ) :
      ContinuousOn (fun y : ℝ ↦ (1+u*y)^e) (Ioc 0 1) :=
    ContinuousOn.cpow (by fun_prop) continuousOn_const (slit u hu)
  have bound (u) (hu : u ∈ domain) (y) (hy : y ∈ Ioc (0:ℝ) 1) (r : ℝ) (hr : r ≤ 0) :
      ‖(1+u*y)^(r:ℂ)‖ ≤ (1/2:ℝ)^r := by
    rw [Complex.norm_cpow_real]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) ((base_re hu hy).trans (Complex.re_le_norm _)) hr
  have meas (u) (hu : u ∈ domain) : AEStronglyMeasurable (f u) μ :=
    wInt.aestronglyMeasurable.mul ((cc u hu _).aestronglyMeasurable measurableSet_Ioc)
  have hInt : Integrable (f z) μ := by
    apply (wInt.norm.mul_const ((1/2:ℝ)^(-(1/6:ℝ)))).mono' (meas z hz)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
    simpa [f,p,norm_mul] using
      mul_le_mul_of_nonneg_left (bound z hz y hy (-(1/6:ℝ)) (by norm_num)) (norm_nonneg (weight y))
  have dm : AEStronglyMeasurable (df z) μ := wInt.aestronglyMeasurable.mul
    (((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).mul (cc z hz _)).aestronglyMeasurable measurableSet_Ioc)
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := f) (F' := df)
    (bound := fun y ↦ ‖weight y‖*(‖p‖*(1/2:ℝ)^(-(7/6:ℝ)))) (op.mem_nhds hz)
    (eventually_of_mem (op.mem_nhds hz) meas) hInt dm
  have h := derivative (by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy u hu
    have hy' : ‖(y:ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg hy.1.le] using hy.2
    have hp : p-1 = ((-(7/6:ℝ):ℝ):ℂ) := by norm_num [p]
    simp only [df,norm_mul,hp]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) hy')
      (bound u hu y hy _ (by norm_num)) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
    (wInt.norm.mul_const _) (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy u hu
      have d : HasDerivAt (fun w : ℂ ↦ 1+w*y) (y:ℂ) u := by
        simpa using ((hasDerivAt_id u).mul_const (y:ℂ)).const_add 1
      simpa [f,df,mul_assoc,mul_comm,mul_left_comm] using (d.cpow_const (c := p) (slit u hu y hy)).const_mul (weight y))
  exact (h.2.const_mul Z⁻¹).differentiableAt.differentiableWithinAt

private theorem ray_eq (c : ℂ) (u : ℝ) : cubicBetaKernel c u = avg (u/(2*c)) := by
  unfold cubicBetaKernel betaAverage avg
  rw [intervalIntegral.integral_of_le zero_le_one]; congr 1
  apply setIntegral_congr_fun measurableSet_Ioc; intro y _
  unfold weight; push_cast; ring_nf

private theorem inv_re_nonneg {c : ℂ} (hc : 0 < c.re) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ ((u:ℂ)/(2*c)).re := by
  rw [div_eq_mul_inv,Complex.mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,Complex.inv_re]
  apply mul_nonneg hu (div_nonneg _ (normSq_nonneg _)); simp; positivity

theorem cubicBeta_analytic {c : ℂ} (hc : 0 < c.re) :
    AnalyticOnNhd ℝ (cubicBetaKernel c) (Ici 0) := by
  let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℂ ℂ) (2*c)⁻¹).restrictScalars ℝ |>.comp ofRealCLM
  have e : cubicBetaKernel c = avg ∘ L := funext fun x ↦ by simp [ray_eq,L,div_eq_mul_inv,mul_comm]
  rw [e]; intro u hu
  have hd : (u:ℂ)/(2*c) ∈ domain := lt_of_lt_of_le (by norm_num) (inv_re_nonneg hc hu)
  have eq : L u = (u:ℂ)/(2*c) := by simp [L,div_eq_mul_inv,mul_comm]
  exact ((avgAnalytic _ (eq ▸ hd)).restrictScalars (𝕜 := ℝ)).comp (L.analyticAt u)

theorem cubicBeta_zero (c : ℂ) : cubicBetaKernel c 0 = 1 := by
  rw [ray_eq]; simp only [ofReal_zero,zero_div,avg,zero_mul,add_zero,one_cpow,mul_one,mass]
  apply inv_mul_cancel₀
  exact mul_ne_zero (Gamma_ne_zero_of_re_pos (by norm_num)) (Gamma_ne_zero_of_re_pos (by norm_num))

theorem cubicBeta_bound {c : ℂ} (hc : 0 < c.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖cubicBetaKernel c u‖ ≤ 1 := by
  rw [ray_eq,avg,norm_mul,norm_inv]
  have h : ‖∫ y, weight y*(1+((u:ℂ)/(2*c))*y)^(-(1/6:ℂ)) ∂μ‖ ≤ ‖Z‖ := by
    rw [← absMass]; apply norm_integral_le_of_norm_le wInt.norm
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
    rw [norm_mul]; apply mul_le_of_le_one_right (norm_nonneg _)
    rw [show -(1/6:ℂ) = ((-(1/6:ℝ):ℝ):ℂ) by norm_num,Complex.norm_cpow_real]
    apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
    apply le_trans _ (Complex.re_le_norm _)
    simp [Complex.add_re,Complex.mul_re,mul_nonneg (inv_re_nonneg hc hu) hy.1.le]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _))

end
end CubicTheta
