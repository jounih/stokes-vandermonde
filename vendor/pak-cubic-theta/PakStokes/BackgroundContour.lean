module

public import PakStokes.BackgroundInverse
public import LaplaceProduct
public import Mathlib.Analysis.Complex.HasPrimitives
import all PakStokes.BackgroundInverse
import all PakStokes.PhysicalAiry
import all PakStokes.PhysicalBackground

/-! Exact straightening of the physical background contour at positive
inverse square-root temperature. Remote vertical connectors are exponentially small. -/
public section
namespace CubicTheta.Physical.BackgroundInverse
open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section

def weight (p b : ℝ) (y : ℂ) := Complex.exp (-(p:ℂ)*phase b y)

private theorem weight_entire (p b : ℝ) : Differentiable ℂ (weight p b) := by
  unfold weight phase; fun_prop

private theorem jac_cont {b : ℝ} (hb : 0<b) : ContinuousOn (jacobian hb) (Ici 0) := by
  have c := (inverse_analytic hb).continuousOn
  unfold jacobian
  apply ContinuousOn.inv₀ ((continuousOn_const.mul (c.pow 2)).add continuousOn_const)
  intro x hx h
  have pos := phase_regular hb (inverse_wedge hb hx)
  change 3*(inverse hb x)^2+k*b=0 at h
  simp [h] at pos

private theorem vertical_bound {p b : ℝ} (hp : 0<p) (hb : 0<b) {y : ℂ} (hy : Wedge y)
    {w : ℝ} (hw : w ∈ Icc y.im 0) :
    ‖weight p b (y.re+w*I)‖ ≤ Real.exp (-(p*(k.re*b))*y.re) := by
  have ht : 0 ≤ -w := neg_nonneg.mpr hw.2
  have sq := pow_le_pow_left₀ ht ((neg_le_neg hw.1).trans hy.2.2) 2
  have sr := Real.sq_sqrt (by norm_num : 0 ≤ (3:ℝ))
  rw [div_pow,sr] at sq
  have cubic : 0 ≤ y.re*(y.re^2-3*w^2) := mul_nonneg hy.1 (by nlinarith)
  have linear : 0 ≤ k.im*b*(-w) := mul_nonneg (by unfold k; positivity) ht
  have lower : k.re*b*y.re ≤ (phase b (y.re+w*I)).re := by
    simp [phase,pow_succ,Complex.mul_re,Complex.mul_im]
    linarith
  simp only [weight,norm_exp,Complex.mul_re,neg_re,neg_im,ofReal_re,ofReal_im,neg_zero,
    zero_mul,sub_zero,Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left lower hp.le]

private theorem inverse_zero {b : ℝ} (hb : 0<b) : inverse hb 0 = 0 := by
  apply phase_injective hb (inverse_wedge hb le_rfl) (by simp [Wedge])
  rw [inverse_spec]; simp [phase]

/-- Finite deformation with the connector error exposed at its exact endpoint. -/
theorem truncation_error {p b V : ℝ} (hp : 0<p) (hb : 0<b) (hV : 0≤V) :
    let y := inverse hb V
    ‖(∫ r in (0:ℝ)..y.re, weight p b r) -
      (∫ v in (0:ℝ)..V, jacobian hb v * Complex.exp (-(p:ℂ)*v))‖ ≤
      (-y.im)*Real.exp (-(p*(k.re*b))*y.re) := by
  let y := inverse hb V
  have hy := inverse_wedge hb hV
  obtain ⟨G,hG⟩ := (weight_entire p b).isExactOn_univ
  have hg w := hG w (Set.mem_univ w)
  have realPath : (∫ r in (0:ℝ)..y.re, weight p b r) = G (y.re:ℂ)-G 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ ↦ G r)
      (a := 0) (b := y.re) (f' := fun r : ℝ ↦ weight p b r) (fun r _ ↦ by
        simpa [Function.comp_def] using! (hg (r:ℂ)).scomp r (Complex.ofRealCLM.hasDerivAt (x := r)))
      (((weight_entire p b).continuous.comp Complex.continuous_ofReal).intervalIntegrable ..)
  have curved : (∫ v in (0:ℝ)..V, jacobian hb v * Complex.exp (-(p:ℂ)*v)) = G y-G 0 := by
    rw [← inverse_zero hb]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G ∘ inverse hb)
    · intro v hv
      rw [uIcc_of_le hV] at hv
      simpa only [weight,inverse_spec,smul_eq_mul] using! (hg (inverse hb v)).scomp v (inverse_derivative hb hv.1)
    · exact (((jac_cont hb).mono (Icc_subset_Ici_self : Icc 0 V ⊆ Ici 0)).mul
        (by fun_prop : Continuous (fun v : ℝ ↦ Complex.exp (-(p:ℂ)*v))).continuousOn).intervalIntegrable_of_Icc hV
  have edge : (∫ w : ℝ in y.im..0, I * weight p b (y.re+w*I)) = G y.re-G y := by
    have path (w : ℝ) : HasDerivAt (fun w : ℝ ↦ G (y.re+w*I)) (I*weight p b (y.re+w*I)) w := by
      have h : HasDerivAt (fun t : ℝ ↦ (y.re:ℂ)+t*I) I w := by
        simpa using! ((Complex.ofRealCLM.hasDerivAt (x := w)).mul_const I).const_add (y.re:ℂ)
      simpa [Function.comp_def,smul_eq_mul] using! (hg ((y.re:ℂ)+w*I)).scomp w h
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun w : ℝ ↦ G (y.re+w*I))
      (f' := fun w : ℝ ↦ I*weight p b (y.re+w*I)) (a := y.im) (b := 0)
      (fun w _ ↦ path w) ((continuous_const.mul ((weight_entire p b).continuous.comp (by fun_prop))).intervalIntegrable ..)
    simpa using he
  change ‖_ - _‖ ≤ _
  rw [realPath,curved,sub_sub_sub_cancel_right,← edge]
  have est := intervalIntegral.norm_integral_le_of_norm_le_const (a := y.im) (b := 0)
    (f := fun w : ℝ ↦ I*weight p b (y.re+w*I)) (C := Real.exp (-(p*(k.re*b))*y.re)) (by
      intro w hw
      rw [uIoc_of_le hy.2.1] at hw
      simpa [norm_mul] using vertical_bound hp hb hy (Set.Ioc_subset_Icc_self hw))
  have hneg : y.im ≤ 0 := hy.2.1
  simpa only [zero_sub,abs_neg,abs_of_nonpos hneg,mul_comm (Real.exp _) _] using! est

private theorem jac_integrable {p b : ℝ} (hp : 0<p) (hb : 0<b) :
    IntegrableOn (fun v : ℝ ↦ jacobian hb v * Complex.exp (-(p:ℂ)*v)) (Ioi 0) := by
  have ha : 0 < k.re*b := by unfold k; positivity
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hp) 0).const_mul (k.re*b)⁻¹).mono'
  · exact (((jac_cont hb).mono Ioi_subset_Ici_self).mul
      (by fun_prop : Continuous (fun v : ℝ ↦ Complex.exp (-(p:ℂ)*v))).continuousOn).aestronglyMeasurable measurableSet_Ioi
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  have hw := inverse_wedge hb hv.le
  have d : k.re*b ≤ ‖3*(inverse hb v)^2+k*b‖ := by
    apply le_trans _ (Complex.re_le_norm _)
    simp only [pow_two,add_re,mul_re (3:ℂ),re_ofNat,im_ofNat,zero_mul,sub_zero,
      mul_re k,ofReal_re,ofReal_im,mul_zero]
    linarith [wedge_prod hw hw]
  simp only [norm_mul,jacobian,norm_inv,Complex.norm_exp,Complex.mul_re,neg_re,neg_im,
    ofReal_re,ofReal_im,neg_zero,zero_mul,sub_zero]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ ha d) (Real.exp_pos _).le

/-- The straightened positive ray and the original real contour have exactly
the same improper integral before taking any real parts. -/
theorem straightened_integral {p b : ℝ} (hp : 0<p) (hb : 0<b) :
    (∫ r in Ioi (0:ℝ), weight p b r) =
    ∫ v in Ioi (0:ℝ), jacobian hb v * Complex.exp (-(p:ℂ)*v) := by
  let s := abscissa b
  let V (u : ℝ) := (phase b (curve b u)).re
  have ha : 0 < k.re*b := by unfold k; positivity
  have cc : 0 < Real.sqrt (k.re*b/3) := by positivity
  have sr : Tendsto s atTop atTop := by
    apply tendsto_atTop_mono' _ _ (tendsto_id.atTop_mul_const cc)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    apply mul_le_mul_of_nonneg_left _ hu
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left ha.le (denom_pos u) (sub_le_self _ (sq_nonneg _)))
  have vr : Tendsto V atTop atTop := tendsto_atTop_mono' _ ((eventually_ge_atTop (0:ℝ)).mono
    fun u hu ↦ curve_lower hb hu) (tendsto_id.atTop_mul_const (mul_pos cc ha))
  have wl : IntegrableOn (fun r : ℝ ↦ weight p b r) (Ioi 0) := by
    apply (J_integrable hp (-(p:ℂ)*k*b)).congr_fun _ measurableSet_Ioi
    intro r _; dsimp [weight,phase]; apply congrArg Complex.exp; ring
  have left := intervalIntegral_tendsto_integral_Ioi 0 wl sr
  have right := intervalIntegral_tendsto_integral_Ioi 0 (jac_integrable hp hb) vr
  apply sub_eq_zero.mp (tendsto_nhds_unique (left.sub right) ?_)
  apply squeeze_zero_norm' (a := fun u ↦ s u*Real.exp (-(p*(k.re*b))*s u))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    have non : 0 ≤ V u := (mul_nonneg hu (mul_nonneg cc.le ha.le)).trans (curve_lower hb hu)
    have wy := curve_wedge (b := b) hu
    have eqn : inverse hb (V u) = curve b u := by
      apply phase_injective hb (inverse_wedge hb non) wy
      rw [inverse_spec]; exact Complex.ext rfl (phase_curve_real hb u).symm
    have bound := truncation_error hp hb non
    dsimp only at bound
    rw [eqn] at bound
    have small : -(curve b u).im ≤ s u := wy.2.2.trans (div_le_self wy.1 (by norm_num))
    exact bound.trans (mul_le_mul_of_nonneg_right small (Real.exp_pos _).le)
  · simpa [Function.comp_def] using! (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) _ (mul_pos hp ha)).comp sr


private theorem rescale_J {p : ℝ} (hp : 0<p) (b : ℝ) :
    J (1/p^2) (-k*b) = p • ∫ r in Ioi (0:ℝ), weight p b r := by
  let f (r : ℝ) := Complex.exp (-((1/p^2:ℝ):ℂ)*(r:ℂ)^3+(-k*b)*r)
  have eqn (r : ℝ) : f (p*r) = weight p b r := by
    unfold f weight phase; congr 1; push_cast; field_simp [hp.ne']; ring
  have sc := integral_comp_mul_left_Ioi' f 0 hp
  simpa only [mul_zero,eqn,J,f] using! sc.symm

private def projection : ℂ →L[ℝ] ℂ :=
  (2:ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (I*k))))

private theorem projection_apply (z : ℂ) : projection z = ((2*(I*k*z).re:ℝ):ℂ) := by
  simp [projection, Complex.real_smul]

/-- One physical Fourier background mode is precisely the normalized ordinary
Laplace sum of its subtracted analytic inverse-cubic kernel. -/
theorem backgroundMode_eq_raySum {p b : ℝ} (hp : 0<p) (hb : 0<b) :
    backgroundMode (1/p^2) b = raySum (kernel hb) p := by
  let f (v : ℝ) := jacobian hb v * Complex.exp (-(p:ℂ)*v)
  have proj (v : ℝ) : projection (jacobian hb v) = kernel hb v := by
    rw [projection_apply]; simp [kernel,jacobian,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  have exp_real (v : ℝ) : Complex.exp (-(p:ℂ)*v) = ((Real.exp (-(p*v)):ℝ):ℂ) := by
    rw [ofReal_exp]; push_cast; rw [neg_mul]
  have wy (v : ℝ) : weighted p (kernel hb) v = projection (f v) := by
    unfold weighted f; rw [exp_real,← proj,← map_smul,Complex.real_smul]; congr 1; ring
  unfold backgroundMode
  rw [← projection_apply]
  rw [rescale_J hp,straightened_integral hp hb,map_smul,raySum_eq_weighted _ hp]
  simp only [wy]
  rw [projection.integral_comp_comm (jac_integrable hp hb)]

theorem mode_pos (n : ℕ+) : 0 < 2*Real.pi*(n:ℝ) :=
  mul_pos (mul_pos two_pos Real.pi_pos) (by exact_mod_cast n.property)

def fullKernel (v : ℝ) : ℂ := ∑' n : ℕ+, kernel (mode_pos n) v

def modeBudget (n : ℕ+) := (((n:ℝ)^4)⁻¹)
def kernelConstant := 6/(k.re^3*(2*Real.pi)^4)

private theorem budget_summable : Summable modeBudget := by
  exact (Real.summable_nat_pow_inv.mpr (by decide : 1<4)).subtype (fun n ↦ 0<n)

private theorem mode_bound (n : ℕ+) {v : ℝ} (hv : 0≤v) :
    ‖kernel (mode_pos n) v‖ ≤ modeBudget n * (kernelConstant*v^2) := by
  apply (kernel_bound (mode_pos n) hv).trans_eq
  unfold modeBudget kernelConstant; ring

theorem fullKernel_bound {v : ℝ} (hv : 0≤v) :
    ‖fullKernel v‖ ≤ (∑' n, modeBudget n) * (kernelConstant*v^2) := by
  have hs := budget_summable.mul_right (kernelConstant*v^2)
  have hn := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ mode_bound n hv) hs
  exact ((norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun n ↦ mode_bound n hv) hs)).trans_eq
    (budget_summable.tsum_mul_right ..)

/-- The zero-action term of the original Poisson series at every positive p
is the normalized Laplace sum of one explicitly specified real-axis kernel. -/
theorem background_eq_raySum {p : ℝ} (hp : 0<p) :
    (∑' n : ℕ+, backgroundMode (1/p^2) (2*Real.pi*n)) = raySum fullKernel p := by
  let f (n : ℕ+) (u : ℝ) := Real.exp (-u) • kernel (mode_pos n) (u/p)
  let M (u : ℝ) := (kernelConstant/p^2)*(Real.exp (-u)*u^2)
  have hi : IntegrableOn M (Ioi 0) := by
    simpa only [M, IntegrableOn, show (3:ℝ)-1=2 by norm_num,Real.rpow_two] using!
      (Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (kernelConstant/p^2)
  have major (n : ℕ+) (u : ℝ) (hu : 0<u) : ‖f n u‖ ≤ modeBudget n*M u := by
    unfold f
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left (mode_bound n (div_nonneg hu.le hp.le)) (Real.exp_pos _).le).trans_eq
    dsimp [M]; ring
  have fi (n : ℕ+) : IntegrableOn (f n) (Ioi 0) := by
    apply (hi.const_mul (modeBudget n)).mono' _ ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (major n))
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (-u))).continuousOn.smul
    exact (kernel_analytic (mode_pos n)).continuousOn.comp (continuous_id.div_const p).continuousOn
      (fun u hu ↦ div_nonneg (le_of_lt hu) hp.le)
  have hs : HasSum (fun n ↦ ∫ u in Ioi 0, f n u) (∫ u in Ioi 0, ∑' n, f n u) := by
    apply hasSum_integral_of_summable_integral_norm fi
    apply Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) _ (budget_summable.mul_right (∫ u in Ioi 0, M u))
    intro n; rw [← integral_const_mul]
    exact integral_mono_ae (fi n).norm (hi.const_mul (modeBudget n)) ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (major n))
  calc _ = ∑' n, ∫ u in Ioi 0, f n u := tsum_congr (fun n ↦ backgroundMode_eq_raySum hp (mode_pos n))
       _ = _ := by
         rw [hs.tsum_eq]; unfold raySum fullKernel
         apply setIntegral_congr_fun measurableSet_Ioi; intro u _
         simp only [f,Complex.real_smul,tsum_mul_left]


end
end CubicTheta.Physical.BackgroundInverse
