module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Poisson summation at positive physical temperature and the cubic Airy
contour. The even extension exp(-t|x|³) is only twice continuously differentiable. -/
public section
namespace CubicTheta.Physical
open Real Complex Set Filter MeasureTheory Asymptotics
open scoped Topology FourierTransform
noncomputable section

def envelope (t x : ℝ) := Real.exp (-t*|x|^3)
def profile (t x : ℝ) : ℂ := envelope t x

private theorem deriv_signed_sq (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y*|y|) (2*|x|) x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · convert! (hasDerivAt_id x).mul (hasDerivAt_abs_neg h) using 1; simp [abs_of_neg h]; ring
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    have h : Tendsto (fun u : ℝ ↦ |u|) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0:ℝ)}ᶜ))
    simp only [abs_zero,mul_zero,zero_add,sub_zero,smul_eq_mul]
    apply h.congr'; filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← mul_assoc,inv_mul_cancel₀ (by exact hu),one_mul]
  · convert! (hasDerivAt_id x).mul (hasDerivAt_abs_pos h) using 1; simp [abs_of_pos h]; ring

private theorem deriv_abs_cube (x : ℝ) : HasDerivAt (fun y : ℝ ↦ |y|^3) (3*x*|x|) x := by
  have eqn : (fun y : ℝ ↦ |y|^3) = fun y : ℝ ↦ y*(y*|y|) := by
    funext y; rw [pow_succ,sq_abs]; ring
  rw [eqn]
  convert! (hasDerivAt_id x).mul (deriv_signed_sq x) using 1; simp only [id_eq]; ring

private theorem deriv_envelope (t x : ℝ) : HasDerivAt (envelope t)
    ((-3*t)*(x*|x|)*envelope t x) x := by
  unfold envelope
  convert! ((deriv_abs_cube x).const_mul (-t)).exp using 1; ring

private def d1 (t x : ℝ) : ℂ := ((-3*t)*(x*|x|)*envelope t x : ℝ)
private def d2 (t x : ℝ) : ℂ := ((9*t^2*x^4 - 6*t*|x|)*envelope t x : ℝ)

private theorem deriv_profile (t x : ℝ) : HasDerivAt (profile t) (d1 t x) x :=
  (deriv_envelope t x).ofReal_comp

private theorem deriv_d1 (t x : ℝ) : HasDerivAt (d1 t) (d2 t x) x := by
  have h := (((deriv_signed_sq x).const_mul (-3*t)).mul (deriv_envelope t x)).ofReal_comp
  convert! h using 1
  unfold d2
  congr 1
  rcases le_total 0 x with hx | hx <;> simp [abs_of_nonneg,abs_of_nonpos,hx] <;> ring

private theorem profile_smooth (t : ℝ) : ContDiff ℝ 2 (profile t) := by
  have h1 : deriv (profile t) = d1 t := funext fun x ↦ (deriv_profile t x).deriv
  have h2 : deriv (d1 t) = d2 t := funext fun x ↦ (deriv_d1 t x).deriv
  rw [show (2 : WithTop ℕ∞) = 1+1 by rfl,contDiff_succ_iff_deriv,h1,contDiff_one_iff_deriv,h2]
  exact ⟨fun x ↦ (deriv_profile t x).differentiableAt,by simp,
    fun x ↦ (deriv_d1 t x).differentiableAt,by unfold d2 envelope; fun_prop⟩

private theorem moment_integrable {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun x : ℝ ↦ |x|^k * envelope t x) := by
  apply Integrable.of_integral_ne_zero
  change (∫ x : ℝ, (fun y : ℝ ↦ y^k*Real.exp (-t*y^3)) |x|) ≠ 0
  rw [integral_comp_abs (f := fun y : ℝ ↦ y^k*Real.exp (-t*y^3))]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := k) (by norm_num)
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1:ℝ) < (k:ℝ)) ht
  simp only [Real.rpow_natCast,Real.rpow_ofNat] at h
  rw [h]
  have hg := Real.Gamma_pos_of_pos (show 0 < ((k:ℝ)+1)/3 by positivity)
  positivity

private theorem profile_integrable {t : ℝ} (ht : 0 < t) : Integrable (profile t) := by
  change Integrable (fun x : ℝ ↦ (envelope t x : ℂ))
  have h : Integrable (envelope t) := by simpa only [pow_zero,one_mul] using moment_integrable ht 0
  exact h.ofReal

private theorem jets_integrable {t : ℝ} (ht : 0 < t) (k : ℕ) (hk : k ≤ 2) :
    Integrable (iteratedDeriv k (profile t)) := by
  have h1 : deriv (profile t) = d1 t := funext fun x ↦ (deriv_profile t x).deriv
  have h2 : deriv (d1 t) = d2 t := funext fun x ↦ (deriv_d1 t x).deriv
  interval_cases k
  · simpa using profile_integrable ht
  · simp only [iteratedDeriv_one,h1]
    apply (((moment_integrable ht 2).const_mul (3*t))).mono'
    · exact (by unfold d1 envelope; fun_prop : Continuous (d1 t)).aestronglyMeasurable
    apply ae_of_all; intro x
    change ‖(((-3*t)*(x*|x|)*envelope t x : ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    simp [abs_mul,abs_of_pos ht,sq]; ring_nf
    have hp : 0 < envelope t x := Real.exp_pos _
    rw [abs_of_pos hp]
  · rw [iteratedDeriv_succ,iteratedDeriv_one,h1,h2]
    have h := (((moment_integrable ht 4).const_mul (9*t^2)).sub
      ((moment_integrable ht 1).const_mul (6*t))).ofReal (𝕜 := ℂ)
    apply h.congr
    apply ae_of_all; intro x
    simp [d2,show |x|^4 = x^4 by rw [show 4=2*2 by decide,pow_mul,sq_abs]; ring]; ring

private theorem decay_of_bound {f : ℝ → ℂ} {C : ℝ}
    (h : ∀ x, (1+x^2)*‖f x‖ ≤ C) :
    f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2:ℝ))) := by
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (0:ℝ))] with x hx
  have hn : 0 < |x| := hx
  rw [Real.rpow_neg (abs_nonneg _),Real.rpow_ofNat,Real.norm_eq_abs,abs_of_pos (by positivity),
    ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  nlinarith [h x,norm_nonneg (f x),sq_abs x]

private theorem profile_bound {t : ℝ} (ht : 0 < t) (x : ℝ) : (1+x^2)*‖profile t x‖ ≤ 2+1/t := by
  have small : envelope t x ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [pow_nonneg (abs_nonneg x) 3])
  have pos : 0 < envelope t x := Real.exp_pos _
  have norm : ‖profile t x‖ = envelope t x := by simp [profile,abs_of_pos pos]
  rw [norm]
  by_cases hx : |x| ≤ 1
  · have hsq : x^2 ≤ 1 := by nlinarith [sq_abs x,mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) pos.le,one_div_pos.mpr ht]
  · have hpow : x^2 ≤ |x|^3 := by rw [show |x|^3 = |x|^2*|x| from pow_succ _ _,sq_abs]; nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ |x|-1)]
    have h := Real.add_one_le_exp (t*|x|^3)
    have he : x^2 * envelope t x ≤ 1/t := by
      unfold envelope
      rw [neg_mul,Real.exp_neg,← div_eq_mul_inv,div_le_div_iff₀ (Real.exp_pos _) ht]
      nlinarith [mul_le_mul_of_nonneg_left hpow ht.le]
    nlinarith

private theorem fourier_decay {t : ℝ} (ht : 0 < t) :
    𝓕 (profile t) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2:ℝ))) :=
  decay_of_bound (Real.one_add_sq_mul_norm_fourier_le (profile_smooth t) (jets_integrable ht))

theorem poisson_physical {t : ℝ} (ht : 0 < t) :
    ∑' n : ℤ, profile t n = ∑' n : ℤ, 𝓕 (profile t) n := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay ((profile_smooth t).continuous) (by norm_num : (1:ℝ)<2)
    (decay_of_bound (profile_bound ht)) (fourier_decay ht) 0
  simpa using h

/-- The one-sided cubic transform. -/
def J (t : ℝ) (z : ℂ) := ∫ r in Ioi (0:ℝ), Complex.exp (-(t:ℂ)*(r:ℂ)^3+z*r)

theorem J_integrable {t : ℝ} (ht : 0 < t) (z : ℂ) :
    IntegrableOn (fun r : ℝ ↦ Complex.exp (-(t:ℂ)*(r:ℂ)^3+z*r)) (Ioi 0) := by
  let M := max 1 ((|z.re|+1)/t)
  let C := (|z.re|+1)*M
  have hC : 0 ≤ C := mul_nonneg (by positivity) (zero_le_one.trans (le_max_left ..))
  apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul (Real.exp C)).mono'
  · exact (by fun_prop : Continuous (fun r : ℝ ↦ Complex.exp (-(t:ℂ)*(r:ℂ)^3+z*r))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
  change 0 < r at hr
  have eqn : -(t:ℂ)*(r:ℂ)^3 = ((-t*r^3:ℝ):ℂ) := by push_cast; rfl
  rw [Complex.norm_exp,eqn,Complex.add_re,ofReal_re]
  change _ ≤ Real.exp C * Real.exp (-1*r)
  rw [← Real.exp_add,Real.exp_le_exp]; simp only [Complex.mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self z.re) hr.le
  by_cases h : r ≤ M
  · have h2 := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ |z.re|+1)
    dsimp [C]; nlinarith [mul_nonneg ht.le (pow_nonneg hr.le 3)]
  · have large : (|z.re|+1)/t ≤ r := (le_max_right ..).trans (le_of_not_ge h)
    have hr1 : 1 ≤ r := (le_max_left ..).trans (le_of_not_ge h)
    have h2 := (div_le_iff₀ ht).mp large
    have h3 : r ≤ r^2 := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
    have h4 := mul_le_mul_of_nonneg_right h3 ht.le
    nlinarith [mul_le_mul_of_nonneg_right (h2.trans h4) hr.le]

def h : ℂ := ⟨Real.sqrt 3 / 2,-1/2⟩
def k : ℂ := ⟨Real.sqrt 3 / 2,1/2⟩
def upper : ℂ := ⟨1/2,Real.sqrt 3 / 2⟩
def lower : ℂ := ⟨1/2,-Real.sqrt 3 / 2⟩

/-- DLMF 9.5.4 parametrized along its lower (inward) and upper (outward)
straight rays. Their directions cube to −1. -/
def airyContour (z : ℂ) :=
  (upper * J (1/3) (-z*upper) - lower * J (1/3) (-z*lower)) / (2*Real.pi*I)

private theorem roots : h*upper = k ∧ h*lower = -I ∧
    upper^3 = -1 ∧ lower^3 = -1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;> apply Complex.ext <;>
    norm_num [pow_succ,h,k,upper,lower,Complex.mul_re,Complex.mul_im] <;> nlinarith [congrArg (fun y : ℝ ↦ y*Real.sqrt 3) hs]

theorem J_scale {α t : ℝ} (ha : 0 < α) (cube : α^3=3*t) (z : ℂ) :
    J (1/3) (z/α) = α * J t z := by
  let f (r : ℝ) := Complex.exp (-(1/3:ℂ)*(r:ℂ)^3+(z/α)*r)
  have sc := integral_comp_mul_left_Ioi' f 0 ha
  simp only [mul_zero] at sc
  change _ = (α:ℂ)*_
  calc _ = α • ∫ x in Ioi (0:ℝ), f (α*x) := by simpa [J,f] using sc.symm
       _ = _ := by
         rw [Complex.real_smul]; congr 1
         apply setIntegral_congr_fun measurableSet_Ioi; intro x _
         unfold f
         have hc : (α:ℂ)^3=3*(t:ℂ) := by exact_mod_cast cube
         have hn : (α:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
         push_cast; rw [mul_pow,hc]; field_simp

/-- Exact coefficient of the physical Airy mode, including its complex phase.
All integrals in the statement run along fixed rays. -/
theorem airy_mode {α t : ℝ} (ha : 0 < α) (cube : α^3=3*t) (b : ℝ) :
    J t (I*b) = I*k*J t (-k*b) + (2*Real.pi*h/α)*airyContour (h*b/α) := by
  have hu : -(h*b/α)*upper = (-k*b)/α := by
    rw [show -(h*b/α)*upper = -(h*upper)*b/α by ring,roots.1]
  have hl : -(h*b/α)*lower = (I*b)/α := by
    rw [show -(h*b/α)*lower = -(h*lower)*b/α by ring,roots.2.1,neg_neg]
  rw [airyContour,hu,hl,J_scale ha cube,J_scale ha cube]
  have hn : (α:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hn,hp,I_ne_zero]
  rw [I_sq]
  linear_combination J t (I*b) * roots.2.1 - J t (-(b*k)) * roots.1

/-- Split the Fourier integral at zero. Negative Fourier frequencies are
allowed as well, so the result can be substituted in the integer Poisson sum. -/
theorem fourier_profile {t : ℝ} (ht : 0 < t) (w : ℝ) :
    𝓕 (profile t) w = J t (I*(2*Real.pi*w)) + J t (-I*(2*Real.pi*w)) := by
  let f (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*w)*I) * profile t x
  have hi : Integrable f := by
    apply (profile_integrable ht).norm.mono'
    · exact (by unfold f profile envelope; fun_prop : Continuous f).aestronglyMeasurable
    · apply ae_of_all; intro x; simp [f,Complex.norm_exp]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change ∫ x, f x = _
  rw [← integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic hi,compl_Iic,
    ← show (∫ x in Ioi (0:ℝ), f (-x)) = ∫ x in Iic 0, f x by simp]
  congr 1 <;> apply setIntegral_congr_fun measurableSet_Ioi <;> intro x hx <;>
    simp only [f,profile,envelope,abs_neg,abs_of_pos (show 0 < x from hx),Complex.ofReal_exp,
      ← Complex.exp_add] <;> congr 1 <;> push_cast <;> ring

private theorem J_conj (t : ℝ) (z : ℂ) : J t (star z) = star (J t z) := by
  unfold J
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]; apply setIntegral_congr_fun measurableSet_Ioi; intro x _
  simp [← Complex.exp_conj]

def physicalMode (α t b : ℝ) : ℂ :=
  I*k*J t (-k*b) + (2*Real.pi*h/α)*airyContour (h*b/α)

theorem fourier_mode {α t : ℝ} (ht : 0 < t) (ha : 0 < α) (cube : α^3=3*t) (w : ℝ) :
    𝓕 (profile t) w = (2*(physicalMode α t (2*Real.pi*w)).re : ℝ) := by
  rw [fourier_profile ht]
  have neg (b : ℝ) : -I*b = star (I*b) := by simp
  let b := 2*Real.pi*w
  have castB : (2:ℂ)*Real.pi*w = (b:ℂ) := by simp [b]
  rw [castB,neg,J_conj,airy_mode ha cube]
  change physicalMode _ _ _ + star (physicalMode _ _ _) = _
  apply Complex.ext <;> simp; ring

theorem zero_mode {t : ℝ} (ht : 0 < t) :
    J t 0 = ((t^(-(1:ℝ)/3)*Real.Gamma (4/3) : ℝ) : ℂ) := by
  have h := _root_.integral_exp_neg_mul_rpow (p := 3) (by norm_num) ht
  rw [show (1:ℝ)/3+1 = 4/3 by norm_num] at h
  simp only [Real.rpow_ofNat] at h
  rw [← h, ← integral_complex_ofReal]; unfold J
  apply setIntegral_congr_fun measurableSet_Ioi; intro x _
  simp [Complex.ofReal_exp]

theorem cubeSeries_airy {α t : ℝ} (ht : 0 < t) (ha : 0 < α) (cube : α^3=3*t) :
    (∑' n : ℕ, (Real.exp (-t*(n:ℝ)^3) : ℂ)) =
      1/2 + J t 0 + ∑' m : ℕ+, ((2*(physicalMode α t (2*Real.pi*m)).re : ℝ) : ℂ) := by
  have hp : Summable (fun n : ℤ ↦ profile t n) := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    ((decay_of_bound (profile_bound ht)).comp_tendsto Int.tendsto_coe_cofinite)
  have hf : Summable (fun n : ℤ ↦ 𝓕 (profile t) n) := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    ((fourier_decay ht).comp_tendsto Int.tendsto_coe_cofinite)
  have ep : (fun n : ℤ ↦ profile t n).Even := by intro n; simp [profile,envelope]
  have ef : (fun n : ℤ ↦ 𝓕 (profile t) n).Even := by
    intro n; simp [fourier_profile ht,add_comm]
  have z := poisson_physical ht
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat ep hp,tsum_int_eq_zero_add_two_mul_tsum_pnat ef hf] at z
  have hpNat := (summable_int_iff_summable_nat_and_neg.mp hp).1
  have pos := tsum_zero_pnat_eq_tsum_nat hpNat
  simp only [Int.cast_natCast,Int.cast_zero,Nat.cast_zero] at pos z
  have normNat (n : ℕ) : profile t n = (Real.exp (-t*(n:ℝ)^3) : ℂ) := by
    simp [profile,envelope,abs_of_nonneg]
  simp only [← normNat]
  rw [← pos]
  rw [fourier_profile ht 0] at z
  simp only [mul_zero,ofReal_zero] at z
  simp only [fourier_mode ht ha cube] at z
  have hz : profile t 0 = 1 := by simp [profile,envelope]
  rw [hz] at z ⊢
  simp only [two_nsmul] at z
  linear_combination z/2


end
end CubicTheta.Physical
