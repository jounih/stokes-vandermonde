module

public import PakStokes.PhysicalBackground
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import all PakStokes.PhysicalAiry

/-! The inverse cubic phase on the physical background contour. An explicit
real parameter gives existence on the whole positive ray. Factorization of
differences singles out the root and excludes critical points in its sector. -/
public section
namespace CubicTheta.Physical.BackgroundInverse
open Complex Set Filter
open scoped Topology
noncomputable section

def phase (b : ℝ) (y : ℂ) := y^3 + k*b*y

/-- Closed sector from angle -π/6 to zero. -/
def Wedge (y : ℂ) := 0 ≤ y.re ∧ y.im ≤ 0 ∧ -y.im ≤ y.re / Real.sqrt 3

private theorem sqrt3 : 0 < Real.sqrt 3 := by positivity

private theorem wedge_prod {x y : ℂ} (hx : Wedge x) (hy : Wedge y) : 0 ≤ (x*y).re := by
  have h1 : 1 ≤ Real.sqrt 3 := by norm_num
  have lower (z : ℂ) (hz : Wedge z) : -z.im ≤ z.re :=
    hz.2.2.trans (div_le_self hz.1 h1)
  have hh := mul_le_mul (lower x hx) (lower y hy) (neg_nonneg.mpr hy.2.1) hx.1
  simpa [Complex.mul_re] using sub_nonneg.mpr (show x.im*y.im ≤ x.re*y.re by simpa using hh)

private theorem linear_pos {b : ℝ} (hb : 0<b) : 0 < (k*b).re := by simp [k]; positivity

theorem phase_injective {b : ℝ} (hb : 0<b) {x y : ℂ} (hx : Wedge x) (hy : Wedge y)
    (eqn : phase b x = phase b y) : x = y := by
  have pos : 0 < (x*x + x*y + y*y + k*b).re := by
    simp only [add_re]; linarith [wedge_prod hx hx,wedge_prod hx hy,wedge_prod hy hy,linear_pos hb]
  have factor : (x-y)*(x*x+x*y+y*y+k*b) = 0 := by
    unfold phase at eqn; linear_combination eqn
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_right (fun h ↦ by simp [h] at pos))

theorem phase_regular {b : ℝ} (hb : 0<b) {y : ℂ} (hy : Wedge y) :
    0 < (3*y^2 + k*b).re := by
  rw [pow_two]; simp only [add_re,mul_re (3:ℂ),re_ofNat,im_ofNat,zero_mul,sub_zero]
  linarith [wedge_prod hy hy,linear_pos hb]

private def slope (u : ℝ) := 1 / (Real.sqrt 3*(1+u^2))
private def abscissa (b u : ℝ) := u * Real.sqrt ((k.re*b)/(3-(slope u)^2))
def curve (b u : ℝ) : ℂ := ⟨abscissa b u, -abscissa b u*slope u⟩

private theorem slope_bounds (u : ℝ) : 0 ≤ slope u ∧ slope u ≤ 1/Real.sqrt 3 := by
  have H : Real.sqrt 3 ≤ Real.sqrt 3*(1+u^2) := by nlinarith [mul_nonneg sqrt3.le (sq_nonneg u)]
  exact ⟨by unfold slope; positivity,one_div_le_one_div_of_le sqrt3 H⟩

private theorem denom_pos (u : ℝ) : 0 < 3-(slope u)^2 := by
  have h := slope_bounds u
  have h' := h.2.trans (show 1/Real.sqrt 3 ≤ 1 by apply (div_le_iff₀ sqrt3).mpr; norm_num)
  nlinarith [mul_nonneg (sub_nonneg.mpr h') (add_nonneg h.1 zero_le_one)]

theorem curve_wedge {b u : ℝ} (hu : 0≤u) : Wedge (curve b u) := by
  have hs : 0 ≤ abscissa b u := mul_nonneg hu (Real.sqrt_nonneg _)
  refine ⟨hs,?_,?_⟩
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (slope_bounds u).1
  · change -(-abscissa b u*slope u) ≤ abscissa b u/Real.sqrt 3
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (slope_bounds u).2 hs

private theorem curve_sq {b : ℝ} (hb : 0<b) (u : ℝ) :
    (abscissa b u)^2*(3-(slope u)^2) = u^2*(k.re*b) := by
  have ha : 0 ≤ k.re*b := by unfold k; positivity
  rw [abscissa,mul_pow,Real.sq_sqrt (div_nonneg ha (denom_pos u).le)]
  field_simp [(denom_pos u).ne']

theorem phase_curve_real {b : ℝ} (hb : 0<b) (u : ℝ) : (phase b (curve b u)).im = 0 := by
  have ht : k.re*(1+u^2)*slope u = k.im := by
    unfold k slope; dsimp; field_simp [sqrt3.ne']
  have eqn := curve_sq hb u
  simp only [phase,pow_succ,pow_zero,one_mul,Complex.add_im,Complex.mul_im,Complex.mul_re,curve,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add]
  linear_combination -(abscissa b u*slope u)*eqn - b*abscissa b u*ht

private theorem curve_lower {b u : ℝ} (hb : 0<b) (hu : 0≤u) :
    u*(Real.sqrt (k.re*b/3)*(k.re*b)) ≤ (phase b (curve b u)).re := by
  let s := abscissa b u
  let t := slope u
  have hs : 0 ≤ s := mul_nonneg hu (Real.sqrt_nonneg _)
  have ht := slope_bounds u
  have unit : t^2 ≤ (1/Real.sqrt 3)^2 := pow_le_pow_left₀ ht.1 ht.2 2
  have sr := Real.sq_sqrt (by norm_num : 0 ≤ (3:ℝ))
  have tsmall : 0 ≤ 1-3*t^2 := by rw [div_pow,one_pow,sr] at unit; linarith
  have ha : 0 ≤ k.re*b := by unfold k; positivity
  have bound : u*Real.sqrt (k.re*b/3) ≤ s := by
    apply mul_le_mul_of_nonneg_left _ hu
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left ha (denom_pos u) (sub_le_self _ (sq_nonneg _))
  have posIm : 0 ≤ k.im*b := by unfold k; positivity
  have h := mul_le_mul_of_nonneg_right bound ha
  change _ ≤ ((⟨s,-s*t⟩:ℂ)^3 + k*b*(⟨s,-s*t⟩ : ℂ)).re
  simp only [pow_succ,pow_zero,one_mul,Complex.add_re,Complex.mul_re,Complex.mul_im,ofReal_re,ofReal_im,
    mul_zero,sub_zero,zero_add]
  nlinarith [mul_nonneg (pow_nonneg hs 3) tsmall,mul_nonneg (mul_nonneg posIm hs) ht.1]

/-- Every nonnegative real v has exactly one inverse in the closed sector. -/
theorem existsUnique_root {b v : ℝ} (hb : 0<b) (hv : 0≤v) :
    ∃! y : ℂ, Wedge y ∧ phase b y = v := by
  let c := Real.sqrt (k.re*b/3)*(k.re*b)
  have hc : 0<c := by dsimp [c,k]; positivity
  let f (u : ℝ) := (phase b (curve b u)).re
  have cts : Continuous f := by
    unfold f phase curve
    simp only [pow_succ,pow_zero,one_mul,Complex.add_re,Complex.mul_re,Complex.mul_im,ofReal_re,ofReal_im,mul_zero,sub_zero,zero_add]
    unfold abscissa
    have ct : Continuous slope := by unfold slope; fun_prop (disch := intro x; positivity)
    fun_prop (disch := exact fun x ↦ (denom_pos x).ne')
  have h₀ : f 0 = 0 := by
    have z : curve b 0 = 0 := by apply Complex.ext <;> simp [curve,abscissa]
    simp [f,z,phase]
  have hU := curve_lower hb (div_nonneg hv hc.le)
  change v/c*c ≤ f (v/c) at hU
  rw [div_mul_cancel₀ _ hc.ne'] at hU
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc (div_nonneg hv hc.le) cts.continuousOn
    (show v ∈ Icc (f 0) (f (v/c)) from ⟨h₀.trans_le hv,hU⟩)
  have root : phase b (curve b u) = v := Complex.ext he (phase_curve_real hb u)
  exact ⟨curve b u,⟨curve_wedge hu.1,root⟩,fun y hy ↦ phase_injective hb hy.1 (curve_wedge hu.1) (hy.2.trans root.symm)⟩

/-- Quantitative inverse estimate, uniform all the way to the origin. -/
theorem phase_distance {b : ℝ} {x y : ℂ} (hx : Wedge x) (hy : Wedge y) :
    ‖x-y‖*(k.re*b) ≤ ‖phase b x - phase b y‖ := by
  have fac : phase b x - phase b y = (x-y)*(x*x+x*y+y*y+k*b) := by unfold phase; ring
  rw [fac,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply le_trans _ (Complex.re_le_norm _)
  simp only [Complex.add_re,Complex.mul_re k,ofReal_re,ofReal_im,mul_zero,sub_zero]
  linarith [wedge_prod hx hx,wedge_prod hx hy,wedge_prod hy hy]

/-- Along the inverse branch the subtracted kernel is quadratically small
in v, uniformly summable over the Fourier frequencies b = 2πn. -/
theorem subtracted_kernel_bound {b v : ℝ} (hb : 0<b) (hv : 0≤v) {y : ℂ}
    (hy : Wedge y) (eqn : phase b y = v) :
    ‖I*k/(3*y^2+k*b)-I/b‖ ≤ 3*v^2/(k.re^3*b^4) := by
  let D : ℂ := 3*y^2+k*b
  have hp : 0 < k.re*b := by unfold k; positivity
  have hD : k.re*b ≤ ‖D‖ := by
    apply le_trans _ (Complex.re_le_norm _)
    simp only [D,pow_two,add_re,mul_re (3:ℂ),re_ofNat,im_ofNat,zero_mul,sub_zero,
      mul_re k,ofReal_re,ofReal_im,mul_zero]
    linarith [wedge_prod hy hy]
  have nz : D ≠ 0 := norm_pos_iff.mp (hp.trans_le hD)
  have bn : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have h := phase_distance (b := b) hy (show Wedge 0 by simp [Wedge])
  rw [eqn,show phase b 0=0 by simp [phase],sub_zero,sub_zero,norm_real,Real.norm_eq_abs,abs_of_nonneg hv] at h
  have yBound := (le_div_iff₀ hp).mpr h
  change ‖I*k/D-I/b‖ ≤ _
  have diff : I*k/D-I/b = -(3*I*y^2)/((b:ℂ)*D) := by field_simp [nz,bn]; unfold D; ring
  rw [diff]; simp only [norm_div,norm_neg,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos hb,
    norm_pow,norm_I,norm_ofNat,mul_one]
  calc 3*‖y‖^2/(b*‖D‖) ≤ 3*(v/(k.re*b))^2/(b*(k.re*b)) :=
         div_le_div₀ (by positivity) (by gcongr) (mul_pos hb hp) (mul_le_mul_of_nonneg_left hD hb.le)
       _ = _ := by ring


private def posRoot {b : ℝ} (hb : 0<b) (x : ℝ) :=
  (existsUnique_root hb (le_max_right x 0)).exists.choose

private theorem posRoot_spec {b : ℝ} (hb : 0<b) (x : ℝ) :
    Wedge (posRoot hb x) ∧ phase b (posRoot hb x) = (max x 0:ℝ) :=
  (existsUnique_root hb (le_max_right x 0)).exists.choose_spec

private theorem posRoot_inactive {b x : ℝ} (hb : 0<b) (hx : x≤0) : posRoot hb x = 0 := by
  apply phase_injective hb (posRoot_spec hb x).1 (by simp [Wedge])
  rw [(posRoot_spec hb x).2,max_eq_right hx]; simp [phase]

private theorem posRoot_continuous {b : ℝ} (hb : 0<b) : Continuous (posRoot hb) := by
  have hp : 0<k.re*b := by unfold k; positivity
  apply LipschitzWith.continuous (K := ⟨(k.re*b)⁻¹,inv_nonneg.mpr hp.le⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := phase_distance (b := b) (posRoot_spec hb x).1 (posRoot_spec hb y).1
  rw [(posRoot_spec hb x).2,(posRoot_spec hb y).2,← ofReal_sub,norm_real,Real.norm_eq_abs] at h
  rw [dist_eq_norm,Real.dist_eq]
  change _ ≤ (k.re*b)⁻¹*_
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hp).mpr (h.trans (abs_max_sub_max_le_abs _ _ _))

/-- Odd extension makes analyticity at the endpoint a two-sided statement. -/
def inverse {b : ℝ} (hb : 0<b) (v : ℝ) := posRoot hb v - posRoot hb (-v)

theorem inverse_spec {b : ℝ} (hb : 0<b) (v : ℝ) : phase b (inverse hb v) = v := by
  by_cases h : 0≤v
  · simpa [inverse,posRoot_inactive hb (neg_nonpos.mpr h),max_eq_left h] using (posRoot_spec hb v).2
  · have h' := (posRoot_spec hb (-v)).2
    rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge h))] at h'
    rw [inverse,posRoot_inactive hb (le_of_not_ge h),zero_sub,phase]
    unfold phase at h'; push_cast at h'; linear_combination -h'

theorem inverse_wedge {b v : ℝ} (hb : 0<b) (hv : 0≤v) : Wedge (inverse hb v) := by
  simpa [inverse,posRoot_inactive hb (neg_nonpos.mpr hv)] using (posRoot_spec hb v).1

theorem inverse_analytic {b : ℝ} (hb : 0<b) : AnalyticOnNhd ℝ (inverse hb) (Ici 0) := by
  intro v hv
  let y := inverse hb v
  have poly : AnalyticAt ℂ (phase b) y := by unfold phase; fun_prop
  have d : HasDerivAt (phase b) (3*y^2+k*b) y := by
    simpa [phase,Pi.add_def] using! ((hasDerivAt_pow 3 y).add ((hasDerivAt_id y).const_mul (k*(b:ℂ))))
  have dn : deriv (phase b) y ≠ 0 := by
    rw [d.deriv]; exact fun h ↦ by have hp := phase_regular hb (inverse_wedge hb hv); simp_all [y]
  have h := poly.analyticAt_localInverse dn
  rw [show phase b y = v from inverse_spec hb v] at h
  have localEq := poly.hasStrictDerivAt.eventually_left_inverse dn
  have cont : Continuous (inverse hb) :=
    (posRoot_continuous hb).sub ((posRoot_continuous hb).comp continuous_neg)
  have realAnalytic := h.restrictScalars.comp (Complex.ofRealCLM.analyticAt v)
  apply realAnalytic.congr
  filter_upwards [cont.continuousAt.preimage_mem_nhds localEq] with u hu
  change poly.hasStrictDerivAt.localInverse (phase b) (deriv (phase b) y) y dn (phase b (inverse hb u)) = inverse hb u at hu
  rw [inverse_spec] at hu
  exact hu


def jacobian {b : ℝ} (hb : 0<b) (v : ℝ) : ℂ := (3*(inverse hb v)^2+k*b)⁻¹

theorem inverse_derivative {b v : ℝ} (hb : 0<b) (hv : 0≤v) :
    HasDerivAt (inverse hb) (jacobian hb v) v := by
  let y := inverse hb v
  have hd := ((inverse_analytic hb v hv).differentiableAt).hasDerivAt
  have dp : HasDerivAt (phase b) (3*y^2+k*b) y := by
    simpa [phase,Pi.add_def] using! ((hasDerivAt_pow 3 y).add ((hasDerivAt_id y).const_mul (k*(b:ℂ))))
  have comp := dp.scomp v hd
  have eqn : (phase b ∘ inverse hb) = Complex.ofReal := funext (inverse_spec hb)
  rw [eqn] at comp
  have mul := comp.unique (Complex.ofRealCLM.hasDerivAt (x := v))
  change deriv (inverse hb) v * (3*y^2+k*b) = 1 at mul
  have hn : 3*y^2+k*b ≠ 0 := fun h ↦ by have x := phase_regular hb (inverse_wedge hb hv); simp_all [y]
  unfold jacobian; change HasDerivAt _ (3*y^2+k*b)⁻¹ v
  convert hd using 1
  field_simp [hn]; linear_combination -mul


def kernel {b : ℝ} (hb : 0<b) (v : ℝ) : ℂ :=
  ((2*(I*k/(3*(inverse hb v)^2+k*b)-I/b).re:ℝ):ℂ)

theorem kernel_bound {b v : ℝ} (hb : 0<b) (hv : 0≤v) :
    ‖kernel hb v‖ ≤ 6*v^2/(k.re^3*b^4) := by
  have h := subtracted_kernel_bound hb hv (inverse_wedge hb hv) (inverse_spec hb v)
  unfold kernel; rw [norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left ((abs_re_le_norm _).trans h) zero_le_two).trans_eq (by ring)

theorem kernel_analytic {b : ℝ} (hb : 0<b) : AnalyticOnNhd ℝ (kernel hb) (Ici 0) := by
  intro v hv
  have hy := inverse_analytic hb v hv
  have den : 3*(inverse hb v)^2+k*b ≠ 0 := by
    intro h
    have hp := phase_regular hb (inverse_wedge hb hv)
    simp [h] at hp
  have rat := (analyticAt_const (v := I*k) (𝕜 := ℝ) (x := v)).div
    (((analyticAt_const.mul (hy.pow 2))).add analyticAt_const) den
  have h := Complex.reCLM.analyticAt _ |>.comp (rat.sub (analyticAt_const (v := I/(b:ℂ))))
  exact (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_const (v := (2:ℝ))).mul h)


end
end CubicTheta.Physical.BackgroundInverse
