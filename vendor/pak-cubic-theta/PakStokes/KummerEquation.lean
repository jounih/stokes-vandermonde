module

public import PakStokes.AiryWronskian
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! The exact Kummer integral remaining in the physical-ray comparison.
Parameter differentiation and a single integration by parts give its ODE. -/
public section
namespace CubicTheta.Physical
open MeasureTheory Set Complex Filter
open scoped Topology
noncomputable section

def exponent (j : ℕ) : ℝ := -(1/6) - j
private def base (v : ℝ) : ℂ := (Real.exp (-v):ℂ)*(v:ℂ)^(-(1/6:ℂ))
private def integrand (j : ℕ) (z : ℂ) (v : ℝ) := base v*((v:ℂ)+2*z)^((exponent j:ℝ):ℂ)
def kummerMoment (j : ℕ) (z : ℂ) := ∫ v in Ioi (0:ℝ), integrand j z v

private theorem baseInt : IntegrableOn base (Ioi 0) := by
  unfold base
  simpa only [show (5/6:ℂ)-1= -(1/6:ℂ) by norm_num] using
    GammaIntegral_convergent (s := 5/6) (by norm_num)

private theorem real_lower {z : ℂ} {v a : ℝ} (hv : 0 ≤ v) (ha : a ≤ z.re) (ha0 : 0 ≤ a) :
    a ≤ ((v:ℂ)+2*z).re := by simp [add_re]; linarith

private theorem bound {z : ℂ} {v a : ℝ} (hv : 0 ≤ v) (ha : a ≤ z.re) (ha0 : 0 < a) (j : ℕ) :
    ‖integrand j z v‖ ≤ ‖base v‖*a^(exponent j) := by
  rw [integrand,norm_mul,Complex.norm_cpow_real]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha0
    ((real_lower hv ha ha0.le).trans (Complex.re_le_norm _)) (by unfold exponent; linarith [Nat.cast_nonneg (α := ℝ) j])) (norm_nonneg _)

private theorem momentInt {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    IntegrableOn (integrand j z) (Ioi 0) := by
  apply (baseInt.norm.mul_const (z.re^(exponent j))).mono'
  · have cc : ContinuousOn (fun v : ℝ ↦ ((v:ℂ)+2*z)^((exponent j:ℝ):ℂ)) (Ioi 0) :=
      ContinuousOn.cpow (by fun_prop) continuousOn_const fun v hv ↦ mem_slitPlane_iff.mpr
        (.inl (hz.trans_le (real_lower (le_of_lt hv) le_rfl hz.le)))
    exact baseInt.aestronglyMeasurable.mul (cc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  exact bound (le_of_lt hv) le_rfl hz j

theorem kummerMoment_deriv {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    HasDerivAt (kummerMoment j) ((2*(exponent j:ℂ))*kummerMoment (j+1) z) z := by
  let s := {w : ℂ | z.re/2 < w.re}
  have hpos : 0 < z.re/2 := by linarith
  have near : s ∈ 𝓝 z := (isOpen_lt continuous_const continuous_re).mem_nhds (by dsimp; linarith)
  let D (w : ℂ) (v : ℝ) := (2*(exponent j:ℂ))*integrand (j+1) w v
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := integrand j) (F' := D)
    (bound := fun v ↦ ‖2*(exponent j:ℂ)‖*(‖base v‖*(z.re/2)^exponent (j+1))) near
    (eventually_of_mem near fun w hw ↦ (momentInt (hpos.trans hw) j).aestronglyMeasurable)
    (momentInt hz j) ((momentInt hz (j+1)).aestronglyMeasurable.const_mul (2*(exponent j:ℂ)))
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv w hw
      simpa [D,norm_mul] using mul_le_mul_of_nonneg_left (bound (le_of_lt hv) (le_of_lt hw) hpos (j+1))
        (norm_nonneg (2*(exponent j:ℂ))))
    ((baseInt.norm.mul_const _).const_mul _) (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv w hw
      have lin := ((hasDerivAt_id w).const_mul (2:ℂ)).const_add (v:ℂ)
      have slit : (v:ℂ)+2*w ∈ slitPlane := mem_slitPlane_iff.mpr
        (.inl (hpos.trans_le (real_lower (le_of_lt hv) (le_of_lt hw) hpos.le)))
      have d := (lin.cpow_const (c := (exponent j:ℂ)) slit).const_mul (base v)
      convert! d using 1
      have e : (exponent (j+1):ℂ) = (exponent j:ℂ)-1 := by unfold exponent; push_cast; ring
      dsimp only [D,integrand]; rw [e]; simp; ring)
  simpa [kummerMoment,D,integral_const_mul] using! h.2

private def primitive (z : ℂ) (v : ℝ) :=
  (Real.exp (-v):ℂ)*(v:ℂ)^((5/6:ℝ):ℂ)*((v:ℂ)+2*z)^((-(7/6:ℝ):ℝ):ℂ)

private def rhs (z : ℂ) (v : ℝ) :=
  (7*z/3)*integrand 2 z v - ((1-6*z)/3)*integrand 1 z v - integrand 0 z v

private theorem primitive_deriv {z : ℂ} (hz : 0 < z.re) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (primitive z) (rhs z v) v := by
  have slit : (v:ℂ)+2*z ∈ slitPlane := mem_slitPlane_iff.mpr (.inl (hz.trans_le (real_lower hv.le le_rfl hz.le)))
  have vn : (v:ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
  have sn := slitPlane_ne_zero slit
  have hE := (hasDerivAt_id v).neg.exp.ofReal_comp
  have hV := ((hasDerivAt_id (v:ℂ)).cpow_const (c := (5/6:ℂ)) (ofReal_mem_slitPlane.mpr hv)).comp_ofReal
  have hS := (((hasDerivAt_id (v:ℂ)).add_const (2*z)).cpow_const (c := -(7/6:ℂ)) slit).comp_ofReal
  have deriv := (hE.mul hV).mul hS
  convert! deriv using 1
  · funext y; simp [primitive]
  let s := (v:ℂ)+2*z
  have pe : (v:ℂ)^(5/6:ℂ) = (v:ℂ)^(-(1/6:ℂ)) * v := by
    rw [show (5/6:ℂ)= -(1/6:ℂ)+1 by norm_num,cpow_add _ _ vn,cpow_one]
  have sub1 : s^(-(7/6:ℂ)) = s^(-(1/6:ℂ))/s := by
    rw [show -(7/6:ℂ)= -(1/6:ℂ)-1 by norm_num,cpow_sub _ _ sn,cpow_one]
  have sub2 : s^(-(13/6:ℂ)) = s^(-(1/6:ℂ))/s^2 := by
    rw [show -(13/6:ℂ)= -(1/6:ℂ)-2 by norm_num,cpow_sub _ _ sn,cpow_ofNat]
  dsimp [rhs,integrand,base,exponent]
  norm_num
  generalize hs : (v:ℂ)+2*z = S at *
  dsimp [s] at sub1 sub2
  rw [hs] at sub1 sub2
  rw [pe,sub1,sub2]
  field_simp [sn]
  rw [← hs]; ring

theorem kummerMoment_equation {z : ℂ} (hz : 0 < z.re) :
    (7*z/3)*kummerMoment 2 z - ((1-6*z)/3)*kummerMoment 1 z - kummerMoment 0 z = 0 := by
  have cc : ContinuousWithinAt (primitive z) (Ici 0) 0 := by
    unfold primitive
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.mul (by fun_prop)
      exact (continuousAt_cpow_const_of_re_pos (.inl (by norm_num)) (by norm_num)).comp continuous_ofReal.continuousAt
    · exact (continuousAt_cpow_const (mem_slitPlane_iff.mpr (.inl (by simpa using (by linarith : 0<2*z.re))))).comp (by fun_prop)
  have it : IntegrableOn (rhs z) (Ioi 0) := by
    unfold rhs; exact  (((momentInt hz 2).const_mul (7*z/3)).sub ((momentInt hz 1).const_mul ((1-6*z)/3))).sub (momentInt hz 0)
  have decay : Tendsto (primitive z) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun v : ℝ ↦ (v^(5/6:ℝ)*Real.exp (-1*v))*z.re^(-(7/6:ℝ)))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
      simp only [primitive,norm_mul,Complex.norm_cpow_real,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),abs_of_pos hv,neg_one_mul]
      rw [mul_comm (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos hz ((real_lower hv.le le_rfl hz.le).trans (Complex.re_le_norm _)) (by norm_num)
    · simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5/6) 1 zero_lt_one).mul_const (z.re^(-(7/6:ℝ)))
  have result := integral_Ioi_of_hasDerivAt_of_tendsto cc (fun _ hv ↦ primitive_deriv hz hv) (show IntegrableOn (rhs z) (Ioi 0) from it) decay
  unfold rhs at result
  rw [integral_sub (f := fun v ↦ (7*z/3)*integrand 2 z v - ((1-6*z)/3)*integrand 1 z v) (g := integrand 0 z) (((momentInt hz 2).const_mul _).sub ((momentInt hz 1).const_mul _)) (momentInt hz 0),
    integral_sub ((momentInt hz 2).const_mul _) ((momentInt hz 1).const_mul _),
    integral_const_mul,integral_const_mul] at result
  simpa [kummerMoment,primitive,Complex.zero_cpow] using result

private theorem moment_bound_on_halfplane {a : ℝ} (ha : 0<a) {z : ℂ} (hz : a ≤ z.re) (j : ℕ) :
    ‖kummerMoment j z‖ ≤ (∫ v in Ioi (0:ℝ), ‖base v‖)*a^exponent j := by
  rw [← integral_mul_const]; apply norm_integral_le_of_norm_le (baseInt.norm.mul_const _)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  exact bound (le_of_lt hv) hz ha j

private theorem sixth_pos {s : ℂ} (hs : s ≠ 0) : 0 < (s^(-(1/6:ℂ))).re := by
  rw [cpow_def_of_ne_zero hs,Complex.exp_re]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo _)
  simp only [Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.one_re,Complex.one_im,zero_div,neg_zero,mul_zero,zero_add,log_im]
  constructor <;> linarith [Complex.neg_pi_lt_arg s,Complex.arg_le_pi s,Real.pi_pos]

theorem kummerMoment_ne_zero {z : ℂ} (hz : 0<z.re) : kummerMoment 0 z ≠ 0 := by
  have pos (v : ℝ) (hv : v ∈ Ioi (0:ℝ)) : 0 < (integrand 0 z v).re := by
    have s : (v:ℂ)+2*z ≠ 0 := fun h ↦ by have := hz.trans_le (real_lower (le_of_lt hv) le_rfl hz.le); simp [h] at this
    have realpow := Complex.ofReal_cpow (le_of_lt hv) (-(1/6:ℝ))
    simp only [ofReal_neg,ofReal_div,ofReal_one,ofReal_ofNat] at realpow
    simp only [integrand,base,exponent,Nat.cast_zero,sub_zero,ofReal_neg,ofReal_div,ofReal_one,ofReal_ofNat]
    rw [← realpow,← ofReal_mul,re_ofReal_mul]
    exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hv _)) (sixth_pos s)
  have ip := (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono fun v hv ↦ (pos v hv).le)
    (momentInt hz 0).re).mpr (by
      rw [inter_eq_right.mpr (fun v hv ↦ Function.mem_support.mpr (pos v hv).ne')]
      simp)
  unfold kummerMoment; intro he
  change 0 < ∫ v in Ioi (0:ℝ), RCLike.re (integrand 0 z v) at ip
  rw [integral_re (momentInt hz 0),he] at ip
  exact (lt_irrefl _ ip)

theorem kummerMoment_origin {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {z : ι → ℂ}
    (hz : Tendsto z l (𝓝 0)) (pos : ∀ᶠ i in l, 0 < (z i).re) :
    Tendsto (fun i ↦ kummerMoment 0 (z i)) l (𝓝 (Gamma (2/3))) := by
  have hg := GammaIntegral_convergent (s := (2/3:ℂ)) (by norm_num)
  let g (v : ℝ) := (Real.exp (-v):ℂ)*(v:ℂ)^(-(1/3:ℂ))
  have gi : IntegrableOn g (Ioi 0) := by
    simpa only [g,show (2/3:ℂ)-1= -(1/3:ℂ) by norm_num] using! hg
  have val : Gamma (2/3) = ∫ v in Ioi (0:ℝ), g v := by
    rw [Gamma_eq_integral (by norm_num),GammaIntegral]; norm_num [g]
  rw [val]
  refine tendsto_integral_filter_of_dominated_convergence _ (pos.mono fun i hi ↦ (momentInt hi 0).aestronglyMeasurable)
    ?_ gi.norm ?_
  · filter_upwards [pos] with i hi
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    have lo : v ≤ ‖(v:ℂ)+2*z i‖ := le_trans (by simp [Complex.add_re]; linarith : v ≤ ((v:ℂ)+2*z i).re) (Complex.re_le_norm _)
    have ineq := Real.rpow_le_rpow_of_nonpos hv lo (by norm_num : -(1/6:ℝ)≤0)
    have half : (-(1/3:ℂ))= -(1/6:ℂ) + -(1/6:ℂ) := by norm_num
    simp only [integrand,base,g,exponent,Nat.cast_zero,sub_zero,half,Complex.cpow_add _ _ (ofReal_ne_zero.mpr hv.ne'),
      norm_mul,Complex.norm_cpow_real]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]; simpa using ineq
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    have h := ((hz.const_mul 2).const_add (v:ℂ))
    simp only [mul_zero,add_zero] at h
    have l := (continuousAt_cpow_const (b := -(1/6:ℂ)) (ofReal_mem_slitPlane.mpr hv)).tendsto.comp h
    have q := l.const_mul (base v)
    have vn : (v:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hv)
    have ve : (v:ℂ)^(-(1/3:ℂ)) = (v:ℂ)^(-(1/6:ℂ))*(v:ℂ)^(-(1/6:ℂ)) := by
      rw [← Complex.cpow_add _ _ vn]; norm_num
    dsimp only [g]; rw [ve]
    simpa [integrand,exponent,base,mul_assoc] using! q

end
end CubicTheta.Physical
