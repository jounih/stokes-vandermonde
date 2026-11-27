module

public import KernelAnalytic
public import LaplaceDerivative

/-! Unnormalized complex-frequency Laplace transforms of exponential-type
densities. Keeping a constant separately gives ordinary convolution as the
product law, without differentiating the convolution. -/
public section
namespace CubicTheta
open Complex Real Set MeasureTheory Filter
open scoped Topology
noncomputable section

@[expose] def ExpType (F : ℝ → ℂ) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D*u)

theorem ExpType.common {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ∃ C E D : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ 0 ≤ D ∧
      (∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D*u)) ∧ (∀ u ≥ 0, ‖G u‖ ≤ E * Real.exp (D*u)) := by
  obtain ⟨C,D,hc,hd,hf⟩ := hf
  obtain ⟨E,T,he,ht,hg⟩ := hg
  refine ⟨C,E,max D T,hc,he,hd.trans (le_max_left ..),?_,?_⟩
  · intro u hu; exact (hf u hu).trans (by gcongr; exact le_max_left ..)
  · intro u hu; exact (hg u hu).trans (by gcongr; exact le_max_right ..)

theorem ExpType.add {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ExpType (fun u ↦ F u + G u) := by
  obtain ⟨C,E,D,hc,he,hd,hf,hg⟩ := hf.common hg
  refine ⟨C+E,D,by positivity,hd,fun u hu ↦ ?_⟩
  rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (hf u hu) (hg u hu))

theorem ExpType.scale {F : ℝ → ℂ} (hf : ExpType F) (a : ℂ) : ExpType (fun u ↦ a * F u) := by
  obtain ⟨C,D,hc,hd,hf⟩ := hf
  refine ⟨‖a‖*C,D,by positivity,hd,fun u hu ↦ ?_⟩
  rw [norm_mul,mul_assoc]; gcongr; exact hf u hu

theorem ExpType.times_u {F : ℝ → ℂ} (hf : ExpType F) : ExpType (fun u ↦ (u:ℂ)*F u) := by
  obtain ⟨C,D,hc,hd,hf⟩ := hf
  refine ⟨C,D+1,hc,by positivity,fun u hu ↦ ?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,add_mul,one_mul,Real.exp_add]
  calc u * ‖F u‖ ≤ Real.exp u * (C*Real.exp (D*u)) :=
         mul_le_mul (by linarith [Real.add_one_le_exp u]) (hf u hu) (norm_nonneg _) (Real.exp_pos _).le
       _ = _ := by ring

theorem ExpType.convolution {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ExpType (borelProduct F G) := by
  obtain ⟨C,E,D,hc,he,hd,hf,hg⟩ := hf.common hg
  exact ⟨C*E,D+1,by positivity,by positivity,fun _ hu ↦ borelProduct_bound hc he hf hg hu⟩

@[expose] def damped (p : ℂ) (F : ℝ → ℂ) (u : ℝ) := Complex.exp (-p*u) * F u

@[expose] def complexLaplace (F : ℝ → ℂ) (p : ℂ) := ∫ u in Ioi (0:ℝ), damped p F u

theorem damped_norm (p : ℂ) (F : ℝ → ℂ) (u : ℝ) :
    ‖damped p F u‖ = Real.exp (-p.re*u) * ‖F u‖ := by
  simp [damped, Complex.norm_exp]

theorem damped_integrable {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) {C D : ℝ}
    (hf : ∀ u ≥ 0, ‖F u‖ ≤ C*Real.exp (D*u)) {p : ℂ} (hp : D < p.re) :
    IntegrableOn (damped p F) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hp) 0).const_mul C).mono'
  · exact ((by fun_prop : Continuous (fun u : ℝ ↦ Complex.exp (-p*u))).continuousOn.mul hc
      ).aestronglyMeasurable measurableSet_Ioi
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  rw [damped_norm]
  calc _ ≤ Real.exp (-p.re*u) * (C*Real.exp (D*u)) :=
         mul_le_mul_of_nonneg_left (hf u hu.le) (Real.exp_pos _).le
       _ = C*(Real.exp (-p.re*u)*Real.exp (D*u)) := by ring
       _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem complexLaplace_product {F G : ℝ → ℂ} {p : ℂ}
    (hf : IntegrableOn (damped p F) (Ioi 0)) (hg : IntegrableOn (damped p G) (Ioi 0)) :
    complexLaplace (borelProduct F G) p = complexLaplace F p * complexLaplace G p := by
  have h := integral_posConvolution hf hg (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have inside (v : ℝ) : (∫ t in 0..v, damped p F t * damped p G (v-t)) =
      damped p (borelProduct F G) v := by
    unfold damped borelProduct
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro t _
    have he : Complex.exp (-p*v) = Complex.exp (-p*t)*Complex.exp (-p*↑(v-t)) := by
      rw [← Complex.exp_add, Complex.ofReal_sub]; congr 1; ring
    rw [he]; ring
  simpa only [inside,complexLaplace] using h

theorem complexLaplace_derivative {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) {C D : ℝ}
    (hf : ∀ u ≥ 0, ‖F u‖ ≤ C*Real.exp (D*u)) {p : ℂ} (hp : D+1 < p.re) :
    HasDerivAt (complexLaplace F) (-complexLaplace (fun u ↦ (u:ℂ)*F u) p) p := by
  let G := fun u : ℝ ↦ -(u:ℂ)*F u
  have meas (q : ℂ) {H : ℝ → ℂ} (hH : ContinuousOn H (Ioi 0)) :
      AEStronglyMeasurable (damped q H) (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous (fun u : ℝ ↦ Complex.exp (-q*u))).continuousOn.mul hH
      ).aestronglyMeasurable measurableSet_Ioi
  have hi : IntegrableOn (fun u : ℝ ↦ C*(Real.exp (-u)*u)) (Ioi 0) := by
    simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, IntegrableOn] using!
      (Real.GammaIntegral_convergent (s := 2) (by norm_num)).const_mul C
  have hd (q : ℂ) (u : ℝ) : HasDerivAt (fun w ↦ damped w F u) (damped q G u) q := by
    have h := (((hasDerivAt_id q).neg.mul_const (u:ℂ)).cexp).mul_const (F u)
    convert h using 1 <;> simp [damped,G]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun q u ↦ damped q F u)
    (F' := fun q u ↦ damped q G u) (bound := fun u : ℝ ↦ C*(Real.exp (-u)*u))
    (s := {q : ℂ | D+1 < q.re}) ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp)
    (.of_forall fun q ↦ meas q hc) (damped_integrable hc hf (by linarith : D < p.re))
    (meas p (continuous_ofReal.neg.continuousOn.mul hc)) (bound_integrable := hi)
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)), ∀ q : ℂ, D+1 < q.re →
      ‖damped q G u‖ ≤ C*(Real.exp (-u)*u) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    change 0 < u at hu
    intro q hq
    have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf u hu.le)) (Real.exp_pos _)
    rw [damped_norm]
    simp only [G,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
    calc _ ≤ Real.exp (-q.re*u)*(u*(C*Real.exp (D*u))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf u hu.le) hu.le) (Real.exp_pos _).le
         _ = (C*u)*(Real.exp (-q.re*u)*Real.exp (D*u)) := by ring
         _ ≤ (C*u)*Real.exp (-u) := by
           rw [← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_pos (sub_pos.mpr hq) hu])) (mul_nonneg hC hu.le)
         _ = _ := by ring
  have res := (h hb (ae_of_all _ fun u q _ ↦ hd q u)).2
  have eqn (u : ℝ) : damped p G u = -damped p (fun v ↦ (v:ℂ)*F v) u := by simp [damped,G]
  unfold complexLaplace
  simpa only [eqn,integral_neg] using! res

end
end CubicTheta
