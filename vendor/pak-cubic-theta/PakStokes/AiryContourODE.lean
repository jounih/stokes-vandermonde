module

public import PakStokes.AiryWronskian
import all PakStokes.PhysicalAiry
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The contour side of the Airy comparison on the actual ray X=hr. -/
public section
namespace CubicTheta.Physical
open Set Filter MeasureTheory Complex
open scoped Topology
noncomputable section

private def density (c : ℂ) (x r : ℝ) := Complex.exp (-(r:ℂ)^3/3-c*x*r)
private def leg (c : ℂ) (j : ℕ) (x : ℝ) :=
  ∫ r in Ioi (0:ℝ), (r:ℂ)^j * density c x r

private theorem majorInt (j : ℕ) : IntegrableOn (fun r : ℝ ↦ r^j * Real.exp (-r^3/3)) (Ioi 0) := by
  apply ((moment_integrable (t := 1/3) (by norm_num) j).integrableOn (s := Ioi 0)).congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
  simp [envelope,abs_of_pos (show 0<r from hr)]; ring_nf; simp

private theorem major {c : ℂ} (hc : 0 ≤ c.re) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖(r:ℂ)^j * density c x r‖ ≤ r^j * Real.exp (-r^3/3) := by
  have he : -(r:ℂ)^3/3 = ((-r^3/3:ℝ):ℂ) := by push_cast; rfl
  simp only [density,norm_mul,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos hr,norm_exp,he,sub_re,
    ofReal_re,Complex.mul_re,ofReal_im,mul_zero,sub_zero]
  gcongr
  nlinarith [mul_nonneg (mul_nonneg hc hx) hr.le]

private theorem legInt {c : ℂ} (hc : 0 ≤ c.re) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    IntegrableOn (fun r : ℝ ↦ (r:ℂ)^j * density c x r) (Ioi 0) := by
  apply (majorInt j).mono'
  · exact (by unfold density; fun_prop : Continuous (fun r : ℝ ↦ (r:ℂ)^j * density c x r)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
  exact major hc hx j hr

private theorem legDeriv {c : ℂ} (hc : 0 ≤ c.re) {x : ℝ} (hx : 0<x) (j : ℕ) :
    HasDerivAt (leg c j) (-c*leg c (j+1) x) x := by
  let f (y r : ℝ) := (r:ℂ)^j * density c y r
  let df (y r : ℝ) := -c*((r:ℂ)^(j+1)*density c y r)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := f) (F' := df)
    (bound := fun r : ℝ ↦ ‖c‖*(r^(j+1)*Real.exp (-r^3/3))) (Ioi_mem_nhds hx)
    (eventually_of_mem (Ioi_mem_nhds hx) (fun y hy ↦ (legInt hc (le_of_lt hy) j).aestronglyMeasurable))
    (legInt hc hx.le j) ((legInt hc hx.le (j+1)).aestronglyMeasurable.const_mul (-c))
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr y hy
      simpa [df,norm_mul] using mul_le_mul_of_nonneg_left (major hc (le_of_lt hy) (j+1) hr) (norm_nonneg c))
    ((majorInt (j+1)).const_mul ‖c‖) (by
      apply ae_of_all; intro r y _
      have d := ((((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul c).mul_const (r:ℂ)).const_sub
        (-(r:ℂ)^3/3)).cexp.const_mul ((r:ℂ)^j)
      convert! d using 1; simp [df,density,pow_succ]; ring)
  simpa only [df,integral_const_mul,leg] using! h.2

private theorem legRec {c : ℂ} (hc : 0 ≤ c.re) {x : ℝ} (hx : 0 < x) :
    leg c 2 x + c*x*leg c 0 x = 1 := by
  let f (r : ℝ) := density c x r
  let D (r : ℝ) := -((r:ℂ)^2*f r + c*x*f r)
  have der (r : ℝ) : HasDerivAt f (D r) r := by
    have dr := Complex.ofRealCLM.hasDerivAt (x := r)
    have d := ((((dr.pow 3).neg.div_const (3:ℂ)).sub (dr.const_mul (c*x))).cexp)
    convert! d using 1; simp [D,f,density]; ring
  have it := ((legInt hc hx.le 2).add ((legInt hc hx.le 0).const_mul (c*x))).neg
  simp only [pow_zero,one_mul] at it
  have decay : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r : ℝ ↦ Real.exp (-r))
    · filter_upwards [eventually_ge_atTop (3:ℝ)] with r hr
      have hm := major hc hx.le 0 (show 0 < r by linarith)
      simp only [pow_zero,one_mul] at hm
      apply hm.trans (Real.exp_le_exp.mpr ?_)
      nlinarith [mul_nonneg (by nlinarith [sq_nonneg (r-3)] : 0 ≤ r^2-3) (by linarith : 0 ≤ r)]
    exact Real.tendsto_exp_neg_atTop_nhds_zero
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ ↦ der r) (show IntegrableOn D (Ioi 0) from it) decay
  dsimp only [D] at h
  rw [integral_neg,integral_add (legInt hc hx.le 2)
    (by simpa [f] using! (legInt hc hx.le 0).const_mul (c*x)),integral_const_mul] at h
  simpa [leg,f,density] using congrArg Neg.neg h

private def radialJet (j : ℕ) (x : ℝ) :=
  (upper * (-(h*upper))^j * leg (h*upper) j x -
   lower * (-(h*lower))^j * leg (h*lower) j x) / (2*Real.pi*I)

private theorem upperPos : 0 ≤ (h*upper).re := by rw [roots.1]; unfold k; simp; positivity
private theorem lowerPos : 0 ≤ (h*lower).re := by rw [roots.2.1]; simp

private theorem radialDeriv (j : ℕ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (radialJet j) (radialJet (j+1) x) x := by
  have d := (((legDeriv upperPos hx j).const_mul (upper * (-(h*upper))^j)).sub
    ((legDeriv lowerPos hx j).const_mul (lower * (-(h*lower))^j))).div_const (2*Real.pi*I)
  convert! d using 1; unfold radialJet; rw [pow_succ,pow_succ]; ring

private theorem fromContour (x : ℝ) : airyContour (h*x) = radialJet 0 x := by
  have term (v : ℂ) : J (1/3) (-(h*x)*v) = leg (h*v) 0 x := by
    unfold J leg; apply setIntegral_congr_fun measurableSet_Ioi; intro r _
    simp only [pow_zero,one_mul,density]; congr 1; push_cast; ring
  rw [airyContour,term,term]; simp [radialJet]

theorem physical_contour_ODE {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun y : ℝ ↦ airyContour (h*y)) x = h^3*x*airyContour (h*x) := by
  have funEq := funext fromContour
  rw [funEq,iteratedDeriv_succ,iteratedDeriv_one]
  have eqn : deriv (radialJet 0) =ᶠ[𝓝 x] radialJet 1 :=
    (lt_mem_nhds hx).mono fun y hy ↦ (radialDeriv 0 hy).deriv
  rw [eqn.deriv_eq,(radialDeriv 1 hx).deriv,fromContour]
  have up := eq_sub_of_add_eq (legRec upperPos hx)
  have lo := eq_sub_of_add_eq (legRec lowerPos hx)
  simp only [radialJet,up,lo,pow_zero,mul_one]
  have cu := roots.2.2.1
  have cl := roots.2.2.2
  field_simp
  simp only [mul_comm upper h] at *
  linear_combination (norm := ring_nf)
    (h^2 * (1-h*upper*x*leg (h*upper) 0 x)) * cu -
    (h^2 * (1-h*lower*x*leg (h*lower) 0 x)) * cl

private theorem radialBound (j : ℕ) : IsBoundedUnder (· ≤ ·) atTop (norm ∘ radialJet j) := by
  let M := ∫ r in Ioi (0:ℝ), r^j*Real.exp (-r^3/3)
  let U := upper * (-(h*upper))^j
  let L := lower * (-(h*lower))^j
  refine ⟨(‖U‖*M+‖L‖*M)/‖2*(Real.pi:ℂ)*I‖, eventually_map.2 ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  change ‖(U*leg (h*upper) j x-L*leg (h*lower) j x)/(2*↑Real.pi*I)‖ ≤ _
  have bound {c : ℂ} (hc : 0 ≤ c.re) : ‖leg c j x‖ ≤ M := by
    apply norm_integral_le_of_norm_le (majorInt j)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
    exact major hc hx.le j hr
  rw [norm_div]; apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply (norm_sub_le ..).trans
  simp only [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (bound upperPos) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (bound lowerPos) (norm_nonneg _))

private theorem radialOrigin : Tendsto (radialJet 0) (𝓝[>] 0) (𝓝 (airyContour 0)) := by
  have limit {c : ℂ} (hc : 0 ≤ c.re) : Tendsto (leg c 0) (𝓝[>] 0) (𝓝 (leg c 0 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ (majorInt 0) ?_
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx ↦ (legInt hc (le_of_lt hx) 0).aestronglyMeasurable
    · apply eventually_of_mem self_mem_nhdsWithin; intro x hx
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
      exact major hc (le_of_lt hx) 0 hr
    · apply ae_of_all; intro r
      apply ContinuousAt.continuousWithinAt
      unfold density; fun_prop
  have eqn := fromContour 0
  change Tendsto (fun y ↦ radialJet 0 y) _ _
  simpa [radialJet,show airyContour 0 = radialJet 0 0 by simpa using eqn] using
    (((limit upperPos).const_mul upper).sub ((limit lowerPos).const_mul lower)).div_const (2*(Real.pi:ℂ)*I)

private theorem origin_nonzero : airyContour 0 ≠ 0 := by
  have j : J (1/3) 0 ≠ 0 := by
    rw [zero_mode (by norm_num),Complex.ofReal_ne_zero]; positivity
  have dif : upper-lower ≠ 0 := by
    apply sub_ne_zero.mpr; intro hh
    have eqn := congrArg Complex.im hh
    simp [upper,lower] at eqn
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  simp only [airyContour,neg_zero,zero_mul,← sub_mul]
  exact div_ne_zero (mul_ne_zero dif j) (mul_ne_zero (mul_ne_zero (by norm_num)
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)

/-- Identify a proposed recessive solution with the physical Airy contour.
Only properties of the proposed solution occur in the hypotheses. -/
theorem identify_physical_contour (g g' : ℝ → ℂ)
    (dg : ∀ x > 0, HasDerivAt g (g' x) x)
    (ddg : ∀ x > 0, HasDerivAt g' (h^3*x*g x) x)
    (dec : Tendsto g atTop (𝓝 0)) (dec' : Tendsto g' atTop (𝓝 0))
    (nz : ∀ x > 0, g x ≠ 0) (g0 : Tendsto g (𝓝[>] 0) (𝓝 (airyContour 0))) :
    ∀ (x : ℝ), 0 < x → airyContour (h*x) = g x := by
  intro x hx
  rw [fromContour]
  apply recessive_eq_of_wronskian (fun y ↦ h^3*y) _ (radialJet 1) g g' (fun _ hy ↦ radialDeriv 0 hy)
    ?_ dg ddg (radialBound 0) (radialBound 1) dec dec' nz origin_nonzero radialOrigin g0 x hx
  intro y hy
  have he : deriv (radialJet 0) =ᶠ[𝓝 y] radialJet 1 :=
    (lt_mem_nhds hy).mono fun _ hp ↦ (radialDeriv 0 hp).deriv
  have ode := physical_contour_ODE hy
  rw [funext fromContour,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq,(radialDeriv 1 hy).deriv,fromContour] at ode
  exact ode ▸ radialDeriv 1 hy

end
end CubicTheta.Physical
