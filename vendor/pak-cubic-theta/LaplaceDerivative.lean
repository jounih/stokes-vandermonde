module

public import LaplaceProduct
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Differentiation of an ordinary Laplace transform on its half-line of convergence. -/
public section
namespace CubicTheta
open MeasureTheory Filter Set Real
open scoped Topology
noncomputable section

theorem weighted_integrable {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi 0)) {C D x : ℝ}
    (growth : ∀ u > 0, ‖F u‖ ≤ C * exp (D*u)) (hx : D < x) :
    IntegrableOn (weighted x F) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hx) 0).const_mul C).mono'
  · exact ((by fun_prop : Continuous (fun u : ℝ ↦ exp (-(x*u)))).continuousOn.smul hF).aestronglyMeasurable
      measurableSet_Ioi
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  change ‖exp (-(x*u)) • F u‖ ≤ C * exp ((D-x)*u)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  calc _ ≤ exp (-(x*u)) * (C * exp (D*u)) := mul_le_mul_of_nonneg_left (growth u hu) (exp_pos _).le
       _ = C * (exp (-(x*u)) * exp (D*u)) := by ring
       _ = _ := by rw [← exp_add]; congr 2; ring

/-- On a tail, differentiating the integral replaces F(u) by -u F(u). The
explicit unit of slack is sufficient for every asymptotic germ used here. -/
theorem rawLaplace_deriv {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi 0)) {C D x : ℝ}
    (growth : ∀ u > 0, ‖F u‖ ≤ C * exp (D*u)) (hx : D+1 < x) :
    HasDerivAt (fun y ↦ ∫ u in Ioi (0:ℝ), weighted y F u)
      (∫ u in Ioi (0:ℝ), weighted x (fun v ↦ (-v) • F v) u) x := by
  let F' (y u : ℝ) : ℂ := weighted y (fun v ↦ (-v) • F v) u
  have hmeas (y : ℝ) {G : ℝ → ℂ} (hc : ContinuousOn G (Ioi 0)) :
      AEStronglyMeasurable (weighted y G) (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous (fun u : ℝ ↦ exp (-(y*u)))).continuousOn.smul hc).aestronglyMeasurable measurableSet_Ioi
  have hmajor : IntegrableOn (fun u : ℝ ↦ C*(exp (-u)*u)) (Ioi 0) := by
    simpa only [show (2:ℝ)-1 = 1 by norm_num, rpow_one, IntegrableOn] using! (GammaIntegral_convergent (s := 2) (by norm_num)).const_mul C
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := F') (bound := fun u : ℝ ↦ C*(exp (-u)*u))
    (Ioi_mem_nhds hx) (.of_forall (fun y ↦ hmeas y hF)) (weighted_integrable hF growth (by linarith))
    (hmeas x (continuous_id.neg.continuousOn.smul hF)) ?_ hmajor ?_).2
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    intro y hy
    change 0 < u at hu
    change D+1 < y at hy
    change ‖exp (-(y*u)) • (-u) • F u‖ ≤ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (exp_pos _), abs_neg, abs_of_pos hu]
    calc _ ≤ exp (-(y*u)) * (u * (C * exp (D*u))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (growth u hu) hu.le) (exp_pos _).le
         _ = (C*u) * (exp (-(y*u)) * exp (D*u)) := by ring
         _ ≤ (C*u) * exp (-u) := by
            have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (growth u hu)) (exp_pos _)
            rw [← exp_add]
            exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [mul_pos (sub_pos.mpr hy) hu]))
              (mul_nonneg hC hu.le)
         _ = _ := by ring
  · refine ae_of_all _ (fun u y _ ↦ ?_)
    have h := (((hasDerivAt_id y).mul_const u).neg.exp).smul_const (F u)
    simpa only [weighted, F', id_eq, one_mul, smul_smul, Function.comp_def] using! h

end
end CubicTheta
