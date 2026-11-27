module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A leading-term Watson lemma for a normalized Laplace transform on a ray.
The kernel is complex valued, and may have exponential growth at infinity. -/
set_option maxHeartbeats 1200000
public section
namespace CubicTheta
open Set Real Filter MeasureTheory
open scoped Topology
noncomputable section

@[expose] def raySum (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), exp (-u) • F (u / x)

private theorem moment (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ u in Ioi (0 : ℝ), u^n * exp (-(r*u)) =
      (1/r)^((n:ℝ)+1) * n.factorial := by
  simpa [Gamma_nat_eq_factorial] using
    (integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) hr)

/-- A local factorization and global exponential bound give a global bound
retaining the zero of order n. -/
private theorem factored_bound {F g : ℝ → ℂ} {n : ℕ} {C D : ℝ} (hD : 0 ≤ D)
    (growth : ∀ u > 0, ‖F u‖ ≤ C * exp (D*u)) (hg : ContinuousAt g 0)
    (fac : ∀ᶠ u in 𝓝 0, F u = u^n • g u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u > 0, ‖F u‖ ≤ u^n * (M * exp (D*u)) := by
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp
    (fac.and (hg.norm.eventually (gt_mem_nhds (show ‖g 0‖ < ‖g 0‖+1 by linarith))))
  let M := max (‖g 0‖+1) (C/δ^n)
  have hM : 0 ≤ M := le_trans (by positivity : 0 ≤ ‖g 0‖+1) (le_max_left ..)
  refine ⟨M,hM, fun u hu ↦ ?_⟩
  have he : 1 ≤ exp (D*u) := Real.one_le_exp (mul_nonneg hD hu.le)
  by_cases h : u < δ
  · obtain ⟨hfu,hgu⟩ := hlocal (y := u) (by simpa [Real.dist_eq, abs_of_pos hu] using h)
    rw [hfu, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hu _)]
    exact mul_le_mul_of_nonneg_left
      (hgu.le.trans ((le_max_left ..).trans (le_mul_of_one_le_right hM he))) (pow_nonneg hu.le _)
  · have hscale : C ≤ M * u^n := calc
          C ≤ M * δ^n := (div_le_iff₀ (pow_pos hδ n)).mp (le_max_right ..)
          _ ≤ M * u^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le (le_of_not_gt h) _) hM
    exact (growth u hu).trans (by
      calc C * exp (D*u) ≤ (M*u^n) * exp (D*u) := mul_le_mul_of_nonneg_right hscale (exp_pos _).le
           _ = _ := by ring)

/-- If F(u) starts with u^n g(0), then the first term of its ray sum is n! g(0)/x^n. -/
theorem raySum_leading {F g : ℝ → ℂ} {n : ℕ} {C D : ℝ}
    (cont : ContinuousOn F (Ioi 0)) (hD : 0 ≤ D)
    (growth : ∀ u > 0, ‖F u‖ ≤ C * exp (D*u))
    (hg : ContinuousAt g 0) (fac : ∀ᶠ u in 𝓝 0, F u = u^n • g u) :
    Tendsto (fun x : ℝ ↦ x^n • raySum F x) atTop (𝓝 ((n.factorial : ℝ) • g 0)) := by
  obtain ⟨M,hM,hmajor⟩ := factored_bound hD growth hg fac
  let integrand (x u : ℝ) : ℂ := (x^n * exp (-u)) • F (u/x)
  let bound (u : ℝ) := M * (u^n * exp (-((1/2:ℝ)*u)))
  have hmoment := moment n (r := 1/2) (by norm_num)
  have hi : IntegrableOn (fun u : ℝ ↦ u^n * exp (-((1/2:ℝ)*u))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [hmoment]; positivity)
  have hmeas : ∀ᶠ x : ℝ in atTop, AEStronglyMeasurable (integrand x) (volume.restrict (Ioi 0)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact ((by fun_prop : Continuous (fun u : ℝ ↦ x^n * exp (-u))).continuousOn.smul
      (cont.comp (continuous_id.div_const x).continuousOn (fun _ hu ↦ div_pos hu hx))).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)), ‖integrand x u‖ ≤ bound u := by
    filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (2*D)] with x hx hxD
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    change 0 < u at hu
    have hxpow := pow_pos hx n
    have cancel : x^n * (u/x)^n = u^n := by rw [← mul_pow]; congr 1; field_simp
    have hexp : exp (-u) * exp (D*(u/x)) ≤ exp (-((1/2:ℝ)*u)) := by
      rw [← exp_add, exp_le_exp]
      have hz : D*(u/x) ≤ u/2 := by
        rw [← mul_div_assoc, div_le_iff₀ hx]; nlinarith [mul_le_mul_of_nonneg_right hxD hu.le]
      linarith
    calc ‖integrand x u‖ = (x^n * exp (-u)) * ‖F (u/x)‖ := by
           change ‖(x^n * exp (-u)) • F (u/x)‖ = _
           rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hxpow (exp_pos _))]
         _ ≤ _ := mul_le_mul_of_nonneg_left (hmajor _ (div_pos hu hx)) (mul_pos hxpow (exp_pos _)).le
         _ = M * (u^n * (exp (-u) * exp (D*(u/x)))) := by
           rw [← cancel]; ring
         _ ≤ bound u := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp (pow_nonneg hu.le _)) hM
  have hpoint (u : ℝ) : Tendsto (fun x ↦ integrand x u) atTop
      (𝓝 ((u^n * exp (-u)) • g 0)) := by
    have hux : Tendsto (fun x : ℝ ↦ u/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    apply ((hg.tendsto.comp hux).const_smul (u^n * exp (-u))).congr'
    filter_upwards [hux.eventually fac, eventually_gt_atTop (0:ℝ)] with x he hx
    change (u^n * exp (-u)) • g (u/x) = (x^n * exp (-u)) • F (u/x)
    rw [he, smul_smul, div_pow]
    congr 1
    field_simp
  have h := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound
    (hi.const_mul M) (ae_of_all _ hpoint)
  have hres : ∫ u in Ioi (0:ℝ), (u^n * exp (-u)) • g 0 = (n.factorial : ℝ) • g 0 := by
    rw [integral_smul_const]
    congr 1
    simpa using moment n (r := 1) zero_lt_one
  rw [hres] at h
  apply h.congr
  intro x
  simp only [integrand, ← smul_smul, integral_smul, raySum]

/-- An analytic kernel of exponential growth has either identically zero ray sum
on the positive ray or a first nonzero power-normalized limit. -/
theorem raySum_dichotomy {F : ℝ → ℂ} (hF : AnalyticOnNhd ℝ F (Ici 0))
    {C D : ℝ} (hD : 0 ≤ D) (growth : ∀ u > 0, ‖F u‖ ≤ C * exp (D*u)) :
    (∀ x > 0, raySum F x = 0) ∨ ∃ (n : ℕ) (z : ℂ), z ≠ 0 ∧
      Tendsto (fun x : ℝ ↦ x^n • raySum F x) atTop (𝓝 z) := by
  by_cases hz : ∀ᶠ u in 𝓝 (0 : ℝ), F u = 0
  · left
    have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_Ici (show (0:ℝ) ∈ Ici 0 by simp) hz
    intro x hx
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    simp [hall (div_pos hu hx).le]
  · right
    obtain ⟨n,g,hg,hg0,fac⟩ := (hF 0 (by simp)).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hz
    refine ⟨n,_, smul_ne_zero (by positivity : (n.factorial:ℝ) ≠ 0) hg0, ?_⟩
    exact raySum_leading (hF.continuousOn.mono Ioi_subset_Ici_self) hD growth hg.continuousAt
      (by simpa using fac)
end
end CubicTheta
