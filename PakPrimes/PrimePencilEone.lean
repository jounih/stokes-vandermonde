module

public import PakPrimes.PrimePencilMoment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Local differentiation and the large-distance bound for the exponential
integral in the nth-prime moment argument. -/

public section
noncomputable section
namespace PakPrimes.PrimePencil

open MeasureTheory Set Real Filter
open scoped Topology

private theorem tail_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t) / t) (Ioi x) := by
  apply ((integrableOn_exp_neg_Ioi x).div_const x).mono'
      (measurable_id.neg.exp.div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have ht' : x < t := ht
  change ‖exp (-t) / t‖ ≤ exp (-t) / x
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) (hx.trans ht'))]
  exact div_le_div_of_nonneg_left (exp_pos _).le hx ht'.le

theorem eone_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt Eone (- exp (-x) / x) x := by
  let f : ℝ → ℝ := fun t => exp (-t) / t
  have hm : Measurable f := measurable_id.neg.exp.div measurable_id
  have hc : ContinuousAt f x :=
    (continuousAt_id.neg.rexp).div continuousAt_id hx.ne'
  have hd := intervalIntegral.integral_hasDerivAt_right (a := x) (b := x)
    (f := f) IntervalIntegrable.refl hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  have heq : Eone =ᶠ[𝓝 x] (fun u => Eone x - ∫ t in x..u, f t) := by
    filter_upwards [lt_mem_nhds hx] with u hu
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (tail_integrable hx) (tail_integrable hu)
    change Eone x - Eone u = ∫ t in x..u, f t at h
    linarith
  simpa [f, neg_div] using ((hd.const_sub (Eone x)).congr_of_eventuallyEq heq)

theorem eone_exp_bound {x : ℝ} (hx : 0 < x) : Eone x ≤ exp (-x) / x := by
  unfold Eone
  calc
    _ ≤ ∫ t in Ioi x, exp (-t) / x := by
      apply setIntegral_mono_on (tail_integrable hx) ((integrableOn_exp_neg_Ioi x).div_const x)
        measurableSet_Ioi
      intro t ht
      exact div_le_div_of_nonneg_left (exp_pos _).le hx (le_of_lt ht)
    _ = _ := by rw [integral_div, integral_exp_neg_Ioi]

theorem eone_pow_integrable (n : ℕ) : IntegrableOn (fun x => Eone x ^ (n + 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1), integrableOn_union]
  have hm := eone_measurable.pow_const (n+1)
  constructor
  · apply (((pencilMoment_integrable (n+1)).mono_set Ioc_subset_Ioi_self).const_mul (exp 1)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hle : 1 ≤ exp 1 * exp (-x) := by
      rw [← exp_add, one_le_exp_iff]; linarith [hx.2]
    change ‖Eone x ^ (n+1)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos (eone_pos hx.1) _)]
    calc
      _ ≤ (exp 1 * exp (-x)) * Eone x ^ (n+1) :=
        le_mul_of_one_le_left (pow_pos (eone_pos hx.1) _).le hle
      _ = _ := by ring
  · apply (integrableOn_exp_neg_Ioi 1).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx₁ : (1 : ℝ) < x := hx
    have hx₀ := zero_lt_one.trans hx₁
    have hb : Eone x ≤ exp (-x) := (eone_exp_bound hx₀).trans
      (div_le_self (exp_pos _).le hx₁.le)
    have hu : Eone x ≤ 1 := hb.trans (exp_le_one_iff.mpr (neg_nonpos.mpr hx₀.le))
    change ‖Eone x ^ (n+1)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos (eone_pos hx₀) _), pow_succ]
    exact (mul_le_of_le_one_left (eone_pos hx₀).le (pow_le_one₀ (eone_pos hx₀).le hu)).trans hb

/-- Positive powers make the undeformed Laplace kernel integrable; multiplying
by the rate therefore forces the outgoing primitive to vanish at rate zero. -/
theorem laplace_eone_boundary (n : ℕ) :
    Tendsto (fun a : ℝ => a * ∫ x in Ioi (0 : ℝ), exp (-a * x) * Eone x ^ (n+1))
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun a : ℝ => a * ∫ x in Ioi (0 : ℝ), Eone x ^ (n+1))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    let g : ℝ → ℝ := fun x => exp (-a * x) * Eone x ^ (n+1)
    have hg : ∀ x ∈ Ioi (0:ℝ), ‖g x‖ ≤ Eone x ^ (n+1) := by
      intro x hx
      dsimp [g]
      have hp := pow_pos (eone_pos hx) (n+1)
      rw [abs_of_pos (mul_pos (exp_pos _) hp)]
      exact mul_le_of_le_one_left hp.le (exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hx.le))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos ha']
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm g).trans ?_) ha'.le
    have hint : IntegrableOn g (Ioi 0) := by
      apply (eone_pow_integrable n).mono' (by dsimp [g]; exact ((measurable_const.mul measurable_id).exp.mul (eone_measurable.pow_const _)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx using hg x hx
    exact setIntegral_mono_on hint.norm (eone_pow_integrable n) measurableSet_Ioi hg
  · simpa using (id (α := Tendsto (fun x : ℝ => x) (𝓝[>] (0:ℝ)) (𝓝 0)) nhdsWithin_le_nhds).mul_const
      (∫ x in Ioi (0 : ℝ), Eone x ^ (n+1))

end PakPrimes.PrimePencil
end
