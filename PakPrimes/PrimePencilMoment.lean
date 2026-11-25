module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! The positive moments in the balanced residues of the nth-prime pencil.
For every positive exponent a, the defining tail integral gives
x^a E₁(x) ≤ Γ(a). Choosing a = 1/(n+1) supplies an integrable gamma
majorant for the nth moment, including at the logarithmic endpoint.
-/

public section
noncomputable section

namespace PakPrimes.PrimePencil

open MeasureTheory Set Real

/-- The real exponential integral, used below only on the positive ray. -/
@[expose] def Eone (x : ℝ) : ℝ := ∫ t in Ioi x, exp (-t) / t

theorem eone_measurable : Measurable Eone := by
  let f : ℝ × ℝ → ℝ := fun p => if p.1 < p.2 then exp (-p.2) / p.2 else 0
  have hm : Measurable f := by
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (measurable_snd.neg.exp.div measurable_snd) measurable_const
  convert hm.stronglyMeasurable.integral_prod_right' (ν := volume) |>.measurable using 1
  funext x
  rw [Eone, ← integral_indicator measurableSet_Ioi]
  rfl

private theorem eone_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t) / t) (Ioi x) := by
  apply ((integrableOn_exp_neg_Ioi x).div_const x).mono'
      (measurable_id.neg.exp.div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have ht' : x < t := ht
  change ‖exp (-t) / t‖ ≤ exp (-t) / x
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) (hx.trans ht'))]
  exact div_le_div_of_nonneg_left (exp_pos _).le hx ht'.le

private theorem integral_pos_on_ray {x : ℝ} {f : ℝ → ℝ} (h : IntegrableOn f (Ioi x))
    (hf : ∀ t ∈ Ioi x, 0 < f t) : 0 < ∫ t in Ioi x, f t := by
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi x)] f := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht using (hf t ht).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnon h]
  have heq : Function.support f ∩ Ioi x = Ioi x := by
    exact inter_eq_right.mpr fun t ht => (hf t ht).ne'
  rw [heq, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem eone_pos {x : ℝ} (hx : 0 < x) : 0 < Eone x :=
  integral_pos_on_ray (eone_integrable hx) fun _t ht => div_pos (exp_pos _) (hx.trans ht)

theorem eone_gamma_bound {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    x ^ a * Eone x ≤ Gamma a := by
  rw [Eone, ← integral_const_mul, Gamma_eq_integral ha]
  have hg := GammaIntegral_convergent ha
  have hs : Ioi x ⊆ Ioi 0 := Ioi_subset_Ioi hx.le
  apply le_trans (setIntegral_mono_on ((eone_integrable hx).const_mul (x^a))
    (hg.mono_set hs) measurableSet_Ioi ?_)
  · apply setIntegral_mono_set hg _ (Filter.Eventually.of_forall hs)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact mul_nonneg (exp_pos _).le (rpow_nonneg (le_of_lt ht) _)
  · intro t ht
    have ht' : x < t := ht
    rw [rpow_sub_one (hx.trans ht').ne']
    calc
      _ = exp (-t) * (x ^ a / t) := by ring
      _ ≤ _ := by gcongr; exact (hx.trans ht').le

/-- The true, untruncated moment appearing at action n+2. -/
@[expose] def pencilMoment (n : ℕ) : ℝ := ∫ x in Ioi 0, exp (-x) * Eone x ^ n

theorem pencilMoment_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => exp (-x) * Eone x ^ n) (Ioi 0) := by
  let a : ℝ := 1 / (n + 1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hexp : a - 1 = -a * n := by
    dsimp [a]; field_simp; ring
  apply ((GammaIntegral_convergent ha).const_mul ((Gamma a)^n)).mono'
    (measurable_id.neg.exp.mul (eone_measurable.pow_const n)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  change ‖exp (-x) * Eone x ^ n‖ ≤ Gamma a ^ n * (exp (-x) * x ^ (a - 1))
  have hr : Eone x ≤ Gamma a * x ^ (-a) := by
    rw [rpow_neg hx'.le, ← div_eq_mul_inv, le_div_iff₀ (rpow_pos_of_pos hx' _), mul_comm]
    exact eone_gamma_bound hx' ha
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (exp_pos _) (pow_pos (eone_pos hx') n))]
  calc
    _ ≤ exp (-x) * (Gamma a * x ^ (-a)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (eone_pos hx').le hr n) (exp_pos _).le
    _ = _ := by rw [mul_pow, hexp, rpow_mul_natCast hx'.le]; ring

theorem pencilMoment_pos (n : ℕ) : 0 < pencilMoment n :=
  integral_pos_on_ray (pencilMoment_integrable n) fun _x hx =>
    mul_pos (exp_pos _) (pow_pos (eone_pos hx) n)

/-- The all-orders candidate residue, indexed by action n+2. -/
@[expose] def pencilResidue (n : ℕ) : ℝ := ((n : ℝ) + 2) / n.factorial * pencilMoment n

theorem pencilResidue_eq (n : ℕ) :
    pencilResidue n = ((n : ℝ) + 2) / n.factorial * pencilMoment n := rfl

theorem pencilResidue_eq_integral (n : ℕ) :
    pencilResidue n = ((n : ℝ) + 2) / n.factorial *
      ∫ x in Ioi (0 : ℝ), exp (-x) * (∫ t in Ioi x, exp (-t) / t) ^ n := rfl

theorem pencilResidue_pos (n : ℕ) : 0 < pencilResidue n := by
  unfold pencilResidue
  have hp := pencilMoment_pos n
  positivity

@[simp] theorem pencilResidue_zero : pencilResidue 0 = 2 := by
  simp [pencilResidue, pencilMoment, integral_exp_Iic_zero]

end PakPrimes.PrimePencil
end
