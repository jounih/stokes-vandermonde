module

public import PakStokes.PhysicalAiry
import all PakStokes.PhysicalAiry
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute splitting of the physical Airy series. The imaginary term i/b
must be removed before estimating the real part of the background. -/
public section
namespace CubicTheta.Physical
open Complex Real Set MeasureTheory Filter
open scoped FourierTransform
noncomputable section

private theorem re_k_pos : 0 < k.re := by unfold k; simp

/-- Subtracting the exactly imaginary leading mode buys three powers of b. -/
theorem background_bound {t b : ℝ} (ht : 0 < t) (hb : 0 < b) :
    |(I*k*J t (-k*b)).re| ≤ ‖I*k‖ * (t * (1/(k.re*b))^4 * 6) := by
  let a := k.re*b
  have ha : 0 < a := mul_pos re_k_pos hb
  let f (x : ℝ) := Complex.exp ((-k*b)*x)
  let e (x : ℝ) := Real.exp (-t*x^3)
  have neg : (-k*b).re = -a := by simp [a]
  have fInt : IntegrableOn f (Ioi (0:ℝ)) := integrableOn_exp_mul_complex_Ioi (neg ▸ neg_lt_zero.mpr ha) 0
  have normf (x : ℝ) : ‖f x‖ = Real.exp (-(a*x)) := by simp [f,Complex.norm_exp,a]
  have esmall (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) : e x ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos ht (pow_pos hx 3)])
  have prodInt : IntegrableOn (fun x : ℝ ↦ f x*(e x:ℂ)) (Ioi 0) := by
    apply fInt.norm.mono'
    · exact (by unfold f e; fun_prop : Continuous (fun x : ℝ ↦ f x*(e x:ℂ))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    simpa [norm_mul,abs_of_pos (show 0 < e x from Real.exp_pos _)] using
      mul_le_of_le_one_right (norm_nonneg (f x)) (esmall x hx)
  have js : J t (-k*b) = ∫ x in Ioi (0:ℝ), f x*(e x:ℂ) := by
    unfold J; apply setIntegral_congr_fun measurableSet_Ioi; intro x _
    simp only [f,e,Complex.ofReal_exp,← Complex.exp_add]; congr 1; push_cast; ring
  have fi : (∫ x in Ioi (0:ℝ), f x) = 1/(k*b) := by
    rw [show (∫ x in Ioi (0:ℝ), f x) = _ from integral_exp_mul_complex_Ioi
      (a := -k*b) (neg ▸ neg_lt_zero.mpr ha) 0]
    simp
  have kn : k ≠ 0 := fun he ↦ by simpa [he] using re_k_pos
  have bn : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have cancel : (I*k*(1/(k*b))).re = 0 := by
    rw [show I*k*(1/(k*b))=I/b by field_simp]; simp
  have moment : (∫ x in Ioi (0:ℝ), x^3*Real.exp (-(a*x))) = (1/a)^4 * 6 := by
    simpa [show (4:ℝ)-1=3 by norm_num,Real.Gamma_nat_eq_factorial,show Nat.factorial 3=6 by decide] using
      integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (by norm_num) ha
  have mint : IntegrableOn (fun x : ℝ ↦ x^3*Real.exp (-(a*x))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [moment]; positivity)
  have estimate : ‖J t (-k*b)-1/(k*b)‖ ≤ t*(1/a)^4*6 := by
    rw [js,← fi,← integral_sub prodInt fInt]
    have h := norm_integral_le_of_norm_le (mint.const_mul t) (f := fun x ↦ f x*(e x:ℂ)-f x) (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      rw [← mul_sub_one,norm_mul,normf,← ofReal_one,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (esmall x hx))]
      have hlin := Real.add_one_le_exp (-t*x^3)
      change _ ≤ t*(x^3*Real.exp (-(a*x)))
      dsimp only [e]
      nlinarith [mul_le_mul_of_nonneg_left hlin (Real.exp_pos (-(a*x))).le])
    simpa [integral_const_mul,moment,mul_assoc] using h
  rw [← sub_zero (I*k*J t (-k*b)).re,← cancel,← sub_re,← mul_sub]
  exact (abs_re_le_norm _).trans ((norm_mul ..).le.trans (mul_le_mul_of_nonneg_left estimate (norm_nonneg _)))

def backgroundMode (t b : ℝ) : ℂ := ((2*(I*k*J t (-k*b)).re : ℝ) : ℂ)
def airyMode (α b : ℝ) : ℂ := ((2*((2*Real.pi*h/α)*airyContour (h*b/α)).re : ℝ) : ℂ)

theorem background_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ+ ↦ backgroundMode t (2*Real.pi*m)) := by
  let C := 2*‖I*k‖*t*6/(k.re*(2*Real.pi))^4
  have h := (Real.summable_nat_pow_inv.mpr (by decide : 1<4)).subtype (fun n ↦ 0<n)
  apply Summable.of_norm_bounded (h.mul_left C)
  intro m
  have pos : 0 < (m:ℝ) := by exact_mod_cast m.property
  have bound := background_bound ht (mul_pos (mul_pos two_pos Real.pi_pos) pos)
  unfold backgroundMode
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ) ≤ 2)).trans_eq
  change _ = C*((m:ℝ)^4)⁻¹
  dsimp [C]; ring

theorem split_mode {α t : ℝ} (ht : 0 < t) (ha : 0 < α) (cube : α^3=3*t) (w : ℝ) :
    𝓕 (profile t) w = backgroundMode t (2*Real.pi*w)+airyMode α (2*Real.pi*w) := by
  rw [fourier_mode ht ha cube]
  simp [physicalMode,backgroundMode,airyMode,mul_add]

theorem airy_summable {α t : ℝ} (ht : 0 < t) (ha : 0 < α) (cube : α^3=3*t) :
    Summable (fun m : ℕ+ ↦ airyMode α (2*Real.pi*m)) := by
  have hf : Summable (fun n : ℤ ↦ 𝓕 (profile t) n) := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    ((fourier_decay ht).comp_tendsto Int.tendsto_coe_cofinite)
  have nat := (summable_int_iff_summable_nat_and_neg.mp hf).1
  have pos : Summable (fun m : ℕ+ ↦ 𝓕 (profile t) m) := by
    simpa [Function.comp_def] using! nat.subtype (fun n ↦ 0<n)
  apply (pos.sub (background_summable ht)).congr
  intro m
  simp [split_mode ht ha cube]

/-- The original cube series, the gamma pole and the two separately summable
real corrections. The background is given by its absolutely convergent rotated
cubic integrals. -/
theorem cubeSeries_airy_split {α t : ℝ} (ht : 0 < t) (ha : 0 < α) (cube : α^3=3*t) :
    (∑' n : ℕ, (Real.exp (-t*(n:ℝ)^3) : ℂ)) =
    1/2 + ((t^(-(1:ℝ)/3)*Real.Gamma (4/3) : ℝ):ℂ) +
    (∑' m : ℕ+, backgroundMode t (2*Real.pi*m)) +
    ∑' m : ℕ+, airyMode α (2*Real.pi*m) := by
  rw [cubeSeries_airy ht ha cube,zero_mode ht,add_assoc (_ + _),
    ← (background_summable ht).tsum_add (airy_summable ht ha cube)]
  congr 1
  apply tsum_congr
  intro m
  exact (fourier_mode ht ha cube m).symm.trans (split_mode ht ha cube m)


end
end CubicTheta.Physical
