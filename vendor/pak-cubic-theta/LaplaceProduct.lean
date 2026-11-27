module

public import Laplace
public import Mathlib.Analysis.Convolution

/-! Multiplication of normalized Laplace transforms requires one power of x.
Using the primitive convolution avoids differentiating an endpoint singularity. -/
public section
namespace CubicTheta
open Real MeasureTheory Set
noncomputable section

@[expose] def borelProduct (F G : ℝ → ℂ) (v : ℝ) := ∫ t in 0..v, F t * G (v-t)

@[expose] def weighted (x : ℝ) (F : ℝ → ℂ) (u : ℝ) := exp (-(x*u)) • F u

theorem raySum_eq_weighted (F : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    raySum F x = x • ∫ u in Ioi (0:ℝ), weighted x F u := by
  have h := integral_comp_mul_left_Ioi' (fun v : ℝ ↦ exp (-v) • F (v/x)) 0 hx
  simpa only [mul_zero, mul_div_cancel_left₀ _ hx.ne', raySum, weighted] using h.symm

theorem raySum_product (F G : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hF : IntegrableOn (weighted x F) (Ioi 0))
    (hG : IntegrableOn (weighted x G) (Ioi 0)) :
    raySum F x * raySum G x = x • raySum (borelProduct F G) x := by
  have h := integral_posConvolution hF hG (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have inner (v : ℝ) : (∫ t in 0..v, weighted x F t * weighted x G (v-t)) =
      weighted x (borelProduct F G) v := by
    unfold weighted borelProduct
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    have he : exp (-(x*v)) = exp (-(x*t)) * exp (-(x*(v-t))) := by
      rw [← exp_add]; congr 1; ring
    change ((exp (-(x*t)) : ℂ) * F t) * ((exp (-(x*(v-t))) : ℂ) * G (v-t)) =
      (exp (-(x*v)) : ℂ) * (F t * G (v-t))
    rw [he, Complex.ofReal_mul]; ring
  simp_rw [inner] at h
  rw [raySum_eq_weighted F hx, raySum_eq_weighted G hx, raySum_eq_weighted _ hx,
    smul_mul_assoc, mul_smul_comm, ← h]

/-- A one-unit increase in exponential type absorbs the length of the convolution interval. -/
theorem borelProduct_bound {F G : ℝ → ℂ} {C E D : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hF : ∀ u ≥ 0, ‖F u‖ ≤ C * exp (D*u)) (hG : ∀ u ≥ 0, ‖G u‖ ≤ E * exp (D*u))
    {v : ℝ} (hv : 0 ≤ v) : ‖borelProduct F G v‖ ≤ C * E * exp ((D+1)*v) := by
  have hle (u : ℝ) (hu : u ∈ uIoc 0 v) : ‖F u * G (v-u)‖ ≤ C*E*exp (D*v) := by
    rw [uIoc_of_le hv] at hu
    rw [norm_mul]
    calc _ ≤ (C*exp (D*u))*(E*exp (D*(v-u))) :=
           mul_le_mul (hF u hu.1.le) (hG _ (sub_nonneg.mpr hu.2)) (norm_nonneg _) (by positivity)
         _ = C*E*(exp (D*u)*exp (D*(v-u))) := by ring
         _ = _ := by rw [← exp_add]; congr 2; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
  rw [sub_zero,abs_of_nonneg hv] at h
  apply h.trans
  rw [add_mul, one_mul, exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_trans (by linarith : v ≤ v+1) (add_one_le_exp v)) (by positivity)

end
end CubicTheta
