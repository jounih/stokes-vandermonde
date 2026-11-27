module

public import LaplaceProduct
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Holomorphic closure of the primitive convolution on a common star-shaped
domain. Integrating on a fixed segment gives a compact parameter space. -/
public section
namespace CubicTheta
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

@[expose] def complexConvolution (F G : ℂ → ℂ) (z : ℂ) :=
  z * ∫ t : ℝ in Ioc 0 1, F (t*z) * G ((1-t:ℝ)*z)

/-- An open common domain stable under contraction toward zero suffices. -/
theorem complexConvolution_analytic {U : Set ℂ} (hU : IsOpen U)
    (star : ∀ z ∈ U, ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*z ∈ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (complexConvolution F G) U := by
  let f (z : ℂ) (t : ℝ) := F (t*z) * G ((1-t:ℝ)*z)
  let D (z : ℂ) (t : ℝ) := deriv F (t*z) * t * G ((1-t:ℝ)*z) +
      F (t*z) * (deriv G ((1-t:ℝ)*z) * (1-t:ℝ))
  let S := U ×ˢ Icc (0:ℝ) 1
  have refl (t : ℝ) (ht : t ∈ Icc 0 1) : 1-t ∈ Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  have m1 : MapsTo (fun p : ℂ × ℝ ↦ (p.2:ℂ)*p.1) S U := fun _ hp ↦ star _ hp.1 _ hp.2
  have m2 : MapsTo (fun p : ℂ × ℝ ↦ ((1-p.2:ℝ):ℂ)*p.1) S U :=
    fun _ hp ↦ star _ hp.1 _ (refl _ hp.2)
  have c1 : Continuous (fun p : ℂ × ℝ ↦ (p.2:ℂ)*p.1) := by fun_prop
  have c2 : Continuous (fun p : ℂ × ℝ ↦ ((1-p.2:ℝ):ℂ)*p.1) := by fun_prop
  have cf : ContinuousOn f.uncurry S := (hF.continuousOn.comp c1.continuousOn m1).mul
    (hG.continuousOn.comp c2.continuousOn m2)
  have cd : ContinuousOn D.uncurry S := by
    exact (((hF.deriv.continuousOn.comp c1.continuousOn m1).mul
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn).mul
      (hG.continuousOn.comp c2.continuousOn m2)).add
      ((hF.continuousOn.comp c1.continuousOn m1).mul
        ((hG.deriv.continuousOn.comp c2.continuousOn m2).mul
          (by fun_prop : Continuous (fun p : ℂ × ℝ ↦ ((1-p.2:ℝ):ℂ))).continuousOn))
  have derivAt (z : ℂ) (hz : z ∈ U) (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (f · t) (D z t) z := by
    have h1 := (hF _ (star z hz t ht)).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul (t:ℂ))
    have h2 := (hG _ (star z hz _ (refl t ht))).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul ((1-t:ℝ):ℂ))
    simpa only [mul_one, Function.comp_def, id_eq, D, f] using! h1.mul h2
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  apply DifferentiableWithinAt.mul differentiableWithinAt_id
  apply DifferentiableAt.differentiableWithinAt
  apply HasFDerivAt.differentiableAt
  apply hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℂ) (F := f)
    (hU.mem_nhds hz) isCompact_Icc measurableSet_Ioc (by simp) Ioc_subset_Icc_self cf
    (fun t ht y hy ↦ (derivAt y hy t ht).differentiableAt.differentiableWithinAt)
  apply ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn cd).congr
  intro p hp
  apply ContinuousLinearMap.ext
  intro y
  rw [fderiv_eq_deriv_mul, (derivAt p.1 hp.1 p.2 hp.2).deriv]
  rfl

theorem complexConvolution_real (F G : ℂ → ℂ) (v : ℝ) :
    complexConvolution F G v = borelProduct (fun t : ℝ ↦ F t) (fun t : ℝ ↦ G t) v := by
  unfold complexConvolution borelProduct
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := 1) (fun t : ℝ ↦ F t * G (v-t)) v
  rw [mul_zero,mul_one] at h
  simp only [Complex.ofReal_sub] at *
  rw [← h]
  change (v:ℂ) * _ = (v:ℂ) * _
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Complex.ofReal_mul, Complex.ofReal_one]
  congr 2 <;> ring

/-- The real kernels passed to the Watson lemma inherit analyticity from the
complex convolution on the shared domain. -/
theorem borelProduct_analytic {U : Set ℂ} (hU : IsOpen U)
    (star : ∀ z ∈ U, ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*z ∈ U)
    (ray : ∀ x : ℝ, 0 ≤ x → (x:ℂ) ∈ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℝ (borelProduct (fun u : ℝ ↦ F u) (fun u : ℝ ↦ G u)) (Ici 0) := by
  have eqn : (fun v : ℝ ↦ complexConvolution F G v) =
      borelProduct (fun u : ℝ ↦ F u) (fun u : ℝ ↦ G u) := funext (complexConvolution_real F G)
  rw [← eqn]
  intro v hv
  exact ((complexConvolution_analytic hU star hF hG) _ (ray v hv)).restrictScalars.comp
    (Complex.ofRealCLM.analyticAt v)

end
end CubicTheta
