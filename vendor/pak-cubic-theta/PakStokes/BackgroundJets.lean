module

public import PakStokes.BackgroundAnalytic
public import LaplaceDerivative
import all PakStokes.BackgroundContour
import all PakStokes.PhysicalAiry
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Every ordinary derivative of the physical zero-action background is a
combination of two polynomial moments of one analytic Laplace kernel. -/
public section
namespace CubicTheta.Physical.BackgroundInverse
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

def momentKernel (j : ℕ) (v : ℝ) : ℂ := (-v)^j • fullKernel v

theorem momentKernel_analytic (j : ℕ) : AnalyticOnNhd ℝ (momentKernel j) (Ici 0) :=
  fun _ hx ↦ (analyticAt_id.neg.pow j).smul (fullKernel_analytic _ hx)

theorem momentKernel_growth (j : ℕ) : ∃ C : ℝ, ∀ v>0, ‖momentKernel j v‖ ≤ C*Real.exp v := by
  let A := (∑' n, modeBudget n)*kernelConstant
  have ha : 0 ≤ A := by
    apply mul_nonneg (tsum_nonneg (fun _ ↦ by unfold modeBudget; positivity))
    unfold kernelConstant k; positivity
  refine ⟨A*(j+2).factorial,fun v hv ↦ ?_⟩
  have h := fullKernel_bound hv.le
  have bound : ‖fullKernel v‖ ≤ A*v^2 := h.trans_eq (by dsimp [A]; ring)
  have large := Real.pow_div_factorial_le_exp v hv.le (j+2)
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j+2).factorial)] at large
  rw [momentKernel,norm_smul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos hv]
  calc _ ≤ v^j*(A*v^2) := mul_le_mul_of_nonneg_left bound (pow_nonneg hv.le _)
       _ = A*v^(j+2) := by rw [pow_add]; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left large ha).trans_eq (by ring)

def rawMoment (j : ℕ) (p : ℝ) := ∫ v in Ioi (0:ℝ), weighted p (momentKernel j) v

def background (p : ℝ) := ∑' n : ℕ+, backgroundMode (1/p^2) (2*Real.pi*n)

theorem rawMoment_deriv (j : ℕ) {p : ℝ} (hp : 2<p) :
    HasDerivAt (rawMoment j) (rawMoment (j+1) p) p := by
  obtain ⟨C,hC⟩ := momentKernel_growth j
  have hd := rawLaplace_deriv ((momentKernel_analytic j).continuousOn.mono Ioi_subset_Ici_self)
    (D := 1) (by simpa using hC) (x := p) (by linarith)
  convert! hd using 1
  unfold rawMoment
  congr 1; ext v
  simp [weighted,momentKernel,pow_succ,mul_comm,mul_left_comm,mul_assoc]

private theorem background_raw {p : ℝ} (hp : 0<p) : background p = (p:ℂ)*rawMoment 0 p := by
  rw [background,background_eq_raySum hp,raySum_eq_weighted _ hp]
  have hz : momentKernel 0 = fullKernel := funext fun v ↦ by simp [momentKernel]
  simp [rawMoment,hz,Complex.real_smul]

/-- The two moments have adjacent integer powers in the normalized convention.
This formula is for the *original rotated Poisson background* at every order. -/
theorem background_derivatives (j : ℕ) :
    iteratedDeriv (j+1) background =ᶠ[atTop] fun p ↦
      (p:ℂ)*rawMoment (j+1) p + ((j+1:ℕ):ℂ)*rawMoment j p := by
  induction j with
  | zero =>
    filter_upwards [eventually_gt_atTop (2:ℝ)] with p hp
    have he : background =ᶠ[𝓝 p] (fun u : ℝ ↦ (u:ℂ)*rawMoment 0 u) :=
      (lt_mem_nhds (show 0<p by linarith)).mono fun _ hu ↦ background_raw hu
    have h := (Complex.ofRealCLM.hasDerivAt (x := p)).mul (rawMoment_deriv 0 hp)
    rw [Nat.zero_add, iteratedDeriv_one, Nat.cast_one]
    rw [he.deriv_eq]
    change HasDerivAt (fun u : ℝ ↦ (u:ℂ)*rawMoment 0 u) ((1:ℂ)*rawMoment 0 p + (p:ℂ)*rawMoment 1 p) p at h
    simpa [add_comm] using! h.deriv
  | succ j ih =>
    obtain ⟨L,hL⟩ := eventually_atTop.1 ih
    filter_upwards [eventually_gt_atTop L,eventually_gt_atTop (2:ℝ)] with p hL' hp
    have near : iteratedDeriv (j+1) background =ᶠ[𝓝 p] (fun u : ℝ ↦
      (u:ℂ)*rawMoment (j+1) u + ((j+1:ℕ):ℂ)*rawMoment j u) :=
      (lt_mem_nhds hL').mono fun u hu ↦ hL u hu.le
    have h := ((Complex.ofRealCLM.hasDerivAt (x := p)).mul (rawMoment_deriv (j+1) hp)).add
      ((rawMoment_deriv j hp).const_mul ((j+1:ℕ):ℂ))
    rw [iteratedDeriv_succ,near.deriv_eq]
    change HasDerivAt (fun u : ℝ ↦ (u:ℂ)*rawMoment (j+1) u + ((j+1:ℕ):ℂ)*rawMoment j u)
      ((1:ℂ)*rawMoment (j+1) p + (p:ℂ)*rawMoment (j+1+1) p + ((j+1:ℕ):ℂ)*rawMoment (j+1) p) p at h
    rw [h.deriv]; push_cast; ring

theorem rawMoment_normalized (j : ℕ) {p : ℝ} (hp : 0<p) :
    (p:ℂ)*rawMoment j p = raySum (momentKernel j) p := by
  rw [raySum_eq_weighted _ hp]; rfl

end
end CubicTheta.Physical.BackgroundInverse
