module

public import PakStokes.BackgroundJets
public import PakStokes.PhysicalSpectrum
import all PakStokes.BackgroundJets
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalExpression
import all PakStokes.WaveProducts

/-! Feed a polynomial in the regularized *original* cube sum to the
separator by inserting the proven background derivatives at zero action. -/
public section
namespace CubicTheta.Physical
open Set Filter MeasureTheory BackgroundInverse
open scoped Topology
noncomputable section

def regularCube (p : ℝ) : ℂ :=
  (∑' n : ℕ, (Real.exp (-(1/p^2)*(n:ℝ)^3):ℂ)) -
    (1/2 + (((1/p^2)^(-(1:ℝ)/3)*Real.Gamma (4/3):ℝ):ℂ))

private theorem regularCube_split (p : ℝ) : regularCube p = cubeResidual p + background p := by
  unfold regularCube cubeResidual background; ring

private theorem eventually_deriv_congr {f g : ℝ → ℂ} (he : f =ᶠ[atTop] g) :
    ∀ᶠ x in atTop, f =ᶠ[𝓝 x] g := by
  obtain ⟨L,hL⟩ := eventually_atTop.1 he
  exact (eventually_gt_atTop L).mono fun x hx ↦ (lt_mem_nhds hx).mono fun y hy ↦ hL y hy.le

private theorem bg_diff (j : ℕ) : ∀ᶠ p in atTop, DifferentiableAt ℝ (iteratedDeriv j background) p := by
  cases j with
  | zero =>
    filter_upwards [eventually_gt_atTop (2:ℝ)] with p hp
    have he : background =ᶠ[𝓝 p] (fun u : ℝ ↦ (u:ℂ)*rawMoment 0 u) :=
      (lt_mem_nhds (show 0<p by linarith)).mono fun _ hu ↦ background_raw hu
    simpa using ((Complex.ofRealCLM.differentiableAt).mul (rawMoment_deriv 0 hp).differentiableAt).congr_of_eventuallyEq he
  | succ j =>
    filter_upwards [eventually_deriv_congr (background_derivatives j),eventually_gt_atTop (2:ℝ)] with p he hp
    exact (((Complex.ofRealCLM.differentiableAt).mul (rawMoment_deriv (j+1) hp).differentiableAt).add
      ((rawMoment_deriv j hp).differentiableAt.const_mul _)).congr_of_eventuallyEq he

private theorem residual_diff (j : ℕ) : ∀ᶠ p in atTop, DifferentiableAt ℝ (iteratedDeriv j cubeResidual) p := by
  have h := (physicalJet j).hasDerivAt_value (physicalJet (j+1))
    ((eventually_gt_atTop (2:ℝ)).mono fun _ hx i ↦ physicalJet_deriv j hx i)
  filter_upwards [h,eventually_deriv_congr (cubeResidual_derivatives j)] with p hd he
  exact hd.differentiableAt.congr_of_eventuallyEq he

theorem regularCube_derivatives (j : ℕ) :
    ∀ᶠ p in atTop, iteratedDeriv j regularCube p =
      iteratedDeriv j cubeResidual p + iteratedDeriv j background p := by
  induction j with
  | zero => simp [regularCube_split]
  | succ j ih =>
    filter_upwards [eventually_deriv_congr ih,residual_diff j,bg_diff j] with p he hr hb
    simp only [iteratedDeriv_succ]
    exact he.deriv_eq.trans (hr.hasDerivAt.add hb.hasDerivAt).deriv

private def cost (j : ℕ) := ∫ v in Ioi (0:ℝ), ‖weighted 2 (momentKernel j) v‖

private theorem cost_nonneg (j : ℕ) : 0 ≤ cost j := integral_nonneg (fun _ ↦ norm_nonneg _)

private theorem rawMoment_bound (j : ℕ) {p : ℝ} (hp : 2≤p) : ‖rawMoment j p‖ ≤ cost j := by
  obtain ⟨C,hC⟩ := momentKernel_growth j
  have hi := weighted_integrable ((momentKernel_analytic j).continuousOn.mono Ioi_subset_Ici_self)
    (D := 1) (by simpa using hC) (x := 2) (by norm_num)
  apply norm_integral_le_of_norm_le hi.norm
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  simp only [weighted,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right hp (le_of_lt hv))

private def bgCost : ℕ → ℝ
  | 0 => cost 0
  | j+1 => cost (j+1) + (j+1)*cost j

private theorem bgCost_nonneg (j : ℕ) : 0≤bgCost j := by
  cases j with
  | zero => exact cost_nonneg 0
  | succ j => exact add_nonneg (cost_nonneg _) (mul_nonneg (by positivity) (cost_nonneg _))

private theorem bgBound (j : ℕ) : ∀ᶠ p : ℝ in atTop, ‖iteratedDeriv j background p‖ ≤ bgCost j*p := by
  cases j with
  | zero =>
    filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
    have h := rawMoment_bound 0 hp
    simp only [iteratedDeriv_zero,background_raw (show 0<p by linarith),norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0≤p by linarith),bgCost]
    linarith [mul_le_mul_of_nonneg_left h (show 0≤p by linarith)]
  | succ j =>
    filter_upwards [background_derivatives j,eventually_ge_atTop (2:ℝ)] with p h hp
    rw [h]; apply (norm_add_le ..).trans
    have hp' : 0≤p := by linarith
    simp only [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp',bgCost]
    have a := mul_le_mul_of_nonneg_left (rawMoment_bound (j+1) hp) hp'
    have b := mul_le_mul_of_nonneg_left (rawMoment_bound j hp) (show (0:ℝ)≤(j+1:ℕ) by positivity)
    push_cast at *
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ j+1 by positivity) (cost_nonneg j)) (show 0≤p-1 by linarith)]

def backgroundCoefficient (j : ℕ) : RayCoefficient where
  value := iteratedDeriv j background
  budget := bgCost j
  loss := 1
  nonneg := bgCost_nonneg j
  bound := by simpa using bgBound j

namespace JetExpression

def withBackground : JetExpression → JetExpression
  | .coeff a => .coeff a
  | .jet j => .add (.jet j) (.coeff (backgroundCoefficient j))
  | .add a b => .add a.withBackground b.withBackground
  | .mul a b => .mul a.withBackground b.withBackground

def evalRegular : JetExpression → ℝ → ℂ
  | .coeff a => a.value
  | .jet j => iteratedDeriv j regularCube
  | .add a b => fun x ↦ a.evalRegular x + b.evalRegular x
  | .mul a b => fun x ↦ a.evalRegular x * b.evalRegular x

theorem withBackground_eval (e : JetExpression) :
    e.withBackground.eval =ᶠ[atTop] e.evalRegular := by
  induction e with
  | coeff a => rfl
  | jet j => exact (regularCube_derivatives j).mono fun _ h ↦ h.symm
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb

end JetExpression
end
end CubicTheta.Physical
