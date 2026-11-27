module

public import PakStokes.PhysicalKummer
public import PakStokes.PhysicalBackground
import all PakStokes.PhysicalBackground
import all PakStokes.PhysicalAiry
import all PakStokes.PhysicalKummer
import all PakStokes.WaveProducts
import all PakStokes.LaplaceWaveJets
import all PakStokes.CubicKummerJets

/-! The Airy correction of the original physical series as a pair of
WaveExpansions. This permits differentiating, multiplying, and regrouping
the physical waves through the same entry points as the coefficient separator. -/
public section
namespace CubicTheta
open Complex Filter Set
open scoped Topology
noncomputable section

namespace WaveExpansion
variable {ι : Type*}

def scale (a : WaveExpansion ι) (C : ℂ) : WaveExpansion ι where
  rate := a.rate
  amplitude := fun i x ↦ C*a.amplitude i x
  loss := a.loss
  budget := fun i ↦ ‖C‖*a.budget i
  re_nonneg := a.re_nonneg
  budget_nonneg := fun i ↦ mul_nonneg (norm_nonneg _) (a.budget_nonneg i)
  summable_budget := a.summable_budget.mul_left _
  bound := by
    filter_upwards [a.bound] with x h i
    simpa [norm_mul,mul_assoc] using mul_le_mul_of_nonneg_left (h i) (norm_nonneg C)

def conjugate (a : WaveExpansion ι) : WaveExpansion ι where
  rate := fun i ↦ star (a.rate i)
  amplitude := fun i x ↦ star (a.amplitude i x)
  loss := a.loss
  budget := a.budget
  re_nonneg := a.re_nonneg
  budget_nonneg := a.budget_nonneg
  summable_budget := a.summable_budget
  bound := by simpa using a.bound

theorem term_scale (a : WaveExpansion ι) (C : ℂ) (x : ℝ) (i : ι) :
    (a.scale C).term x i = C*a.term x i := by simp [scale,term,mul_left_comm]

theorem term_conjugate (a : WaveExpansion ι) (x : ℝ) (i : ι) :
    a.conjugate.term x i = star (a.term x i) := by
  simp [conjugate,term,← Complex.exp_conj]

/-- A uniform positive decay gap gives flatness of the full sum at every
algebraic scale. The single reserved unit absorbs the summable index budget. -/
theorem flat_of_rate_gap (a : WaveExpansion ι) {d : ℝ} (hd : 0 < d)
    (gap : ∀ i, d ≤ (a.rate i).re) (v : ℝ) :
    Tendsto (fun x : ℝ ↦ x^v • a.value x) atTop (𝓝 0) := by
  let B := ∑' i, a.budget i
  have small := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (v+a.loss) d hd).const_mul
    (B*Real.exp d)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ (by simpa using small)
  filter_upwards [a.bound,eventually_gt_atTop (1:ℝ)] with x ha hx
  have xp : 0 < x := lt_trans zero_lt_one hx
  let M := Real.exp (d-d*x)*x^a.loss
  have major (i : ι) : ‖a.term x i‖ ≤ a.budget i*M := by
    simp only [term,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
      ofReal_re,ofReal_im,mul_zero,sub_zero]
    calc _ ≤ Real.exp (-(a.rate i).re*x)*(a.budget i*Real.exp (a.rate i).re*x^a.loss) :=
              mul_le_mul_of_nonneg_left (ha i) (Real.exp_pos _).le
         _ = (a.budget i*x^a.loss)*Real.exp ((a.rate i).re-(a.rate i).re*x) := by
              rw [sub_eq_add_neg,Real.exp_add]; simp only [neg_mul]; ring
         _ ≤ (a.budget i*x^a.loss)*Real.exp (d-d*x) := by
              apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
                (mul_nonneg (a.budget_nonneg i) (pow_nonneg xp.le _))
              nlinarith [mul_nonneg (sub_nonneg.mpr (gap i)) (sub_nonneg.mpr hx.le)]
         _ = _ := by dsimp [M]; ring
  have hs := a.summable_budget.mul_right M
  have hn := Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) major hs
  have h := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum major hs)
  rw [a.summable_budget.tsum_mul_right] at h
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos xp _)]
  apply (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg xp.le v)).trans_eq
  dsimp [B,M]
  rw [Real.rpow_add xp,Real.rpow_natCast,sub_eq_add_neg,Real.exp_add]
  ring

end WaveExpansion

namespace Physical
open LaplaceWave

def alphaConst : ℝ := (3:ℝ)^(1/3:ℝ)
def alphaAt (p : ℝ) := alphaConst/p^(2/3:ℝ)
def lengthScale := 2*Real.pi/alphaConst
def action : ℂ := radialAction*((lengthScale^(3/2:ℝ):ℝ):ℂ)
def coefficient : ℂ := 2*Real.pi*h/alphaConst * airyWaveConstant * ((lengthScale^(-(1/4:ℝ)):ℝ):ℂ)

private theorem alphaPos : 0<alphaConst := by unfold alphaConst; positivity
private theorem lengthPos : 0<lengthScale := div_pos (mul_pos two_pos Real.pi_pos) alphaPos
theorem action_pos : 0<action.re := by
  simp only [action,Complex.mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  exact mul_pos dpos (Real.rpow_pos_of_pos lengthPos _)

private theorem alpha_cube {p : ℝ} (hp : 0<p) : (alphaAt p)^3=3*(1/p^2) := by
  have cube (r s : ℝ) (hr : 0≤r) : (r^s)^3 = r^(s*3) := by
    exact (Real.rpow_mul_natCast hr s 3).symm
  unfold alphaAt alphaConst
  rw [div_pow,cube _ _ (by norm_num),cube _ _ hp.le]; norm_num; ring

theorem physical_mode_scaled {p : ℝ} (hp : 0<p) (n : ℕ+) :
    airyMode (alphaAt p) (2*Real.pi*n) =
      coefficient*kummerTerm action p n + star (coefficient*kummerTerm action p n) := by
  let r := lengthScale*(n:ℝ)*p^(2/3:ℝ)
  have hn : 0 < (n:ℝ) := by exact_mod_cast n.property
  have hr : 0<r := mul_pos (mul_pos lengthPos hn) (Real.rpow_pos_of_pos hp _)
  have rArg : h*(↑(2*Real.pi*(n:ℝ)):ℂ)/↑(alphaAt p) = h*r := by
    unfold r lengthScale alphaAt; push_cast; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have rp (s : ℝ) : r^s = lengthScale^s*(n:ℝ)^s*p^((2/3:ℝ)*s) := by
    unfold r
    rw [Real.mul_rpow (mul_nonneg lengthPos.le hn.le) (Real.rpow_nonneg hp.le _),
      Real.mul_rpow lengthPos.le hn.le,← Real.rpow_mul hp.le]
  have freq : radialAction*((r^(3/2:ℝ):ℝ):ℂ) = cubicRate action n*p := by
    rw [rp]; norm_num [cubicRate,action]; ring
  have fac : kummerFactor radialAction (r^(3/2:ℝ)) = kummerFactor (cubicRate action n) p := by
    unfold kummerFactor
    simp only [mul_assoc (2:ℂ),freq]
  have pref : (2*↑Real.pi*h/(alphaAt p:ℂ))*airyWaveConstant*((r^(-(1/4:ℝ)):ℝ):ℂ) =
      coefficient*modeFactor n*((p^(1/2:ℝ):ℝ):ℂ) := by
    have powers : p^(2/3:ℝ)*p^((2/3:ℝ)*(-(1/4:ℝ))) = p^(1/2:ℝ) := by
      rw [← Real.rpow_add hp]; norm_num
    rw [rp]
    unfold coefficient modeFactor alphaAt
    rw [← powers]; push_cast; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have complexMode : (2*↑Real.pi*h/(alphaAt p:ℂ))*airyContour (h*r) = coefficient*kummerTerm action p n := by
    rw [physical_contour_factor hr,fac]
    unfold radialFrequency kummerTerm
    rw [freq,neg_mul,← neg_mul (cubicRate action n) p]
    linear_combination Complex.exp (-cubicRate action n*p)*kummerFactor (cubicRate action n) p * pref
  unfold airyMode
  rw [rArg,complexMode]
  apply Complex.ext <;> simp <;> ring

def physicalJet (j : ℕ) : WaveExpansion (ℕ+ ⊕ ℕ+) :=
  let a := (kummerJet action action_pos j).scale coefficient
  a.add a.conjugate

def physicalCorrection (p : ℝ) := ∑' m : ℕ+, airyMode (alphaAt p) (2*Real.pi*m)

theorem physicalCorrection_value :
    physicalCorrection =ᶠ[atTop] (physicalJet 0).value := by
  let a := (kummerJet action action_pos 0).scale coefficient
  filter_upwards [eventually_gt_atTop (0:ℝ),a.norm_summable,a.conjugate.norm_summable,a.value_add a.conjugate]
    with p hp hs hc hsum
  change _ = (a.add a.conjugate).value p
  rw [hsum,WaveExpansion.value,WaveExpansion.value,← hs.of_norm.tsum_add hc.of_norm]
  apply tsum_congr; intro n
  rw [physical_mode_scaled hp,WaveExpansion.term_conjugate]
  dsimp only [a]; rw [WaveExpansion.term_scale,kummerJet_term action_pos hp]

private theorem physicalJet_deriv (j : ℕ) {p : ℝ} (hp : 2<p) (i : ℕ+ ⊕ ℕ+) :
    HasDerivAt (fun y ↦ (physicalJet j).term y i) ((physicalJet (j+1)).term p i) p := by
  have h (n : ℕ+) := (kummerJet_term_deriv action_pos j hp n).const_mul coefficient
  cases i with
  | inl n =>
    simpa only [physicalJet,WaveExpansion.term,WaveExpansion.add,Sum.elim_inl,WaveExpansion.scale,
      mul_left_comm] using! h n
  | inr n =>
    change HasDerivAt (fun y ↦ ((kummerJet action action_pos j).scale coefficient).conjugate.term y n)
      (((kummerJet action action_pos (j+1)).scale coefficient).conjugate.term p n) p
    simp only [WaveExpansion.term_conjugate,WaveExpansion.term_scale]
    exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt p (h n)

theorem physicalCorrection_derivatives (j : ℕ) :
    iteratedDeriv j physicalCorrection =ᶠ[atTop] (physicalJet j).value := by
  have h := WaveExpansion.iteratedDeriv_value physicalJet (fun k ↦
    (eventually_gt_atTop (2:ℝ)).mono fun x hx i ↦ physicalJet_deriv k hx i) j
  obtain ⟨L,hL⟩ := eventually_atTop.1 physicalCorrection_value
  filter_upwards [h,eventually_gt_atTop L] with x hh hx
  have near : physicalCorrection =ᶠ[𝓝 x] (physicalJet 0).value :=
    (lt_mem_nhds hx).mono fun y hy ↦ hL y hy.le
  exact (near.iteratedDeriv_eq j).trans hh

theorem cubeSeries_physicalJet :
    ∀ᶠ p : ℝ in atTop,
      (∑' n : ℕ, (Real.exp (-(1/p^2)*(n:ℝ)^3):ℂ)) =
      1/2 + (((1/p^2)^(-(1:ℝ)/3)*Real.Gamma (4/3):ℝ):ℂ) +
      (∑' m : ℕ+, backgroundMode (1/p^2) (2*Real.pi*m)) + (physicalJet 0).value p := by
  filter_upwards [eventually_gt_atTop (0:ℝ),physicalCorrection_value] with p hp he
  rw [← he]
  exact cubeSeries_airy_split (by positivity) (div_pos alphaPos (Real.rpow_pos_of_pos hp _)) (alpha_cube hp)

/-- The residual is defined solely from the original series and the rotated
background. Its derivatives in inverse square-root temperature are the wave jets. -/
def cubeResidual (p : ℝ) : ℂ :=
  (∑' n : ℕ, (Real.exp (-(1/p^2)*(n:ℝ)^3):ℂ)) -
    (1/2 + (((1/p^2)^(-(1:ℝ)/3)*Real.Gamma (4/3):ℝ):ℂ) +
      ∑' m : ℕ+, backgroundMode (1/p^2) (2*Real.pi*m))

theorem cubeResidual_derivatives (j : ℕ) :
    iteratedDeriv j cubeResidual =ᶠ[atTop] (physicalJet j).value := by
  have he : cubeResidual =ᶠ[atTop] physicalCorrection := by
    filter_upwards [cubeSeries_physicalJet,physicalCorrection_value] with p hs hw
    unfold cubeResidual
    rw [hs, hw]; ring
  obtain ⟨L,hL⟩ := eventually_atTop.1 he
  filter_upwards [eventually_gt_atTop L,physicalCorrection_derivatives j] with x hx hd
  have near : cubeResidual =ᶠ[𝓝 x] physicalCorrection :=
    (lt_mem_nhds hx).mono fun y hy ↦ hL y hy.le
  exact (near.iteratedDeriv_eq j).trans hd

theorem cubeResidual_flat (j : ℕ) (v : ℝ) :
    Tendsto (fun p : ℝ ↦ p^v • iteratedDeriv j cubeResidual p) atTop (𝓝 0) := by
  have gap (n : ℕ+) : action.re ≤ (cubicRate action n).re := by
    have hn : 1 ≤ (n:ℝ) := by exact_mod_cast n.property
    have h := Real.one_le_rpow hn (by norm_num : (0:ℝ) ≤ 3/2)
    simpa [cubicRate] using mul_le_mul_of_nonneg_right h action_pos.le
  apply ((physicalJet j).flat_of_rate_gap action_pos (fun i ↦ ?_) v).congr'
  · filter_upwards [cubeResidual_derivatives j] with p hp; rw [hp]
  · rcases i with n|n <;> exact gap n

end Physical
end
end CubicTheta
